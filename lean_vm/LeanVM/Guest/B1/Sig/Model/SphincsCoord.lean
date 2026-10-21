/-
  LeanVM.Guest.B1.Sig.Model.SphincsCoord

  One coordinate of the leanSPHINCS forest under a hash model (`SphincsCoord` over `M.sem`): the
  sub-trees' forest keys and folds, the super-child and the top fold, sound for `coordRecover` run
  in `Option` with the model's answered hash.
-/

module

public import LeanVM.Guest.B1.Sig.Model.SphincsKey
public import LeanVM.Guest.B1.Sig.Model.SphincsFold

/-!
# A coordinate of the forest under a hash model

| deployed | here |
|---|---|
| `sSub_sound_w` | `sSub_model` |
| `sp_subTops`, `sp_topTops` | `sp_subTopsW`, `sp_topTopsW` |
| `sCoordT_sound_w`, `sCoord_sound_w`, `sCoords_sound_w` | `sCoordT_model`, `sCoord_model`, `sCoords_model` |

The forest keys are a callee's (`sp_forest_key__L{t}`): the lemmas take `FkSoundWWith M C wfk`, the
deployed `FkSoundW` with the key's leaf answered.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {M : HashModel} {C : CallRel} {rd : Reader}

theorem holdsListB_cons_dispatch (x : V) (fs : List String) (args rets : List V) (ss : List Stmt) (next : Prop)
    (kret : List E → Prop) (σ : Val) :
    Stmt.HoldsListB M.sem C rd σ (.dispatch x fs args rets :: ss) next kret ↔
      (∃ (j : Nat) (h : j < fs.length), σ x = ofK (gpow j) ∧ C fs[j] (args.map σ) (rets.map σ)) ∧
        Stmt.HoldsListB M.sem C rd σ ss next kret := Iff.rfl

/-- **A sub-tree under a model** (`sSub_sound_w`): the forest key of codeword `t` from the chain
values `subVals`, answered, folded up two levels at the key `a` along `subSibs`, lands in the
output the key's top bit names; the other output is `subSibs`' top node; the codeword's cell is
`t`; the bound gains the key's field. -/
theorem sSub_model {wfk : List E → List E → Nat → E} (hfk : FkSoundWWith M C wfk) {σ : Val}
    (hmd : σ (.n 3) = mdw 64 true) {c j : Nat} {subAt bound : V} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (sSub c j subAt bound b).1 next kret) :
    (∃ t < 256, ∃ a < 8, selIdx (σ (.n b)) 0 8 = a ∧ σ (.n (b + 1)) = word (a * 2 ^ 40) 0 0 ∧
      σ (sSub c j subAt bound b).2.2.1 = word t 0 0 ∧
      (∃ leaf, FkLeafWith M.H t (σ (.n 1)) (σ subAt + word (a * 2 ^ 40) 0 0) (subVals wfk σ b) leaf ∧
        mFoldWith M.H (σ (.n 1)) (foldAddr σ subAt subFoldT a) (fun l => a.testBit l) (subSibs σ b) 2 0 leaf =
          some (σ ((sSub c j subAt bound b).2.2.2.1 (2 * (a / 4))))) ∧
      σ ((sSub c j subAt bound b).2.2.2.1 (2 - 2 * (a / 4))) = subSibs σ b 2 ∧
      σ (sSub c j subAt bound b).2.2.2.2 = σ bound + lit (a * 2 ^ (58 + 3 * (2 * c + j)))) ∧ next := by
  simp only [sSub, hintW, rangeS, cst, addS, List.cons_append, List.nil_append, holdsListB_cons_atom,
    Atom.HoldsB, true_and] at h
  obtain ⟨-, -, -, -, hadd, h⟩ := h
  obtain ⟨⟨t, ht, -, hC⟩, h⟩ := (holdsListB_cons_dispatch _ _ _ _ _ _ _ _).mp h
  rw [fkNames_length] at ht
  obtain ⟨ka, pp, hargs, leaf, hleaf, hrets⟩ :=
    hfk t ht _ _ (by rw [List.getD_eq_getElem _ _ (by rw [fkNames_length]; exact ht)]; exact hC)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hargs
  have hr1 : σ (.n (b + 12)) = leaf := (List.cons.inj hrets).1
  have hr2 : σ (.n (b + 13)) = word t 0 0 := (List.cons.inj (List.cons.inj hrets).2).1
  obtain ⟨a, ha, hsel, -, hs, h1, h2, h⟩ := spMatch_model hmd (by decide) (by norm_num) h
  simp only [holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB] at h
  obtain ⟨hb, hn⟩ := h
  refine ⟨⟨t, ht, a, ha, hsel, h1, hr2, ⟨leaf, ?_, ?_⟩, ?_, ?_⟩, hn⟩
  · rw [← hargs.1, ← hargs.2, hadd, h1] at hleaf
    exact hleaf
  · have e : a / 2 ^ (subFoldT.height - 1) = a / 4 := rfl
    rw [e, hr1] at hs
    refine (mFoldWith_congr _ _ _ _ 2 0 (fun l _ hl => ?_) _).trans hs
    simp only [subSibs, hsel, show l ≠ 2 by omega, ↓reduceIte]
  · show σ (spOut subFoldT (b + 14) (2 - 2 * (a / 4))) = subSibs σ b 2
    simp only [subSibs, hsel, ↓reduceIte]
  · exact hb.trans (by rw [h2])

section Scheme

open Sphincs Sphincs.Concrete

variable {inst : HasQuery Sphincs.HashSpec Option}

/-- **A sub-tree's two top nodes in the scheme, answered** (`sp_subTops`). -/
theorem sp_subTopsW (hq : SQW M.H inst) {pp : E} (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (t : LutIdx) (vals sibs : Nat → E) {leaf x y : E}
    (hleaf : FkLeafWith M.H t.val pp (eOfNat (fpos index.val c.val s.val j.val a.val)) vals leaf)
    (hx : mFoldWith M.H pp (fun l => eOfNat (fpos index.val c.val s.val j.val 0) + word (subFoldT.addr a.val l) 0 0)
        (fun l => a.val.testBit l) sibs 2 0 leaf = some (if a.val / 4 = 0 then x else y))
    (hy : (if a.val / 4 = 0 then y else x) = sibs 2) :
    @childRecover Option _ inst (spp pp) index c s j a (lut t) (fun i => sv (vals i.val)) = some (sv leaf) ∧
      @subFold Option _ inst (spp pp) index c s j a (fun l => sv (sibs l.val)) (subHeight - 1) (sv leaf) =
        some (sv (if a.val / 4 = 0 then x else y)) ∧
      orderTops (a.val.testBit (subHeight - 1)) (sv (if a.val / 4 = 0 then x else y)) (sv (sibs 2)) = (sv x, sv y) := by
  obtain ⟨ends, hends, o, ho, rfl⟩ := hleaf
  refine ⟨?_, ?_, ?_⟩
  · refine sChildRecover_cellsW hq (ka := eOfNat (fpos index.val c.val s.val j.val a.val)) (lut t) vals ends
      (fchain_addr index c s j a) (childLeaf_addr index c s j a) (fun k hk => ?_) ho
    have := hends k hk
    rw [fEndsWith, show (⟨k % 6, Nat.mod_lt _ (by norm_num)⟩ : FChain) = ⟨k, hk⟩ from Fin.ext (Nat.mod_eq_of_lt hk),
      ← spCode_lut t.isLt ⟨k, hk⟩]
    exact this
  · exact sSubFold_cellsW hq (A := fun l => eOfNat (fpos index.val c.val s.val j.val 0) + word (subFoldT.addr a.val l) 0 0)
      (fun l node hn => subNode_addr index c s j a l node hn) sibs (subHeight - 1) (by decide) _ hx
  · rw [← hy, orderTops_sv, show subHeight - 1 = 2 from rfl, testBit_top (show a.val < 2 ^ (2 + 1) from a.isLt)]
    have ha : a.val / 4 = 0 ∨ a.val / 4 = 1 := by have := a.isLt; simp only [subHeight] at this; omega
    rcases ha with h | h <;> simp [h]

/-- **A coordinate's two top nodes in the scheme, answered** (`sp_topTops`). -/
theorem sp_topTopsW (hq : SQW M.H inst) {pp : E} (index : Index) (c : Coord) (s : SuperIdx) (tsibs : Nat → E)
    {x y sup : E}
    (hx : mFoldWith M.H pp (fun l => eOfNat (fpos index.val c.val 0 0 0) + word (topFoldT.addr s.val l) 0 0)
        (fun l => s.val.testBit l) tsibs 3 0 sup = some (if s.val / 8 = 0 then x else y))
    (hy : (if s.val / 8 = 0 then y else x) = tsibs 3) :
    @topFold Option _ inst (spp pp) index c s (fun l => sv (tsibs l.val)) (topHeight - 1) (sv sup) =
        some (sv (if s.val / 8 = 0 then x else y)) ∧
      orderTops (s.val.testBit (topHeight - 1)) (sv (if s.val / 8 = 0 then x else y)) (sv (tsibs 3)) = (sv x, sv y) := by
  refine ⟨sTopFold_cellsW hq (A := fun l => eOfNat (fpos index.val c.val 0 0 0) + word (topFoldT.addr s.val l) 0 0)
      (fun l node hn => topNode_addr index c s l node hn) tsibs (topHeight - 1) (by decide) _ hx, ?_⟩
  rw [← hy, orderTops_sv, show topHeight - 1 = 3 from rfl, testBit_top (show s.val < 2 ^ (3 + 1) from s.isLt)]
  have hs : s.val / 8 = 0 ∨ s.val / 8 = 1 := by have := s.isLt; simp only [topHeight] at this; omega
  rcases hs with h | h <;> simp [h]

/-- **A coordinate under a model** (after its tree's address; `sCoordT_sound_w`): with the opening
`coordOpeningT`, the scheme's two top nodes of a mark land in its outputs, every hash answered. -/
theorem sCoordT_model (hq : SQW M.H inst) {wfk : List E → List E → Nat → E} (hfk : FkSoundWWith M C wfk) {σ : Val}
    (hmd : σ (.n 3) = mdw 64 true) (index : Index) (c : Coord) {bound treeAt : V} {b0 : Nat}
    (htree : σ treeAt = eOfNat (fpos index.val c.val 0 0 0)) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (sCoordT c.val bound treeAt b0).1 next kret) :
    (∃ mark : CoordMark,
      @coordRecover Option _ inst (spp (σ (.n 1))) index c mark (coordOpeningT wfk σ c.val bound b0) =
        some (sv (σ (sCoordT c.val bound treeAt b0).2.2.2.1.1), sv (σ (sCoordT c.val bound treeAt b0).2.2.2.1.2)) ∧
      σ (sCoordT c.val bound treeAt b0).2.2.1.1 = word (mark.word 0).val 0 0 ∧
      σ (sCoordT c.val bound treeAt b0).2.2.1.2 = word (mark.word 1).val 0 0 ∧
      σ (sCoordT c.val bound treeAt b0).2.2.2.2 = σ bound + lit ((mark.child 0).val * 2 ^ (58 + 3 * (2 * c.val))) +
        lit ((mark.child 1).val * 2 ^ (58 + 3 * (2 * c.val + 1))) + lit (mark.super.val * 2 ^ (26 + 4 * c.val))) ∧
      next := by
  simp only [sCoordT] at h ⊢
  simp only [List.append_assoc, List.cons_append, List.nil_append, holdsListB_append, hintW, rangeS, cst,
    addS, ivs, b2s, holdsListB_cons_atom, Atom.HoldsB, true_and] at h
  obtain ⟨-, -, hleaf, h⟩ := h
  obtain ⟨⟨t0, ht0, a0, ha0, -, hk0, hw0, ⟨lf0, hlf0, ho0⟩, hy0, hb0⟩, h⟩ := sSub_model hfk hmd h
  obtain ⟨hb1, hsub1, h⟩ := h
  obtain ⟨⟨t1, ht1, a1, ha1, -, hk1, hw1, ⟨lf1, hlf1, ho1⟩, hy1, hb1'⟩, h⟩ := sSub_model hfk hmd h
  obtain ⟨hf0, hf1, hiv0, hiv1, hmd4, hc1, h7, h8, hmd9, hc2, h⟩ := h
  obtain ⟨s, hs, hsels, -, hts, hr1, hr2, h⟩ := spMatch_model hmd (by decide) (by norm_num) h
  simp only [holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB] at h
  obtain ⟨hbound, hn⟩ := h
  have hop : coordOpeningT wfk σ c.val bound b0 = ⟨![subOpening wfk σ (b0 + 7),
      subOpening wfk σ ((sSub c.val 0 (.n (b0 + 6)) bound (b0 + 7)).2.1 + 2)],
      fun l => sv (topSibs σ (sSub c.val 1 (.n ((sSub c.val 0 (.n (b0 + 6)) bound (b0 + 7)).2.1 + 1))
        (sSub c.val 0 (.n (b0 + 6)) bound (b0 + 7)).2.2.2.2 ((sSub c.val 0 (.n (b0 + 6)) bound (b0 + 7)).2.1 + 2)).2.1
        b0 l.val)⟩ := rfl
  generalize sSub c.val 0 (.n (b0 + 6)) bound (b0 + 7) = S0 at *
  generalize sSub c.val 1 (.n (S0.2.1 + 1)) S0.2.2.2.2 (S0.2.1 + 2) = S1 at *
  have hi := index.isLt
  have hc := c.isLt
  simp only [totalHeight, forestCoords] at hi hc
  let sF : SuperIdx := ⟨s, hs⟩
  let a0F : ChildIdx := ⟨a0, ha0⟩
  let a1F : ChildIdx := ⟨a1, ha1⟩
  let t0F : LutIdx := ⟨t0, ht0⟩
  let t1F : LutIdx := ⟨t1, ht1⟩
  have hLeaf : σ (.n (b0 + 6)) = eOfNat (fpos index.val c.val s 0 0) := by
    rw [hleaf, htree, hr1, show s * 2 ^ 35 = 2 ^ 35 * s by ring, sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  have hSub1 : σ (.n (S0.2.1 + 1)) = eOfNat (fpos index.val c.val s 1 0) := by
    rw [hsub1, hLeaf, hb1, show (2 : Nat) ^ 39 = 2 ^ 39 * 1 by ring, sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  have hKey0 : σ (.n (b0 + 6)) + word (a0 * 2 ^ 40) 0 0 = eOfNat (fpos index.val c.val s 0 a0) := by
    rw [hLeaf, show a0 * 2 ^ 40 = 2 ^ 40 * a0 by ring, sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  have hKey1 : σ (.n (S0.2.1 + 1)) + word (a1 * 2 ^ 40) 0 0 = eOfNat (fpos index.val c.val s 1 a1) := by
    rw [hSub1, show a1 * 2 ^ 40 = 2 ^ 40 * a1 by ring, sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  have hA0 : foldAddr σ (.n (b0 + 6)) subFoldT a0 =
      fun l => eOfNat (fpos index.val c.val s 0 0) + word (subFoldT.addr a0 l) 0 0 := by
    funext l; rw [foldAddr, hLeaf]
  have hA1 : foldAddr σ (.n (S0.2.1 + 1)) subFoldT a1 =
      fun l => eOfNat (fpos index.val c.val s 1 0) + word (subFoldT.addr a1 l) 0 0 := by
    funext l; rw [foldAddr, hSub1]
  have hAT : foldAddr σ treeAt topFoldT s = fun l => eOfNat (fpos index.val c.val 0 0 0) + word (topFoldT.addr s l) 0 0 := by
    funext l; rw [foldAddr, htree]
  rw [hKey0] at hlf0
  rw [hKey1] at hlf1
  rw [hA0] at ho0
  rw [hA1] at ho1
  rw [hAT, show s / 2 ^ (topFoldT.height - 1) = s / 8 from rfl] at hts
  -- the super-child
  have hiv1' : σ (.n (S1.2.1 + 3)) = iv1 := hiv1
  rw [hiv0, hiv1', hmd4] at hc1
  rw [h7, h8, hmd9, word_zero] at hc2
  have hr32 : ([σ (S1.2.2.2.1 0), σ (S1.2.2.2.1 2)].flatMap cellBytes).length = 32 := by
    rw [length_flatMap_cellBytes']; rfl
  have hc2' : M.sem.check ![σ (S1.2.2.2.1 0), σ (S1.2.2.2.1 2), 0, 0] (σ (.n (S1.2.1 + 5)))
      (σ (.n (S1.2.1 + 6))) (σ (.n (S1.2.1 + 10))) (σ (.n (S1.2.1 + 11)))
      (mdw (64 + ([σ (S1.2.2.2.1 0), σ (S1.2.2.2.1 2)].flatMap cellBytes).length) true) := by rw [hr32]; exact hc2
  obtain ⟨-, -, -, hsup⟩ := compress_two_model (M := M) (blockBytes_two _ _) (by rw [hr32]; omega)
    (by rw [hr32]; omega) hc1 hc2'
  have hsup' : hcellWith M.H [σ (.n 1), eOfNat (fpos index.val c.val s 0 0) + word (tw 18) 0 0,
      σ (S0.2.2.2.1 0), σ (S0.2.2.2.1 2), σ (S1.2.2.2.1 0), σ (S1.2.2.2.1 2)] =
      some (σ (.n (S1.2.1 + 10)), σ (.n (S1.2.1 + 11))) := by
    rw [hcellWith, ← hsup, blockBytes_four, ← List.flatMap_append, hf1, hLeaf, hf0]
    rfl
  -- the mark and the opening
  let mark : CoordMark := ⟨sF, ![a0F, a1F], ![t0F, t1F]⟩
  have ha0' : a0 / 4 = 0 ∨ a0 / 4 = 1 := by omega
  have ha1' : a1 / 4 = 0 ∨ a1 / 4 = 1 := by omega
  have hs' : s / 8 = 0 ∨ s / 8 = 1 := by omega
  have e0 : σ (S0.2.2.2.1 (2 * (a0 / 4))) =
      (if a0F.val / 4 = 0 then σ (S0.2.2.2.1 0) else σ (S0.2.2.2.1 2)) := by
    rcases ha0' with h | h <;> simp [h, a0F]
  have e0' : σ (S0.2.2.2.1 (2 - 2 * (a0 / 4))) =
      (if a0F.val / 4 = 0 then σ (S0.2.2.2.1 2) else σ (S0.2.2.2.1 0)) := by
    rcases ha0' with h | h <;> simp [h, a0F]
  have e1 : σ (S1.2.2.2.1 (2 * (a1 / 4))) =
      (if a1F.val / 4 = 0 then σ (S1.2.2.2.1 0) else σ (S1.2.2.2.1 2)) := by
    rcases ha1' with h | h <;> simp [h, a1F]
  have e1' : σ (S1.2.2.2.1 (2 - 2 * (a1 / 4))) =
      (if a1F.val / 4 = 0 then σ (S1.2.2.2.1 2) else σ (S1.2.2.2.1 0)) := by
    rcases ha1' with h | h <;> simp [h, a1F]
  rw [e0] at ho0
  rw [e0'] at hy0
  rw [e1] at ho1
  rw [e1'] at hy1
  obtain ⟨hl0, hn0, ht0'⟩ := sp_subTopsW (inst := inst) hq index c sF 0 a0F t0F (subVals wfk σ (b0 + 7))
    (subSibs σ (b0 + 7)) hlf0 ho0 hy0
  obtain ⟨hl1, hn1, ht1'⟩ := sp_subTopsW (inst := inst) hq index c sF 1 a1F t1F (subVals wfk σ (S0.2.1 + 2))
    (subSibs σ (S0.2.1 + 2)) hlf1 ho1 hy1
  refine ⟨⟨mark, ?_, hw0, hw1, ?_⟩, hn⟩
  · rw [hop]
    have hsupH := sSuperHash_cellsW (inst := inst) hq (superChild_addr index c sF) hsup'
    have hT : (fun j : SubIdx => orderTops ((mark.child j).val.testBit (subHeight - 1))
        (![sv (if a0F.val / 4 = 0 then σ (S0.2.2.2.1 0) else σ (S0.2.2.2.1 2)),
          sv (if a1F.val / 4 = 0 then σ (S1.2.2.2.1 0) else σ (S1.2.2.2.1 2))] j)
        ((![subOpening wfk σ (b0 + 7), subOpening wfk σ (S0.2.1 + 2)] j).path subTopLevel)) =
        fun j => if j = 0 then (sv (σ (S0.2.2.2.1 0)), sv (σ (S0.2.2.2.1 2)))
          else (sv (σ (S1.2.2.2.1 0)), sv (σ (S1.2.2.2.1 2))) := by
      funext j
      fin_cases j
      · exact ht0'
      · exact ht1'
    have hts' : mFoldWith M.H (σ (.n 1)) (fun l => eOfNat (fpos index.val c.val 0 0 0) + word (topFoldT.addr s l) 0 0)
        (fun l => s.testBit l) (topSibs σ S1.2.1 b0) 3 0 (σ (.n (S1.2.1 + 10))) =
        some (if sF.val / 8 = 0 then σ (spOut topFoldT (S1.2.1 + 12) 0) else σ (spOut topFoldT (S1.2.1 + 12) 2)) := by
      refine (mFoldWith_congr _ _ _ _ 3 0 (fun l _ hl => ?_) _).trans (hts.trans ?_)
      · simp only [topSibs, hsels, show l ≠ 3 by omega, ↓reduceIte]
      · rcases hs' with h | h <;> simp [h, sF]
    obtain ⟨htf, hord⟩ := sp_topTopsW (inst := inst) hq index c sF (topSibs σ S1.2.1 b0) hts'
      (by rcases hs' with h | h <;> simp [topSibs, hsels, h, sF])
    have := sCoordRecover_someW (inst := inst) (P := spp (σ (.n 1))) (index := index) (c := c) (mark := mark)
      (opening := ⟨![subOpening wfk σ (b0 + 7), subOpening wfk σ (S0.2.1 + 2)],
        fun l => sv (topSibs σ S1.2.1 b0 l.val)⟩)
      (leaf := ![sv lf0, sv lf1])
      (node := ![sv (if a0F.val / 4 = 0 then σ (S0.2.2.2.1 0) else σ (S0.2.2.2.1 2)),
        sv (if a1F.val / 4 = 0 then σ (S1.2.2.2.1 0) else σ (S1.2.2.2.1 2))])
      (fun j => by fin_cases j <;> assumption) (fun j => by fin_cases j <;> assumption)
      (by rw [hT]; exact hsupH) htf
    rw [this]
    exact congrArg some hord
  · rw [hbound, hb1', hb0, hr2]
    rfl

/-- **A coordinate under a model** (`sCoord_sound_w`). -/
theorem sCoord_model (hq : SQW M.H inst) {wfk : List E → List E → Nat → E} (hfk : FkSoundWWith M C wfk) {σ : Val}
    (hmd : σ (.n 3) = mdw 64 true) (index : Index) (c : Coord) (hidx : σ (.n 142) = eOfNat index.val) {bound : V}
    {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (sCoord c.val bound b).1 next kret) :
    (∃ mark : CoordMark,
      @coordRecover Option _ inst (spp (σ (.n 1))) index c mark (coordOpening wfk σ c.val bound b) =
        some (sv (σ (sCoord c.val bound b).2.2.2.1.1), sv (σ (sCoord c.val bound b).2.2.2.1.2)) ∧
      σ (sCoord c.val bound b).2.2.1.1 = word (mark.word 0).val 0 0 ∧
      σ (sCoord c.val bound b).2.2.1.2 = word (mark.word 1).val 0 0 ∧
      σ (sCoord c.val bound b).2.2.2.2 = σ bound + lit ((mark.child 0).val * 2 ^ (58 + 3 * (2 * c.val))) +
        lit ((mark.child 1).val * 2 ^ (58 + 3 * (2 * c.val + 1))) + lit (mark.super.val * 2 ^ (26 + 4 * c.val))) ∧
      next := by
  rw [sCoord_eq] at h ⊢
  rw [holdsListB_append] at h
  have hfree : Stmt.freeInList [] (if c.val = 0 then [] else
      [cst b (word (c.val * hiMul) 0 0), addS (.n (b + 1)) (.n 142) (.n b)]) = true := by
    split <;> rfl
  obtain ⟨htree, h⟩ := sPre_sound index.isLt c.isLt hidx ((holdsListB_free hfree σ _ _).mp h)
  exact sCoordT_model hq hfk hmd index c htree h

/-- **The coordinates under a model** (`sCoords_sound_w`), with the openings `coordsOpenings`. -/
theorem sCoords_model (hq : SQW M.H inst) {wfk : List E → List E → Nat → E} (hfk : FkSoundWWith M C wfk) {σ : Val}
    (hmd : σ (.n 3) = mdw 64 true) (index : Index) (hidx : σ (.n 142) = eOfNat index.val) :
    ∀ (m c : Nat) (bound : V) (b : Nat) {next : Prop} {kret : List E → Prop} (_ : c + m ≤ 8),
      Stmt.HoldsListB M.sem C rd σ (sCoords m c bound b).1 next kret →
      (∃ marks : Nat → CoordMark,
        (∀ r (hr : r < m),
          @coordRecover Option _ inst (spp (σ (.n 1))) index ⟨c + r, by simp only [forestCoords]; omega⟩
              (marks (c + r)) (coordsOpenings wfk σ m c bound b (c + r)) =
            some (sv (σ ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).1),
              sv (σ ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).2)) ∧
          σ ((sCoords m c bound b).2.2.1.getD r (.n 0, .n 0)).1 = word ((marks (c + r)).word 0).val 0 0 ∧
          σ ((sCoords m c bound b).2.2.1.getD r (.n 0, .n 0)).2 = word ((marks (c + r)).word 1).val 0 0) ∧
        σ (sCoords m c bound b).2.2.2.2 = σ bound + ∑ r ∈ Finset.range m, coordWeight (c + r) (marks (c + r))) ∧
      next
  | 0, _, bound, _, _, _, _, h => ⟨⟨fun _ => ⟨0, fun _ => 0, fun _ => 0⟩, fun _ h => absurd h (by omega),
      by simp [sCoords]⟩, h⟩
  | m + 1, c, bound, b, next, kret, hcm, h => by
      simp only [sCoords, holdsListB_append] at h ⊢
      obtain ⟨⟨mark, hrec, hw0, hw1, hb⟩, h⟩ :=
        sCoord_model hq hfk hmd index ⟨c, by simp only [forestCoords]; omega⟩ hidx h
      obtain ⟨⟨marks, hr, hbs⟩, hn⟩ := sCoords_model hq hfk hmd index hidx m (c + 1) _ _ (by omega) h
      refine ⟨⟨fun k => if k = c then mark else marks k, fun r hr' => ?_, ?_⟩, hn⟩
      · rcases r with _ | r
        · simp only [Nat.add_zero, ↓reduceIte, List.getD_cons_zero, coordsOpenings]
          exact ⟨hrec, hw0, hw1⟩
        · have := hr r (by omega)
          simp only [List.getD_cons_succ, show c + (r + 1) ≠ c by omega, ↓reduceIte, coordsOpenings]
          have hF : (⟨c + (r + 1), by simp only [forestCoords]; omega⟩ : Coord) =
              ⟨c + 1 + r, by simp only [forestCoords]; omega⟩ := Fin.ext (by simp only; omega)
          rw [hF, show c + (r + 1) = c + 1 + r by omega]
          exact this
      · have hsum : ∑ r ∈ Finset.range m, coordWeight (c + (r + 1))
            ((fun k => if k = c then mark else marks k) (c + (r + 1))) =
            ∑ r ∈ Finset.range m, coordWeight (c + 1 + r) (marks (c + 1 + r)) :=
          Finset.sum_congr rfl fun r _ => by
            simp only [show c + (r + 1) = c + 1 + r by omega, show c + 1 + r ≠ c by omega, ↓reduceIte]
        rw [hbs, hb, Finset.sum_range_succ', hsum]
        simp only [Nat.add_zero, ↓reduceIte]
        rw [coordWeight]
        abel

end Scheme

end
end LeanVM.Guest.B1.Sig
