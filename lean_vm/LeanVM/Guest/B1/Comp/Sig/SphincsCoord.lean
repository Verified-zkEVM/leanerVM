/-
  LeanVM.Guest.B1.Comp.Sig.SphincsCoord

  A leanSPHINCS coordinate complete over a completeness model: its sub-trees' forest keys and
  folds, the super-child, the top tree, for a mark and opening whose recovery the scheme's run with
  the model's answers returns (`SphincsCoordComplete.lean`).
-/

module

public import LeanVM.Guest.B1.Comp.Sig.SphincsKey
public import LeanVM.Guest.B1.Comp.Sig.SphincsFold
public import LeanVM.Guest.B1.Comp.Sig.SphincsScheme
public import LeanVM.Guest.B1.Sig.SphincsCoordComplete

/-!
# A coordinate over a completeness model

`SphincsCoordComplete.lean` over a `CompModel`, the forest keys complete over the model
(`FkCompleteC`), every hash preset to the model's answer. The deployed lemmas conclude that the
scheme's coordinate recovery *is* the cells'; here the recovery's `Option` run returning is the
hypothesis (taken apart by `sCoordRecover_someInv`, `sChildRecover_someInv`, `sSubFold_cellsE`,
`sSuperHash_cellsE`, `sTopFold_cellsE`), so every string is answered, and the conclusion is that
its value is the cells':

| deployed | here |
|---|---|
| `sSubPre_complete`, `sSub_complete` | `sSubPre_comp`, `sSub_comp` |
| `coordA_complete`, `coordB_complete` | the same, by `CompletesB.of_free` |
| `coordD_complete` | `coordD_comp` |
| `sCoordT_complete`, `sCoord_complete`, `sCoords_complete` | `sCoordT_comp`, `sCoord_comp`, `sCoords_comp` |
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader}

theorem holdsListB_cons_dispatchS {S : BlakeSem} (x : V) (fs : List String) (args rets : List V)
    (ss : List Stmt) (next : Prop) (kret : List E → Prop) (σ : Val) :
    Stmt.HoldsListB S C rd σ (.dispatch x fs args rets :: ss) next kret ↔
      (∃ (j : Nat) (h : j < fs.length), σ x = ofK (gpow j) ∧ C fs[j] (args.map σ) (rets.map σ)) ∧
        Stmt.HoldsListB S C rd σ ss next kret := Iff.rfl

/-! ## A sub-tree -/

/-- **The statements before a sub-tree's fold are complete over the model** (`sSubPre_complete`): key `a` and codeword `t` in range, the
forest key of the values at the key's address. -/
theorem sSubPre_comp (hfk : FkCompleteC CM C) (hrd : MemOK rd 256) {σ : Val} (hpp : IsCanonical128 (σ (.n 1)))
    {subAt : V} {b : Nat} (hb : 2 ≤ b) (hsub : NB b subAt) (hsubc : IsCanonical128 (σ subAt)) {t a : Nat}
    (ht : t < 256) (ha : a < 8) (vals : Nat → E) (hvals : ∀ k, IsCanonical128 (vals k))
    (hans : FkAnsC CM t (σ (.n 1)) (σ subAt + word (a * 2 ^ 40) 0 0) vals) :
    CompletesB CM.sem C rd b (b + 14) (sSubPre subAt b) σ (fun σ' =>
      σ' (.n b) = ofK (gpow a) ∧ σ' (.n (b + 1)) = word (a * 2 ^ 40) 0 0 ∧
      σ' (.n (b + 12)) = fkLeafC CM t (σ (.n 1)) (σ subAt + word (a * 2 ^ 40) 0 0) vals ∧
      σ' (.n (b + 13)) = word t 0 0 ∧ AgreeBelow b σ σ') := by
  obtain ⟨ks, hks, rfl⟩ := hsub
  obtain ⟨y1, u1, u2, hl1, hk1, hl2⟩ := rangeCheck_witness (hrd.mono (by norm_num) : MemOK rd 8) (by norm_num) ha
  obtain ⟨y2, w1, w2, hm1, hk2, hm2⟩ := rangeCheck_witness hrd (by norm_num) ht
  set KA := σ (.n ks) + word (a * 2 ^ 40) 0 0
  set vs : List E := [ofK (gpow a), word (a * 2 ^ 40) 0 0, word (2 ^ 7) 0 0, y1, u1, u2, ofK (gpow t), g255, y2,
    w1, w2, KA, fkLeafC CM t (σ (.n 1)) KA vals, word t 0 0]
  set σ' := upds σ ((List.range 14).map fun k => (b + k, vs.getD k 0))
  have he : Ext b (b + 14) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 14, σ' (.n (b + k)) = vs.getD k 0 := upds_range_at b _ 14 σ
  have hk : ∀ k < b, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have v0 : σ' (.n b) = ofK (gpow a) := by have := v 0 (by omega); rwa [Nat.add_zero] at this
  refine ⟨σ', he, ⟨v0, v 1 (by omega), v 12 (by omega), v 13 (by omega), he.agree⟩, fun next kret hn => ?_⟩
  simp only [sSubPre, rangeS, hintW, cst, addS, List.cons_append, List.nil_append, holdsListB_cons_atom, Atom.HoldsB,
    true_and]
  refine ⟨by rw [v 2 (by omega)]; rfl, ?_⟩
  rw [v0, v 2 (by omega), v 3 (by omega), v 4 (by omega), v 5 (by omega), v 6 (by omega), v 7 (by omega),
    v 8 (by omega), v 9 (by omega), v 10 (by omega), v 11 (by omega), hk ks hks, v 1 (by omega)]
  simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨⟨hl1, by rw [word_two_pow (by norm_num)]; exact hk1, hl2⟩, trivial, ⟨hm1, by rw [g255_eq]; exact hk2, hm2⟩,
    rfl, ?_⟩
  refine (holdsListB_cons_dispatchS _ _ _ _ _ _ _ _).mpr ⟨⟨t, by rw [fkNames_length]; exact ht, ?_, ?_⟩, hn⟩
  · rw [v 6 (by omega)]; rfl
  · simp only [List.map_cons, List.map_nil]
    rw [v 11 (by omega), v 12 (by omega), v 13 (by omega), hk 1 (by omega)]
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
    rw [← List.getD_eq_getElem fkNames "" (by rw [fkNames_length]; exact ht)]
    exact hfk t ht KA _ (isCanonical128_add hsubc (isCanonical128_word _ _)) hpp vals hvals hans


/-- **A sub-tree is complete over the model** (`sSub_complete`), its forest key and fold answered: key `a`, codeword `t`, the forest key of the values folded two
levels over the siblings, the bound gaining the key's field. -/
theorem sSub_comp (hfk : FkCompleteC CM C) (hrd : MemOK rd 256) {σ : Val} (hmd : σ (.n 3) = mdw 64 true)
    (hpp : IsCanonical128 (σ (.n 1))) {c j : Nat} {subAt bound : V} {b : Nat} (hb : 4 ≤ b) (hsub : NB b subAt)
    (hbound : NB b bound) (hsubc : IsCanonical128 (σ subAt)) {t a : Nat} (ht : t < 256) (ha : a < 8)
    (vals sibs : Nat → E) (hvals : ∀ k, IsCanonical128 (vals k)) (hsibs : ∀ l, IsCanonical128 (sibs l))
    (hans : FkAnsC CM t (σ (.n 1)) (σ subAt + word (a * 2 ^ 40) 0 0) vals)
    (hfold : mFoldAns CM (σ (.n 1)) (foldAddr σ subAt subFoldT a) (fun l => a.testBit l) sibs 2 0
      (fkLeafC CM t (σ (.n 1)) (σ subAt + word (a * 2 ^ 40) 0 0) vals)) :
    CompletesB CM.sem C rd b (sSub c j subAt bound b).2.1 (sSub c j subAt bound b).1 σ (fun σ' =>
      σ' (.n (b + 1)) = word (a * 2 ^ 40) 0 0 ∧ σ' (sSub c j subAt bound b).2.2.1 = word t 0 0 ∧
      σ' ((sSub c j subAt bound b).2.2.2.1 (2 * (a / 4))) = mFoldC CM (σ (.n 1)) (foldAddr σ subAt subFoldT a)
        (fun l => a.testBit l) sibs 2 0 (fkLeafC CM t (σ (.n 1)) (σ subAt + word (a * 2 ^ 40) 0 0) vals) ∧
      σ' ((sSub c j subAt bound b).2.2.2.1 (2 - 2 * (a / 4))) = sibs 2 ∧
      σ' (sSub c j subAt bound b).2.2.2.2 = σ bound + lit (a * 2 ^ (58 + 3 * (2 * c + j))) ∧
      AgreeBelow b σ σ') := by
  have hF : subFoldT.height = 3 ∨ subFoldT.height = 4 := Or.inl rfl
  have ha' : a < 2 ^ subFoldT.height := ha
  obtain ⟨-, -, -, hq, hout, -, hpRe, -⟩ := spMatch_layout (b := b + 14) hF ha'
  have hend := sSubArms_snd c j subAt b
  rw [sSub_eq]
  dsimp only
  rw [hend]
  have hS1 : NB b (V.n 1) := ⟨1, by omega, rfl⟩
  have hS3 : NB b (V.n 3) := ⟨3, by omega, rfl⟩
  refine CompletesB.append (m := b + 14) (by omega) (by omega) (sSubPre_below hsub)
    (sSubPre_comp hfk hrd hpp (by omega) hsub hsubc ht ha vals hvals hans) fun σ1 _ ⟨h0, h1, h12, h13, hag1⟩ => ?_
  have hk1 : ∀ v : V, NB b v → σ1 v = σ v := fun v ⟨k, hk, e⟩ => by rw [e]; exact (hag1 k hk).symm
  have hA : foldAddr σ1 subAt subFoldT a = foldAddr σ subAt subFoldT a := by
    funext l'; simp only [foldAddr, hk1 subAt hsub]
  have hmatch := spMatch_comp (CM := CM) (C := C) (rd := rd) (σ := σ1) (pp := .n 1) (md := .n 3) (adr := subAt)
    (node := .n (b + 12)) (ret1 := .n (b + 1)) (x := .n b) (F := subFoldT) hF
    (r1 := fun a => word (a * 2 ^ 40) 0 0) (r2 := fun a => lit (a * 2 ^ (58 + 3 * (2 * c + j)))) (b := b + 14)
    ha' ⟨hS1.mono (by omega), hS3.mono (by omega), hsub.mono (by omega), ⟨b + 12, by omega, rfl⟩,
      ⟨b + 1, by omega, rfl⟩, ⟨b, by omega, rfl⟩⟩ (by rw [hk1 _ hS3, hmd]) (by rw [hk1 _ hS1]; exact hpp)
    (by rw [hk1 _ hsub]; exact hsubc) (by rw [h12]; exact (isCanonical128_hcellC _).1) sibs hsibs
    (by rw [hk1 _ hS1, hA, h12]; exact hfold) h0 h1
  rw [← sSubArms, hend] at hmatch
  refine CompletesB.append (m := b + 14 + 101) (by omega) (by omega)
    (by have := spMatch_below (r1 := fun a => word (a * 2 ^ 40) 0 0)
          (r2 := fun a => lit (a * 2 ^ (58 + 3 * (2 * c + j)))) hF (b := b + 14) (pp := .n 1) (md := .n 3)
          (adr := subAt) (node := .n (b + 12)) (ret1 := .n (b + 1)) (x := .n b)
          ⟨hS1.mono (by omega), hS3.mono (by omega), hsub.mono (by omega), ⟨b + 12, by omega, rfl⟩,
            ⟨b + 1, by omega, rfl⟩, ⟨b, by omega, rfl⟩⟩
        rw [← sSubArms, hend] at this; exact this)
    hmatch.withExt fun σ2 _ ⟨⟨ho, hs, hr⟩, he2⟩ => ?_
  have hk2 : ∀ k < b + 14, σ2 (.n k) = σ1 (.n k) := fun k hk => (he2.agree k hk).symm
  have hbd : σ2 bound = σ bound := by
    obtain ⟨kb, hkb, e⟩ := hbound; rw [e, hk2 kb (by omega), ← e, hk1 bound ⟨kb, hkb, e⟩]
  set val := σ2 bound + σ2 (spRet2 subFoldT (b + 14))
  have hne : ∀ p, p < b + 14 + 101 → (V.n p) ≠ .n (b + 14 + 101) := fun p hp e => by
    simp only [V.mk.injEq] at e; omega
  refine CompletesB.atom_cons val le_rfl ?_ ?_ (CompletesB.nil _ _ _ ?_)
  · obtain ⟨kb, hkb, e⟩ := hbound
    simp only [Atom.vals, spRet2]
    exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨kb, by omega, e⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))
  · obtain ⟨kb, hkb, e⟩ := hbound
    show _ = _ + _
    rw [Function.update_self, e, Function.update_of_ne (hne kb (by omega)), spRet2,
      Function.update_of_ne (hne _ (by simp only [subFoldT]; omega)), ← e]
    rfl
  · have hu : ∀ p, p < b + 14 + 101 → Function.update σ2 (.n (b + 14 + 101)) val (.n p) = σ2 (.n p) :=
      fun p hp => Function.update_of_ne (hne p hp) _ _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hu _ (by omega), hk2 _ (by omega), h1]
    · rw [hu _ (by omega), hk2 _ (by omega), h13]
    · rw [spOut_eq, hu _ (hout _ (by omega)).2.1, ← spOut_eq]
      refine ho.trans ?_
      rw [hk1 _ hS1, h12, hA]; rfl
    · rw [spOut_eq, hu _ (hout _ (by omega)).2.1, ← spOut_eq]
      exact hs
    · rw [Function.update_self]
      show σ2 bound + σ2 (spRet2 subFoldT (b + 14)) = _
      rw [hbd, hr]
    · exact fun k hk => (hag1 k hk).trans ((hk2 k (by omega)).symm.trans (hu k (by omega)).symm)


/-- **The super-child's hash is complete over the model** (`coordD_complete`), its cells answered. -/
theorem coordD_comp {σ : Val} {b0 : Nat} (hpp : IsCanonical128 (σ (.n 1)))
    (hla : IsCanonical128 (σ (.n (b0 + 6))))
    (hx : IsCanonical128 (σ (spOut subFoldT (b0 + 21) 0)) ∧ IsCanonical128 (σ (spOut subFoldT (b0 + 21) 2)) ∧
      IsCanonical128 (σ (spOut subFoldT (b0 + 139) 0)) ∧ IsCanonical128 (σ (spOut subFoldT (b0 + 139) 2)))
    (hans : AnsCells CM [σ (.n 1), σ (.n (b0 + 6)) + word (tw 18) 0 0, σ (spOut subFoldT (b0 + 21) 0),
      σ (spOut subFoldT (b0 + 21) 2), σ (spOut subFoldT (b0 + 139) 0), σ (spOut subFoldT (b0 + 139) 2)]) :
    CompletesB CM.sem C rd (b0 + 241) (b0 + 253) (coordD b0) σ (fun σ' =>
      σ' (.n (b0 + 251)) = (hcellC CM [σ (.n 1), σ (.n (b0 + 6)) + word (tw 18) 0 0, σ (spOut subFoldT (b0 + 21) 0),
        σ (spOut subFoldT (b0 + 21) 2), σ (spOut subFoldT (b0 + 139) 0), σ (spOut subFoldT (b0 + 139) 2)]).1 ∧
      AgreeBelow (b0 + 241) σ σ') := by
  set f := b0 + 241
  set A := σ (.n (b0 + 6)) + word (tw 18) 0 0
  set X00 := σ (spOut subFoldT (b0 + 21) 0)
  set X02 := σ (spOut subFoldT (b0 + 21) 2)
  set X10 := σ (spOut subFoldT (b0 + 139) 0)
  set X12 := σ (spOut subFoldT (b0 + 139) 2)
  have ebytes : blockBytes ![σ (.n 1), A, X00, X02] ++ [X10, X12].flatMap cellBytes =
      [σ (.n 1), A, X00, X02, X10, X12].flatMap cellBytes := by
    simp only [blockBytes_four, ← List.flatMap_append]; rfl
  set x := hmidC CM ![σ (.n 1), A, X00, X02]
  set o := hbC CM (blockBytes ![σ (.n 1), A, X00, X02] ++ [X10, X12].flatMap cellBytes)
  set vs : List E := [word (tw 18) 0 0, A, iv0, iv1, mdw 64 false, x.1, x.2, 0, 0, mdw 96 true, o.1, o.2]
  set σ' := upds σ ((List.range 12).map fun k => (f + k, vs.getD k 0))
  have he : Ext f (f + 12) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 12, σ' (.n (f + k)) = vs.getD k 0 := upds_range_at f _ 12 σ
  have hk : ∀ k < f, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have hr : ([X10, X12].flatMap cellBytes).length = 32 := by rw [length_flatMap_cellBytes']; rfl
  have hcmp := compress_two_C (CM := CM) (b0 := ![σ (.n 1), A, X00, X02]) (b1 := ![X10, X12, 0, 0])
    (blockBytes_two X10 X12) (by rw [hr]; omega) (by rw [hr]; omega)
    (fin4_canonical.mpr ⟨hpp, isCanonical128_add hla (isCanonical128_word _ _), hx.1, hx.2.1⟩)
    (fin4_canonical.mpr ⟨hx.2.2.1, hx.2.2.2, isCanonical128_zero, isCanonical128_zero⟩)
    (by rw [ebytes]; exact hans)
  rw [hr] at hcmp
  have ho0 : σ' (spOut subFoldT (b0 + 21) 0) = X00 := hk _ (by simp [subFoldT]; omega)
  have ho2 : σ' (spOut subFoldT (b0 + 21) 2) = X02 := hk _ (by simp [subFoldT]; omega)
  have ho10 : σ' (spOut subFoldT (b0 + 139) 0) = X10 := hk _ (by simp [subFoldT]; omega)
  have ho12 : σ' (spOut subFoldT (b0 + 139) 2) = X12 := hk _ (by simp [subFoldT]; omega)
  refine ⟨σ', he, ⟨?_, he.agree⟩, fun next kret hn => ?_⟩
  · rw [show b0 + 251 = f + 10 by omega, v 10 (by omega)]
    simp only [vs, o, List.getD_cons_succ, List.getD_cons_zero, hcellC]
    rw [ebytes]
  · simp only [coordD, ivs, cst, addS, b2s, List.cons_append, List.nil_append, holdsListB_cons_atom, holdsListB_nil,
      Atom.HoldsB]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    rw [v0, v 1 (by omega), v 2 (by omega), show f + 2 + 1 = f + 3 by omega, v 3 (by omega), v 4 (by omega),
      v 5 (by omega), v 6 (by omega), v 7 (by omega), v 8 (by omega), v 9 (by omega), v 10 (by omega),
      v 11 (by omega), hk 1 (by omega), hk (b0 + 6) (by omega), ho0, ho2, ho10, ho12]
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero, word_zero]
    obtain ⟨hc1, hc2⟩ := hcmp
    refine ⟨?_, ?_, ?_, ?_, ?_, hc1, ?_, ?_, ?_, hc2, hn⟩ <;> trivial


/-! ## A coordinate's recovery, as the model's cells -/

section Scheme

open Sphincs Sphincs.Concrete

variable {inst : HasQuery Sphincs.HashSpec Option}

/-- **A sub-tree's run, as the model's cells**: a returning child leaf and fold make the forest key
and the fold answered, the fold's node the model's. -/
theorem subTree_someC (hq : SQW CM.H inst) {pp : E} (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (w : LutIdx) (vals sibs : Nat → E) {lf nd : Sphincs.Digest}
    (hl : @childRecover Option _ inst (spp pp) index c s j a (lut w) (fun i => sv (vals i.val)) = some lf)
    (hn : @subFold Option _ inst (spp pp) index c s j a (fun l => sv (sibs l.val)) (subHeight - 1) lf =
      some nd) :
    FkAnsC CM w.val pp (eOfNat (fpos index.val c.val s.val j.val a.val)) vals ∧
    mFoldAns CM pp (fun l => eOfNat (fpos index.val c.val s.val j.val 0) + word (subFoldT.addr a.val l) 0 0)
      (fun l => a.val.testBit l) sibs 2 0
      (fkLeafC CM w.val pp (eOfNat (fpos index.val c.val s.val j.val a.val)) vals) ∧
    nd = sv (mFoldC CM pp (fun l => eOfNat (fpos index.val c.val s.val j.val 0) + word (subFoldT.addr a.val l) 0 0)
      (fun l => a.val.testBit l) sibs 2 0
      (fkLeafC CM w.val pp (eOfNat (fpos index.val c.val s.val j.val a.val)) vals)) := by
  obtain ⟨ends, hends, o, ho, hlo⟩ := sChildRecover_someInv (H := CM.H) hq
    (ka := eOfNat (fpos index.val c.val s.val j.val a.val))
    (aL := eOfNat (fpos index.val c.val s.val j.val a.val) + eOfNat (tw 16)) (lut w) vals
    (fchain_addr index c s j a) (childLeaf_addr index c s j a) hl
  have hW : FkLeafWith CM.H w.val pp (eOfNat (fpos index.val c.val s.val j.val a.val)) vals o.1 := by
    refine ⟨ends, fun k hk => ?_, o, ho, rfl⟩
    have := hends k hk
    rw [fEndsWith, show (⟨k % 6, Nat.mod_lt _ (by norm_num)⟩ : FChain) = ⟨k, hk⟩ from
      Fin.ext (Nat.mod_eq_of_lt hk), ← spCode_lut w.isLt ⟨k, hk⟩] at this
    exact this
  obtain ⟨hF, hleq⟩ := fkLeafWith_iff_C.mp hW
  rw [hlo, hleq] at hn
  rw [sSubFold_cellsE hq (A := fun l => eOfNat (fpos index.val c.val s.val j.val 0) +
      word (subFoldT.addr a.val l) 0 0) (fun l node hn => subNode_addr index c s j a l node hn) sibs
      (subHeight - 1) (by decide)] at hn
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨hyA, hyv⟩ := (mFoldWith_eq_some_iff _ _ _ _ _ _ _).mp hy
  exact ⟨hF, hyA, by rw [← hyv]; rfl⟩

/-- The two top nodes of a sub-tree, in the order of the key's top bit. -/
theorem orderTops_sub (a : ChildIdx) (Y Z : E) :
    orderTops (a.val.testBit (subHeight - 1)) (sv Y) (sv Z) =
      (sv (if a.val / 4 = 0 then Y else Z), sv (if a.val / 4 = 0 then Z else Y)) := by
  rw [orderTops_sv, show subHeight - 1 = 2 from rfl, testBit_top (show a.val < 2 ^ (2 + 1) from a.isLt)]
  have ha : a.val / 4 = 0 ∨ a.val / 4 = 1 := by have := a.isLt; simp only [subHeight] at this; omega
  rcases ha with h | h <;> simp [h]

/-- The two top nodes of a coordinate's top tree, in the order of the super-child's top bit. -/
theorem orderTops_top (s : SuperIdx) (Y Z : E) :
    orderTops (s.val.testBit (topHeight - 1)) (sv Y) (sv Z) =
      (sv (if s.val / 8 = 0 then Y else Z), sv (if s.val / 8 = 0 then Z else Y)) := by
  rw [orderTops_sv, show topHeight - 1 = 3 from rfl, testBit_top (show s.val < 2 ^ (3 + 1) from s.isLt)]
  have hs : s.val / 8 = 0 ∨ s.val / 8 = 1 := by have := s.isLt; simp only [topHeight] at this; omega
  rcases hs with h | h <;> simp [h]

end Scheme

section Scheme

open Sphincs Sphincs.Concrete

variable {inst : HasQuery Sphincs.HashSpec Option}

/-- **A coordinate is complete over the model** (after its tree's address; `sCoordT_complete`): for
a mark and an opening whose recovery the scheme's run with the model's answers returns, the
recovered two top nodes land in its outputs, the codeword cells hold the mark's codewords, and the
bound gains the mark's fields. -/
theorem sCoordT_comp (hq : SQW CM.H inst) (hfk : FkCompleteC CM C) (hrd : MemOK rd 256) {σ : Val}
    (hmd : σ (.n 3) = mdw 64 true) (hpp : IsCanonical128 (σ (.n 1))) (index : Index) (c : Coord) {bound treeAt : V}
    {b0 : Nat} (hb0 : 4 ≤ b0) (htB : NB b0 treeAt) (hbB : NB b0 bound)
    (htree : σ treeAt = eOfNat (fpos index.val c.val 0 0 0)) (mark : CoordMark) (opening : CoordOpening)
    {x : Sphincs.Digest × Sphincs.Digest}
    (hrec : @coordRecover Option _ inst (spp (σ (.n 1))) index c mark opening = some x) :
    CompletesB CM.sem C rd b0 (sCoordT c.val bound treeAt b0).2.1 (sCoordT c.val bound treeAt b0).1 σ (fun σ' =>
      x = (sv (σ' (sCoordT c.val bound treeAt b0).2.2.2.1.1), sv (σ' (sCoordT c.val bound treeAt b0).2.2.2.1.2)) ∧
      IsCanonical128 (σ' (sCoordT c.val bound treeAt b0).2.2.2.1.1) ∧
      IsCanonical128 (σ' (sCoordT c.val bound treeAt b0).2.2.2.1.2) ∧
      σ' (sCoordT c.val bound treeAt b0).2.2.1.1 = word (mark.word 0).val 0 0 ∧
      σ' (sCoordT c.val bound treeAt b0).2.2.1.2 = word (mark.word 1).val 0 0 ∧
      σ' (sCoordT c.val bound treeAt b0).2.2.2.2 = σ bound + coordWeight c.val mark ∧ AgreeBelow b0 σ σ') := by
  rw [sCoordT_eq]
  dsimp only
  have hidx := index.isLt
  have hc8 := c.isLt
  simp only [totalHeight, forestCoords] at hidx hc8
  have hs16 := mark.super.isLt
  have ha0 := (mark.child 0).isLt
  have ha1 := (mark.child 1).isLt
  simp only [topHeight, subHeight] at hs16 ha0 ha1
  have hS1 : NB b0 (V.n 1) := ⟨1, by omega, rfl⟩
  have hS3 : NB b0 (V.n 3) := ⟨3, by omega, rfl⟩
  -- the scheme's run, as the model's cells
  obtain ⟨leaf, node, sup, top, hl, hn, hsup, htop, hx⟩ := sCoordRecover_someInv hrec
  have hv0 := sv_finCells (opening.sub 0).values
  have hv1 := sv_finCells (opening.sub 1).values
  have hp0 := sv_finCells (opening.sub 0).path
  have hp1' := sv_finCells (opening.sub 1).path
  have htp := sv_finCells opening.top
  obtain ⟨hF0, hM0, hn0⟩ := subTree_someC (CM := CM) hq index c mark.super 0 (mark.child 0) (mark.word 0)
    (finCells (opening.sub 0).values) (finCells (opening.sub 0).path) (by rw [← hv0]; exact hl 0)
    (by rw [← hp0]; exact hn 0)
  obtain ⟨hF1, hM1, hn1⟩ := subTree_someC (CM := CM) hq index c mark.super 1 (mark.child 1) (mark.word 1)
    (finCells (opening.sub 1).values) (finCells (opening.sub 1).path) (by rw [← hv1]; exact hl 1)
    (by rw [← hp1']; exact hn 1)
  set pp := σ (.n 1) with hpp_def
  set Y0 := mFoldC CM pp (fun l => eOfNat (fpos index.val c.val mark.super.val 0 0) +
    word (subFoldT.addr (mark.child 0).val l) 0 0) (fun l => (mark.child 0).val.testBit l)
    (finCells (opening.sub 0).path) 2 0
    (fkLeafC CM (mark.word 0).val pp (eOfNat (fpos index.val c.val mark.super.val 0 (mark.child 0).val))
      (finCells (opening.sub 0).values)) with hY0
  set Y1 := mFoldC CM pp (fun l => eOfNat (fpos index.val c.val mark.super.val 1 0) +
    word (subFoldT.addr (mark.child 1).val l) 0 0) (fun l => (mark.child 1).val.testBit l)
    (finCells (opening.sub 1).path) 2 0
    (fkLeafC CM (mark.word 1).val pp (eOfNat (fpos index.val c.val mark.super.val 1 (mark.child 1).val))
      (finCells (opening.sub 1).values)) with hY1
  set Z0 := finCells (opening.sub 0).path 2
  set Z1 := finCells (opening.sub 1).path 2
  set T00 := if (mark.child 0).val / 4 = 0 then Y0 else Z0 with hT00
  set T02 := if (mark.child 0).val / 4 = 0 then Z0 else Y0 with hT02
  set T10 := if (mark.child 1).val / 4 = 0 then Y1 else Z1 with hT10
  set T12 := if (mark.child 1).val / 4 = 0 then Z1 else Y1 with hT12
  have hfun : (fun j : SubIdx => orderTops ((mark.child j).val.testBit (subHeight - 1)) (node j)
      ((opening.sub j).path subTopLevel)) = fun j => if j = 0 then (sv T00, sv T02) else (sv T10, sv T12) := by
    funext j
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
      rw [hn0, show (opening.sub 0).path subTopLevel = sv Z0 from (congrFun hp0 subTopLevel).trans rfl, orderTops_sub]
      rfl
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
      rw [hn1, show (opening.sub 1).path subTopLevel = sv Z1 from (congrFun hp1' subTopLevel).trans rfl, orderTops_sub]
      rfl
  rw [hfun, sSuperHash_cellsE hq (superChild_addr index c mark.super)] at hsup
  obtain ⟨oS, hoS, hsupv⟩ := Option.map_eq_some_iff.mp hsup
  obtain ⟨hSans, rfl⟩ := hcellWith_eq_some_iff.mp hoS
  set SUP := (hcellC CM [pp, eOfNat (fpos index.val c.val mark.super.val 0 0) + word (tw 18) 0 0, T00, T02, T10,
    T12]).1 with hSUP
  rw [← hsupv, htp, sTopFold_cellsE hq (A := fun l => eOfNat (fpos index.val c.val 0 0 0) +
      word (topFoldT.addr mark.super.val l) 0 0) (fun l nd hnd => topNode_addr index c mark.super l nd hnd)
      (finCells opening.top) (topHeight - 1) (by decide)] at htop
  obtain ⟨yT, hyT, htopv⟩ := Option.map_eq_some_iff.mp htop
  obtain ⟨hTans, hyTv⟩ := (mFoldWith_eq_some_iff _ _ _ _ _ _ _).mp hyT
  rw [show topHeight - 1 = 3 from rfl] at hTans hyTv
  rw [← htopv, show opening.top topTopLevel = sv (finCells opening.top 3) from (congrFun htp topTopLevel).trans rfl, orderTops_top,
    ← hyTv] at hx
  -- block A
  refine CompletesB.append (m := b0 + 7) (by omega) (by omega) (coordA_below htB)
    (CompletesB.of_free (F := []) rfl (coordA_complete (C := C) hrd htB hs16)).withExt
    fun σA _ ⟨⟨hA0, hA1, hA6, hagA⟩, heA⟩ => ?_
  have hkA : ∀ v : V, NB b0 v → σA v = σ v := fun v ⟨k, hk, e⟩ => by rw [e]; exact (hagA k hk).symm
  have hLA : σA (.n (b0 + 6)) = eOfNat (fpos index.val c.val mark.super.val 0 0) := by
    rw [hA6, htree, show mark.super.val * 2 ^ 35 = 2 ^ 35 * mark.super.val by ring,
      sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  have hpA : σA (.n 1) = σ (.n 1) := hkA _ hS1
  have hfA : foldAddr σA (.n (b0 + 6)) subFoldT (mark.child 0).val =
      fun l => eOfNat (fpos index.val c.val mark.super.val 0 0) + word (subFoldT.addr (mark.child 0).val l) 0 0 := by
    funext l; rw [foldAddr, hLA]
  have hkey0 : σA (.n (b0 + 6)) + word ((mark.child 0).val * 2 ^ 40) 0 0 =
      eOfNat (fpos index.val c.val mark.super.val 0 (mark.child 0).val) := by
    rw [hLA, show (mark.child 0).val * 2 ^ 40 = 2 ^ 40 * (mark.child 0).val by ring,
      sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  -- the first sub-tree
  have hsub0 := sSub_comp (CM := CM) (C := C) (rd := rd) (c := c.val) (j := 0) hfk hrd (σ := σA)
    (by rw [hkA _ hS3, hmd]) (by rw [hkA _ hS1]; exact hpp) (b := b0 + 7) (by omega) ⟨b0 + 6, by omega, rfl⟩
    (hbB.mono (by omega)) (by rw [hLA]; exact isCanonical128_eOfNat _) (mark.word 0).isLt ha0
    (finCells (opening.sub 0).values) (finCells (opening.sub 0).path) (canonical_finCells _)
    (canonical_finCells _) (by rw [hpA, hkey0]; exact hF0) (by rw [hpA, hkey0, hfA]; exact hM0)
  rw [sSub_snd, sSub_word, sSub_outs, sSub_bound] at hsub0
  have hsub0B := sSub_below (c := c.val) (j := 0) (b := b0 + 7) (by omega) ⟨b0 + 6, by omega, rfl⟩
    (hbB.mono (by omega)) (bound := bound)
  rw [sSub_snd] at hsub0B
  refine CompletesB.append (m := b0 + 123) (by omega) (by omega) hsub0B hsub0.withExt
    fun σ0 _ ⟨⟨h01, h0w, h0o, h0s, h0b, hag0⟩, he0⟩ => ?_
  have hk0 : ∀ k < b0 + 7, σ0 (.n k) = σA (.n k) := fun k hk => (hag0 k hk).symm
  rw [hpA, hfA, hkey0] at h0o
  -- the second sub-tree's address
  refine CompletesB.append (m := b0 + 125) (by omega) (by omega) (coordB_below b0)
    (CompletesB.of_free (F := []) rfl (coordB_complete (C := C) (rd := rd))).withExt
    fun σB _ ⟨⟨hB, hagB⟩, heB⟩ => ?_
  have hkB : ∀ k < b0 + 123, σB (.n k) = σ0 (.n k) := fun k hk => (hagB k hk).symm
  have hLB : σB (.n (b0 + 124)) = eOfNat (fpos index.val c.val mark.super.val 1 0) := by
    rw [hB, hk0 _ (by omega), hLA, show (2 : Nat) ^ 39 = 2 ^ 39 * 1 by ring, sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  -- the second sub-tree
  have hpB : σB (.n 1) = σ (.n 1) := by rw [hkB 1 (by omega), hk0 1 (by omega), hkA _ hS1]
  have hmB : σB (.n 3) = σ (.n 3) := by rw [hkB 3 (by omega), hk0 3 (by omega), hkA _ hS3]
  have hfB : foldAddr σB (.n (b0 + 124)) subFoldT (mark.child 1).val =
      fun l => eOfNat (fpos index.val c.val mark.super.val 1 0) + word (subFoldT.addr (mark.child 1).val l) 0 0 := by
    funext l; rw [foldAddr, hLB]
  have hkey1 : σB (.n (b0 + 124)) + word ((mark.child 1).val * 2 ^ 40) 0 0 =
      eOfNat (fpos index.val c.val mark.super.val 1 (mark.child 1).val) := by
    rw [hLB, show (mark.child 1).val * 2 ^ 40 = 2 ^ 40 * (mark.child 1).val by ring,
      sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  have hsub1 := sSub_comp (CM := CM) (C := C) (rd := rd) (c := c.val) (j := 1) hfk hrd (σ := σB)
    (by rw [hmB, hmd]) (by rw [hpB]; exact hpp) (b := b0 + 125) (by omega) ⟨b0 + 124, by omega, rfl⟩
    ⟨b0 + 122, by omega, rfl⟩ (by rw [hLB]; exact isCanonical128_eOfNat _) (mark.word 1).isLt ha1
    (finCells (opening.sub 1).values) (finCells (opening.sub 1).path) (canonical_finCells _)
    (canonical_finCells _) (by rw [hpB, hkey1]; exact hF1) (by rw [hpB, hkey1, hfB]; exact hM1)
  rw [sSub_snd, sSub_word, sSub_outs, sSub_bound] at hsub1
  have hsub1B := sSub_below (c := c.val) (j := 1) (b := b0 + 125) (by omega) ⟨b0 + 124, by omega, rfl⟩
    ⟨b0 + 122, by omega, rfl⟩ (subAt := .n (b0 + 124)) (bound := .n (b0 + 122))
  rw [sSub_snd] at hsub1B
  refine CompletesB.append (m := b0 + 241) (by omega) (by omega) hsub1B hsub1.withExt
    fun σ1 _ ⟨⟨h11, h1w, h1o, h1s, h1b, hag1⟩, he1⟩ => ?_
  rw [hpB, hfB, hkey1] at h1o
  have hk1 : ∀ k < b0 + 125, σ1 (.n k) = σB (.n k) := fun k hk => (hag1 k hk).symm
  have hq0 : (mark.child 0).val / 4 = 0 ∨ (mark.child 0).val / 4 = 1 := by omega
  have hq1 : (mark.child 1).val / 4 = 0 ∨ (mark.child 1).val / 4 = 1 := by omega
  have hqs : mark.super.val / 8 = 0 ∨ mark.super.val / 8 = 1 := by omega
  have hO : ∀ k (b : Nat), spOut subFoldT b k = .n (spOutN subFoldT b k) := fun k b => spOut_eq _ _ _
  have hON : ∀ k b, k < 3 → spOutN subFoldT b k = b + 12 + k := fun k b hk => by
    simp [spOutN, subFoldT, hk]
  -- the sub-trees' top nodes
  have hX0 : ∀ k < 3, σ1 (spOut subFoldT (b0 + 21) k) = σ0 (spOut subFoldT (b0 + 21) k) := fun k hk => by
    rw [hO, hON k _ hk, hk1 _ (by omega), hkB _ (by omega)]
  have hT0 : σ0 (spOut subFoldT (b0 + 21) 0) = T00 ∧ σ0 (spOut subFoldT (b0 + 21) 2) = T02 := by
    rcases hq0 with h | h <;> rw [h] at h0o h0s <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.sub_zero,
      Nat.sub_self] at h0o h0s <;> simp only [hT00, hT02, h, ↓reduceIte, one_ne_zero] <;>
      first | exact ⟨by simpa [Nat.add_assoc] using h0o, by simpa [Nat.add_assoc] using h0s⟩ | exact ⟨by simpa [Nat.add_assoc] using h0s, by simpa [Nat.add_assoc] using h0o⟩
  have hT1 : σ1 (spOut subFoldT (b0 + 139) 0) = T10 ∧ σ1 (spOut subFoldT (b0 + 139) 2) = T12 := by
    rcases hq1 with h | h <;> rw [h] at h1o h1s <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.sub_zero,
      Nat.sub_self] at h1o h1s <;> simp only [hT10, hT12, h, ↓reduceIte, one_ne_zero] <;>
      first | exact ⟨by simpa [Nat.add_assoc] using h1o, by simpa [Nat.add_assoc] using h1s⟩ | exact ⟨by simpa [Nat.add_assoc] using h1s, by simpa [Nat.add_assoc] using h1o⟩
  have hcT : ∀ (q : Nat) (Y Z : E), IsCanonical128 Y → IsCanonical128 Z →
      IsCanonical128 (if q = 0 then Y else Z) ∧ IsCanonical128 (if q = 0 then Z else Y) := fun q Y Z hY hZ => by
    split <;> exact ⟨‹_›, ‹_›⟩
  have hcan0 := hcT ((mark.child 0).val / 4) Y0 Z0 (mFoldC_canonical _ _ _ _ _ _ _ (Or.inl (by norm_num))) (canonical_finCells _ _)
  have hcan1 := hcT ((mark.child 1).val / 4) Y1 Z1 (mFoldC_canonical _ _ _ _ _ _ _ (Or.inl (by norm_num))) (canonical_finCells _ _)
  have hp1 : σ1 (.n 1) = σ (.n 1) := by rw [hk1 1 (by omega), hpB]
  have hla1 : σ1 (.n (b0 + 6)) = eOfNat (fpos index.val c.val mark.super.val 0 0) := by
    rw [hk1 _ (by omega), hkB _ (by omega), hk0 _ (by omega), hLA]
  -- the super-child
  refine CompletesB.append (m := b0 + 253) (by omega) (by omega) (coordD_below b0)
    (coordD_comp (CM := CM) (C := C) (rd := rd) (σ := σ1) (by rw [hp1]; exact hpp)
      (by rw [hla1]; exact isCanonical128_eOfNat _)
      ⟨by rw [hX0 0 (by omega), hT0.1]; exact hcan0.1, by rw [hX0 2 (by omega), hT0.2]; exact hcan0.2,
        by rw [hT1.1]; exact hcan1.1, by rw [hT1.2]; exact hcan1.2⟩
      (by rw [hp1, hla1, hX0 0 (by omega), hX0 2 (by omega), hT0.1, hT0.2, hT1.1, hT1.2]; exact hSans)).withExt
    fun σD _ ⟨⟨hD, hagD⟩, heD⟩ => ?_
  rw [hp1, hla1, hX0 0 (by omega), hX0 2 (by omega), hT0.1, hT0.2, hT1.1, hT1.2, ← hSUP] at hD
  have hkD : ∀ k < b0 + 241, σD (.n k) = σ1 (.n k) := fun k hk => (hagD k hk).symm
  have hkD0 : ∀ v : V, NB b0 v → σD v = σ v := fun v ⟨k, hk, e⟩ => by
    rw [e, hkD k (by omega), hk1 k (by omega), hkB k (by omega), hk0 k (by omega), hkA _ ⟨k, hk, rfl⟩]
  have hfD : foldAddr σD treeAt topFoldT mark.super.val =
      fun l => eOfNat (fpos index.val c.val 0 0 0) + word (topFoldT.addr mark.super.val l) 0 0 := by
    funext l; rw [foldAddr, hkD0 _ htB, htree]
  -- the top tree
  have hM := spMatch_comp (CM := CM) (C := C) (rd := rd) (σ := σD) (pp := .n 1) (md := .n 3) (adr := treeAt)
    (node := .n (b0 + 251)) (ret1 := .n (b0 + 1)) (x := .n b0) (F := topFoldT) (Or.inr rfl)
    (r1 := fun s => word (s * 2 ^ 35) 0 0) (r2 := fun s => lit (s * 2 ^ (26 + 4 * c.val))) (b := b0 + 253)
    (a := mark.super.val) hs16 ⟨hS1.mono (by omega), hS3.mono (by omega), htB.mono (by omega),
      ⟨b0 + 251, by omega, rfl⟩, ⟨b0 + 1, by omega, rfl⟩, ⟨b0, by omega, rfl⟩⟩
    (by rw [hkD0 _ hS3, hmd]) (by rw [hkD0 _ hS1]; exact hpp) (by rw [hkD0 _ htB, htree]; exact isCanonical128_eOfNat _)
    (by rw [hD]; exact (isCanonical128_hcellC _).1) (finCells opening.top) (canonical_finCells _)
    (by rw [hkD0 _ hS1, hfD, hD]; exact hTans)
    (by rw [hkD _ (by omega), hk1 _ (by omega), hkB _ (by omega), hk0 _ (by omega), hA0])
    (by rw [hkD _ (by omega), hk1 _ (by omega), hkB _ (by omega), hk0 _ (by omega), hA1])
  have hMB := spMatch_below (r1 := fun s => word (s * 2 ^ 35) 0 0) (r2 := fun s => lit (s * 2 ^ (26 + 4 * c.val)))
    (Or.inr rfl) (b := b0 + 253) (pp := .n 1) (md := .n 3) (adr := treeAt) (node := .n (b0 + 251))
    (ret1 := .n (b0 + 1)) (x := .n b0) (F := topFoldT)
    ⟨hS1.mono (by omega), hS3.mono (by omega), htB.mono (by omega), ⟨b0 + 251, by omega, rfl⟩,
      ⟨b0 + 1, by omega, rfl⟩, ⟨b0, by omega, rfl⟩⟩
  rw [← topArms, topArms_snd] at hM hMB
  refine CompletesB.append (m := b0 + 253 + 309) (by omega) (by omega) hMB hM.withExt
    fun σM _ ⟨⟨hMo, hMs, hMr⟩, heM⟩ => ?_
  rw [hkD0 _ hS1, hfD, hD, show topFoldT.height - 1 = 3 from rfl, show (2 : Nat) ^ 3 = 8 from rfl, ← hpp_def,
    hyTv] at hMo
  rw [show topFoldT.height - 1 = 3 from rfl, show (2 : Nat) ^ 3 = 8 from rfl] at hMs
  have hkM : ∀ k < b0 + 253, σM (.n k) = σD (.n k) := fun k hk => (heM.agree k hk).symm
  set val := σM (.n (b0 + 240)) + σM (spRet2 topFoldT (b0 + 253))
  have hne : ∀ p, p < b0 + 253 + 309 → (V.n p) ≠ .n (b0 + 253 + 309) := fun p hp e => by
    simp only [V.mk.injEq] at e; omega
  have hR2 : spRet2 topFoldT (b0 + 253) = .n (b0 + 275) := by simp [spRet2, topFoldT]
  have hOT : ∀ k (b : Nat), spOut topFoldT b k = .n (spOutN topFoldT b k) := fun k b => spOut_eq _ _ _
  have hOTN : ∀ k b, k < 3 → spOutN topFoldT b k = b + 19 + k := fun k b hk => by
    simp [spOutN, topFoldT, hk]
  refine CompletesB.atom_cons val le_rfl ?_ ?_ (CompletesB.nil _ _ _ ?_)
  · simp only [Atom.vals, hR2]
    exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨b0 + 240, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))
  · show _ = _ + _
    rw [Function.update_self, Function.update_of_ne (hne _ (by omega)), hR2,
      Function.update_of_ne (hne _ (by omega)), ← hR2]
  · set σZ := Function.update σM (.n (b0 + 253 + 309)) val
    have hu : ∀ p, p < b0 + 253 + 309 → σZ (.n p) = σM (.n p) := fun p hp => Function.update_of_ne (hne p hp) _ _
    have hZ1 : ∀ p, p < b0 + 241 → σZ (.n p) = σ1 (.n p) := fun p hp => by
      rw [hu p (by omega), hkM p (by omega), hkD p hp]
    have hZ0 : ∀ p, p < b0 + 123 → σZ (.n p) = σ0 (.n p) := fun p hp => by
      rw [hZ1 p (by omega), hk1 p (by omega), hkB p hp]
    have hTp0 : σZ (spOut topFoldT (b0 + 253) 0) = σM (spOut topFoldT (b0 + 253) 0) := by
      rw [hOT, hOTN 0 _ (by omega)]; exact hu _ (by omega)
    have hTp2 : σZ (spOut topFoldT (b0 + 253) 2) = σM (spOut topFoldT (b0 + 253) 2) := by
      rw [hOT, hOTN 2 _ (by omega)]; exact hu _ (by omega)
    have hTOP : σM (spOut topFoldT (b0 + 253) 0) =
          (if mark.super.val / 8 = 0 then yT else finCells opening.top 3) ∧
        σM (spOut topFoldT (b0 + 253) 2) = (if mark.super.val / 8 = 0 then finCells opening.top 3 else yT) := by
      rcases hqs with h | h <;> rw [h] at hMo hMs <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.sub_zero,
        Nat.sub_self] at hMo hMs <;> simp only [h, ↓reduceIte, one_ne_zero] <;>
        first | exact ⟨by simpa using hMo, by simpa using hMs⟩ | exact ⟨by simpa using hMs, by simpa using hMo⟩
    have hcanT := hcT (mark.super.val / 8) yT (finCells opening.top 3)
      (by rw [← hyTv]; exact mFoldC_canonical _ _ _ _ _ _ _ (Or.inl (by norm_num))) (canonical_finCells _ _)
    refine ⟨?_, by rw [hTp0, hTOP.1]; exact hcanT.1, by rw [hTp2, hTOP.2]; exact hcanT.2,
      by rw [hZ0 _ (by omega)]; exact h0w, by rw [hZ1 _ (by omega)]; exact h1w, ?_,
      fun k hk => (hagA k hk).trans ((hk0 k (by omega)).symm.trans ((hkB k (by omega)).symm.trans
        ((hk1 k (by omega)).symm.trans ((hkD k (by omega)).symm.trans ((hkM k (by omega)).symm.trans
          (hu k (by omega)).symm)))))⟩
    · rw [hx, hTp0, hTp2, hTOP.1, hTOP.2, ← hyTv]
    · rw [show σZ (.n (b0 + 253 + 309)) = val from Function.update_self _ _ _]
      show σM (.n (b0 + 240)) + σM (spRet2 topFoldT (b0 + 253)) = _
      rw [hMr, hkM _ (by omega), hkD _ (by omega), h1b, hkB _ (by omega), h0b, hkA _ hbB, coordWeight]
      simp only [Nat.add_zero]
      abel

end Scheme

section Scheme

open Sphincs Sphincs.Concrete

variable {inst : HasQuery Sphincs.HashSpec Option}

/-- **A coordinate is complete over the model** (`sCoord_complete`), for a mark and an opening whose
recovery the scheme's run with the model's answers returns. -/
theorem sCoord_comp (hq : SQW CM.H inst) (hfk : FkCompleteC CM C) (hrd : MemOK rd 256) {σ : Val}
    (hmd : σ (.n 3) = mdw 64 true) (hpp : IsCanonical128 (σ (.n 1))) (index : Index) (c : Coord)
    (hidx : σ (.n 142) = eOfNat index.val) {bound : V} {b : Nat} (hb : 143 ≤ b) (hbB : NB b bound)
    (mark : CoordMark) (opening : CoordOpening) {x : Sphincs.Digest × Sphincs.Digest}
    (hrec : @coordRecover Option _ inst (spp (σ (.n 1))) index c mark opening = some x) :
    CompletesB CM.sem C rd b (sCoord c.val bound b).2.1 (sCoord c.val bound b).1 σ (fun σ' =>
      x = (sv (σ' (sCoord c.val bound b).2.2.2.1.1), sv (σ' (sCoord c.val bound b).2.2.2.1.2)) ∧
      IsCanonical128 (σ' (sCoord c.val bound b).2.2.2.1.1) ∧ IsCanonical128 (σ' (sCoord c.val bound b).2.2.2.1.2) ∧
      σ' (sCoord c.val bound b).2.2.1.1 = word (mark.word 0).val 0 0 ∧
      σ' (sCoord c.val bound b).2.2.1.2 = word (mark.word 1).val 0 0 ∧
      σ' (sCoord c.val bound b).2.2.2.2 = σ bound + coordWeight c.val mark ∧ AgreeBelow b σ σ') := by
  have hidx' := index.isLt
  have hc8 := c.isLt
  simp only [totalHeight, forestCoords] at hidx' hc8
  rw [sCoord_eq]
  dsimp only
  by_cases h0 : c.val = 0
  · simp only [h0, ↓reduceIte, List.nil_append]
    have := sCoordT_comp (CM := CM) (C := C) (rd := rd) hq hfk hrd hmd hpp index c (bound := bound) (treeAt := .n 142)
      (b0 := b) (by omega) ⟨142, by omega, rfl⟩ hbB (by rw [hidx]; congr 1; simp [fpos, h0]) mark opening hrec
    rw [h0] at this
    exact this
  · simp only [h0, ↓reduceIte]
    have hpre : CompletesB CM.sem C rd b (b + 2) [cst b (word (c.val * hiMul) 0 0), addS (.n (b + 1)) (.n 142) (.n b)] σ
        (fun σ' => σ' (.n (b + 1)) = eOfNat (fpos index.val c.val 0 0 0) ∧ AgreeBelow b σ σ') := by
      set σ' := upds σ [(b, word (c.val * hiMul) 0 0), (b + 1, σ (.n 142) + word (c.val * hiMul) 0 0)]
      have he : Ext b (b + 2) σ σ' := upds_ext σ _ (by simp)
      have hk : ∀ k < b, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
      have v0 : σ' (.n b) = word (c.val * hiMul) 0 0 := by simp [σ', upds]
      have v1 : σ' (.n (b + 1)) = σ (.n 142) + word (c.val * hiMul) 0 0 := by simp [σ', upds]
      refine ⟨σ', he, ⟨?_, he.agree⟩, fun next kret hn => ?_⟩
      · rw [v1, hidx, show c.val * hiMul = 2 ^ 32 * c.val by simp only [hiMul]; ring, sp_add_word (by omega)]
        congr 1; simp only [fpos]; ring
      · simp only [cst, addS, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB]
        rw [v0, v1, hk 142 (by omega)]
        exact ⟨rfl, rfl, hn⟩
    refine CompletesB.append (m := b + 2) (by omega) (by rw [sCoordT_snd]; omega) ?_ hpre fun σ1 _ ⟨h1, hag1⟩ => ?_
    · simp only [cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil, List.cons_append,
        List.nil_append]
      exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨142, by omega, rfl⟩ (.cons ⟨b, by omega, rfl⟩
        (.nil _))))
    have hk1 : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
    refine (sCoordT_comp (CM := CM) (C := C) (rd := rd) hq hfk hrd (by rw [hk1 3 (by omega), hmd])
      (by rw [hk1 1 (by omega)]; exact hpp) index c (bound := bound) (treeAt := .n (b + 1)) (b0 := b + 2) (by omega)
      ⟨b + 1, by omega, rfl⟩ (hbB.mono (by omega)) h1 mark opening (x := x) (by rw [hk1 1 (by omega)]; exact hrec)).mono le_rfl le_rfl fun σ2 ⟨h2, hc1, hc2, h3, h4, h5, hag2⟩ =>
      ⟨?_, hc1, hc2, h3, h4, ?_, fun k hk => (hag1 k hk).trans (hag2 k (by omega))⟩
    · exact h2
    · rw [h5]; obtain ⟨kb, hkb, e⟩ := hbB; rw [e, hk1 kb hkb]

/-- **The coordinates are complete over the model** (`sCoords_complete`): for marks and openings
whose recoveries the scheme's run with the model's answers returns, the recovered top nodes land in
the coordinates' outputs. -/
theorem sCoords_comp (hq : SQW CM.H inst) (hfk : FkCompleteC CM C) (hrd : MemOK rd 256) (index : Index)
    (marks : Nat → CoordMark) (openings : Nat → CoordOpening) (tops : Nat → Sphincs.Digest × Sphincs.Digest) :
    ∀ (m c : Nat) (bound : V) (b : Nat) (σ : Val) (_ : c + m ≤ 8), 143 ≤ b → NB b bound →
      σ (.n 3) = mdw 64 true → IsCanonical128 (σ (.n 1)) → σ (.n 142) = eOfNat index.val →
      (∀ r (hr : r < m), @coordRecover Option _ inst (spp (σ (.n 1))) index ⟨c + r, by simp only [forestCoords]; omega⟩
        (marks (c + r)) (openings (c + r)) = some (tops (c + r))) →
      CompletesB CM.sem C rd b (sCoords m c bound b).2.1 (sCoords m c bound b).1 σ (fun σ' =>
        (∀ r, r < m →
          tops (c + r) = (sv (σ' ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).1),
              sv (σ' ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).2)) ∧
          IsCanonical128 (σ' ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).1) ∧
          IsCanonical128 (σ' ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).2) ∧
          σ' ((sCoords m c bound b).2.2.1.getD r (.n 0, .n 0)).1 = word ((marks (c + r)).word 0).val 0 0 ∧
          σ' ((sCoords m c bound b).2.2.1.getD r (.n 0, .n 0)).2 = word ((marks (c + r)).word 1).val 0 0) ∧
        σ' (sCoords m c bound b).2.2.2.2 = σ bound + ∑ r ∈ Finset.range m, coordWeight (c + r) (marks (c + r)) ∧
        AgreeBelow b σ σ')
  | 0, _, bound, b, σ, _, _, _, _, _, _, _ => CompletesB.nil _ _ _ ⟨fun _ h => absurd h (by omega), by simp [sCoords],
      fun _ _ => rfl⟩
  | m + 1, c, bound, b, σ, hcm, hb, hbB, hmd, hpp, hidx, hrec => by
      simp only [sCoords]
      obtain ⟨b0, hb0, hs1, hs2, hs3, hs4⟩ := sCoord_outs c bound b
      refine CompletesB.append (m := (sCoord c bound b).2.1) (by omega) (by
          have := sCoords_snd_ge m (c + 1) (sCoord c bound b).2.2.2.2 (sCoord c bound b).2.1; omega)
        (sCoord_below hb hbB)
        (sCoord_comp (CM := CM) (C := C) (rd := rd) hq hfk hrd hmd hpp index ⟨c, by simp only [forestCoords]; omega⟩ hidx hb
          hbB (marks c) (openings c) (x := tops c) (by simpa using hrec 0 (by omega))) fun σ1 _ ⟨h1, hca, hcb, hw0, hw1, hbd, hag1⟩ => ?_
      have hk1 : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
      have hbound' : NB (sCoord c bound b).2.1 (sCoord c bound b).2.2.2.2 := ⟨b0 + 562, by omega, hs4⟩
      refine (sCoords_comp hq hfk hrd index marks openings tops m (c + 1) _ _ σ1 (by omega) (by omega) hbound'
        (by rw [hk1 3 (by omega), hmd]) (by rw [hk1 1 (by omega)]; exact hpp)
        (by rw [hk1 142 (by omega), hidx]) (fun r hr => by
          have hF : (⟨c + 1 + r, by simp only [forestCoords]; omega⟩ : Coord) =
              ⟨c + (r + 1), by simp only [forestCoords]; omega⟩ := Fin.ext (by simp only; omega)
          rw [hk1 1 (by omega), hF, show c + 1 + r = c + (r + 1) by omega]
          exact hrec (r + 1) (by omega))).mono le_rfl le_rfl fun σ2 ⟨hr, hbs, hag2⟩ => ⟨fun r hr' => ?_, ?_, ?_⟩
      · have hk2 : ∀ k < b0 + 563, σ2 (.n k) = σ1 (.n k) := fun k hk => (hag2 k (by omega)).symm
        rcases r with _ | r
        · simp only [List.getD_cons_zero, Nat.add_zero]
          simp only at h1 hca hcb hw0 hw1
          rw [hs3] at h1 hca hcb
          rw [hs2] at hw0 hw1
          rw [hs2, hs3]
          rw [hk2 _ (by omega), hk2 _ (by omega), hk2 _ (by omega), hk2 _ (by omega)]
          exact ⟨h1, hca, hcb, hw0, hw1⟩
        · have := hr r (by omega)
          simp only [List.getD_cons_succ]
          rw [show c + (r + 1) = c + 1 + r by omega]
          exact this
      · have hk2 : ∀ k < b0 + 563, σ2 (.n k) = σ1 (.n k) := fun k hk => (hag2 k (by omega)).symm
        rw [hbs, Finset.sum_range_succ']
        have hb1 : σ1 (sCoord c bound b).2.2.2.2 = σ bound + coordWeight c (marks c) := hbd
        rw [hb1]
        have hsum : ∑ r ∈ Finset.range m, coordWeight (c + (r + 1)) (marks (c + (r + 1))) =
            ∑ r ∈ Finset.range m, coordWeight (c + 1 + r) (marks (c + 1 + r)) :=
          Finset.sum_congr rfl fun r _ => by rw [show c + (r + 1) = c + 1 + r by omega]
        rw [hsum, add_assoc, add_comm (∑ r ∈ Finset.range m, _)]
        simp only [Nat.add_zero]
      · exact fun k hk => (hag1 k hk).trans (hag2 k (by omega))

end Scheme

end
end LeanVM.Guest.B1.Sig
