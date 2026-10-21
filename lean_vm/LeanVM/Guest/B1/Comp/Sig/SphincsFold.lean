/-
  LeanVM.Guest.B1.Comp.Sig.SphincsFold

  The forest folds complete over a completeness model: a level, the levels of an arm, an arm
  with its outputs preset, and a fold's dispatch (`SphincsFoldComplete.lean`).
-/

module

public import LeanVM.Guest.B1.Comp.Sig.Group
public import LeanVM.Guest.B1.Sig.SphincsFoldComplete

/-!
# The forest folds over a completeness model

A level hashes `lvlCells` (the sibling and the node in the order of the bit) into the model's
answer `lvlHashC`; the levels of a fold reach the model's fold `mFoldC` when the model answers
every level (`mFoldAns`). `spLevel_comp`, `spLevels_comp`, `spArm_comp`, `spMatch_comp`, and at the
deployed model `spMatch_of_comp` (`spMatch_complete`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader}

/-- The cells a level hashes, from the sibling `s` and the node reached `x`. -/
def lvlCells (pp A : E) (bit : Bool) (s x : E) : List E :=
  [pp, A, if bit then s else x, if bit then x else s]

variable (CM) in
/-- The node a level hashes over the model (`lvlHash`). -/
def lvlHashC (pp A : E) (bit : Bool) (s x : E) : E × E := hcellC CM (lvlCells pp A bit s x)

theorem lvlHashC_deployed (pp A : E) (bit : Bool) (s x : E) :
    lvlHashC CompModel.deployed pp A bit s x = lvlHash pp A bit s x := rfl

/-- A model fold, its last level taken last (`mFold_succ`). -/
theorem mFoldC_succ (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m l : Nat) (x : E), mFoldC CM pp A bits sibs (m + 1) l x =
      (hcellC CM [pp, A (l + m), if bits (l + m) then sibs (l + m) else mFoldC CM pp A bits sibs m l x,
        if bits (l + m) then mFoldC CM pp A bits sibs m l x else sibs (l + m)]).1
  | 0, l, x => rfl
  | m + 1, l, x => by
      rw [mFoldC, mFoldC_succ pp A bits sibs m (l + 1)]
      simp only [show l + 1 + m = l + (m + 1) by omega]
      rfl

/-- An answered model fold, its last level taken last. -/
theorem mFoldAns_succ (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m l : Nat) (x : E), mFoldAns CM pp A bits sibs (m + 1) l x ↔
      mFoldAns CM pp A bits sibs m l x ∧
      AnsCells CM [pp, A (l + m), if bits (l + m) then sibs (l + m) else mFoldC CM pp A bits sibs m l x,
        if bits (l + m) then mFoldC CM pp A bits sibs m l x else sibs (l + m)]
  | 0, l, x => by simp [mFoldAns, mFoldC]
  | m + 1, l, x => by
      rw [mFoldAns, mFoldAns_succ pp A bits sibs m (l + 1), mFoldAns, mFoldC]
      simp only [show l + 1 + m = l + (m + 1) by omega, and_assoc]

/-- **A level is complete over the model** (`spLevel_complete`): from the sibling `s`, its cells
answered, its outputs preset to the model's answer. -/
theorem spLevel_comp {σ : Val} {pp md adr cur o0 o1 : V} {addr b : Nat} {bit : Bool} (hin : NB b pp ∧ NB b md ∧
    NB b adr ∧ NB b cur) (ho0 : Out b (b + 5) o0) (ho1 : Out b (b + 5) o1) (hmd : σ md = mdw 64 true)
    (hpp : IsCanonical128 (σ pp)) (hadr : IsCanonical128 (σ adr)) (hcur : IsCanonical128 (σ cur)) {s : E}
    (hs : IsCanonical128 s)
    (ha : AnsCells CM (lvlCells (σ pp) (σ adr + word addr 0 0) bit s (σ cur)))
    (ho : (σ o0, σ o1) = lvlHashC CM (σ pp) (σ adr + word addr 0 0) bit s (σ cur)) :
    CompletesB CM.sem C rd b (b + 5) (spLevel pp md adr addr bit cur b o0 o1) σ (fun σ' => σ' (.n b) = s) := by
  obtain ⟨⟨kp, hkp, rfl⟩, ⟨km, hkm, rfl⟩, ⟨ka, hka, rfl⟩, ⟨kc, hkc, rfl⟩⟩ := hin
  set A := σ (.n ka) + word addr 0 0
  set vs : List E := [s, word addr 0 0, A, iv0, iv1]
  set σ' := upds σ ((List.range 5).map fun k => (b + k, vs.getD k 0))
  have he : Ext b (b + 5) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 5, σ' (.n (b + k)) = vs.getD k 0 := upds_range_at b _ 5 σ
  have hk : ∀ k < b, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have hAc : IsCanonical128 A := isCanonical128_add hadr (isCanonical128_word _ _)
  refine ⟨σ', he, ?_, fun next kret hn => ?_⟩
  · have := v 0 (by omega); rwa [Nat.add_zero] at this
  · have hb0 : σ' (.n b) = s := by have := v 0 (by omega); rwa [Nat.add_zero] at this
    have hc4 : CM.sem.check ![σ (.n kp), A, if bit then s else σ (.n kc), if bit then σ (.n kc) else s] iv0 iv1
        (σ o0) (σ o1) (mdw 64 true) := by
      rw [show σ o0 = _ from congrArg Prod.fst ho, show σ o1 = _ from congrArg Prod.snd ho]
      exact compress4_C ⟨hpp, hAc, by split <;> assumption, by split <;> assumption⟩ ha
    cases bit <;>
    · simp only [spLevel, hintW, cst, addS, ivs, b2s, Bool.false_eq_true, ↓reduceIte, List.cons_append,
        List.nil_append, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, true_and] at hc4 ⊢
      rw [v 1 (by omega), v 2 (by omega), v 3 (by omega), show b + 3 + 1 = b + 4 by omega, v 4 (by omega),
        hk ka hka, hk kp hkp, hk km hkm, hk kc hkc, hb0, he.out ho0, he.out ho1, hmd]
      simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
      refine ⟨?_, ?_, ?_, ?_, hc4, hn⟩ <;> trivial


/-- **The levels of a fold are complete over the model** (`spLevels_complete`), from canonical
siblings, every level answered. -/
theorem spLevels_comp {pp md adr : V} (F : Fold) (index : Nat) (sibs : Nat → E)
    (hsibs : ∀ l, IsCanonical128 (sibs l)) :
    ∀ (m l : Nat) (cur : V) (b : Nat) (σ : Val), NB b pp ∧ NB b md ∧ NB b adr ∧ NB b cur →
      σ md = mdw 64 true → IsCanonical128 (σ pp) → IsCanonical128 (σ adr) → IsCanonical128 (σ cur) →
      mFoldAns CM (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) sibs m l (σ cur) →
      CompletesB CM.sem C rd b (b + 7 * m) (spLevels pp md adr F index m l cur b).1 σ (fun σ' =>
        σ' (spLevels pp md adr F index m l cur b).2 =
          mFoldC CM (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) sibs m l (σ cur))
  | 0, _, cur, b, σ, _, _, _, _, _, _ => CompletesB.nil _ _ _ rfl
  | m + 1, l, cur, b, σ, ⟨hp, hm, ha, hc⟩, hmd, hpp, hadr, hcur, hans => by
      simp only [spLevels]
      set h := lvlHashC CM (σ pp) (σ adr + word (F.addr index l) 0 0) (index.testBit l) (sibs l) (σ cur)
      set σ1 := upds σ [(b + 5, h.1), (b + 6, h.2)]
      have he1 : Ext b (b + 7) σ σ1 := upds_ext σ _ (by simp)
      have hk1 : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => (he1.agree k hk).symm
      have hkeep : ∀ v : V, NB b v → σ1 v = σ v := fun v ⟨k, hk, e⟩ => by rw [e]; exact hk1 k hk
      have h5 : σ1 (.n (b + 5)) = h.1 := by simp [σ1, upds]
      have h6 : σ1 (.n (b + 6)) = h.2 := by simp [σ1, upds]
      obtain ⟨hbl, -, -⟩ := spLevels_below (pp := pp) (md := md) (adr := adr) F index m (l + 1) (.n (b + 5)) (b + 7)
        ⟨hp.mono (by omega), hm.mono (by omega), ha.mono (by omega), ⟨b + 5, by omega, rfl⟩⟩
      have hlvl : CompletesB CM.sem C rd b (b + 7) (spLevel pp md adr (F.addr index l) (index.testBit l) cur b (.n (b + 5))
          (.n (b + 6))) σ (fun σ' => σ' (.n (b + 5)) = h.1 ∧ AgreeBelow b σ σ') := by
        refine CompletesB.of_ext he1 ((spLevel_comp (CM := CM) (C := C) (rd := rd) ⟨hp, hm, ha, hc⟩
          (out_of_ge ⟨b + 5, le_rfl, rfl⟩) (out_of_ge ⟨b + 6, by omega, rfl⟩) (by rw [hkeep md hm, hmd])
          (by rw [hkeep pp hp]; exact hpp) (by rw [hkeep adr ha]; exact hadr) (by rw [hkeep cur hc]; exact hcur)
          (hsibs l) (by rw [hkeep pp hp, hkeep adr ha, hkeep cur hc]; exact hans.1)
          (by rw [h5, h6, hkeep pp hp, hkeep adr ha, hkeep cur hc])).withExt.mono le_rfl (by omega)
          fun σ' ⟨_, he'⟩ => ⟨by rw [he'.apply (Or.inr (by omega)), h5],
            fun k hk => (he1.agree k hk).trans (he'.agree k hk)⟩)
      refine CompletesB.append (m := b + 7) (by omega) (by omega)
        (spLevel_below ⟨hp.mono (by omega), hm.mono (by omega), ha.mono (by omega), hc.mono (by omega)⟩
          ⟨b + 5, by omega, rfl⟩ ⟨b + 6, by omega, rfl⟩ (by omega)) hlvl fun σ' _ ⟨hv5, hag⟩ => ?_
      have hk' : ∀ v : V, NB b v → σ' v = σ v := fun v ⟨k, hk, e⟩ => by rw [e]; exact (hag k hk).symm
      have hA : foldAddr σ' adr F index = foldAddr σ adr F index := by
        funext l'; simp only [foldAddr, hk' adr ha]
      refine (spLevels_comp F index sibs hsibs m (l + 1) (.n (b + 5)) (b + 7) σ'
        ⟨hp.mono (by omega), hm.mono (by omega), ha.mono (by omega), ⟨b + 5, by omega, rfl⟩⟩
        (by rw [hk' md hm, hmd]) (by rw [hk' pp hp]; exact hpp) (by rw [hk' adr ha]; exact hadr)
        (by rw [hv5]; exact (isCanonical128_hcellC _).1)
        (by rw [hk' pp hp, hv5, hA]; exact hans.2)).mono (by omega) (by omega) fun σ'' h'' => ?_
      rw [h'', hk' pp hp, hv5, mFoldC, hA]
      rfl


/-- **An arm is complete over the model** (`spArm_complete`), its levels answered, its outputs and
constants preset: the node reached, `height - 1` levels
up from the node over the siblings, in the outputs its top bit names. -/
theorem spArm_comp {σ : Val} {pp md adr node ret1 ret2 : V} {F : Fold} {out : Nat → V} {r1 r2 : E}
    {index b : Nat} (hF : 2 ≤ F.height) (hin : NB b pp ∧ NB b md ∧ NB b adr ∧ NB b node)
    (hout : ∀ k, Out b (b + 7 * (F.height - 2) + 5) (out k)) (hr1 : Out b (b + 7 * (F.height - 2) + 5) ret1)
    (hr2 : Out b (b + 7 * (F.height - 2) + 5) ret2) (hmd : σ md = mdw 64 true) (hpp : IsCanonical128 (σ pp))
    (hadr : IsCanonical128 (σ adr)) (hnode : IsCanonical128 (σ node)) (sibs : Nat → E)
    (hsibs : ∀ l, IsCanonical128 (sibs l))
    (hans : mFoldAns CM (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) sibs (F.height - 1) 0 (σ node))
    (ho : (σ (out (2 * (index / 2 ^ (F.height - 1)))), σ (out (2 * (index / 2 ^ (F.height - 1)) + 1))) =
      lvlHashC CM (σ pp) (σ adr + word (F.addr index (F.height - 2)) 0 0) (index.testBit (F.height - 2))
        (sibs (F.height - 2)) (mFoldC CM (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) sibs
          (F.height - 2) 0 (σ node)))
    (hret1 : σ ret1 = r1) (hret2 : σ ret2 = r2) :
    CompletesB CM.sem C rd b (b + 7 * (F.height - 2) + 5) (spArm pp md adr node F out ret1 ret2 r1 r2 index b) σ
      (fun _ => True) := by
  obtain ⟨hp, hm, ha, hn⟩ := hin
  rw [show F.height - 1 = F.height - 2 + 1 by omega, mFoldAns_succ] at hans
  obtain ⟨hlb, hlv, hlvge⟩ := spLevels_below (pp := pp) (md := md) (adr := adr) F index (F.height - 2) 0 node b
    ⟨hp, hm, ha, hn⟩
  simp only [spArm, List.append_assoc]
  refine CompletesB.append (m := b + 7 * (F.height - 2)) (by omega) (by omega) hlb
    (spLevels_comp F index sibs hsibs (F.height - 2) 0 node b σ ⟨hp, hm, ha, hn⟩ hmd hpp hadr hnode hans.1).withExt
    fun σ1 _ ⟨hv, he1⟩ => ?_
  have hk1 : ∀ v : V, NB b v → σ1 v = σ v := fun v hv' => he1.out (out_of_lt hv')
  have hko : ∀ v : V, Out b (b + 7 * (F.height - 2) + 5) v → σ1 v = σ v := fun v hv' =>
    he1.out (hv'.mono le_rfl (by omega))
  refine CompletesB.append_tail ((spLevel_comp (CM := CM) (C := C) (rd := rd) (s := sibs (F.height - 2))
    ⟨hp.mono (by omega), hm.mono (by omega), ha.mono (by omega), hlv⟩
    ((hout _).mono (by omega) le_rfl) ((hout _).mono (by omega) le_rfl) (by rw [hk1 md hm, hmd])
    (by rw [hk1 pp hp]; exact hpp) (by rw [hk1 adr ha]; exact hadr) ?_ (hsibs _) ?_ ?_).mono (by omega) (by omega)
    fun _ _ => trivial) fun σ2 he2 next kret hnx => ?_
  · rw [hv]
    rcases Nat.eq_zero_or_pos (F.height - 2) with h0 | h0
    · rw [h0]; exact hnode
    · obtain ⟨k, hk⟩ : ∃ k, F.height - 2 = k + 1 := ⟨F.height - 2 - 1, by omega⟩
      rw [hk, mFoldC_succ]; exact (isCanonical128_hcellC _).1
  · rw [hv, hk1 pp hp, hk1 adr ha]
    simpa [lvlCells, foldAddr, Nat.zero_add] using hans.2
  · rw [hko _ (hout _), hko _ (hout _), ho, hv, hk1 pp hp, hk1 adr ha]
  · simp only [hintW, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, true_and]
    have hk2 : ∀ v : V, Out b (b + 7 * (F.height - 2) + 5) v → σ2 v = σ v := fun v hv' =>
      (he2.out (hv'.mono (by omega) le_rfl)).trans (hko v hv')
    exact ⟨by rw [hk2 _ hr1, hret1], by rw [hk2 _ hr2, hret2], hnx⟩

/-! ## A fold's dispatch -/


/-- **A fold's dispatch is complete over the model** (`spMatch_complete`), its levels answered: at `x = g^a`, the fold of `node` at leaf `a` over the
siblings lands in the output the leaf's top bit names, the last sibling in the other, the arm's
second constant in `ret2`. -/
theorem spMatch_comp {σ : Val} {pp md adr node ret1 x : V} {F : Fold} (hF : F.height = 3 ∨ F.height = 4)
    {r1 r2 : Nat → E} {b a : Nat} (ha : a < 2 ^ F.height)
    (hin : NB b pp ∧ NB b md ∧ NB b adr ∧ NB b node ∧ NB b ret1 ∧ NB b x)
    (hmd : σ md = mdw 64 true) (hpp : IsCanonical128 (σ pp)) (hadr : IsCanonical128 (σ adr))
    (hnode : IsCanonical128 (σ node)) (sibs : Nat → E) (hsibs : ∀ l, IsCanonical128 (sibs l))
    (hans : mFoldAns CM (σ pp) (foldAddr σ adr F a) (fun l => a.testBit l) sibs (F.height - 1) 0 (σ node))
    (hx : σ x = ofK (gpow a)) (hret1 : σ ret1 = r1 a) :
    CompletesB CM.sem C rd b (spArms pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b).2
      [.match_ x (spArms pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b).1] σ
      (fun σ' => σ' (spOut F b (2 * (a / 2 ^ (F.height - 1)))) =
          mFoldC CM (σ pp) (foldAddr σ adr F a) (fun l => a.testBit l) sibs (F.height - 1) 0 (σ node) ∧
        σ' (spOut F b (2 - 2 * (a / 2 ^ (F.height - 1)))) = sibs (F.height - 1) ∧ σ' (spRet2 F b) = r2 a) := by
  obtain ⟨hp, hm, hadB, hn, hr1B, hxB⟩ := hin
  obtain ⟨hba, hbae, h2, hh, hout, hpRb, hpRe, hpRo, d1, d2, d3, d4, d5, d6⟩ := spMatch_layout (b := b) hF ha
  have hH : 2 ^ (F.height - 1) < 2 ^ F.height := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hend : (spArms pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b).2 =
      b + (2 ^ F.height * (7 * (F.height - 2) + 5) + 4 + 1) := by
    rw [spArms_snd_eq]; simp only [Nat.zero_add]; rw [spArm_base]
    simp only [Nat.two_pow_pos, ↓reduceIte, hH]
  rw [hend]
  set ba := b + (a * (7 * (F.height - 2) + 5) + (if 0 < a then 4 else 0) + (if 2 ^ (F.height - 1) < a then 1 else 0))
  set en := b + (2 ^ F.height * (7 * (F.height - 2) + 5) + 4 + 1)
  set q := a / 2 ^ (F.height - 1)
  set pO := spOutN F b (2 * q)
  set pO1 := spOutN F b (2 * q + 1)
  set pS := spOutN F b (2 - 2 * q)
  set pR := b + 7 * (F.height - 2) + 8
  set y := mFoldC CM (σ pp) (foldAddr σ adr F a) (fun l => a.testBit l) sibs (F.height - 2) 0 (σ node)
  set o := lvlHashC CM (σ pp) (σ adr + word (F.addr a (F.height - 2)) 0 0) (a.testBit (F.height - 2))
    (sibs (F.height - 2)) y
  set σ1 := upds σ [(pO, o.1), (pO1, o.2), (pS, sibs (F.height - 1)), (pR, r2 a)]
  have hmem : ∀ p ∈ [(pO, o.1), (pO1, o.2), (pS, sibs (F.height - 1)), (pR, r2 a)], b ≤ p.1 ∧ p.1 < en := by
    have := hout (2 * q) (by omega); have := hout (2 * q + 1) (by omega); have := hout (2 - 2 * q) (by omega)
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> omega
  have he1 : Ext b en σ σ1 := upds_ext σ _ hmem
  have hk1 : ∀ v : V, NB b v → σ1 v = σ v := fun v hv => he1.out (out_of_lt hv)
  have l1 : σ1 (.n pO) = o.1 := upds_cons_self _ _ _ _
  have l2 : σ1 (.n pO1) = o.2 := by
    simp only [σ1]; rw [upds_cons_ne _ _ _ (Ne.symm d1)]; exact upds_cons_self _ _ _ _
  have l3 : σ1 (.n pS) = sibs (F.height - 1) := by
    simp only [σ1]; rw [upds_cons_ne _ _ _ (Ne.symm d2), upds_cons_ne _ _ _ (Ne.symm d3)]; exact upds_cons_self _ _ _ _
  have l4 : σ1 (.n pR) = r2 a := by
    simp only [σ1]
    rw [upds_cons_ne _ _ _ (Ne.symm d4), upds_cons_ne _ _ _ (Ne.symm d5), upds_cons_ne _ _ _ (Ne.symm d6)]
    exact upds_cons_self _ _ _ _
  have houtA : ∀ k, Out ba (ba + (7 * (F.height - 2) + 5)) (spOut F b k) := fun k => by
    rw [spOut_eq, spOutN_min]
    rcases (hout (min k 3) (by omega)).2.2 with h' | h'
    · exact out_of_lt ⟨_, h', rfl⟩
    · exact out_of_ge ⟨_, h', rfl⟩
  have hR2 : Out ba (ba + (7 * (F.height - 2) + 5)) (spRet2 F b) := by
    rcases hpRo with h' | h'
    · exact out_of_lt ⟨pR, h', rfl⟩
    · exact out_of_ge ⟨pR, h', rfl⟩
  have hA : foldAddr σ1 adr F a = foldAddr σ adr F a := by funext l'; simp only [foldAddr, hk1 adr hadB]
  have harm := spArm_comp (CM := CM) (C := C) (rd := rd) (σ := σ1) (pp := pp) (md := md) (adr := adr) (node := node)
    (ret1 := ret1) (ret2 := spRet2 F b) (F := F) (out := spOut F b) (r1 := r1 a) (r2 := r2 a) (index := a)
    (b := ba) (by omega) ⟨hp.mono hba, hm.mono hba, hadB.mono hba, hn.mono hba⟩ houtA (out_of_lt (hr1B.mono hba))
    hR2 (by rw [hk1 md hm, hmd]) (by rw [hk1 pp hp]; exact hpp) (by rw [hk1 adr hadB]; exact hadr)
    (by rw [hk1 node hn]; exact hnode) sibs hsibs
    (by rw [hk1 pp hp, hk1 node hn, hA]; exact hans)
    (by rw [spOut_eq, spOut_eq, l1, l2, hk1 pp hp, hk1 adr hadB, hk1 node hn, hA]) (by rw [hk1 ret1 hr1B, hret1]) l4
  obtain ⟨σ', he', -, hh2⟩ := harm
  have hget := spArms_get_base pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b a ha
  rw [List.getElem?_eq_getElem (by rw [spArms_length]; exact ha), Option.some.injEq] at hget
  simp only [Nat.zero_add] at hget
  rw [spArm_base] at hget
  refine ⟨σ', he1.comp (he'.mono hba hbae), ⟨?_, ?_, ?_⟩, fun next kret hnx => ?_⟩
  · rw [he'.out (houtA _), spOut_eq, l1, show F.height - 1 = F.height - 2 + 1 by omega, mFoldC_succ]
    simp only [o, lvlHashC, lvlCells, Nat.zero_add, foldAddr]
    rfl
  · rw [he'.out (houtA _), spOut_eq, l3]
  · rw [he'.out hR2]; exact l4
  · refine (holdsListB_match_singleS x _ next kret σ').mpr ⟨a, by rw [spArms_length]; exact ha, ?_, ?_⟩
    · rw [he'.out (out_of_lt (hxB.mono hba)), hk1 x hxB, hx]
    · rw [hget]; exact hh2 next kret hnx


/-- The deployed `spMatch_complete`, from the model's at `CompModel.deployed`. -/
theorem spMatch_of_comp {σ : Val} {pp md adr node ret1 x : V} {F : Fold} (hF : F.height = 3 ∨ F.height = 4)
    {r1 r2 : Nat → E} {b a : Nat} (ha : a < 2 ^ F.height)
    (hin : NB b pp ∧ NB b md ∧ NB b adr ∧ NB b node ∧ NB b ret1 ∧ NB b x)
    (hmd : σ md = mdw 64 true) (hpp : IsCanonical128 (σ pp)) (hadr : IsCanonical128 (σ adr))
    (hnode : IsCanonical128 (σ node)) (sibs : Nat → E) (hsibs : ∀ l, IsCanonical128 (sibs l))
    (hx : σ x = ofK (gpow a)) (hret1 : σ ret1 = r1 a) :
    Completes C rd b (spArms pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b).2
      [.match_ x (spArms pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b).1] σ
      (fun σ' => σ' (spOut F b (2 * (a / 2 ^ (F.height - 1)))) =
          mFold (σ pp) (foldAddr σ adr F a) (fun l => a.testBit l) sibs (F.height - 1) 0 (σ node) ∧
        σ' (spOut F b (2 - 2 * (a / 2 ^ (F.height - 1)))) = sibs (F.height - 1) ∧ σ' (spRet2 F b) = r2 a) := by
  have := spMatch_comp (CM := CompModel.deployed) (C := C) (rd := rd) (r2 := r2) hF ha hin hmd hpp hadr hnode
    sibs hsibs (mFoldAns_deployed _ _ _ _ _ _ _) hx hret1
  rw [mFoldC_deployed] at this
  exact this.of_deployed

end
end LeanVM.Guest.B1.Sig
