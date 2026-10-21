/-
  LeanVM.Guest.B1.Comp.Da.Cell

  `da_verify_cell` over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Basic
public import LeanVM.Guest.B1.Da.CellM

/-!
# `da_verify_cell` over a completeness model

The backward half of `da_verify_cell_iff` over a `CompModel`, from W2's meaning over the model's
answers (`Meaning_da_verify_cellWith CM.hm`: the symbols' bytes answered): the 32 blocks of the
packed cells check through the model's chain of the symbols' bytes (`vc_bytes`,
`CompModel.chain_checks_blocks`), the states `chainSt` in place of the deployed `vcSt`;
`da_verify_cell_comp` (and its form with the symbols named, `cellOutM_comp`). At
`CompModel.deployed` the deployed backward direction (`da_verify_cell_of_comp`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

section
variable (lv : E) (x w : ℕ → E) (S : ℕ → E × E)

/-- The values of `da_verify_cell` with the chain's states `S` (`vcVals` at the deployed chain). -/
def vcValsS (k : ℕ) : E :=
  if k = 0 then lv else
  if k < 257 then x (k - 1) else
  if k < 265 then [wY, wY * x 1, x 0 + wY * x 1, w 0, w 0 * x 0, w 1, w 1 * x 1, vcS x w 0].getD (k - 257) 0
  else
  if k < 1408 then (vcPv x w ((k - 256) / 9)).getD ((k - 256) % 9) 0 else
  if k < 1506 then [(S ((k - 1408) / 3)).1, (S ((k - 1408) / 3)).2,
    vcMd ((k - 1408) / 3)].getD ((k - 1408) % 3) 0 else
  [(S 32).1, (S 32).2, vcS x w 127].getD (k - 1506) 0

theorem vcValsS_sym {k : ℕ} (hk : k < 256) : vcValsS lv x w S (k + 1) = x k := by
  unfold vcValsS; rw [ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel]

theorem vcValsS_p0 {r : ℕ} (hr : r < 8) : vcValsS lv x w S (257 + r) =
    [wY, wY * x 1, x 0 + wY * x 1, w 0, w 0 * x 0, w 1, w 1 * x 1, vcS x w 0].getD r 0 := by
  unfold vcValsS
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel_left]

theorem vcValsS_p {e r : ℕ} (he : 1 ≤ e) (he' : e < 128) (hr : r < 9) :
    vcValsS lv x w S (256 + 9 * e + r) = (vcPv x w e).getD r 0 := by
  unfold vcValsS
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show (256 + 9 * e + r - 256) / 9 = e by omega, show (256 + 9 * e + r - 256) % 9 = r by omega]

theorem vcValsS_st {b r : ℕ} (hr : r < 3) (hb : 1408 + 3 * b + r < 1506) :
    vcValsS lv x w S (1408 + 3 * b + r) = [(S b).1, (S b).2, vcMd b].getD r 0 := by
  unfold vcValsS
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_pos' hb, show (1408 + 3 * b + r - 1408) / 3 = b by omega,
    show (1408 + 3 * b + r - 1408) % 3 = r by omega]

theorem vcValsS_end {r : ℕ} (hr : r < 3) :
    vcValsS lv x w S (1506 + r) = [(S 32).1, (S 32).2, vcS x w 127].getD r 0 := by
  unfold vcValsS
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_neg' (by omega), Nat.add_sub_cancel_left]

end

theorem vcBlkB_bwd {Sm : BlakeSem} {rd : Reader} {σ : Val} {b : ℕ}
    (h1 : σ (.n (1410 + 3 * b)) = word (64 * (b + 1)) (if b + 1 = 32 then 4294967295 else 0) 0)
    (h2 : Sm.check ![σ (.n (vcP (4 * b))), σ (.n (vcP (4 * b + 1))), σ (.n (vcP (4 * b + 2))),
        σ (.n (vcP (4 * b + 3)))] (σ (.n (1408 + 3 * b))) (σ (.n (1409 + 3 * b)))
        (σ (.n (1411 + 3 * b))) (σ (.n (1412 + 3 * b))) (σ (.n (1410 + 3 * b)))) :
    ∀ a ∈ vcBlk b, a.HoldsB Sm rd σ := by
  simpa only [vcBlk, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true] using
    And.intro h1 h2

/-- **`da_verify_cell` is complete over a completeness model**: when the model answers the
symbols' bytes, the relation holds under the model's semantics. -/
theorem da_verify_cell_comp {CM : CompModel} {rd : Reader} {args rets : List E}
    (h : Meaning_da_verify_cellWith CM.hm rd args rets) :
    coreProgram.RelB CM.sem rd "da_verify_cell" args rets := by
  obtain ⟨lv, d0, d1, s, rfl, rfl, syms, ws, hsl, hwl, hws, ⟨d, hH, hd⟩, hs⟩ := h
  let sy : ℕ → K := fun k => syms.getD k 0
  let x : ℕ → E := fun k => ofK (sy k)
  let w : ℕ → E := fun k => ws.getD k 0
  have hload : ∀ k < 256, LoadHolds rd lv k (w k) := fun k hk => by
    have := hws k (by omega)
    rwa [← List.getD_eq_getElem _ 0] at this
  have hsyms : (List.range 256).map sy = syms := by
    rw [← hsl]
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, sy]
    exact List.getD_eq_getElem _ _ h2
  -- the chain
  have hH' : CM.H ((List.range (31 + 1)).flatMap fun j => blockBytes (vcBlocks sy j)) = some d := by
    rw [vc_bytes sy, hsyms]; exact hH
  have hchk := CM.chain_checks_blocks (md := vcMd) hH'
    (fun j _ r => by fin_cases r <;> exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl)
    (fun j hj => by simp only [vcMd]; congr 1; simp only [decide_eq_false_iff_not]; omega)
    (by simp [vcMd])
  set X := (List.range (31 + 1)).flatMap fun j => blockBytes (vcBlocks sy j) with hX
  let S := CM.chainSt X d
  have hlenX : X.length = 64 * 32 := by rw [hX, CompModel.length_flatMap_blocks]
  have hS0 : S 0 = ivCells := CM.chainSt_zero X d
  have hst : S 32 = (d0, d1) := by
    rw [hd]; exact CM.chainSt_succ_of d (n := 31) (by rw [hlenX])
  have hsum : vcS x w 127 = s := by rw [hs]; rfl
  rw [relB_of_find find_da_verify_cell]
  let σ : Val := fun v => vcValsS lv x w S v.idx
  have hσ : ∀ k, σ (.n k) = vcValsS lv x w S k := fun _ => rfl
  have hsym : ∀ k < 256, σ (.n (k + 1)) = x k := fun k hk => vcValsS_sym lv x w S hk
  have hcell : ∀ e < 128, σ (.n (vcP e)) = vcCell sy e := by
    intro e he
    have hp : σ (.n (vcP e)) = x (2 * e) + wY * x (2 * e + 1) := by
      rcases Nat.eq_zero_or_pos e with rfl | hpos
      · exact vcValsS_p0 lv x w S (r := 2) (by omega)
      · rw [show vcP e = 256 + 9 * e + 2 by unfold vcP; rw [ite_neg' (by omega)]; omega]
        exact vcValsS_p lv x w S (r := 2) hpos he (by omega)
    rw [hp, vc_pack (ofK_isInK _) (ofK_isInK _)]
    simp [vcCell]
  refine ⟨σ, rfl, ?_⟩
  simp only [vcBody, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
    forall_mem_flatMap_range, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true,
    true_and, List.map_cons, List.map_nil]
  refine ⟨⟨⟨⟨⟨?_, fun i hi => ?_⟩, ?_, ?_⟩, fun b hb => ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · -- pair 0
    refine (forall_holdsB_noBlake (by simp [vcPair0, atomNoBlake])).mpr ?_
    have hv : ∀ r < 8, σ (.n (257 + r)) =
        [wY, wY * x 1, x 0 + wY * x 1, w 0, w 0 * x 0, w 1, w 1 * x 1, vcS x w 0].getD r 0 :=
      fun r hr => vcValsS_p0 lv x w S hr
    have h1 : σ (.n 1) = x 0 := hsym 0 (by omega)
    have h2 : σ (.n 2) = x 1 := hsym 1 (by omega)
    have h0 : σ (.n 0) = lv := rfl
    simp only [vcPair0, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, h0, h1, h2,
      hv 0 (by omega), hv 1 (by omega), hv 2 (by omega), hv 3 (by omega), hv 4 (by omega),
      hv 5 (by omega), hv 6 (by omega), hv 7 (by omega), List.getD_cons_succ, List.getD_cons_zero,
      true_and]
    refine ⟨⟨ofK_isInK _, ofK_isInK _⟩, hload 0 (by omega), hload 1 (by omega), ?_⟩
    simp [vcS, Finset.sum_range_succ]
  · -- pair i + 1
    refine (forall_holdsB_noBlake (by simp [vcPair, atomNoBlake])).mpr ?_
    refine vcPair_bwd (e := i + 1) (lv := lv)
      (fun r hr => vcValsS_p lv x w S (by omega) (by omega) hr)
      (hsym _ (by omega)) (hsym _ (by omega)) ?_ rfl (ofK_isInK _) (ofK_isInK _)
      (hload _ (by omega)) (hload _ (by omega)) (vcS_succ x w i)
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact vcValsS_p0 lv x w S (r := 7) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [show 255 + 9 * (j + 1 + 1) = 256 + 9 * (j + 1) + 8 by omega]
      exact vcValsS_p lv x w S (by omega) (by omega) (by omega)
  · show vcValsS lv x w S (1408 + 3 * 0 + 0) = _
    rw [vcValsS_st lv x w S (b := 0) (r := 0) (by omega) (by omega), iv0_word]
    simp only [List.getD_cons_zero, hS0]; rfl
  · show vcValsS lv x w S (1408 + 3 * 0 + 1) = _
    rw [vcValsS_st lv x w S (b := 0) (r := 1) (by omega) (by omega), iv1_word]
    simp only [List.getD_cons_succ, List.getD_cons_zero, hS0]; rfl
  · refine vcBlkB_bwd ?_ ?_
    · rw [hσ, show 1410 + 3 * b = 1408 + 3 * b + 2 by omega,
        vcValsS_st lv x w S (b := b) (r := 2) (by omega) (by omega), word_metadata]; rfl
    · rw [hcell _ (by omega), hcell _ (by omega), hcell _ (by omega), hcell _ (by omega)]
      simp only [hσ]
      have e0 := vcValsS_st lv x w S (b := b) (r := 0) (by omega) (by omega)
      have e1 := vcValsS_st lv x w S (b := b) (r := 1) (by omega) (by omega)
      have e2 := vcValsS_st lv x w S (b := b) (r := 2) (by omega) (by omega)
      have e3 := vcValsS_st lv x w S (b := b + 1) (r := 0) (by omega) (by omega)
      have e4 := vcValsS_st lv x w S (b := b + 1) (r := 1) (by omega) (by omega)
      rw [Nat.add_zero, show 1408 + 3 * (b + 1) = 1411 + 3 * b by omega] at e3
      rw [show 1408 + 3 * (b + 1) + 1 = 1412 + 3 * b by omega] at e4
      rw [Nat.add_zero] at e0
      rw [show 1408 + 3 * b + 1 = 1409 + 3 * b by omega] at e1
      rw [show 1408 + 3 * b + 2 = 1410 + 3 * b by omega] at e2
      rw [e0, e1, e2, e3, e4]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      exact hchk b (by omega)
  · show vcValsS lv x w S (1506 + 0) = vcValsS lv x w S (1408 + 3 * 32 + 0)
    rw [vcValsS_end lv x w S (r := 0) (by omega),
      vcValsS_st lv x w S (b := 32) (r := 0) (by omega) (by omega)]
    rfl
  · show vcValsS lv x w S (1506 + 1) = vcValsS lv x w S (1408 + 3 * 32 + 1)
    rw [vcValsS_end lv x w S (r := 1) (by omega),
      vcValsS_st lv x w S (b := 32) (r := 1) (by omega) (by omega)]
    rfl
  · show vcValsS lv x w S (1506 + 2) = vcValsS lv x w S (256 + 9 * 127 + 8)
    rw [vcValsS_end lv x w S (r := 2) (by omega),
      vcValsS_p lv x w S (e := 127) (r := 8) (by omega) (by omega) (by omega)]
    rfl
  · show [vcValsS lv x w S (1506 + 0), vcValsS lv x w S (1506 + 1),
      vcValsS lv x w S (1506 + 2)] = _
    rw [vcValsS_end lv x w S (r := 0) (by omega), vcValsS_end lv x w S (r := 1) (by omega),
      vcValsS_end lv x w S (r := 2) (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, hst, hsum]

/-- `da_verify_cell` over a completeness model, its symbols named (`CellOutM`). -/
theorem cellOutM_comp {CM : CompModel} {rd : Reader} {args rets : List E} {syms : List K}
    (h : CellOutM CM.hm rd args rets syms) :
    coreProgram.RelB CM.sem rd "da_verify_cell" args rets :=
  da_verify_cell_comp (meaning_of_cellOutM h)

/-! ## At the deployed model -/

theorem meaning_da_verify_cellWith_deployed {rd : Reader} {args rets : List E} :
    Meaning_da_verify_cellWith CompModel.deployed.hm rd args rets ↔
      Meaning_da_verify_cell rd args rets := by
  simp only [Meaning_da_verify_cellWith, Meaning_da_verify_cell, Ans, CompModel.hm,
    CompModel.deployed, Option.some.injEq, exists_eq_left']

theorem da_verify_cell_of_comp {rd : Reader} {args rets : List E}
    (h : Meaning_da_verify_cell rd args rets) : coreProgram.Rel rd "da_verify_cell" args rets := by
  rw [← relB_deployed]
  exact da_verify_cell_comp (CM := CompModel.deployed) (meaning_da_verify_cellWith_deployed.mpr h)

end
end LeanVM.Guest.B1.Digest
