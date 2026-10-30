/-
  LeanVM.Guest.B1.Tables.Vt.AsmTotals

  `verify_tables`' three bus totals are the specification's: the push, pull and count totals of
  `busRest` on the layout of the announced sizes.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SpecPhase

/-!
# The totals (G:2119-2180)

`vt_asm_totals`: with the facts `verify_sub` hands `verify_tables` (the point, the heights and
row counts, `block_kappa`, the squares, the bus weights), `bus_table_total[PUSH]`,
`bus_table_total[PULL]` and `bus_table_total[COUNT]` are the totals of `vtBus` (`vtAcc0`,
`vtAcc1`, `vtAcc2`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (blockSel)

@[expose] public section

theorem vt_length_eqKernel_foldl : ∀ (pt out : List E),
    (pt.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).length =
      out.length * 2 ^ pt.length
  | [], out => by simp
  | r :: pt, out => by
    rw [List.foldl_cons, vt_length_eqKernel_foldl pt, List.length_append, List.length_map,
      List.length_map, List.length_cons, pow_succ]
    ring

theorem vt_length_eqKernel (pt : List E) : (eqKernel pt).length = 2 ^ pt.length := by
  rw [eqKernel, vt_length_eqKernel_foldl]; simp

theorem vt_take3 (W : List E) (h : 3 ≤ W.length) :
    W.take 3 = [W.getD 0 0, W.getD 1 0, W.getD 2 0] := by
  match W, h with
  | a :: b :: c :: _, _ => rfl

theorem vt_take6 (W : List E) (h : 6 ≤ W.length) :
    W.take 6 = [W.getD 0 0, W.getD 1 0, W.getD 2 0, W.getD 3 0, W.getD 4 0, W.getD 5 0] := by
  match W, h with
  | a :: b :: c :: d :: e :: f :: _, _ => rfl

theorem vtWFinalPc_eq : vtWFinalPc = Verifier.gpow (2 ^ 19 - 1) := by
  rw [vtWFinalPc, vt_word_ofK, Verifier.gpow, gen_pow_eq_ofK,
    show K.ofBits 12261764870545049476 = Parameters.gpow (2 ^ 19 - 1) by decide +kernel]

theorem vt_beta1 {rd : Reader} {σ : Val} (h : VtH rd σ) : σ (.n 2853) = σ (.n 15) + 1 := by
  have a1 := h.atom 2405 (.const (.n 2852) (word 1 0 0)) (by decide +kernel)
  have a2 := h.atom 2406 (.add (.n 2853) (.n 15) (.n 2852)) (by decide +kernel)
  simp only [Atom.Holds] at a1 a2
  rw [a2, a1, tb_word_one]

theorem vt_pushPad_var {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 4411) = σ (.n 3036) + σ (.n 4406) + (1 + σ (.n 3984)) + σ (.n 27) := by
  have a1 := h.atom 3905 (.add (.n 4407) (.n 3036) (.n 4406)) (by decide +kernel)
  have a2 := h.atom 3906 (.const (.n 4408) (word 1 0 0)) (by decide +kernel)
  have a3 := h.atom 3907 (.add (.n 4409) (.n 4408) (.n 3984)) (by decide +kernel)
  have a4 := h.atom 3908 (.add (.n 4410) (.n 4407) (.n 4409)) (by decide +kernel)
  have a5 := h.atom 3909 (.add (.n 4411) (.n 4410) (.n 27)) (by decide +kernel)
  simp only [Atom.Holds] at a1 a2 a3 a4 a5
  rw [a5, a4, a3, a2, a1, tb_word_one]

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ)
include hμ

set_option maxHeartbeats 1000000 in
/-- **The three totals.** -/
theorem vt_asm_totals {σ : Val} (h : VtH Lm.read σ) {bc : List K} (hbc : bc.length = 2 ^ 23)
    {point : List E} (hz : TbReadsAt Lm.read (σ (.n 8)) point)
    (hmu : σ (.n 9) = gen ^ point.length) (hml : point.length < 33)
    (hsq : TbReadsAt Lm.read (σ (.n 13)) gSquaresList) {lm : ℕ} (hlm : lm ≤ 32)
    {rows : List ℕ} (hr : rows.length = 6) (hτ : ∀ t < 6, vtHt rows t < 29)
    (hdim : ∀ t < 6, LoadHolds Lm.read (σ (.n 10)) (t + 1) (gen ^ vtHt rows t))
    (hbk : TbReadsAt Lm.read (σ (.n 12))
      (blockKappaWords (gen ^ lm) ((vtTauList (vtHt rows)).map (gen ^ ·))))
    {alphas : List E} (hal : alphas.length = 4)
    (hW : TbReadsAt Lm.read (σ (.n 14)) (eqKernel alphas))
    (hpw : ∀ t < 6, σ (.n (vtPadV t)) = paddingWeight (point.take (vtHt rows t)) (vtRw rows t)) :
    σ (.n 4411) = (vtAcc0 (layoutOf bc lm rows) alphas (σ (.n 15)) point
      [σ (.n 2914), σ (.n 2927), σ (.n 2940)] (σ (.n 2639)) (σ (.n 27))).2 ∧
    σ (.n 4924) = (vtAcc1 (layoutOf bc lm rows) alphas (σ (.n 15)) point
      [σ (.n 2914), σ (.n 2927), σ (.n 2940)] (σ (.n 4444)) (σ (.n 4502)) (σ (.n 2639))
      (σ (.n 27)) (σ (.n 28))).2 ∧
    σ (.n 5816) = (vtAcc2 (layoutOf bc lm rows) alphas (σ (.n 15)) point
      [σ (.n 2914), σ (.n 2927), σ (.n 2940)] (σ (.n 4444)) (σ (.n 4502)) (σ (.n 2639))
      (σ (.n 27)) (σ (.n 28)) (σ (.n 29))).2 := by
  obtain ⟨l1, l2, k1, k2, s0, s1, s2, c0, c1, c2, hS, hsum, hSC, hsumC⟩ :=
    vt_sels hμ Lm h hz hmu hml hsq hlm hτ hdim hbk
  obtain ⟨i1, i1', i2, i2', m0, m1, m2, -⟩ := vt_fw h hz l1 (by omega) l2 k1 k2
  have hWl : (eqKernel alphas).length = 16 := by rw [vt_length_eqKernel, hal]; rfl
  set W : ℕ → E := fun i ↦ (eqKernel alphas).getD i 0 with hWd
  have hw : ∀ i < 16, LoadHolds Lm.read (σ (.n 14)) i (W i) := fun i hi ↦ by
    have := hW i (by omega)
    rwa [← List.getD_eq_getElem _ 0] at this
  have hpw' : ∀ t < 6, paddingWeight (point.take (vtHt rows t)) (vtRw rows t) =
      σ (.n (vtPadV t)) := fun t ht ↦ (hpw t ht).symm
  have e0 := vt_total0 hbc alphas (σ (.n 15)) point [σ (.n 2914), σ (.n 2927), σ (.n 2940)]
    (σ (.n 2639)) (σ (.n 27)) _ _ _ (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t)))
    s0.symm s1.symm s2.symm (fun i hi ↦ hS i hi) hpw' hr
  have e1 := vt_total1 hbc alphas (σ (.n 15)) point [σ (.n 2914), σ (.n 2927), σ (.n 2940)]
    (σ (.n 4444)) (σ (.n 4502)) (σ (.n 2639)) (σ (.n 27)) (σ (.n 28)) _ _ _ (fun c ↦ σ (.n c))
    (fun t ↦ σ (.n (vtPadV t))) s0.symm s1.symm s2.symm (fun i hi ↦ hS i hi) hpw' hr
  have e2 := vt_total2 (bc := bc) (lm := lm) alphas (σ (.n 15)) point
    [σ (.n 2914), σ (.n 2927), σ (.n 2940)] (σ (.n 4444)) (σ (.n 4502)) (σ (.n 2639))
    (σ (.n 27)) (σ (.n 28)) (σ (.n 29)) (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W
    (fun i hi ↦ hSC i hi) hpw' hr
  have hpush := vt_push_total h hw
  have hfw := vt_push_fw h hw
  rw [vt_beta1 h] at hpush
  have hpad : σ (.n 4406) = vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W
      (σ (.n 15) + 1) vtPushPadData := by
    have := (vt_pushPad_var h).symm.trans hpush
    linear_combination this
  have hfp : ∀ (L : Layout), L.logMemory = lm → L.logBytecode = 19 →
      vtFpPush L alphas point [σ (.n 2914), σ (.n 2927), σ (.n 2940)] (σ (.n 2639)) =
        [W 0 + W 1 + W 2, W 0 * gen + W 1 * σ (.n 2908) + W 2 + W 3 * σ (.n 2914) +
          W 4 * σ (.n 2927) + W 5 * σ (.n 2940), W 0 * gen ^ 2 + W 1 * σ (.n 2983) + W 2 +
          σ (.n 2639)] ∧
      vtFpPull L alphas point [σ (.n 2914), σ (.n 2927), σ (.n 2940)] (σ (.n 4444))
          (σ (.n 4502)) (σ (.n 2639)) =
        [W 0 + W 1 * vtWFinalPc + W 2, W 0 * gen + W 1 * σ (.n 2908) + W 2 * σ (.n 4444) +
          W 3 * σ (.n 2914) + W 4 * σ (.n 2927) + W 5 * σ (.n 2940),
          W 0 * gen ^ 2 + W 1 * σ (.n 2983) + W 2 * σ (.n 4502) + σ (.n 2639)] := by
    intro L hL1 hL2
    simp only [vtFpPush, vtFpPull, fingerprints, hL1, hL2, vt_take3 (eqKernel alphas) (by omega),
      vt_take6 (eqKernel alphas) (by omega), ← i1, ← i2, vtWFinalPc_eq, dot, List.zipWith_cons_cons,
      List.zipWith_nil_left, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append,
      sepState, sepMem, sepBytecode, Verifier.gpow, pow_zero]
    refine ⟨?_, ?_⟩ <;> simp only [List.cons.injEq, and_true] <;> refine ⟨?_, ?_, ?_⟩ <;> ring
  obtain ⟨fP, fQ⟩ := hfp (layoutOf bc lm rows) (vt_layout_logMemory bc lm rows)
    (vt_layout_logBytecode bc lm rows hbc)
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, fP, hpush, hfw, hsum]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring
  · rw [e1, fQ, vt_pull_total h hw, hpad, c0, c1, c2, i1', i2', m0, m1, m2]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring
  · rw [e2, vt_count_total h W, hsumC]
    ring

end

end
end LeanVM.Guest.B1.Tables
