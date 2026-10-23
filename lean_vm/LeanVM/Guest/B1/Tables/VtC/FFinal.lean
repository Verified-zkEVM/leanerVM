/-
  LeanVM.Guest.B1.Tables.VtC.FFinal

  `Vt/AsmForms.lean`'s forms' values and `Vt/AsmFinal.lean`'s final check on the window `VtF`:
  `termsPure`'s terminal value over the six tables is the guest's `air_acc` (`σ 11197`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FForms0
public import LeanVM.Guest.B1.Tables.VtC.FForms1
public import LeanVM.Guest.B1.Tables.VtC.FForms2
public import LeanVM.Guest.B1.Tables.VtC.FForms3
public import LeanVM.Guest.B1.Tables.VtC.FForms4
public import LeanVM.Guest.B1.Tables.VtC.FForms5
public import LeanVM.Guest.B1.Tables.VtC.FAir
public import LeanVM.Guest.B1.Tables.Vt.AsmFinal

/-!
# The forms and the final check, on the window

What the soundness proof read outside the window becomes hypotheses: the push and count blocks'
selectors (`vt_sels`'s), the pull blocks' copies of the push ones (`VtPullSelsH`, `vtPullSels*`'s),
`zeta1` (`vt_zeta1`'s) and the batching challenge's powers (`vt_xi_pow`'s).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (accFold_spec accumulateSide_fst blockSel termsPure
  length_tableWeights jumpConstraints_eq pyNConstraints)

@[expose] public section

/-- The pull blocks' selectors are their push twins' (`vtPullSels0 .. 5`). -/
def VtPullSelsH (σ : Val) : Prop :=
  ([σ (.n 4569), σ (.n 4576), σ (.n 4583), σ (.n 4590), σ (.n 4597)] = [σ (.n 3051), σ (.n 3066), σ (.n 3081), σ (.n 3096), σ (.n 3111)]) ∧
  ([σ (.n 4604), σ (.n 4611), σ (.n 4618), σ (.n 4625), σ (.n 4632)] = [σ (.n 3130), σ (.n 3149), σ (.n 3168), σ (.n 3187), σ (.n 3206)]) ∧
  ([σ (.n 4639), σ (.n 4646), σ (.n 4653)] = [σ (.n 3225), σ (.n 3244), σ (.n 3263)]) ∧
  ([σ (.n 4660), σ (.n 4667), σ (.n 4674), σ (.n 4681), σ (.n 4688)] = [σ (.n 3282), σ (.n 3301), σ (.n 3320), σ (.n 3339), σ (.n 3358)]) ∧
  ([σ (.n 4695), σ (.n 4702), σ (.n 4709), σ (.n 4716), σ (.n 4723)] = [σ (.n 3377), σ (.n 3396), σ (.n 3415), σ (.n 3434), σ (.n 3453)]) ∧
  ([σ (.n 4730), σ (.n 4737), σ (.n 4744), σ (.n 4751), σ (.n 4758), σ (.n 4765), σ (.n 4772), σ (.n 4779), σ (.n 4786), σ (.n 4793), σ (.n 4800), σ (.n 4807), σ (.n 4814), σ (.n 4821), σ (.n 4828), σ (.n 4835), σ (.n 4842), σ (.n 4849), σ (.n 4856), σ (.n 4863), σ (.n 4870), σ (.n 4877), σ (.n 4884), σ (.n 4891), σ (.n 4898), σ (.n 4905), σ (.n 4912), σ (.n 4919)] = [σ (.n 3472), σ (.n 3491), σ (.n 3510), σ (.n 3529), σ (.n 3548), σ (.n 3567), σ (.n 3586), σ (.n 3605), σ (.n 3624), σ (.n 3643), σ (.n 3662), σ (.n 3681), σ (.n 3700), σ (.n 3719), σ (.n 3738), σ (.n 3757), σ (.n 3776), σ (.n 3795), σ (.n 3814), σ (.n 3833), σ (.n 3852), σ (.n 3871), σ (.n 3890), σ (.n 3909), σ (.n 3928), σ (.n 3947), σ (.n 3966), σ (.n 3985)])

set_option maxHeartbeats 1000000 in
/-- **The forms' values.** -/
theorem vt_forms_valF {rd : Reader} {σ : Val} (hF : VtF rd σ) (bc : List K)
    (hbc : bc.length = 2 ^ 23) {point : List E} {lm : ℕ} {rows : List ℕ} (hr : rows.length = 6)
    (hP : ∀ i < 51, σ (.n (vtPushPadData.getD i default).2.2.1) =
      blockSel (vtSizesP lm (vtHt rows)) point.length (3 + i) point)
    (hC : ∀ i < 45, σ (.n (vtCountPadData.getD i default).2.2.1) =
      blockSel (vtSizesC (vtHt rows)) point.length i point)
    (hpull : VtPullSelsH σ) {alphas : List E} (hal : alphas.length = 4)
    (hW : TbReadsAt rd (σ (.n 14)) (eqKernel alphas)) {t : ℕ} (ht : t < 6) :
    ((vtAcc2 (layoutOf bc lm rows) alphas (σ (.n 15)) point
        [σ (.n 2914), σ (.n 2927), σ (.n 2940)] (σ (.n 4444)) (σ (.n 4502)) (σ (.n 2639))
        (σ (.n 27)) (σ (.n 28)) (σ (.n 29))).1.getD t []).map
        (·.evaluate ((vtEvT σ t).getD · 0)) =
      (vtFV.getD t []).map fun v ↦ σ (.n v) := by
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hpull
  have hkl : (eqKernel alphas).length = 16 := by
    rw [show (16 : ℕ) = 2 ^ alphas.length by rw [hal]; rfl]
    exact vt_length_eqKernel alphas
  have hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i ((eqKernel alphas).getD i 0) :=
    fun i hi ↦ by
      have := hW i (by omega)
      rwa [← List.getD_eq_getElem _ 0] at this
  obtain ⟨e0, e1, e2⟩ := vt_forms hbc alphas (σ (.n 15)) point
    [σ (.n 2914), σ (.n 2927), σ (.n 2940)] (σ (.n 4444)) (σ (.n 4502)) (σ (.n 2639))
    (σ (.n 27)) (σ (.n 28)) (σ (.n 29)) (fun c ↦ σ (.n c)) hP hC hr ⟨t, ht⟩ ((vtEvT σ t).getD · 0)
  simp only at e0 e1 e2
  rw [vt_three _ ((vt_forms3_shape bc lm hr _ _ _ _ _ _ _ _ _ _).2 t ht) {}]
  simp only [List.map_cons, List.map_nil, e0, e1, e2]
  have hev : ∀ c < vtW6.getD t 0, σ (.n (vtEvB (vtB6.getD t 0 + c))) = (vtEvT σ t).getD c 0 :=
    fun c hc ↦ (vt_evT_getD σ t c hc).symm
  interval_cases t
  · simp only [vtFV, List.getD_cons_zero, List.map_cons, List.map_nil]
    rw [vtSide00F hF hw hev, vtSide10F hF hw hev, q0, vtSide20F hF hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide01F hF hw hev, vtSide11F hF hw hev, q1, vtSide21F hF hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide02F hF hw hev, vtSide12F hF hw hev, q2, vtSide22F hF hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide03F hF hw hev, vtSide13F hF hw hev, q3, vtSide23F hF hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide04F hF hw hev, vtSide14F hF hw hev, q4, vtSide24F hF hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide05F hF hw hev, vtSide15F hF hw hev, q5, vtSide25F hF hev]
    rfl


set_option maxHeartbeats 4000000 in
/-- **The final check.** -/
theorem vt_asm_finalF {rd : Reader} {σ : Val} (hV : VtF rd σ) (bc : List K)
    (hbc : bc.length = 2 ^ 23) {point : List E} {lm : ℕ} {rows : List ℕ} (hr : rows.length = 6)
    (hdim : ∀ t < 6, LoadHolds rd (σ (.n 10)) (t + 1) (gen ^ vtHt rows t))
    (hP : ∀ i < 51, σ (.n (vtPushPadData.getD i default).2.2.1) =
      blockSel (vtSizesP lm (vtHt rows)) point.length (3 + i) point)
    (hC : ∀ i < 45, σ (.n (vtCountPadData.getD i default).2.2.1) =
      blockSel (vtSizesC (vtHt rows)) point.length i point)
    (hpull : VtPullSelsH σ)
    (hz1 : TbReadsAt rd (σ (.n 2767)) (point.map (1 + ·)))
    (hxi : σ (.n 5896) = 1 ∧ σ (.n 5897) = σ (.n 5895) ∧ σ (.n 5898) = σ (.n 5895) ^ 2 ∧
      σ (.n 5899) = σ (.n 5895) ^ 3 ∧ σ (.n 5900) = σ (.n 5895) ^ 4)
    {alphas : List E} (hal : alphas.length = 4)
    (hW : TbReadsAt rd (σ (.n 14)) (eqKernel alphas)) {n : ℕ}
    (hgn : σ (.n 5817) = gen ^ n) (hhn : ∀ t < 6, vtHt rows t ≤ n) (hnp : n ≤ point.length)
    {pts : List E} (hpl : pts.length = n)
    (hcp : ∀ j ≤ n, LoadHolds rd (σ (.n 5915)) j (pts.take j).prod)
    (hpe : EqPrefix rd (σ (.n 5936)) 1 (σ (.n 18)) (σ (.n 2767)) n)
    (hchi : ∀ i < n, LoadHolds rd (σ (.n 18)) (n - 1 - i) (pts.getD i 0)) :
    (termsPure ((powers (σ (.n 5895)) 5).take 2) ((powers (σ (.n 5895)) 5).drop 2) pts.reverse
      (List.zip (vtRows (tableHeightsOf rows)
        (vtAcc2 (layoutOf bc lm rows) alphas (σ (.n 15)) point
          [σ (.n 2914), σ (.n 2927), σ (.n 2940)] (σ (.n 4444)) (σ (.n 4502)) (σ (.n 2639))
          (σ (.n 27)) (σ (.n 28)) (σ (.n 29))).1 point pts) (vtEvsT σ)) 0 0 []).1 =
      σ (.n 11197) := by
  set F := (vtAcc2 (layoutOf bc lm rows) alphas (σ (.n 15)) point
    [σ (.n 2914), σ (.n 2927), σ (.n 2940)] (σ (.n 4444)) (σ (.n 4502)) (σ (.n 2639))
    (σ (.n 27)) (σ (.n 28)) (σ (.n 29))).1 with hF
  have hFv : ∀ t < 6, (F.getD t []).map (·.evaluate ((vtEvT σ t).getD · 0)) =
      (vtFV.getD t []).map fun v ↦ σ (.n v) := fun t ht ↦
    vt_forms_valF hV bc hbc hr hP hC hpull hal hW ht
  have hF6 := (vt_forms3_shape bc lm hr alphas (σ (.n 15)) point
    [σ (.n 2914), σ (.n 2927), σ (.n 2940)] (σ (.n 4444)) (σ (.n 4502)) (σ (.n 2639))
    (σ (.n 27)) (σ (.n 28)) (σ (.n 29))).1
  have hH6 : (tableHeightsOf rows).length = 6 := vt_tableHeightsOf_length hr
  set Wt := tableWeights (tableHeightsOf rows) point pts.reverse with hWt
  have hW6 : Wt.length = 6 := by rw [hWt, length_tableWeights, hH6]
  -- the weights
  have hwt : ∀ t < 6, ∀ {x τv cp pe : E}, σ (.n 5817) = x * τv →
      LoadHolds rd (σ (.n 10)) (t + 1) τv → LoadHolds rd (σ (.n 5915) * x) 0 cp →
      LoadHolds rd (σ (.n 5936) * τv) 0 pe → Wt.getD t 0 = cp * pe := by
    intro t ht x τv cp pe hx hτl hcpL hpeL
    exact vt_weight_guest hpl hnp hcp hpe hchi hz1 hgn (by rw [hH6]; exact ht) (hhn t ht) hx
      (tb_loadHolds_unique hτl (hdim t ht)) hcpL hpeL
  obtain ⟨x0, l0, c0, p0, v0⟩ := vtAir0F hV
  obtain ⟨x1, l1, c1, p1, v1⟩ := vtAir1F hV
  obtain ⟨x2, l2, c2, p2, v2⟩ := vtAir2F hV
  obtain ⟨x3, l3, c3, p3, v3⟩ := vtAir3F hV
  have hev4 : ∀ c < 14, σ (.n (vtEvB (53 + c))) = (vtEvT σ 4).getD c 0 :=
    fun c hc ↦ (vt_evT_getD σ 4 c hc).symm
  obtain ⟨x4, l4, c4, p4, v4⟩ := vtAir4F hV hev4
  obtain ⟨x5, l5, c5, p5, v5⟩ := vtAir5F hV
  have w0 := hwt 0 (by norm_num) x0 l0 c0 p0
  have w1 := hwt 1 (by norm_num) x1 l1 c1 p1
  have w2 := hwt 2 (by norm_num) x2 l2 c2 p2
  have w3 := hwt 3 (by norm_num) x3 l3 c3 p3
  have w4 := hwt 4 (by norm_num) x4 l4 c4 p4
  have w5 := hwt 5 (by norm_num) x5 l5 c5 p5
  have f0 := hFv 0 (by norm_num)
  have f1 := hFv 1 (by norm_num)
  have f2 := hFv 2 (by norm_num)
  have f3 := hFv 3 (by norm_num)
  have f4 := hFv 4 (by norm_num)
  have f5 := hFv 5 (by norm_num)
  simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons,
    List.map_nil] at f0 f1 f2 f3 f4 f5
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := vt_nConstraints_each
  obtain ⟨xp0, xp1, xp2, xp3, xp4⟩ := hxi
  rw [vtRows, ← hWt, vt_six Wt hW6 0, vt_tables_six, vt_six (tableHeightsOf rows) hH6 0,
    vt_six F hF6 [], vtEvsT]
  simp only [List.zip_cons_cons, List.zip_nil_left, termsPure, f0, f1, f2, f3, f4, f5,
    w0, w1, w2, w3, w4, w5, n0, n1, n2, n3, n4, n5, (vt_constraints _).1, (vt_constraints _).2.1,
    (vt_constraints _).2.2.1, (vt_constraints _).2.2.2.1, (vt_constraints _).2.2.2.2.1,
    (vt_constraints _).2.2.2.2.2, jumpConstraints_eq]
  rw [vt_air_totalF hV, v0, v1, v2, v3, v4, v5, xp0, xp1, xp2, xp3, xp4, tb_word_one]
  simp only [powers, powersFrom, dot, List.take, List.drop, List.zipWith_cons_cons,
    List.zipWith_nil_right, List.foldl_cons, List.foldl_nil]
  ring


end
end LeanVM.Guest.B1.Tables
