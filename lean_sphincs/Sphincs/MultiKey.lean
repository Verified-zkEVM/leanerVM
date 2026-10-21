import Sphincs.MultiPad

/-! **The padded reduction of one key.** The experiments of the padded adversary in terms of the
weighted counts of the game of `Y`: its wins within `q` hash calls are wins of the padded
adversary within `q + F`, and the short calls of its internalized experiment are at most the
calls of `Y` on its key plus `F` plus two. With `Y` the reduction to key `j` these are counts of
the multi-user game checking key `j`. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Multi

open MultiEager Completeness Internalize Short Eager SeedCoupling KeyOnly

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ### Changing the weights -/

theorem cntW_hom {ω ω' : Type} [AddCommMonoid ω] [AddCommMonoid ω'] (w : HashInput → ω) (f : ω →+ ω')
    {α : Type} (g : OracleComp OracleWorld α) :
    cntW (fun x => f (w x)) g = (fun r => (r.1, f r.2)) <$> cntW w g := by
  induction g using OracleComp.inductionOn with
  | pure value => simp [cntW_pure]
  | query_bind input next ih =>
      simp only [cntW_query_bind, ih, map_bind, bind_map_left, map_pure, map_add]
      congr 1
      funext answer
      congr 1
      funext r
      cases input <;> simp [weightOf]

theorem runW_hom {ω ω' : Type} [AddCommMonoid ω] [AddCommMonoid ω'] (w : HashInput → ω) (f : ω →+ ω')
    {α : Type} (g : OracleComp OracleWorld α) :
    runW (fun x => f (w x)) g = (fun r => (r.1, f r.2)) <$> runW w g := by
  rw [runW, runW, cntW_hom, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
    Functor.map_map]

theorem countHashQueries_eq_cntW {α : Type} (g : OracleComp OracleWorld α) :
    countHashQueries g = cntW (fun _ => (1 : ℕ)) g := by
  induction g using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [countHashQueries_query_bind, cntW_query_bind]
      simp only [ih]
      cases input <;> rfl

theorem countShort_eq_cntW {α : Type} (g : OracleComp OracleWorld α) :
    SphincsBase.QueryCap.counted ShortQuery g = cntW wS g := by
  induction g using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [SphincsBase.QueryCap.counted_query_bind, cntW_query_bind]
      simp only [ih]
      cases input with
      | inl d => rfl
      | inr x => simp [weightOf, wS, ShortQuery]

variable [Params]

theorem gameCoreDet_eq_P (Y : Security.Adversary) : Det.gameCoreDet Y = Prod.fst <$> gameCoreDetP Y := by
  simp only [Det.gameCoreDet, gameCoreDetP, map_bind, map_pure]

/-- The experiment as a weighted count. -/
theorem experimentDet_eq_runW (Y : Security.Adversary) :
    Det.experimentDet Y = (fun r => (r.1.1, r.2)) <$> runW (fun _ => (1 : ℕ)) (gameCoreDetP Y) := by
  rw [Det.experimentDet_eq_rightRun, rightRun, countHashQueries_eq_cntW, gameCoreDet_eq_P, ← runW_map]
  rfl

/-- The internalized experiment as the short count of the game. -/
theorem experimentDet_internalize_eq (Y : Security.Adversary) :
    Det.experimentDet (internalize Y) =ᵈ (fun r => (r.1.1, r.2)) <$> runW wS (gameCoreDetP Y) := by
  refine (Det.evalDist_experimentDet_internalize Y).trans ?_
  rw [leftRun, countShort, countShort_eq_cntW, gameCoreDet_eq_P, ← runW_map]
  rfl

/-! ### The padded experiments -/

/-- **A win within `q` hash calls is a win of the padded adversary within `q + F`.** -/
theorem winWithin_le_padAdv (F q : ℕ) (Y : Security.Adversary) :
    Det.winWithin Y q ≤ Det.budgetedAdvantageDet (padAdv F Y) (q + F) := by
  unfold Det.winWithin Det.budgetedAdvantageDet
  rw [experimentDet_eq_runW, experimentDet_eq_runW, prEvent_map, prEvent_map,
    (runW_padAdv (fun _ => (1 : ℕ)) F Y).prEvent_eq, prEvent_map, gameCoreDetP_eq_gameCnt, runW_map,
    prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun r _ h => ?_
  simp only [smul_eq_mul, mul_one] at h ⊢
  exact ⟨h.1, by omega⟩

omit [Params] in
theorem wJ_padInput (p : PublicParameter) : (wJ (padInput p)).1 = 1 ∧ (wJ (padInput p)).2 p = 0 := by
  simp [wJ, wS, wPi, padInput_short, padInput_not_ofKey]

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- **The short calls of the padded adversary's internalized experiment**: at most the calls of `Y`
on its key, `F` and two, in mean. -/
theorem mean_short_padAdv (F M : ℕ) (Y : Security.Adversary) :
    mean (Det.experimentDet (internalize (padAdv F Y))) (fun r => ((min r.2 M : ℕ) : ℝ≥0∞)) ≤
      mean (runW wJ (gameCoreDetP Y)) (fun r => ((r.2.2 r.1.2 + 2 + max F (r.2.1 - r.2.2 r.1.2) : ℕ) : ℝ≥0∞)) := by
  rw [mean_congr (experimentDet_internalize_eq (padAdv F Y)), mean_map,
    show wS = fun x => (AddMonoidHom.fst ℕ (PublicParameter → ℕ)) (wJ x) from rfl, runW_hom, mean_map,
    mean_congr (runW_padAdv wJ F Y), mean_map, gameCoreDetP_eq_gameCnt, runW_map, mean_map]
  refine mean_mono_reach _ fun r hr => ?_
  have hc := gameCnt_counts Y r hr
  have hp := wJ_padInput r.1.1.2
  have key : min (r.2.1 + (F - r.1.2)) M ≤ r.2.2 r.1.1.2 + 2 + max F (r.2.1 - r.2.2 r.1.1.2) := by
    omega
  simp only [Function.comp_apply, AddMonoidHom.coe_fst, Prod.fst_add, Prod.smul_fst, smul_eq_mul, hp.1, mul_one]
  exact_mod_cast key

/-- The short calls of the padded adversary's internalized experiment, pointwise. -/
theorem support_short_padAdv (F : ℕ) (Y : Security.Adversary) (r : Bool × ℕ)
    (hr : Reach (Det.experimentDet (internalize (padAdv F Y))) r) :
    ∃ r', Reach (runW wS (gameCnt Y)) r' ∧ r.2 ≤ r'.2 + F := by
  rw [reach_congr (experimentDet_internalize_eq (padAdv F Y)), reach_map_iff] at hr
  obtain ⟨r1, hr1, rfl⟩ := hr
  rw [reach_congr (runW_padAdv wS F Y), reach_map_iff] at hr1
  obtain ⟨r3, hr3, rfl⟩ := hr1
  refine ⟨r3, hr3, ?_⟩
  have hp : wS (padInput r3.1.1.2) = 1 := by simp [wS, padInput_short]
  simp only [smul_eq_mul, hp, mul_one]
  omega

end Sphincs.Security.Multi
