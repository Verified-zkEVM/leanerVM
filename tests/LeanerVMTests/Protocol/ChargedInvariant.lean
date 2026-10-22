/-
  LeanerVMTests.Protocol.ChargedInvariant

  The charged invariant on a two-query computation against a random oracle answering in
  `Fin 4`.
-/

module

public import LeanerVM.Protocol.ToVCVio.ChargedInvariant

/-!
# Charged-invariant controls

The invariant is "no cached answer is `0`". A fresh query breaks it with probability `1/4`, so
two queries break it with probability at most `2/4`, and a single query breaks it with
probability exactly `1/4`: the bound is attained, and it fails without the query budget. The
expected number of cached answers equal to `0` after two queries is at most `2/4`, and in a
two-element set at most `2 · 2/4`.

The potential form charges a bad event that two queries complete together, both oracles
answering `0`, once: the potential is the chance of completing it, every fresh query is charged
`1/16`, and the bound is `2/16`, where the invariant form charges each query `1/4`.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Protocol OracleComp OracleSpec MeasureTheory
open scoped ENNReal

@[expose] public section

/-- Two oracles, each answering in `Fin 4`. -/
abbrev TestSpec : OracleSpec (Fin 2) := Fin 2 →ₒ Fin 4

/-- One query. -/
def oneQuery : OracleComp TestSpec (Fin 4) :=
  (TestSpec.query 0 : OracleComp TestSpec (Fin 4))

/-- Two queries at distinct indices. -/
def twoQueries : OracleComp TestSpec (Fin 4 × Fin 4) := do
  let a ← (TestSpec.query 0 : OracleComp TestSpec (Fin 4))
  let b ← (TestSpec.query 1 : OracleComp TestSpec (Fin 4))
  return (a, b)

theorem twoQueries_bound : IsTotalQueryBound twoQueries 2 := by
  rw [twoQueries, isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun _ ↦ ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by omega, fun _ ↦ trivial⟩

/-- No cached answer is `0`. -/
def NoZero (c : TestSpec.QueryCache) : Prop := ∀ t, c t ≠ some 0

/-- A fresh query at a cache without `0` caches `0` with probability `1/4`. -/
theorem noZero_step (c : TestSpec.QueryCache) (t : Fin 2) (hc : NoZero c) :
    Pr{let u ← $ᵗ TestSpec.Range t}[¬ NoZero (c.cacheQuery t u)] ≤ 4⁻¹ := by
  refine (prEvent_mono _ _ (fun u ↦ u = 0) fun u hu ↦ ?_).trans
    (SampleableType.prEvent_uniformSample_eq_singleton (α := Fin 4) 0).le
  simp only [NoZero, not_forall, not_not] at hu
  obtain ⟨t', ht'⟩ := hu
  by_cases h : t' = t
  · subst h
    simpa using ht'
  · exact absurd ((QueryCache.cacheQuery_of_ne c u h).symm.trans ht') (hc t')

-- Two queries: the invariant fails with probability at most `2 · 1/4`.
example :
    Pr{let z ← (simulateQ TestSpec.randomOracle twoQueries).run ∅}[¬ NoZero z.2] ≤ 2 * 4⁻¹ :=
  probEvent_not_good_le_mul NoZero (fun c t _ hc ↦ noZero_step c t hc) twoQueries_bound
    (fun _ ↦ by simp)

-- One query fails the invariant with probability exactly `1/4`: the bound `1 · 1/4` is
-- attained, and no bound `0 · 1/4` holds, so the query budget is needed.
example :
    Pr{let z ← (simulateQ TestSpec.randomOracle oneQuery).run ∅}[¬ NoZero z.2] = 4⁻¹ := by
  have hrun : (simulateQ TestSpec.randomOracle oneQuery).run ∅ =
      (fun u ↦ (u, (∅ : TestSpec.QueryCache).cacheQuery 0 u)) <$> ($ᵗ Fin 4) := by
    simp [oneQuery, map_eq_bind_pure_comp]
  rw [hrun, prEvent_map, prEvent_congr _ _ (fun u ↦ u = 0) fun u ↦ ?_]
  · simpa using SampleableType.prEvent_uniformSample_eq_singleton (α := Fin 4) 0
  · constructor
    · intro h
      by_contra hu
      refine h fun t ht ↦ ?_
      by_cases h0 : t = 0
      · subst h0
        exact hu (by simpa using ht)
      · rw [QueryCache.cacheQuery_of_ne _ _ h0] at ht
        simp at ht
    · rintro rfl h
      exact h 0 (QueryCache.cacheQuery_self _ _ _)

-- Expected count: at most `2 · 1/4` cached answers are `0` after two queries.
example :
    ∫⁻ r, r ∂𝒟[(fun z ↦ answersIn (fun _ u ↦ u = 0) z.2) <$>
      (simulateQ TestSpec.randomOracle twoQueries).run ∅] ≤ 2 * 4⁻¹ := by
  simpa using expected_fresh_le (fun _ u ↦ u = 0)
    (fun _ ↦ (SampleableType.prEvent_uniformSample_eq_singleton (α := Fin 4) 0).le)
    twoQueries_bound ∅

-- A target set of two answers: at most `2 · 2/4` in expectation.
example :
    ∫⁻ r, r ∂𝒟[(fun z ↦ answersIn (fun _ (u : Fin 4) ↦ u ∈ ({0, 1} : Finset (Fin 4))) z.2) <$>
      (simulateQ TestSpec.randomOracle twoQueries).run ∅] ≤ 2 * (2 / 4) := by
  simpa using expected_fresh_in_le ({0, 1} : Finset (Fin 4)) twoQueries_bound

/-! ### A bad event completed by two queries, charged once -/

/-- Both oracles have answered `0`. -/
def BothZero (c : TestSpec.QueryCache) : Prop := c 0 = some 0 ∧ c 1 = some 0

/-- `1` once both oracles answered `0`; `1/4`, the chance of completing it, while one has
answered `0` and the other is unqueried; `0` otherwise. -/
noncomputable def pending (c : TestSpec.QueryCache) : ℝ≥0∞ :=
  if c 0 = some 0 ∧ c 1 = some 0 then 1
  else if (c 0 = some 0 ∧ c 1 = none) ∨ (c 1 = some 0 ∧ c 0 = none) then 4⁻¹ else 0

/-- The expectation of `a` on the answer `0` of a uniform draw. -/
theorem lintegral_ite_zero (a : ℝ≥0∞) :
    ∫⁻ r, r ∂𝒟[(fun u : Fin 4 ↦ if u = 0 then a else 0) <$> ($ᵗ Fin 4)] = a * 4⁻¹ := by
  let : MeasurableSpace (Fin 4) := ⊤
  have h := prEvent_eq_lintegral_id_evalDist_map_ite ($ᵗ Fin 4) (fun u ↦ u = 0)
  rw [SampleableType.prEvent_uniformSample_eq_singleton, lintegral_id_evalDist_map] at h
  rw [lintegral_id_evalDist_map]
  calc ∫⁻ x, (if x = 0 then a else 0) ∂𝒟[$ᵗ Fin 4]
      = ∫⁻ x, a * (if x = 0 then 1 else 0) ∂𝒟[$ᵗ Fin 4] :=
        lintegral_congr fun x ↦ by split_ifs <;> simp
    _ = a * ∫⁻ x, (if x = 0 then 1 else 0) ∂𝒟[$ᵗ Fin 4] :=
        lintegral_const_mul a Measurable.of_discrete
    _ = a * 4⁻¹ := by rw [← h]; simp

/-- A fresh query whose answer `0` moves the potential to `a`, and any other answer to `0`. -/
theorem pending_step_of (c : TestSpec.QueryCache) (t : Fin 2) (a : ℝ≥0∞)
    (hfun : ∀ u, pending (c.cacheQuery t u) = if u = 0 then a else 0)
    (hle : a * 4⁻¹ ≤ pending c + 16⁻¹) :
    ∫⁻ r, r ∂𝒟[(fun u ↦ pending (c.cacheQuery t u)) <$> ($ᵗ TestSpec.Range t)] ≤
      pending c + 16⁻¹ := by
  have h : (fun u ↦ pending (c.cacheQuery t u)) = fun u : Fin 4 ↦ if u = 0 then a else 0 :=
    funext hfun
  rw [h, lintegral_ite_zero]
  exact hle

/-- The potential grows in expectation by at most `1/16` per fresh query. -/
theorem pending_step (c : TestSpec.QueryCache) (t : Fin 2) (ht : c t = none) :
    ∫⁻ r, r ∂𝒟[(fun u ↦ pending (c.cacheQuery t u)) <$> ($ᵗ TestSpec.Range t)] ≤
      pending c + 16⁻¹ := by
  have hq : (4 : ℝ≥0∞)⁻¹ * 4⁻¹ = 16⁻¹ := by
    rw [← ENNReal.mul_inv (by simp) (by simp)]
    norm_num
  fin_cases t
  · replace ht : c 0 = none := ht
    rcases hc : c 1 with _ | v
    · refine pending_step_of c 0 4⁻¹ (fun u ↦ ?_) (by simp [pending, ht, hc, hq])
      by_cases hu : u = 0 <;> simp [pending, hu, hc, QueryCache.cacheQuery_of_ne]
    · by_cases hv : v = 0
      · subst hv
        refine pending_step_of c 0 1 (fun u ↦ ?_) (by simp [pending, ht, hc])
        by_cases hu : u = 0 <;> simp [pending, hu, hc, QueryCache.cacheQuery_of_ne]
      · refine pending_step_of c 0 0 (fun u ↦ ?_) (by simp)
        by_cases hu : u = 0 <;> simp [pending, hu, hc, hv, QueryCache.cacheQuery_of_ne]
  · replace ht : c 1 = none := ht
    rcases hc : c 0 with _ | v
    · refine pending_step_of c 1 4⁻¹ (fun u ↦ ?_) (by simp [pending, ht, hc, hq])
      by_cases hu : u = 0 <;> simp [pending, hu, hc, QueryCache.cacheQuery_of_ne]
    · by_cases hv : v = 0
      · subst hv
        refine pending_step_of c 1 1 (fun u ↦ ?_) (by simp [pending, ht, hc])
        by_cases hu : u = 0 <;> simp [pending, hu, hc, QueryCache.cacheQuery_of_ne]
      · refine pending_step_of c 1 0 (fun u ↦ ?_) (by simp)
        by_cases hu : u = 0 <;> simp [pending, hu, hc, hv, QueryCache.cacheQuery_of_ne]

-- The pair completes with probability at most `2 · 1/16`, although each query of the pair
-- breaks the invariant with probability up to `1/4`.
example :
    Pr{let z ← (simulateQ TestSpec.randomOracle twoQueries).run ∅}[BothZero z.2] ≤ 2 * 16⁻¹ := by
  refine (probEvent_le_of_potential BothZero pending (fun c hc ↦ by simp [pending, hc.1, hc.2])
    (fun _ _ ↦ 16⁻¹) pending_step twoQueries ∅).trans ?_
  simpa [pending] using expected_charge_le_mul (fun _ _ _ ↦ le_rfl) twoQueries_bound ∅

end

end LeanerVMTests.Protocol
