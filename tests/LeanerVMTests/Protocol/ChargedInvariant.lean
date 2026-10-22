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

A repeated query is charged once. A charge growing with the cache, as a collision's does, over
infinitely many oracles, is bounded within the budget. On the log of fresh queries, the event
"the first answer is `0`", which no predicate on the cache states, has probability at most
`1/4` with no charge at all.
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

theorem twoQueries_bound : IsTotalQueryBound twoQueries 2 :=
  ⟨by decide, fun _ ↦ ⟨by decide, fun _ ↦ trivial⟩⟩

/-- No cached answer is `0`. -/
def NoZero (c : TestSpec.QueryCache) : Prop := ∀ t, c t ≠ some 0

/-- A fresh query at a cache without `0` caches `0` with probability `1/4`. -/
theorem noZero_step (c : TestSpec.QueryCache) (t : Fin 2) (hc : NoZero c) :
    Pr{let u ← $ᵗ TestSpec.Range t}[¬ NoZero (c.cacheQuery t u)] ≤ 4⁻¹ := by
  refine (prEvent_mono _ _ (fun u ↦ u = 0) fun u hu ↦ by_contra fun hu0 ↦ hu fun t' ↦ ?_).trans
    (SampleableType.prEvent_uniformSample_eq_singleton (α := Fin 4) 0).le
  by_cases h : t' = t
  · subst h
    simpa using hu0
  · rw [QueryCache.cacheQuery_of_ne c u h]
    exact hc t'

-- Two queries: the invariant fails with probability at most `2 · 1/4`.
example :
    Pr{let z ← (simulateQ TestSpec.randomOracle twoQueries).run ∅}[¬ NoZero z.2] ≤ 2 * 4⁻¹ :=
  prEvent_not_good_le_mul NoZero twoQueries_bound (fun _ ↦ by simp)
    (fun c t _ hc _ ↦ noZero_step c t hc)

-- One query fails the invariant with probability exactly `1/4`: the bound `1 · 1/4` is
-- attained, and no bound `0 · 1/4` holds, so the query budget is needed.
example :
    Pr{let z ← (simulateQ TestSpec.randomOracle oneQuery).run ∅}[¬ NoZero z.2] = 4⁻¹ := by
  have hrun : (simulateQ TestSpec.randomOracle oneQuery).run ∅ =
      (fun u ↦ (u, (∅ : TestSpec.QueryCache).cacheQuery 0 u)) <$> ($ᵗ Fin 4) := by
    simp [oneQuery, map_eq_bind_pure_comp]
  rw [hrun, prEvent_map, prEvent_congr _ _ (fun u ↦ u = 0) fun u ↦ by
    simp [NoZero, Fin.forall_fin_two, QueryCache.cacheQuery_of_ne]]
  simpa using SampleableType.prEvent_uniformSample_eq_singleton (α := Fin 4) 0

-- Expected count: at most `2 · 1/4` cached answers are `0` after two queries.
example :
    ∫⁻ r, r ∂𝒟[(fun z ↦ answersIn (fun _ u ↦ u = 0) z.2) <$>
      (simulateQ TestSpec.randomOracle twoQueries).run ∅] ≤ 2 * 4⁻¹ := by
  simpa only [Finset.mem_singleton, Finset.card_singleton, Fintype.card_fin, Nat.cast_one,
    Nat.cast_ofNat, one_div] using expected_fresh_in_le ({0} : Finset (Fin 4)) twoQueries_bound

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

/-- The expectation of a function that is `a` at the answer `0` and `0` elsewhere. -/
theorem lintegral_ite_zero (t : Fin 2) (a : ℝ≥0∞) {f : TestSpec.Range t → ℝ≥0∞}
    (hf : ∀ u, f u = if u = 0 then a else 0) :
    ∫⁻ r, r ∂𝒟[f <$> ($ᵗ TestSpec.Range t)] = a * 4⁻¹ := by
  let : MeasurableSpace (Fin 4) := ⊤
  rw [funext hf, lintegral_id_evalDist_map]
  simp [lintegral_fintype]

/-- The potential grows in expectation by at most `1/16` per fresh query. -/
theorem pending_step (c : TestSpec.QueryCache) (t : Fin 2) (ht : c t = none) :
    ∫⁻ r, r ∂𝒟[(fun u ↦ pending (c.cacheQuery t u)) <$> ($ᵗ TestSpec.Range t)] ≤
      pending c + 16⁻¹ := by
  have hq : (4 : ℝ≥0∞)⁻¹ * 4⁻¹ = 16⁻¹ := by
    rw [← ENNReal.mul_inv (by simp) (by simp)]
    norm_num
  rw [lintegral_ite_zero t (pending (c.cacheQuery t 0)) fun u ↦ ?_]
  · fin_cases t <;> simp at ht <;> simp [pending, ht, QueryCache.cacheQuery_of_ne] <;>
      split_ifs <;> simp only [hq, zero_add, le_self_add, zero_le, le_refl]
  · split_ifs with hu
    · rw [hu]
    · fin_cases t <;> simp [pending, hu, QueryCache.cacheQuery_of_ne]

-- The pair completes with probability at most `2 · 1/16`, although each query of the pair
-- breaks the invariant with probability up to `1/4`.
example :
    Pr{let z ← (simulateQ TestSpec.randomOracle twoQueries).run ∅}[BothZero z.2] ≤ 2 * 16⁻¹ := by
  refine (prEvent_le_of_potential (fun z ↦ BothZero z.2) pending
    (fun z hz ↦ by simp [pending, hz.1, hz.2]) (fun _ _ ↦ 16⁻¹) pending_step twoQueries ∅).trans ?_
  simpa [pending] using
    QueryHistory.cache.expected_charge_le_mul twoQueries_bound ∅ fun _ _ _ _ ↦ le_rfl

/-! ### A cached query is not charged -/

/-- The same query twice. -/
def sameTwice : OracleComp TestSpec (Fin 4) := do
  let _ ← (TestSpec.query 0 : OracleComp TestSpec (Fin 4))
  (TestSpec.query 0 : OracleComp TestSpec (Fin 4))

-- Every run of the same query twice is charged once, at the empty cache.
example (charge : TestSpec.QueryCache → Fin 2 → ℝ≥0∞) {z : Fin 4 × TestSpec.QueryCache × ℝ≥0∞}
    (hz : z ∈ support ((simulateQ (chargedRandomOracle charge) sameTwice).run (∅, 0))) :
    z.2.2 = charge ∅ 0 := by
  rw [sameTwice, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    QueryHistory.chargedOracle_run_of_none _ _ (by rfl), mem_support_bind_iff] at hz
  obtain ⟨p, hp, hz⟩ := hz
  rw [support_map] at hp
  obtain ⟨u, -, rfl⟩ := hp
  dsimp only at hz
  rw [QueryHistory.chargedOracle_run_of_some _ _
    (QueryCache.cacheQuery_self (∅ : TestSpec.QueryCache) 0 u), support_pure,
    Set.mem_singleton_iff] at hz
  simp [hz]

/-! ### A charge growing with the cache, over infinitely many oracles -/

/-- Two queries to oracles indexed by `ℕ`. -/
def twoQueriesNat : OracleComp (ℕ →ₒ Fin 4) (Fin 4 × Fin 4) := do
  let a ← ((ℕ →ₒ Fin 4).query 0 : OracleComp (ℕ →ₒ Fin 4) (Fin 4))
  let b ← ((ℕ →ₒ Fin 4).query 1 : OracleComp (ℕ →ₒ Fin 4) (Fin 4))
  return (a, b)

theorem twoQueriesNat_bound : IsTotalQueryBound twoQueriesNat 2 :=
  ⟨by decide, fun _ ↦ ⟨by decide, fun _ ↦ trivial⟩⟩

-- A query charged a quarter of the size of the cache, as a collision is: no bound holds at
-- every cache, but within two queries from the empty cache the charge is at most `1/4`.
example :
    ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$> (simulateQ (chargedRandomOracle
      (fun c _ ↦ c.enncard * 4⁻¹)) twoQueriesNat).run (∅, 0)] ≤ 2 * 4⁻¹ := by
  refine QueryHistory.cache.expected_charge_le_mul twoQueriesNat_bound ∅ fun c _ _ hc ↦ ?_
  rw [QueryHistory.cache_view, QueryHistory.cache_view, QueryCache.enncard_empty, zero_add,
    Nat.cast_ofNat, ← one_add_one_eq_two, ENNReal.add_le_add_iff_right ENNReal.one_ne_top] at hc
  exact (mul_le_mul' hc le_rfl).trans_eq (one_mul _)

/-! ### An order-dependent event on the log of fresh queries -/

/-- The first fresh answer is `0`. -/
def FirstZero : TestSpec.QueryLog → Prop
  | [] => False
  | e :: _ => (e.2 : Fin 4) = 0

/-- `1/4` before any query, the chance that the first answer is `0`; then whether it was. -/
noncomputable def firstPotential (s : TestSpec.QueryCache × TestSpec.QueryLog) : ℝ≥0∞ :=
  match s.2 with
  | [] => 4⁻¹
  | e :: _ => if (e.2 : Fin 4) = 0 then 1 else 0

-- Whatever the number of queries, the first answer is `0` with probability at most `1/4`: the
-- potential is not charged.
example :
    Pr{let z ← (simulateQ QueryHistory.freshLog.randomOracle twoQueries).run (∅, [])}[
      FirstZero z.2.2] ≤ 4⁻¹ := by
  refine (QueryHistory.freshLog.prEvent_le_of_potential (fun z ↦ FirstZero z.2.2)
    firstPotential (fun z hz ↦ ?_) (fun _ _ ↦ 0) (fun s t _ ↦ ?_) twoQueries (∅, [])).trans ?_
  · obtain ⟨_, _, _ | ⟨e, l⟩⟩ := z
    · exact absurd hz id
    · simp [firstPotential, show (e.2 : Fin 4) = 0 from hz]
  · obtain ⟨c, _ | ⟨e, l⟩⟩ := s
    · rw [lintegral_ite_zero t 1 fun u ↦ by simp [firstPotential]]
      simp [firstPotential]
    · exact lintegral_id_evalDist_map_le_of_le _ fun u ↦ by simp [firstPotential]
  · exact add_le_of_le_of_nonpos le_rfl <| (QueryHistory.freshLog.expected_charge_le_mul
      twoQueries_bound (∅, []) (κ := 0) fun _ _ _ _ ↦ le_rfl).trans_eq (mul_zero _)

end

end LeanerVMTests.Protocol
