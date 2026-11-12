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
probability exactly `1/4`: the bound is attained, and it fails without the query budget.

The potential form charges a bad event that two queries complete together, both oracles
answering `0`, once: the potential is the chance of completing it, every fresh query is charged
`1/16`, and the bound is `2/16`, where the invariant form charges each query `1/4`.

The step bound need only hold within the budget: from the empty cache, two queries never cache
three answers, a bound of `0` although a fresh query at a cache of two entries caches a third
with certainty. On the log of fresh queries, the event "the first answer is `0`", which no
predicate on the cache states, has probability at most `1/4` with no charge at all.

Two runs in sequence: both oracles answering `0` has probability at most `1/16 + 1/16` when the
second run starts from the potential the first leaves, in expectation; from its largest value,
`1/4` after a first answer `0`, the bound would be `1/4 + 1/16`.

The fresh log of a logged run: a query asked twice from the empty state leaves its run's log with
two equal entries and the fresh log with one, the run's log deduplicated.
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

open Classical in
/-- `1` once the invariant is broken, `0` before. -/
noncomputable def broken (c : TestSpec.QueryCache) : ℝ≥0∞ := if NoZero c then 0 else 1

/-- The indicator of a broken invariant grows by at most `1/4` in expectation at a fresh query. -/
theorem broken_step (c : TestSpec.QueryCache) (t : Fin 2) :
    ∫⁻ r, r ∂𝒟[(fun u ↦ broken (c.cacheQuery t u)) <$> ($ᵗ TestSpec.Range t)] ≤
      broken c + 4⁻¹ := by
  classical
  by_cases hc : NoZero c
  · have h := (prEvent_eq_lintegral_id_evalDist_map_ite ($ᵗ TestSpec.Range t)
      (fun u ↦ ¬ NoZero (c.cacheQuery t u))).symm.trans_le (noZero_step c t hc)
    simpa only [broken, hc, ↓reduceIte, zero_add, ite_not] using h
  · refine (lintegral_id_evalDist_map_le_of_le _ (c := 1) fun u ↦ ?_).trans (by simp [broken, hc])
    unfold broken
    split_ifs <;> simp

-- Two queries: the invariant fails with probability at most `2 · 1/4`.
example :
    Pr{let z ← (simulateQ TestSpec.randomOracle twoQueries).run ∅}[¬ NoZero z.2] ≤ 2 * 4⁻¹ := by
  have h0 : NoZero ∅ := fun _ ↦ by simp
  rw [← QueryHistory.randomOracle_cache]
  simpa [broken, h0] using QueryHistory.cache.prEvent_le_of_potential (fun z ↦ ¬ NoZero z.2) broken
    (fun z hz ↦ by simp [broken, hz]) twoQueries_bound ∅ fun c t _ _ ↦ broken_step c t

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
  rw [← QueryHistory.randomOracle_cache]
  simpa [pending] using QueryHistory.cache.prEvent_le_of_potential (fun z ↦ BothZero z.2) pending
    (fun z hz ↦ by simp [pending, hz.1, hz.2]) twoQueries_bound ∅ fun c t ht _ ↦ pending_step c t ht

/-! ### A step bound within the budget -/

/-- Two queries to oracles indexed by `ℕ`. -/
def twoQueriesNat : OracleComp (ℕ →ₒ Fin 4) (Fin 4 × Fin 4) := do
  let a ← ((ℕ →ₒ Fin 4).query 0 : OracleComp (ℕ →ₒ Fin 4) (Fin 4))
  let b ← ((ℕ →ₒ Fin 4).query 1 : OracleComp (ℕ →ₒ Fin 4) (Fin 4))
  return (a, b)

theorem twoQueriesNat_bound : IsTotalQueryBound twoQueriesNat 2 :=
  ⟨by decide, fun _ ↦ ⟨by decide, fun _ ↦ trivial⟩⟩

open Classical in
/-- `1` on a cache of at least three entries, `0` on a smaller one. -/
noncomputable def three (c : (ℕ →ₒ Fin 4).QueryCache) : ℝ≥0∞ := if 3 ≤ c.enncard then 1 else 0

-- Within two queries from the empty cache a fresh query leaves at most two entries, so the
-- potential never moves: no run of two queries caches three answers.
example :
    Pr{let z ← (simulateQ (ℕ →ₒ Fin 4).randomOracle twoQueriesNat).run ∅}[3 ≤ z.2.enncard] ≤
      0 := by
  rw [← QueryHistory.randomOracle_cache]
  refine (QueryHistory.cache.prEvent_le_of_potential (fun z ↦ 3 ≤ z.2.enncard) three
    (fun z hz ↦ by simp [three, hz]) (κ := 0) twoQueriesNat_bound ∅ fun c t _ hc ↦
      (lintegral_id_evalDist_map_le_of_le _ fun u ↦ ?_).trans zero_le).trans_eq ?_
  · rw [QueryHistory.cache_view, QueryHistory.cache_view, QueryCache.enncard_empty, zero_add] at hc
    have h2 : (c.cacheQuery t u).enncard ≤ 2 :=
      (QueryCache.enncard_cacheQuery_le c t u).trans (hc.trans_eq (by norm_num))
    have h3 : ¬ 3 ≤ (c.cacheQuery t u).enncard := not_le.mpr (h2.trans_lt (by norm_num))
    simp [three, h3]
  · simp [three]

-- Outside the budget the step bound fails: at a cache of two entries a fresh query caches a
-- third with certainty.
example : ¬ ∀ (c : (ℕ →ₒ Fin 4).QueryCache) (t : ℕ), c t = none →
    ∫⁻ r, r ∂𝒟[(fun u ↦ three (c.cacheQuery t u)) <$> ($ᵗ Fin 4)] ≤ three c + 0 := by
  intro h
  have h0 : ((∅ : (ℕ →ₒ Fin 4).QueryCache).cacheQuery 0 0) 1 = none := by
    rw [QueryCache.cacheQuery_of_ne (t' := 1) (t := 0) _ _ (by decide)]
    rfl
  have h2 : (((∅ : (ℕ →ₒ Fin 4).QueryCache).cacheQuery 0 0).cacheQuery 1 0).enncard = 2 := by
    rw [QueryCache.enncard_cacheQuery _ _ _ h0,
      QueryCache.enncard_cacheQuery (∅ : (ℕ →ₒ Fin 4).QueryCache) 0 0 rfl,
      QueryCache.enncard_empty]
    norm_num
  have hc2 : (((∅ : (ℕ →ₒ Fin 4).QueryCache).cacheQuery 0 0).cacheQuery 1 0) 2 = none := by
    rw [QueryCache.cacheQuery_of_ne (t' := 2) (t := 1) _ _ (by decide),
      QueryCache.cacheQuery_of_ne (t' := 2) (t := 0) _ _ (by decide)]
    rfl
  have hthree : ∀ u,
      three ((((∅ : (ℕ →ₒ Fin 4).QueryCache).cacheQuery 0 0).cacheQuery 1 0).cacheQuery 2 u) =
        1 := fun u ↦ by
    rw [three, QueryCache.enncard_cacheQuery _ _ _ hc2, h2]
    norm_num
  have hone : ∫⁻ r, r ∂𝒟[(fun _ ↦ (1 : ℝ≥0∞)) <$> ($ᵗ Fin 4)] = 1 := by simp
  have := h _ 2 hc2
  rw [funext hthree, hone] at this
  norm_num [three, h2] at this

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
    firstPotential (fun z hz ↦ ?_) (κ := 0) twoQueries_bound (∅, [])
    fun s t _ _ ↦ ?_).trans_eq ?_
  · obtain ⟨_, _, _ | ⟨e, l⟩⟩ := z
    · exact absurd hz id
    · simp [firstPotential, show (e.2 : Fin 4) = 0 from hz]
  · obtain ⟨c, _ | ⟨e, l⟩⟩ := s
    · rw [lintegral_ite_zero t 1 fun u ↦ by simp [firstPotential]]
      simp [firstPotential]
    · exact lintegral_id_evalDist_map_le_of_le _ fun u ↦ by simp [firstPotential]
  · simp [firstPotential]

/-! ### Two runs in sequence -/

/-- One query to oracle `1`. -/
def oneQueryOne : OracleComp TestSpec (Fin 4) :=
  (TestSpec.query 1 : OracleComp TestSpec (Fin 4))

theorem oneQuery_bound : IsTotalQueryBound oneQuery 1 := ⟨by decide, fun _ ↦ trivial⟩

theorem oneQueryOne_bound : IsTotalQueryBound oneQueryOne 1 := ⟨by decide, fun _ ↦ trivial⟩

-- Both oracles answer `0` with probability at most `1/16 + 1/16`: the first run's charge, then
-- the second run's from the potential the first leaves.
example :
    Pr{let z ← (simulateQ TestSpec.randomOracle (oneQuery >>= fun _ ↦ oneQueryOne)).run ∅}[
      BothZero z.2] ≤ 16⁻¹ + 16⁻¹ := by
  have hpend : ∀ z : Fin 4 × TestSpec.QueryCache, BothZero z.2 → 1 ≤ pending z.2 :=
    fun z hz ↦ by simp [pending, hz.1, hz.2]
  rw [← QueryHistory.randomOracle_cache]
  refine (QueryHistory.cache.prEvent_bind_le_of_potential oneQuery (fun _ ↦ oneQueryOne) ∅
    (fun z ↦ BothZero z.2) pending oneQuery_bound (fun c t ht _ ↦ pending_step c t ht)
    (ε := 16⁻¹) fun z₁ _ ↦ ?_).trans_eq ?_
  · simpa using QueryHistory.cache.prEvent_le_of_potential (fun z ↦ BothZero z.2) pending hpend
      oneQueryOne_bound z₁.2 fun c t ht _ ↦ pending_step c t ht
  · simp [pending]

-- The same composition for a draw: the second of two uniform draws is `0` with probability at
-- most `1/4`, whatever the first.
example :
    Pr{let y ← ($ᵗ Fin 4 >>= fun _ ↦ $ᵗ Fin 4)}[y = 0] ≤ 0 + 4⁻¹ := by
  refine (prEvent_bind_le_add_iSup ($ᵗ Fin 4) (fun _ ↦ $ᵗ Fin 4) (fun _ ↦ False) (· = 0)).trans
    (add_le_add (by simp) (iSup₂_le fun _ _ ↦ iSup_le fun _ ↦ ?_))
  simpa using (SampleableType.prEvent_uniformSample_eq_singleton (α := Fin 4) 0).le

/-! ## The fresh log of a logged run -/

/-- One query, asked twice. -/
def repeatQuery : OracleComp TestSpec (Fin 4 × Fin 4) := do
  let a ← (TestSpec.query 0 : OracleComp TestSpec (Fin 4))
  let b ← (TestSpec.query 0 : OracleComp TestSpec (Fin 4))
  return (a, b)

-- Deduplication keeps each input's first occurrence.
example : List.dedupKeys ([⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 3⟩] : TestSpec.QueryLog) = [⟨0, 1⟩, ⟨1, 2⟩] := by
  decide

/-- From the empty state, the fresh log is the run's log deduplicated
(`withQueryLog_freshLog_support`): the run's log has the query twice, with one answer, and the
fresh log once, so the two logs differ. -/
theorem repeatQuery_freshLog {z : ((Fin 4 × Fin 4) × TestSpec.QueryLog) ×
    TestSpec.QueryCache × TestSpec.QueryLog}
    (hz : z ∈ support ((simulateQ QueryHistory.freshLog.randomOracle
      repeatQuery.withQueryLog).run (∅, []))) :
    z.2.2 = List.dedupKeys z.1.2 ∧ z.1.2 = [⟨0, z.1.1.1⟩, ⟨0, z.1.1.1⟩] ∧ z.2.2 ≠ z.1.2 := by
  have h₁ :=
    (QueryHistory.withQueryLog_freshLog_support repeatQuery QueryHistory.isFreshLog_empty hz).1
  simp only [QueryCache.empty_apply, Option.isNone_none, List.filter_true, List.nil_append]
    at h₁
  simp [repeatQuery, withQueryLog_bind, withQueryLog_query, QueryHistory.randomOracle,
    map_eq_bind_pure_comp] at hz
  obtain ⟨y, rfl⟩ := hz
  refine ⟨h₁, rfl, ?_⟩
  rw [h₁, show ([⟨0, y⟩, ⟨0, y⟩] : TestSpec.QueryLog) = [⟨0, y⟩] ++ [⟨0, y⟩] from rfl,
    QueryLog.dedupKeys_concat]
  simp

end

end LeanerVMTests.Protocol
