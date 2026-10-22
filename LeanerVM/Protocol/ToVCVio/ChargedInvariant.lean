/-
  LeanerVM.Protocol.ToVCVio.ChargedInvariant

  The expected potential of a lazy random oracle's record of queries grows by at most the
  expected sum of per-query charges; so does the probability of an event the potential
  dominates. Candidate for VCVio.
-/

module

public import LeanerVM.Protocol.ToVCVio.EventExpectation
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# The charged invariant of a lazy random oracle

A `QueryHistory spec σ` is a state `σ` recording a lazy random oracle's queries: it shows the
cache (`view`) and records a fresh query with its answer (`record`), the cache gaining that
entry. `QueryHistory.cache` is the cache alone; `QueryHistory.freshLog` is the cache with the
fresh queries in the order they were made, for predicates about what was known earlier.
`H.randomOracle` is the lazy random oracle on `H`'s state, whose cache is that of `randomOracle`
(`QueryHistory.randomOracle_run_view`); `QueryHistory.cache.randomOracle` is `randomOracle`.
`H.chargedOracle charge` keeps a running total beside the state: a fresh query `t` at state `s`
adds `charge s t`, a cached query adds nothing. Forgetting the total it is `H.randomOracle`
(`QueryHistory.chargedOracle_run_map`). Expectations are `∫⁻ r, r ∂𝒟[f <$> mx]`.

The main theorem, `QueryHistory.potential_le_expected_charge`, is a supermartingale bound: if at
every fresh query the expected potential `Φ` of the state after the uniform answer is at most
the potential before plus the charge, the expected final potential is at most the initial one
plus the expected total charge. A charge may thus pay in advance for a bad event that a group of
later queries completes. Its consequences, in the namespace `QueryHistory`:

* `prEvent_le_of_potential`: an event on the output and the final state on which `Φ ≥ 1` has
  probability at most the initial potential plus the expected total charge;
* `prEvent_not_good_le_expected_charge`: an invariant `Good` of the state, broken at a fresh
  query from a good state with probability at most the charge, is broken at the end with
  probability at most the expected total charge;
* `enncard_le_of_mem_support`: a computation making at most `n` queries adds at most `n`
  entries to the cache;
* `charge_le_of_mem_support`, `expected_charge_le_mul`, `prEvent_not_good_le_mul`: if every
  state such a computation can reach is charged at most `κ`, its total charge, its expected
  total charge and the probability that it breaks `Good` are at most `n * κ`. A charge growing
  with the cache, such as `|c| / |Y|` for a collision, is bounded at `(|c₀| + n) / |Y|`;
* `expected_fresh_le`: if a fresh answer lies in `S` with probability at most `p`, the expected
  number of fresh answers in `S` is at most `n * p`.

`potential_le_expected_charge`, `prEvent_le_of_potential`,
`prEvent_not_good_le_expected_charge`, `prEvent_not_good_le_mul`, `enncard_le_of_mem_support`
and `expected_fresh_in_le` (for a set of answers, `n * |S| / |Y|`) state them for
`randomOracle` and its cache.

Related notions in VCVio: `expectedSimulatedQueryCount` (pull request 817) is the expected
number of charged queries of a stateful simulation, a query charged by its index, and
`lintegral_resource_le_add_expectedSimulatedQueryCount` bounds a resource growing by at most one
per charged query; `prEvent_randomOracle_le_expectedFreshQueryCharge` (pull request 824) bounds a
bad event of the random oracle by the expected charge of its fresh keys, a key charged by itself
and the event read off a fixed table. Here a query is charged by the state at the time it is
made, and the bound is a supermartingale over that state.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

@[expose] public section

variable {ι : Type} [DecidableEq ι]

/-- A state recording the queries of a lazy random oracle: `view` reads the cache off it, and
`record` adds a fresh query `t` with its answer `u`, which caches `u` at `t`. -/
structure QueryHistory (spec : OracleSpec.{0, 0} ι) (σ : Type) where
  /-- The cache the state records. -/
  view : σ → spec.QueryCache
  /-- Record a fresh query and its answer. -/
  record : σ → (t : spec.Domain) → spec.Range t → σ
  /-- Recording a fresh query caches its answer. -/
  view_record : ∀ s t u, view s t = none → view (record s t u) = (view s).cacheQuery t u

/-- The number of entries of the cache `c` whose answer satisfies `S`. -/
noncomputable def answersIn {spec : OracleSpec.{0, 0} ι}
    (S : (t : spec.Domain) → spec.Range t → Prop) (c : spec.QueryCache) : ℝ≥0∞ :=
  ((c.toSet ∩ {p | S p.1 p.2}).encard : ℝ≥0∞)

omit [DecidableEq ι] in
@[simp]
theorem answersIn_empty {spec : OracleSpec.{0, 0} ι}
    (S : (t : spec.Domain) → spec.Range t → Prop) : answersIn S (∅ : spec.QueryCache) = 0 := by
  simp [answersIn]

/-- Caching a fresh answer adds one to the count when the answer satisfies `S`. -/
theorem answersIn_cacheQuery {spec : OracleSpec.{0, 0} ι}
    (S : (t : spec.Domain) → spec.Range t → Prop) {c : spec.QueryCache} {t : spec.Domain}
    (hc : c t = none) (u : spec.Range t) [Decidable (S t u)] :
    answersIn S (c.cacheQuery t u) = answersIn S c + if S t u then 1 else 0 := by
  have hset : (c.cacheQuery t u).toSet = insert ⟨t, u⟩ c.toSet := by
    ext ⟨t', u'⟩
    by_cases ht : t' = t
    · subst ht
      simp [hc, eq_comm]
    · simp [ht]
  have hnot : (⟨t, u⟩ : (t : spec.Domain) × spec.Range t) ∉ c.toSet ∩ {p | S p.1 p.2} :=
    fun h ↦ by simp [hc] at h
  unfold answersIn
  rw [hset]
  split_ifs with hS
  · rw [Set.insert_inter_of_mem (show _ ∈ {p : (t : spec.Domain) × spec.Range t | S p.1 p.2}
      from hS), Set.encard_insert_of_notMem hnot]
    simp
  · rw [Set.insert_inter_of_notMem (show _ ∉ {p : (t : spec.Domain) × spec.Range t | S p.1 p.2}
      from hS)]
    simp

/-- `n - 1` queries after one, when there is one. -/
private theorem cast_pred_add_one {n : ℕ} (hn : 0 < n) : ((n - 1 : ℕ) : ℝ≥0∞) + 1 = n := by
  rw [← Nat.cast_add_one, Nat.sub_add_cancel (Nat.succ_le_of_lt hn)]

namespace QueryHistory

variable {spec : OracleSpec.{0, 0} ι}

/-- The cache alone. -/
def cache : QueryHistory spec spec.QueryCache where
  view c := c
  record c t u := c.cacheQuery t u
  view_record _ _ _ _ := rfl

/-- The cache and the fresh queries in the order they were made. -/
def freshLog : QueryHistory spec (spec.QueryCache × spec.QueryLog) where
  view s := s.1
  record s t u := (s.1.cacheQuery t u, s.2 ++ [⟨t, u⟩])
  view_record _ _ _ _ := rfl

@[simp] theorem cache_view (c : spec.QueryCache) : cache.view c = c := rfl

@[simp] theorem cache_record (c : spec.QueryCache) (t : spec.Domain) (u : spec.Range t) :
    cache.record c t u = c.cacheQuery t u := rfl

@[simp] theorem freshLog_view (s : spec.QueryCache × spec.QueryLog) : freshLog.view s = s.1 :=
  rfl

@[simp] theorem freshLog_record (s : spec.QueryCache × spec.QueryLog) (t : spec.Domain)
    (u : spec.Range t) : freshLog.record s t u = (s.1.cacheQuery t u, s.2 ++ [⟨t, u⟩]) := rfl

variable {σ : Type} (H : QueryHistory spec σ) [∀ t, SampleableType (spec.Range t)] {α : Type}

/-- The lazy random oracle on `H`'s state: a cached query returns its answer and keeps the
state, a fresh one is answered uniformly and recorded. -/
def randomOracle : QueryImpl spec (StateT σ ProbComp) := fun t ↦ StateT.mk fun s ↦
  match H.view s t with
  | some u => pure (u, s)
  | none => (fun u ↦ (u, H.record s t u)) <$> ($ᵗ spec.Range t)

/-- `H.randomOracle` with a running total of charges: a fresh query `t` at state `s` adds
`charge s t`, a cached query adds nothing. -/
def chargedOracle (charge : σ → spec.Domain → ℝ≥0∞) :
    QueryImpl spec (StateT (σ × ℝ≥0∞) ProbComp) := fun t ↦ StateT.mk fun s ↦
  match H.view s.1 t with
  | some u => pure (u, s)
  | none => (fun u ↦ (u, H.record s.1 t u, s.2 + charge s.1 t)) <$> ($ᵗ spec.Range t)

theorem randomOracle_run_of_some {t : spec.Domain} {s : σ} {u : spec.Range t}
    (h : H.view s t = some u) : (H.randomOracle t).run s = pure (u, s) := by
  simp [randomOracle, h]

theorem randomOracle_run_of_none {t : spec.Domain} {s : σ} (h : H.view s t = none) :
    (H.randomOracle t).run s = (fun u ↦ (u, H.record s t u)) <$> ($ᵗ spec.Range t) := by
  simp [randomOracle, h]

theorem chargedOracle_run_of_some (charge : σ → spec.Domain → ℝ≥0∞) {t : spec.Domain} {s : σ}
    {u : spec.Range t} (h : H.view s t = some u) (total : ℝ≥0∞) :
    (H.chargedOracle charge t).run (s, total) = pure (u, s, total) := by
  simp [chargedOracle, h]

theorem chargedOracle_run_of_none (charge : σ → spec.Domain → ℝ≥0∞) {t : spec.Domain} {s : σ}
    (h : H.view s t = none) (total : ℝ≥0∞) :
    (H.chargedOracle charge t).run (s, total) =
      (fun u ↦ (u, H.record s t u, total + charge s t)) <$> ($ᵗ spec.Range t) := by
  simp [chargedOracle, h]

/-- On the cache alone, the oracle is `randomOracle`. -/
theorem randomOracle_cache :
    (cache : QueryHistory spec spec.QueryCache).randomOracle = spec.randomOracle := by
  funext t
  refine StateT.ext fun c ↦ ?_
  cases h : c t with
  | some u =>
    rw [randomOracle_run_of_some cache (u := u) h, QueryImpl.withCaching_run_some _ h]
  | none =>
    rw [randomOracle_run_of_none cache h, QueryImpl.withCaching_run_none _ h]
    rfl

omit [DecidableEq ι] [∀ t, SampleableType (spec.Range t)] in
/-- Running a query and then a continuation under a stateful implementation. -/
private theorem run_query_bind {τ : Type} (impl : QueryImpl spec (StateT τ ProbComp))
    (t : spec.Domain) (k : spec.Range t → OracleComp spec α) (s : τ) :
    (simulateQ impl (liftM (spec.query t) >>= k)).run s =
      (impl t).run s >>= fun p ↦ (simulateQ impl (k p.1)).run p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

/-- The oracle on `H`'s state keeps the cache of `randomOracle`. -/
theorem randomOracle_run_view (oa : OracleComp spec α) (s : σ) :
    Prod.map id H.view <$> (simulateQ H.randomOracle oa).run s =
      (simulateQ spec.randomOracle oa).run (H.view s) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ H.view (fun t s ↦ by
    cases h : H.view s t with
    | some u =>
      rw [H.randomOracle_run_of_some h, QueryImpl.withCaching_run_some _ h]
      simp
    | none =>
      rw [H.randomOracle_run_of_none h, QueryImpl.withCaching_run_none _ h]
      simp [Functor.map_map, H.view_record _ _ _ h]) oa s

/-- Forgetting the total, the charged oracle is `H.randomOracle`. -/
theorem chargedOracle_run_map (charge : σ → spec.Domain → ℝ≥0∞) (oa : OracleComp spec α)
    (s : σ) (total : ℝ≥0∞) :
    Prod.map id Prod.fst <$> (simulateQ (H.chargedOracle charge) oa).run (s, total) =
      (simulateQ H.randomOracle oa).run s :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (fun t p ↦ by
    obtain ⟨s, a⟩ := p
    cases h : H.view s t with
    | some u =>
      rw [H.chargedOracle_run_of_some charge h, H.randomOracle_run_of_some h]
      simp
    | none =>
      rw [H.chargedOracle_run_of_none charge h, H.randomOracle_run_of_none h]
      simp [Functor.map_map]) oa (s, total)

/-- A run from total `total` is a run from total `0` with `total` added. -/
theorem chargedOracle_run_total (charge : σ → spec.Domain → ℝ≥0∞) (oa : OracleComp spec α)
    (s : σ) (total : ℝ≥0∞) :
    (simulateQ (H.chargedOracle charge) oa).run (s, total) =
      (fun z ↦ (z.1, z.2.1, total + z.2.2)) <$>
        (simulateQ (H.chargedOracle charge) oa).run (s, 0) := by
  induction oa using OracleComp.inductionOn generalizing s total with
  | pure a => simp
  | query_bind t k ih =>
    rw [run_query_bind, run_query_bind]
    cases h : H.view s t with
    | some u =>
      rw [H.chargedOracle_run_of_some charge h, H.chargedOracle_run_of_some charge h,
        pure_bind, pure_bind]
      exact ih u s total
    | none =>
      rw [H.chargedOracle_run_of_none charge h, H.chargedOracle_run_of_none charge h,
        bind_map_left, bind_map_left, map_bind]
      refine bind_congr fun u ↦ ?_
      rw [ih u _ (total + charge s t), ih u _ (0 + charge s t), Functor.map_map]
      simp [add_assoc]

/-- The expected total of a run from total `total` is `total` plus that of a run from `0`. -/
private theorem lintegral_total_eq_add (charge : σ → spec.Domain → ℝ≥0∞)
    (oa : OracleComp spec α) (s : σ) (total : ℝ≥0∞) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$> (simulateQ (H.chargedOracle charge) oa).run (s, total)] =
      total + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (H.chargedOracle charge) oa).run (s, 0)] := by
  rw [H.chargedOracle_run_total charge oa s total, Functor.map_map]
  exact lintegral_id_evalDist_map_const_add _ (OracleComp.prEvent_true_eq_one _) total _

/-- **Expected potential.** If at every fresh query the expected potential of the state after
the uniform answer is at most the potential before plus the query's charge, the expected final
potential of a run is at most the initial potential plus the expected total charge. -/
theorem potential_le_expected_charge (Φ : σ → ℝ≥0∞) (charge : σ → spec.Domain → ℝ≥0∞)
    (hstep : ∀ s t, H.view s t = none →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (H.record s t u)) <$> ($ᵗ spec.Range t)] ≤ Φ s + charge s t)
    (oa : OracleComp spec α) (s : σ) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ Φ z.2) <$> (simulateQ H.randomOracle oa).run s] ≤
      Φ s + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (H.chargedOracle charge) oa).run (s, 0)] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, evalDist_pure, lintegral_dirac]
    exact le_self_add
  | query_bind t k ih =>
    rw [run_query_bind, run_query_bind]
    cases h : H.view s t with
    | some u =>
      rw [H.randomOracle_run_of_some h, H.chargedOracle_run_of_some charge h, pure_bind,
        pure_bind]
      exact ih u s
    | none =>
      rw [H.randomOracle_run_of_none h, H.chargedOracle_run_of_none charge h, bind_map_left,
        bind_map_left, lintegral_id_evalDist_map_bind, lintegral_id_evalDist_map_bind]
      dsimp only
      simp only [zero_add, H.lintegral_total_eq_add charge _ _ (charge s t)]
      rw [lintegral_id_evalDist_map_const_add _ (OracleComp.prEvent_true_eq_one _),
        ← add_assoc]
      calc _ ≤ ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (H.record s t u) + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
              (simulateQ (H.chargedOracle charge) (k u)).run (H.record s t u, 0)]) <$>
              ($ᵗ spec.Range t)] :=
            lintegral_id_evalDist_map_mono _ fun u ↦ ih u _
        _ = _ := lintegral_id_evalDist_map_add _ _ _
        _ ≤ _ := add_le_add_left (hstep s t h) _

/-- An event on the output and the final state on which the potential is at least `1` has
probability at most the initial potential plus the expected total charge. -/
theorem prEvent_le_of_potential (E : α × σ → Prop) (Φ : σ → ℝ≥0∞) (hE : ∀ z, E z → 1 ≤ Φ z.2)
    (charge : σ → spec.Domain → ℝ≥0∞)
    (hstep : ∀ s t, H.view s t = none →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (H.record s t u)) <$> ($ᵗ spec.Range t)] ≤ Φ s + charge s t)
    (oa : OracleComp spec α) (s : σ) :
    Pr{let z ← (simulateQ H.randomOracle oa).run s}[E z] ≤
      Φ s + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (H.chargedOracle charge) oa).run (s, 0)] := by
  classical
  rw [prEvent_eq_lintegral_id_evalDist_map_ite]
  refine le_trans (lintegral_id_evalDist_map_mono _ fun z ↦ ?_)
    (H.potential_le_expected_charge Φ charge hstep oa s)
  split_ifs with h
  · exact hE z h
  · exact bot_le

/-- **The charged invariant.** Let `Good` hold of the initial state, and let a fresh query `t`
at a good state `s` break it with probability at most `charge s t` over the uniform answer.
Then the final state is bad with probability at most the expected total charge. -/
theorem prEvent_not_good_le_expected_charge (Good : σ → Prop)
    (charge : σ → spec.Domain → ℝ≥0∞)
    (hstep : ∀ s t, H.view s t = none → Good s →
      Pr{let u ← $ᵗ spec.Range t}[¬ Good (H.record s t u)] ≤ charge s t)
    (oa : OracleComp spec α) {s : σ} (hs : Good s) :
    Pr{let z ← (simulateQ H.randomOracle oa).run s}[¬ Good z.2] ≤
      ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$> (simulateQ (H.chargedOracle charge) oa).run (s, 0)] := by
  classical
  have h := H.prEvent_le_of_potential (fun z ↦ ¬ Good z.2) (fun s ↦ if ¬ Good s then 1 else 0)
    (fun z hz ↦ by simp [hz]) charge (fun s t ht ↦ ?_) oa s
  · simpa only [hs, not_true_eq_false, ↓reduceIte, zero_add] using h
  · by_cases hg : Good s
    · simp only [hg, not_true_eq_false, ↓reduceIte, zero_add]
      exact (prEvent_eq_lintegral_id_evalDist_map_ite _ _).symm.trans_le (hstep s t ht hg)
    · simp only [hg, not_false_eq_true, ↓reduceIte]
      exact (lintegral_id_evalDist_map_le_of_le _ fun u ↦ by split_ifs <;> simp).trans le_self_add

/-- A computation making at most `n` queries adds at most `n` entries to the cache. -/
theorem enncard_le_of_mem_support {oa : OracleComp spec α} {n : ℕ} (hn : IsTotalQueryBound oa n)
    (s : σ) {z : α × σ} (hz : z ∈ support ((simulateQ H.randomOracle oa).run s)) :
    (H.view z.2).enncard ≤ (H.view s).enncard + n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_self_add
  | query_bind t k ih =>
    obtain ⟨hpos, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    rw [run_query_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    cases h : H.view s t with
    | some u =>
      rw [H.randomOracle_run_of_some h, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact (ih u (hk u) s hz).trans (by gcongr; omega)
    | none =>
      rw [H.randomOracle_run_of_none h, support_map] at hp
      obtain ⟨u, -, rfl⟩ := hp
      refine (ih u (hk u) _ hz).trans ?_
      rw [H.view_record _ _ _ h, ← cast_pred_add_one hpos, add_comm _ (1 : ℝ≥0∞), ← add_assoc]
      gcongr
      exact QueryCache.enncard_cacheQuery_le _ t u

/-- If every state reached within the budget is charged at most `κ` at a fresh query, a run of
at most `n` queries adds at most `n * κ` to the total. A state is reached within the budget if
its cache, with one more entry, is at most `n` entries larger than the initial one. -/
theorem charge_le_of_mem_support {charge : σ → spec.Domain → ℝ≥0∞} {κ : ℝ≥0∞}
    {oa : OracleComp spec α} {n : ℕ} (hn : IsTotalQueryBound oa n) (s : σ)
    (hκ : ∀ s' t, H.view s' t = none → (H.view s').enncard + 1 ≤ (H.view s).enncard + n →
      charge s' t ≤ κ)
    (total : ℝ≥0∞) {z : α × σ × ℝ≥0∞}
    (hz : z ∈ support ((simulateQ (H.chargedOracle charge) oa).run (s, total))) :
    z.2.2 ≤ total + n * κ := by
  induction oa using OracleComp.inductionOn generalizing n s total with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_self_add (a := total)
  | query_bind t k ih =>
    obtain ⟨hpos, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    have hsplit : (n : ℝ≥0∞) * κ = κ + ((n - 1 : ℕ) : ℝ≥0∞) * κ := by
      rw [← cast_pred_add_one hpos, add_mul, one_mul, add_comm]
    rw [run_query_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    cases h : H.view s t with
    | some u =>
      rw [H.chargedOracle_run_of_some charge h, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      refine (ih u (hk u) s (fun s' t' ht' hs' ↦ hκ s' t' ht' (hs'.trans ?_)) total hz).trans ?_
      · gcongr
        omega
      · rw [hsplit]
        gcongr
        exact le_add_self
    | none =>
      rw [H.chargedOracle_run_of_none charge h, support_map] at hp
      obtain ⟨u, -, rfl⟩ := hp
      refine (ih u (hk u) _ (fun s' t' ht' hs' ↦ hκ s' t' ht' (hs'.trans ?_)) _ hz).trans ?_
      · rw [H.view_record _ _ _ h, ← cast_pred_add_one hpos, add_comm _ (1 : ℝ≥0∞),
          ← add_assoc]
        gcongr
        exact QueryCache.enncard_cacheQuery_le _ t u
      · rw [hsplit, ← add_assoc]
        gcongr
        refine hκ s t h ?_
        gcongr
        exact_mod_cast hpos

/-- The expected total charge of a run of at most `n` queries, every state reached within the
budget charged at most `κ`, is at most `n * κ`. -/
theorem expected_charge_le_mul {charge : σ → spec.Domain → ℝ≥0∞} {κ : ℝ≥0∞}
    {oa : OracleComp spec α} {n : ℕ} (hn : IsTotalQueryBound oa n) (s : σ)
    (hκ : ∀ s' t, H.view s' t = none → (H.view s').enncard + 1 ≤ (H.view s).enncard + n →
      charge s' t ≤ κ) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$> (simulateQ (H.chargedOracle charge) oa).run (s, 0)] ≤
      n * κ :=
  lintegral_id_evalDist_map_le_of_le_of_mem_support _ fun _ hz ↦
    (H.charge_le_of_mem_support hn s hκ 0 hz).trans (zero_add _).le

/-- **The charged invariant, uniform charge.** If a fresh query at a good state reached within
the budget breaks `Good` with probability at most `κ`, a computation making at most `n` queries
from a good state ends in a bad one with probability at most `n * κ`. -/
theorem prEvent_not_good_le_mul (Good : σ → Prop) {κ : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    (hn : IsTotalQueryBound oa n) {s : σ} (hs : Good s)
    (hstep : ∀ s' t, H.view s' t = none → Good s' →
      (H.view s').enncard + 1 ≤ (H.view s).enncard + n →
      Pr{let u ← $ᵗ spec.Range t}[¬ Good (H.record s' t u)] ≤ κ) :
    Pr{let z ← (simulateQ H.randomOracle oa).run s}[¬ Good z.2] ≤ n * κ := by
  classical
  let charge : σ → spec.Domain → ℝ≥0∞ := fun s' _ ↦
    if (H.view s').enncard + 1 ≤ (H.view s).enncard + n then κ else 1
  refine (H.prEvent_not_good_le_expected_charge Good charge (fun s' t ht hg ↦ ?_) oa hs).trans
    (H.expected_charge_le_mul hn s fun s' t _ hs' ↦ by simp [charge, hs'])
  by_cases hs' : (H.view s').enncard + 1 ≤ (H.view s).enncard + n
  · simpa [charge, hs'] using hstep s' t ht hg hs'
  · simp [charge, hs']

/-- **Expected count.** If a fresh answer satisfies `S` with probability at most `p`, a
computation making at most `n` queries caches in expectation at most `n * p` fresh answers
satisfying `S`. -/
theorem expected_fresh_le (S : (t : spec.Domain) → spec.Range t → Prop) {p : ℝ≥0∞}
    (hS : ∀ t, Pr{let u ← $ᵗ spec.Range t}[S t u] ≤ p) {oa : OracleComp spec α} {n : ℕ}
    (hn : IsTotalQueryBound oa n) (s : σ) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ answersIn S (H.view z.2)) <$> (simulateQ H.randomOracle oa).run s] ≤
      answersIn S (H.view s) + n * p := by
  classical
  refine (H.potential_le_expected_charge (fun s ↦ answersIn S (H.view s)) (fun _ _ ↦ p)
    (fun s t ht ↦ ?_) oa s).trans
    (add_le_add_right (H.expected_charge_le_mul hn s fun _ _ _ _ ↦ le_rfl) _)
  simp only [H.view_record _ _ _ ht, answersIn_cacheQuery S ht]
  rw [lintegral_id_evalDist_map_const_add _ (OracleComp.prEvent_true_eq_one _),
    ← prEvent_eq_lintegral_id_evalDist_map_ite]
  exact add_le_add_right (hS t) _

end QueryHistory

/-! ## The cache of `randomOracle` -/

variable {spec : OracleSpec.{0, 0} ι} [∀ t, SampleableType (spec.Range t)] {α : Type}

/-- The lazy random oracle with a running total of charges: a fresh query `t` at cache `c` adds
`charge c t`, a cached query adds nothing. -/
abbrev chargedRandomOracle (charge : spec.QueryCache → spec.Domain → ℝ≥0∞) :
    QueryImpl spec (StateT (spec.QueryCache × ℝ≥0∞) ProbComp) :=
  QueryHistory.cache.chargedOracle charge

/-- Forgetting the total, the charged oracle is `randomOracle`. -/
theorem chargedRandomOracle_run_map (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (oa : OracleComp spec α) (c : spec.QueryCache) (total : ℝ≥0∞) :
    Prod.map id Prod.fst <$> (simulateQ (chargedRandomOracle charge) oa).run (c, total) =
      (simulateQ spec.randomOracle oa).run c := by
  rw [← QueryHistory.randomOracle_cache]
  exact QueryHistory.cache.chargedOracle_run_map charge oa c total

/-- **Expected potential**, for the cache of `randomOracle`. -/
theorem potential_le_expected_charge (Φ : spec.QueryCache → ℝ≥0∞)
    (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (hstep : ∀ c t, c t = none →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (c.cacheQuery t u)) <$> ($ᵗ spec.Range t)] ≤ Φ c + charge c t)
    (oa : OracleComp spec α) (c : spec.QueryCache) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ Φ z.2) <$> (simulateQ spec.randomOracle oa).run c] ≤
      Φ c + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (chargedRandomOracle charge) oa).run (c, 0)] := by
  rw [← QueryHistory.randomOracle_cache]
  exact QueryHistory.cache.potential_le_expected_charge Φ charge hstep oa c

/-- An event on the output and the final cache on which the potential is at least `1`, for
`randomOracle`. -/
theorem prEvent_le_of_potential (E : α × spec.QueryCache → Prop) (Φ : spec.QueryCache → ℝ≥0∞)
    (hE : ∀ z, E z → 1 ≤ Φ z.2) (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (hstep : ∀ c t, c t = none →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (c.cacheQuery t u)) <$> ($ᵗ spec.Range t)] ≤ Φ c + charge c t)
    (oa : OracleComp spec α) (c : spec.QueryCache) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run c}[E z] ≤
      Φ c + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (chargedRandomOracle charge) oa).run (c, 0)] := by
  rw [← QueryHistory.randomOracle_cache]
  exact QueryHistory.cache.prEvent_le_of_potential E Φ hE charge hstep oa c

/-- **The charged invariant**, for the cache of `randomOracle`. -/
theorem prEvent_not_good_le_expected_charge (Good : spec.QueryCache → Prop)
    (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (hstep : ∀ c t, c t = none → Good c →
      Pr{let u ← $ᵗ spec.Range t}[¬ Good (c.cacheQuery t u)] ≤ charge c t)
    (oa : OracleComp spec α) {c : spec.QueryCache} (hc : Good c) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run c}[¬ Good z.2] ≤
      ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (chargedRandomOracle charge) oa).run (c, 0)] := by
  rw [← QueryHistory.randomOracle_cache]
  exact QueryHistory.cache.prEvent_not_good_le_expected_charge Good charge hstep oa hc

/-- A computation making at most `n` queries to `randomOracle` adds at most `n` entries to
its cache. -/
theorem enncard_le_of_mem_support {oa : OracleComp spec α} {n : ℕ} (hn : IsTotalQueryBound oa n)
    (c : spec.QueryCache) {z : α × spec.QueryCache}
    (hz : z ∈ support ((simulateQ spec.randomOracle oa).run c)) :
    z.2.enncard ≤ c.enncard + n := by
  rw [← QueryHistory.randomOracle_cache] at hz
  exact QueryHistory.cache.enncard_le_of_mem_support hn c hz

/-- **The charged invariant, uniform charge**, for the cache of `randomOracle`. -/
theorem prEvent_not_good_le_mul (Good : spec.QueryCache → Prop) {κ : ℝ≥0∞}
    {oa : OracleComp spec α} {n : ℕ} (hn : IsTotalQueryBound oa n) {c : spec.QueryCache}
    (hc : Good c)
    (hstep : ∀ c' t, c' t = none → Good c' → c'.enncard + 1 ≤ c.enncard + n →
      Pr{let u ← $ᵗ spec.Range t}[¬ Good (c'.cacheQuery t u)] ≤ κ) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run c}[¬ Good z.2] ≤ n * κ := by
  rw [← QueryHistory.randomOracle_cache]
  exact QueryHistory.cache.prEvent_not_good_le_mul Good hn hc hstep

/-- **Expected count, for a set of answers.** A computation making at most `n` queries to a
random oracle answering in `Y` caches in expectation at most `n * |S| / |Y|` fresh answers in
`S`. -/
theorem expected_fresh_in_le {Y : Type} [SampleableType Y] [Fintype Y] (S : Finset Y)
    {oa : OracleComp (ι →ₒ Y) α} {n : ℕ} (hn : IsTotalQueryBound oa n) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ answersIn (fun _ (u : Y) ↦ u ∈ S) z.2) <$>
      (simulateQ (ι →ₒ Y).randomOracle oa).run ∅] ≤ n * (S.card / Fintype.card Y) := by
  classical
  have hS (t : ι) :
      Pr{let u ← $ᵗ (ι →ₒ Y).Range t}[u ∈ S] ≤ (S.card / Fintype.card Y : ℝ≥0∞) := by
    rw [SampleableType.prEvent_uniformSample (α := Y)]
    simp
  rw [← QueryHistory.randomOracle_cache]
  simpa using QueryHistory.cache.expected_fresh_le (fun _ (u : Y) ↦ u ∈ S) hS hn ∅

end

end LeanerVM.Protocol
