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
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import LeanerVM.Protocol.ToVCVio.QueryLog

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
  number of fresh answers in `S` is at most `n * p`;
* `charge_le_of_isQueryBound`, `expected_charge_le_of_isQueryBound`: a charge paid by a query
  bound of VCVio's general form (`IsQueryBound`, a budget spent query by query), the budget
  priced so that a fresh query is charged at most the price it spends, totals at most the price
  of the initial budget;
* `expected_charge_le_sum`: a charge that is a sum of components, component `j` at most `κ j` on
  the queries satisfying `p j` and zero on the others, has expected total at most
  `∑ j, n j * κ j` when the computation makes at most `n j` queries satisfying `p j`
  (`IsQueryBoundP`); the budgets are combined by `isQueryBound_pi_of_isQueryBoundP`.

Two runs in sequence, `oa >>= ob` against a stateful implementation:
`prEvent_simulateQ_bind_le_lintegral` bounds an event by the expectation over the first run's end
of `1` on a bad event of it and of the second run's bound otherwise, and
`prEvent_simulateQ_bind_le_add_iSup` by the bad event's probability plus the second run's largest
bound. `QueryHistory.prEvent_bind_le_of_potential` composes the expectation form with the
potential: the second run's bound from a good end of the first is the potential there plus `ε`,
and the total is the initial potential, the first run's expected charge and `ε`.

**The fresh log of a logged run.** `QueryHistory.IsFreshLog s` says the log of a `freshLog` state
lists its cache's entries, each input once (`IsFreshLog.enncard_eq`: as many as the cache has).
`QueryHistory.withQueryLog_freshLog_support`: a run of `oa.withQueryLog` from such a state ends in
one whose log is the old log followed by the run's queries at their first occurrence
(`QueryLog.dedupKeys`) the old cache did not hold, with the old cache kept and every logged query
cached with its logged answer.

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
  unfold answersIn
  split_ifs with hS <;> simp [hset, Set.insert_inter_of_mem, Set.insert_inter_of_notMem, hS,
    Set.encard_insert_of_notMem, hc]

/-- One query, then `n - 1` more. -/
private theorem cast_eq_one_add_pred {n : ℕ} (hn : 0 < n) : (n : ℝ≥0∞) = 1 + (n - 1 : ℕ) := by
  rw [add_comm, ← Nat.cast_add_one, Nat.sub_add_cancel hn]

omit [DecidableEq ι] in
/-- Bounds on finitely many kinds of query, at most `n j` queries satisfying `p j` for each
`j ∈ S`, are one query bound of VCVio's general form on a budget per kind: a query is allowed when
every kind it is of has budget left, and spends one of each. -/
theorem isQueryBound_pi_of_isQueryBoundP {spec : OracleSpec.{0, 0} ι} {α J : Type}
    (S : Finset J) (p : J → ι → Prop) [∀ j, DecidablePred (p j)] {oa : OracleComp spec α}
    {n : J → ℕ} (h : ∀ j ∈ S, oa.IsQueryBoundP (p j) (n j)) :
    oa.IsQueryBound n (fun t b ↦ ∀ j ∈ S, p j t → 0 < b j)
      (fun t b j ↦ if p j t then b j - 1 else b j) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t k ih =>
    have h' := fun j hj ↦ (isQueryBoundP_query_bind_iff (p j) t k (n j)).mp (h j hj)
    exact (isQueryBound_query_bind_iff _ _ _ _ _).mpr
      ⟨fun j hj hp ↦ (h' j hj).1.resolve_left (not_not.mpr hp),
        fun u ↦ ih u fun j hj ↦ (h' j hj).2 u⟩

/-! ## Two runs in sequence -/

section Sequence

variable {spec : OracleSpec.{0, 0} ι} {τ β γ : Type} (impl : QueryImpl spec (StateT τ ProbComp))
  (oa : OracleComp spec β) (ob : β → OracleComp spec γ) (s : τ) (E : γ × τ → Prop)
  (E₁ : β × τ → Prop) (E₂ : β × τ → γ × τ → Prop)

omit [DecidableEq ι] in
/-- **Two runs in sequence.** Run `oa` from the state `s` against a stateful implementation, then
`ob` on its output from the state it leaves. If on every pair of reachable runs an event `E` of
the final output and state implies an event `E₁` of the first run's output and state or an event
`E₂` of both, then `E` has probability at most the expectation, over the first run's end `z₁`, of
`1` when `E₁ z₁` holds and of the probability of `E₂ z₁` over the second run otherwise. -/
theorem prEvent_simulateQ_bind_le_lintegral [DecidablePred E₁]
    (hE : ∀ z₁ ∈ support ((simulateQ impl oa).run s),
      ∀ z₂ ∈ support ((simulateQ impl (ob z₁.1)).run z₁.2), E z₂ → E₁ z₁ ∨ E₂ z₁ z₂) :
    Pr{let z ← (simulateQ impl (oa >>= ob)).run s}[E z] ≤
      ∫⁻ r, r ∂𝒟[(fun z₁ ↦ if E₁ z₁ then 1 else
        Pr{let z₂ ← (simulateQ impl (ob z₁.1)).run z₁.2}[E₂ z₁ z₂]) <$>
          (simulateQ impl oa).run s] := by
  rw [simulateQ_bind, StateT.run_bind, prEvent_bind_eq_lintegral_id_evalDist_map]
  refine lintegral_id_evalDist_map_mono_of_mem_support _ fun z₁ hz₁ ↦ ?_
  split_ifs with h
  · exact prEvent_le_one _ _
  · exact prEvent_mono_of_support _ _ _ fun z₂ hz₂ hE₂ ↦ (hE z₁ hz₁ z₂ hz₂ hE₂).resolve_left h

omit [DecidableEq ι] in
/-- **Two runs in sequence, at the worst end of the first.** Under the hypotheses of
`prEvent_simulateQ_bind_le_lintegral`, `E` has probability at most that of `E₁` plus the largest
probability of `E₂` over the second run, from an end of the first run outside `E₁`. A bound for
the first run and one for the second from any good state it can leave compose; a bound for the
second run that depends on the state the first leaves is better composed in expectation
(`QueryHistory.prEvent_bind_le_of_potential`). -/
theorem prEvent_simulateQ_bind_le_add_iSup
    (hE : ∀ z₁ ∈ support ((simulateQ impl oa).run s),
      ∀ z₂ ∈ support ((simulateQ impl (ob z₁.1)).run z₁.2), E z₂ → E₁ z₁ ∨ E₂ z₁ z₂) :
    Pr{let z ← (simulateQ impl (oa >>= ob)).run s}[E z] ≤
      Pr{let z₁ ← (simulateQ impl oa).run s}[E₁ z₁] +
        ⨆ z₁ ∈ support ((simulateQ impl oa).run s), ⨆ (_ : ¬ E₁ z₁),
          Pr{let z₂ ← (simulateQ impl (ob z₁.1)).run z₁.2}[E₂ z₁ z₂] := by
  rw [simulateQ_bind, StateT.run_bind]
  exact (prEvent_bind_le_add_iSup _ _ E₁ E).trans (add_le_add le_rfl
    (iSup₂_mono fun z₁ hz₁ ↦ iSup_mono fun hn ↦ prEvent_mono_of_support _ _ _
      fun z₂ hz₂ hE₂ ↦ (hE z₁ hz₁ z₂ hz₂ hE₂).resolve_left hn))

end Sequence

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
    (cache : QueryHistory spec spec.QueryCache).randomOracle = spec.randomOracle :=
  funext fun t ↦ StateT.ext fun c ↦ by
    cases h : c t with
    | some u => rw [randomOracle_run_of_some cache h, QueryImpl.withCaching_run_some _ h]
    | none => rw [randomOracle_run_of_none cache h, QueryImpl.withCaching_run_none _ h]; rfl

omit [DecidableEq ι] [∀ t, SampleableType (spec.Range t)] in
/-- Running a query and then a continuation under a stateful implementation. -/
private theorem run_query_bind {τ : Type} (impl : QueryImpl spec (StateT τ ProbComp))
    (t : spec.Domain) (k : spec.Range t → OracleComp spec α) (s : τ) :
    (simulateQ impl (liftM (spec.query t) >>= k)).run s =
      (impl t).run s >>= fun p ↦ (simulateQ impl (k p.1)).run p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

omit [∀ t, SampleableType (spec.Range t)] in
/-- A fresh query and at most `n - 1` more add at most `n` entries to the cache. -/
private theorem enncard_view_record_add_le {s : σ} {t : spec.Domain} (h : H.view s t = none)
    (u : spec.Range t) {n : ℕ} (hn : 0 < n) :
    (H.view (H.record s t u)).enncard + (n - 1 : ℕ) ≤ (H.view s).enncard + n := by
  rw [H.view_record _ _ _ h, cast_eq_one_add_pred hn, ← add_assoc]
  exact add_le_add (QueryCache.enncard_cacheQuery_le _ t u) le_rfl

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
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (fun t ⟨s, a⟩ ↦ by
    cases h : H.view s t with
    | some u => simp [H.chargedOracle_run_of_some charge h, H.randomOracle_run_of_some h]
    | none =>
      simp [H.chargedOracle_run_of_none charge h, H.randomOracle_run_of_none h,
        Functor.map_map]) oa (s, total)

/-- A run from total `total` is a run from total `0` with `total` added. -/
theorem chargedOracle_run_total (charge : σ → spec.Domain → ℝ≥0∞) (oa : OracleComp spec α)
    (s : σ) (total : ℝ≥0∞) :
    (simulateQ (H.chargedOracle charge) oa).run (s, total) =
      (fun z ↦ (z.1, z.2.1, total + z.2.2)) <$>
        (simulateQ (H.chargedOracle charge) oa).run (s, 0) := by
  have := OracleComp.map_run_simulateQ_eq_of_query_map_eq (H.chargedOracle charge)
    (H.chargedOracle charge) (fun p ↦ (p.1, total + p.2))
    (fun t ⟨s, a⟩ ↦ by
      cases h : H.view s t with
      | some u => simp [H.chargedOracle_run_of_some charge h]
      | none => simp [H.chargedOracle_run_of_none charge h, Functor.map_map, add_assoc]) oa (s, 0)
  rwa [add_zero, eq_comm] at this

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
      simp only [zero_add, H.chargedOracle_run_total charge _ _ (charge s t), Functor.map_map,
        lintegral_id_evalDist_map_const_add _ (OracleComp.prEvent_true_eq_one _)]
      refine (lintegral_id_evalDist_map_mono _ fun u ↦ ih u (H.record s t u)).trans ?_
      rw [lintegral_id_evalDist_map_add, ← add_assoc]
      exact add_le_add_left (hstep s t h) _

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
  refine (lintegral_id_evalDist_map_mono _ fun z ↦ ?_).trans
    (H.potential_le_expected_charge Φ charge hstep oa s)
  split_ifs with h
  exacts [hE z h, bot_le]

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
  refine (H.prEvent_le_of_potential (fun z ↦ ¬ Good z.2) (fun s ↦ if ¬ Good s then 1 else 0)
    (fun z hz ↦ by simp [hz]) charge (fun s t ht ↦ ?_) oa s).trans_eq
    (by simp only [hs, not_true_eq_false, ↓reduceIte, zero_add])
  split_ifs with hg
  · exact (prEvent_eq_lintegral_id_evalDist_map_ite _ _).symm.trans_le
      ((hstep s t ht hg).trans_eq (zero_add _).symm)
  · exact (lintegral_id_evalDist_map_le_of_le _ fun u ↦ by split_ifs <;> simp).trans le_self_add

/-- A computation making at most `n` queries adds at most `n` entries to the cache. -/
theorem enncard_le_of_mem_support {oa : OracleComp spec α} {n : ℕ} (hn : IsTotalQueryBound oa n)
    (s : σ) {z : α × σ} (hz : z ∈ support ((simulateQ H.randomOracle oa).run s)) :
    (H.view z.2).enncard ≤ (H.view s).enncard + n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure a =>
    obtain rfl : z = (a, s) := by simpa using hz
    exact le_self_add
  | query_bind t k ih =>
    obtain ⟨hpos, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    rw [run_query_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    cases h : H.view s t with
    | some u =>
      rw [H.randomOracle_run_of_some h, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact (ih u (hk u) s hz).trans (add_le_add le_rfl (Nat.cast_le.mpr (n.sub_le 1)))
    | none =>
      rw [H.randomOracle_run_of_none h, support_map] at hp
      obtain ⟨u, -, rfl⟩ := hp
      exact (ih u (hk u) _ hz).trans (H.enncard_view_record_add_le h u hpos)

/-- **Charges within a budget.** Let `oa` meet a query bound of VCVio's general form from the
budget `b`: a query `t` is allowed at a budget `b'` when `canQuery t b'`, and leaves `cost t b'`.
Let `w` price budgets, an allowed query never raising the price. If a fresh query at a state
reached within `n` queries is charged at most the price it spends, a run of at most `n` queries
adds at most `w b` to the total. -/
theorem charge_le_of_isQueryBound {B : Type*} {canQuery : spec.Domain → B → Prop}
    {cost : spec.Domain → B → B} (w : B → ℝ≥0∞) {charge : σ → spec.Domain → ℝ≥0∞}
    {oa : OracleComp spec α} {b : B} (hb : oa.IsQueryBound b canQuery cost) {n : ℕ}
    (hn : IsTotalQueryBound oa n) (s : σ) (hcost : ∀ t b', canQuery t b' → w (cost t b') ≤ w b')
    (hw : ∀ s' t b', H.view s' t = none → (H.view s').enncard + 1 ≤ (H.view s).enncard + n →
      canQuery t b' → charge s' t + w (cost t b') ≤ w b')
    (total : ℝ≥0∞) {z : α × σ × ℝ≥0∞}
    (hz : z ∈ support ((simulateQ (H.chargedOracle charge) oa).run (s, total))) :
    z.2.2 ≤ total + w b := by
  induction oa using OracleComp.inductionOn generalizing b n s total with
  | pure a =>
    obtain rfl : z = (a, s, total) := by simpa using hz
    exact le_self_add
  | query_bind t k ih =>
    obtain ⟨hpos, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    obtain ⟨hcan, hkb⟩ := (isQueryBound_query_bind_iff t k b canQuery cost).mp hb
    rw [run_query_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    cases h : H.view s t with
    | some u =>
      rw [H.chargedOracle_run_of_some charge h, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      have hle : ((n - 1 : ℕ) : ℝ≥0∞) ≤ n := Nat.cast_le.mpr (n.sub_le 1)
      exact (ih u (hkb u) (hk u) s (fun s' t' b' ht' hs' ↦
        hw s' t' b' ht' (hs'.trans (add_le_add le_rfl hle))) total hz).trans
        (add_le_add le_rfl (hcost t b hcan))
    | none =>
      rw [H.chargedOracle_run_of_none charge h, support_map] at hp
      obtain ⟨u, -, rfl⟩ := hp
      refine (ih u (hkb u) (hk u) _ (fun s' t' b' ht' hs' ↦
        hw s' t' b' ht' (hs'.trans (H.enncard_view_record_add_le h u hpos))) _ hz).trans ?_
      rw [add_assoc]
      exact add_le_add le_rfl (hw s t b h (add_le_add le_rfl (Nat.one_le_cast.mpr hpos)) hcan)

/-- The expected total charge of a run within a budget of VCVio's general form, priced by `w`
as in `charge_le_of_isQueryBound`, is at most the price `w b` of the budget. -/
theorem expected_charge_le_of_isQueryBound {B : Type*} {canQuery : spec.Domain → B → Prop}
    {cost : spec.Domain → B → B} (w : B → ℝ≥0∞) {charge : σ → spec.Domain → ℝ≥0∞}
    {oa : OracleComp spec α} {b : B} (hb : oa.IsQueryBound b canQuery cost) {n : ℕ}
    (hn : IsTotalQueryBound oa n) (s : σ) (hcost : ∀ t b', canQuery t b' → w (cost t b') ≤ w b')
    (hw : ∀ s' t b', H.view s' t = none → (H.view s').enncard + 1 ≤ (H.view s).enncard + n →
      canQuery t b' → charge s' t + w (cost t b') ≤ w b') :
    ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$> (simulateQ (H.chargedOracle charge) oa).run (s, 0)] ≤ w b :=
  lintegral_id_evalDist_map_le_of_le_of_mem_support _ fun _ hz ↦
    (H.charge_le_of_isQueryBound w hb hn s hcost hw 0 hz).trans (zero_add _).le

/-- If every state reached within the budget is charged at most `κ` at a fresh query, a run of
at most `n` queries adds at most `n * κ` to the total. A state is reached within the budget if
its cache, with one more entry, is at most `n` entries larger than the initial one. -/
theorem charge_le_of_mem_support {charge : σ → spec.Domain → ℝ≥0∞} {κ : ℝ≥0∞}
    {oa : OracleComp spec α} {n : ℕ} (hn : IsTotalQueryBound oa n) (s : σ)
    (hκ : ∀ s' t, H.view s' t = none → (H.view s').enncard + 1 ≤ (H.view s).enncard + n →
      charge s' t ≤ κ)
    (total : ℝ≥0∞) {z : α × σ × ℝ≥0∞}
    (hz : z ∈ support ((simulateQ (H.chargedOracle charge) oa).run (s, total))) :
    z.2.2 ≤ total + n * κ :=
  H.charge_le_of_isQueryBound (canQuery := fun _ b ↦ 0 < b) (cost := fun _ b ↦ b - 1)
    (fun b : ℕ ↦ (b : ℝ≥0∞) * κ) hn hn s
    (fun _ b _ ↦ mul_le_mul' (Nat.cast_le.mpr (b.sub_le 1)) le_rfl)
    (fun s' t b ht hs hb ↦ by
      rw [cast_eq_one_add_pred hb, add_mul, one_mul]
      exact add_le_add (hκ s' t ht hs) le_rfl) total hz

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
  refine (H.prEvent_not_good_le_expected_charge Good
    (fun s' _ ↦ if (H.view s').enncard + 1 ≤ (H.view s).enncard + n then κ else 1)
    (fun s' t ht hg ↦ ?_) oa hs).trans
    (H.expected_charge_le_mul hn s fun s' t _ hs' ↦ by simp [hs'])
  split_ifs with hs'
  exacts [hstep s' t ht hg hs', by simp]

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

/-! ### Charges paid by a budget per kind of query -/

/-- **A sum of charges, each paid by its own budget.** Let the charge be a sum of components over
`S`, component `j` at most `κ j` at a fresh query satisfying `p j` and zero at any other, at the
states reached within `N` queries. A computation making at most `N` queries, at most `n j` of them
satisfying `p j`, has expected total charge at most `∑ j ∈ S, n j * κ j`. A component charged at
every query takes `p j` true and `n j = N`; when every query is of some kind, `N` may be
`∑ j ∈ S, n j`. The kinds are read off the query input alone, as `IsQueryBoundP` counts every
query of the computation's tree: a component nonzero only at inputs the state singles out, among
inputs of one shape, is budgeted by all the queries of that shape. -/
theorem expected_charge_le_sum {J : Type} (S : Finset J) (p : J → spec.Domain → Prop)
    [∀ j, DecidablePred (p j)] {charge : J → σ → spec.Domain → ℝ≥0∞} {κ : J → ℝ≥0∞}
    {oa : OracleComp spec α} {N : ℕ} (hN : IsTotalQueryBound oa N) {n : J → ℕ}
    (hn : ∀ j ∈ S, oa.IsQueryBoundP (p j) (n j)) (s : σ)
    (hκ : ∀ j ∈ S, ∀ s' t, H.view s' t = none →
      (H.view s').enncard + 1 ≤ (H.view s).enncard + N →
      charge j s' t ≤ if p j t then κ j else 0) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
      (simulateQ (H.chargedOracle fun s' t ↦ ∑ j ∈ S, charge j s' t) oa).run (s, 0)] ≤
      ∑ j ∈ S, n j * κ j := by
  refine H.expected_charge_le_of_isQueryBound (fun b ↦ ∑ j ∈ S, (b j : ℝ≥0∞) * κ j)
    (isQueryBound_pi_of_isQueryBoundP S p hn) hN s (fun t b _ ↦ ?_)
    (fun s' t b ht hs hcan ↦ ?_)
  · exact Finset.sum_le_sum fun j _ ↦
      mul_le_mul' (Nat.cast_le.mpr (by dsimp only; split_ifs <;> omega)) le_rfl
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj ↦ ?_
    have hc := hκ j hj s' t ht hs
    dsimp only
    split_ifs at hc ⊢ with hp
    · rw [cast_eq_one_add_pred (hcan j hj hp) (n := b j), add_mul, one_mul]
      exact add_le_add hc le_rfl
    · rw [nonpos_iff_eq_zero.mp hc, zero_add]

/-- **Two runs, one potential.** Run `oa` from `s` on `H`'s lazy random oracle, then `ob` on its
output. Let the potential `Φ` grow by at most `charge` in expectation at a fresh query, let it be
at least `1` on a bad event `E₁` of the first run's end, and let the second run, from a reachable
end `z₁` of the first outside `E₁`, give `E₂ z₁` probability at most `Φ z₁.2 + ε`. If `E`
implies `E₁ ∨ E₂` on reachable runs, it has probability at most the initial potential, plus the
first run's expected total charge, plus `ε`: the second run starts from the potential the first
leaves, in expectation, not from its largest value. -/
theorem prEvent_bind_le_of_potential {β γ : Type} (oa : OracleComp spec β)
    (ob : β → OracleComp spec γ) (s : σ) (E : γ × σ → Prop) (E₁ : β × σ → Prop)
    (E₂ : β × σ → γ × σ → Prop)
    (hE : ∀ z₁ ∈ support ((simulateQ H.randomOracle oa).run s),
      ∀ z₂ ∈ support ((simulateQ H.randomOracle (ob z₁.1)).run z₁.2),
        E z₂ → E₁ z₁ ∨ E₂ z₁ z₂)
    (Φ : σ → ℝ≥0∞) (charge : σ → spec.Domain → ℝ≥0∞)
    (hstep : ∀ s t, H.view s t = none →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (H.record s t u)) <$> ($ᵗ spec.Range t)] ≤ Φ s + charge s t)
    (hE₁ : ∀ z₁, E₁ z₁ → 1 ≤ Φ z₁.2) {ε : ℝ≥0∞}
    (hsecond : ∀ z₁ ∈ support ((simulateQ H.randomOracle oa).run s), ¬ E₁ z₁ →
      Pr{let z₂ ← (simulateQ H.randomOracle (ob z₁.1)).run z₁.2}[E₂ z₁ z₂] ≤ Φ z₁.2 + ε) :
    Pr{let z ← (simulateQ H.randomOracle (oa >>= ob)).run s}[E z] ≤
      Φ s + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (H.chargedOracle charge) oa).run (s, 0)] + ε := by
  classical
  refine (prEvent_simulateQ_bind_le_lintegral _ oa ob s E E₁ E₂ hE).trans <|
    (lintegral_id_evalDist_map_mono_of_mem_support _ (g := fun z₁ ↦ Φ z₁.2 + ε)
      fun z₁ hz₁ ↦ ?_).trans ?_
  · split_ifs with h
    exacts [(hE₁ z₁ h).trans le_self_add, hsecond z₁ hz₁ h]
  · rw [lintegral_id_evalDist_map_add _ (fun z₁ : β × σ ↦ Φ z₁.2) fun _ ↦ ε]
    exact add_le_add (H.potential_le_expected_charge Φ charge hstep oa s)
      (lintegral_id_evalDist_map_le_of_le _ fun _ ↦ le_rfl)

/-! ### The fresh log of a logged run -/

section FreshLog

/-- A state of `freshLog` whose log lists the cache's entries, each input once: every state a run
from the empty one reaches. -/
def IsFreshLog (s : spec.QueryCache × spec.QueryLog) : Prop :=
  (∀ e ∈ s.2, s.1 e.1 = some e.2) ∧ (∀ t u, s.1 t = some u → ⟨t, u⟩ ∈ s.2) ∧
    (s.2.map (·.1)).Nodup

omit [DecidableEq ι] [∀ t, SampleableType (spec.Range t)] in
theorem isFreshLog_empty : IsFreshLog ((∅ : spec.QueryCache), ([] : spec.QueryLog)) :=
  ⟨by simp, by simp [QueryCache.empty_apply], by simp⟩

omit [∀ t, SampleableType (spec.Range t)] in
/-- Recording a fresh query keeps the log the cache's. -/
theorem IsFreshLog.record {s : spec.QueryCache × spec.QueryLog} (h : IsFreshLog s)
    {t : spec.Domain} (ht : s.1 t = none) (u : spec.Range t) :
    IsFreshLog (freshLog.record s t u) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  have hne : ∀ e ∈ s.2, e.1 ≠ t := fun ⟨t', u'⟩ he het ↦ by
    have := h₁ _ he
    simp only at het this
    subst het
    rw [ht] at this
    cases this
  refine ⟨fun e he ↦ ?_, fun t' u' ht' ↦ ?_, ?_⟩
  · simp only [freshLog_record, List.mem_append, List.mem_singleton] at he ⊢
    rcases he with he | rfl
    · rw [QueryCache.cacheQuery_of_ne _ _ (hne e he)]
      exact h₁ e he
    · exact QueryCache.cacheQuery_self _ _ _
  · simp only [freshLog_record] at ht' ⊢
    by_cases htt : t' = t
    · subst htt
      rw [QueryCache.cacheQuery_self] at ht'
      cases ht'
      simp
    · rw [QueryCache.cacheQuery_of_ne _ _ htt] at ht'
      exact List.mem_append_left _ (h₂ t' u' ht')
  · simp only [freshLog_record, List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨h₃, by simp, fun a ha b hb hab ↦ ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    exact hne e he (hab.trans (by simpa using hb))

omit [∀ t, SampleableType (spec.Range t)] in
/-- A log that is the cache's has as many entries as the cache. -/
theorem IsFreshLog.enncard_eq {s : spec.QueryCache × spec.QueryLog} (h : IsFreshLog s) :
    s.1.enncard = s.2.length := by
  classical
  have hset : s.1.toSet = ↑s.2.toFinset := by
    ext ⟨t, u⟩
    simp only [QueryCache.mem_toSet, List.coe_toFinset]
    exact ⟨h.2.1 t u, h.1 _⟩
  rw [QueryCache.enncard, hset, Set.encard_coe_eq_coe_finsetCard,
    List.toFinset_card_of_nodup (h.2.2.of_map _)]
  rfl

/-- **The state after a logged run.** Run a logged computation on `freshLog`'s lazy random
oracle from a state whose log is the cache's. At every end, the log of fresh queries is the old
one followed by the run's queries at their first occurrence that the old cache did not hold; it
is still the cache's; the old cache is kept; and every logged query is cached with its logged
answer. -/
theorem withQueryLog_freshLog_support {α : Type} (oa : OracleComp spec α)
    {s : spec.QueryCache × spec.QueryLog} (hs : IsFreshLog s)
    {z : (α × spec.QueryLog) × spec.QueryCache × spec.QueryLog}
    (hz : z ∈ support ((simulateQ freshLog.randomOracle oa.withQueryLog).run s)) :
    z.2.2 = s.2 ++ (QueryLog.dedupKeys z.1.2).filter (fun e ↦ (s.1 e.1).isNone) ∧
      IsFreshLog z.2 ∧ s.1 ≤ z.2.1 ∧ ∀ e ∈ z.1.2, z.2.1 e.1 = some e.2 := by
  induction oa using OracleComp.inductionOn generalizing s z with
  | pure a =>
    simp only [withQueryLog_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨by simp, hs, le_rfl, by simp⟩
  | query_bind t k ih =>
    have hq : (liftM (spec.query t) >>= k).withQueryLog = liftM (spec.query t) >>= fun u ↦
        Prod.map id (⟨t, u⟩ :: ·) <$> (k u).withQueryLog := by
      rw [withQueryLog_bind, withQueryLog_query, bind_assoc]
      simp
    rw [hq, run_query_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨u, s'⟩, hus, hz⟩ := hz
    rw [simulateQ_map, StateT.run_map, support_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    cases h : s.1 t with
    | some u₀ =>
      rw [freshLog.randomOracle_run_of_some (s := s) h, support_pure,
        Set.mem_singleton_iff] at hus
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hus
      obtain ⟨h₁, h₂, h₃, h₄⟩ := ih u hs hz'
      refine ⟨?_, h₂, h₃, ?_⟩
      · simp only [Prod.map_snd, QueryLog.dedupKeys_cons, h, Option.isNone_some, List.filter_cons, Bool.false_eq_true, ↓reduceIte,
          List.filter_filter, h₁]
        congr 1
        refine List.filter_congr fun x _ ↦ ?_
        by_cases hx : x.1 = t
        · obtain ⟨x₁, x₂⟩ := x
          simp only at hx
          subst hx
          simp [h]
        · simp [hx]
      · simp only [Prod.map_snd, List.mem_cons, forall_eq_or_imp]
        exact ⟨h₃ h, h₄⟩
    | none =>
      rw [freshLog.randomOracle_run_of_none (s := s) h, support_map] at hus
      obtain ⟨v, -, hv⟩ := hus
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hv
      obtain ⟨h₁, h₂, h₃, h₄⟩ := ih v (hs.record h v) hz'
      have hle : s.1 ≤ (freshLog.record s t v).1 := QueryCache.le_cacheQuery _ h
      refine ⟨?_, h₂, hle.trans h₃, ?_⟩
      · simp only [Prod.map_snd, QueryLog.dedupKeys_cons, h, Option.isNone_none, List.filter_cons, ↓reduceIte, List.filter_filter, h₁,
          freshLog_record, List.append_assoc, List.singleton_append]
        congr 2
        refine List.filter_congr fun x _ ↦ ?_
        by_cases hx : x.1 = t
        · obtain ⟨x₁, x₂⟩ := x
          simp only at hx
          subst hx
          simp
        · simp [hx]
      · simp only [Prod.map_snd, List.mem_cons, forall_eq_or_imp]
        refine ⟨h₃ ?_, h₄⟩
        simp

end FreshLog

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
      (simulateQ spec.randomOracle oa).run c :=
  QueryHistory.randomOracle_cache (spec := spec) ▸ QueryHistory.cache.chargedOracle_run_map ..

/-- **Expected potential**, for the cache of `randomOracle`. -/
theorem potential_le_expected_charge (Φ : spec.QueryCache → ℝ≥0∞)
    (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (hstep : ∀ c t, c t = none →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (c.cacheQuery t u)) <$> ($ᵗ spec.Range t)] ≤ Φ c + charge c t)
    (oa : OracleComp spec α) (c : spec.QueryCache) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ Φ z.2) <$> (simulateQ spec.randomOracle oa).run c] ≤
      Φ c + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (chargedRandomOracle charge) oa).run (c, 0)] :=
  QueryHistory.randomOracle_cache (spec := spec) ▸
    QueryHistory.cache.potential_le_expected_charge Φ charge hstep oa c

/-- An event on the output and the final cache on which the potential is at least `1`, for
`randomOracle`. -/
theorem prEvent_le_of_potential (E : α × spec.QueryCache → Prop) (Φ : spec.QueryCache → ℝ≥0∞)
    (hE : ∀ z, E z → 1 ≤ Φ z.2) (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (hstep : ∀ c t, c t = none →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (c.cacheQuery t u)) <$> ($ᵗ spec.Range t)] ≤ Φ c + charge c t)
    (oa : OracleComp spec α) (c : spec.QueryCache) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run c}[E z] ≤
      Φ c + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (chargedRandomOracle charge) oa).run (c, 0)] :=
  QueryHistory.randomOracle_cache (spec := spec) ▸
    QueryHistory.cache.prEvent_le_of_potential E Φ hE charge hstep oa c

/-- **The charged invariant**, for the cache of `randomOracle`. -/
theorem prEvent_not_good_le_expected_charge (Good : spec.QueryCache → Prop)
    (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (hstep : ∀ c t, c t = none → Good c →
      Pr{let u ← $ᵗ spec.Range t}[¬ Good (c.cacheQuery t u)] ≤ charge c t)
    (oa : OracleComp spec α) {c : spec.QueryCache} (hc : Good c) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run c}[¬ Good z.2] ≤
      ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (chargedRandomOracle charge) oa).run (c, 0)] :=
  QueryHistory.randomOracle_cache (spec := spec) ▸
    QueryHistory.cache.prEvent_not_good_le_expected_charge Good charge hstep oa hc

/-- A computation making at most `n` queries to `randomOracle` adds at most `n` entries to
its cache. -/
theorem enncard_le_of_mem_support {oa : OracleComp spec α} {n : ℕ} (hn : IsTotalQueryBound oa n)
    (c : spec.QueryCache) {z : α × spec.QueryCache}
    (hz : z ∈ support ((simulateQ spec.randomOracle oa).run c)) :
    z.2.enncard ≤ c.enncard + n :=
  QueryHistory.cache.enncard_le_of_mem_support hn c
    (QueryHistory.randomOracle_cache (spec := spec) ▸ hz)

/-- **The charged invariant, uniform charge**, for the cache of `randomOracle`. -/
theorem prEvent_not_good_le_mul (Good : spec.QueryCache → Prop) {κ : ℝ≥0∞}
    {oa : OracleComp spec α} {n : ℕ} (hn : IsTotalQueryBound oa n) {c : spec.QueryCache}
    (hc : Good c)
    (hstep : ∀ c' t, c' t = none → Good c' → c'.enncard + 1 ≤ c.enncard + n →
      Pr{let u ← $ᵗ spec.Range t}[¬ Good (c'.cacheQuery t u)] ≤ κ) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run c}[¬ Good z.2] ≤ n * κ :=
  QueryHistory.randomOracle_cache (spec := spec) ▸
    QueryHistory.cache.prEvent_not_good_le_mul Good hn hc hstep

/-- **Expected count, for a set of answers.** A computation making at most `n` queries to a
random oracle answering in `Y` caches in expectation at most `n * |S| / |Y|` fresh answers in
`S`. -/
theorem expected_fresh_in_le {Y : Type} [SampleableType Y] [Fintype Y] (S : Finset Y)
    {oa : OracleComp (ι →ₒ Y) α} {n : ℕ} (hn : IsTotalQueryBound oa n) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ answersIn (fun _ (u : Y) ↦ u ∈ S) z.2) <$>
      (simulateQ (ι →ₒ Y).randomOracle oa).run ∅] ≤ n * (S.card / Fintype.card Y) := by
  classical
  rw [← QueryHistory.randomOracle_cache]
  simpa only [QueryHistory.cache_view, answersIn_empty, zero_add] using
    QueryHistory.cache.expected_fresh_le (fun _ (u : Y) ↦ u ∈ S)
      (fun _ ↦ (SampleableType.prEvent_uniformSample_le_div_iff (α := Y) _).2 (by simp)) hn ∅

end

end LeanerVM.Protocol
