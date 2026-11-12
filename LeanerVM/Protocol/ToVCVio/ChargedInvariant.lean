/-
  LeanerVM.Protocol.ToVCVio.ChargedInvariant

  A potential of a lazy random oracle's record of queries, raised in expectation by at most `κ`
  at each fresh query within a budget of `n`, bounds an event it dominates by the initial
  potential plus `n * κ`. Candidate for VCVio.
-/

module

public import LeanerVM.Protocol.ToVCVio.EventExpectation
public import VCVio.OracleComp.QueryTracking.ExpectedQueryCount
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import LeanerVM.Protocol.ToVCVio.QueryLog

/-!
# A charged potential of a lazy random oracle

A `QueryHistory spec σ` is a state `σ` recording a lazy random oracle's queries: it shows the
cache (`view`) and records a fresh query with its answer (`record`), the cache gaining that
entry. `QueryHistory.cache` is the cache alone; `QueryHistory.freshLog` is the cache with the
fresh queries in the order they were made, for predicates about what was known earlier.
`H.randomOracle` is the lazy random oracle on `H`'s state, whose cache is that of `randomOracle`
(`QueryHistory.randomOracle_run_view`); `QueryHistory.cache.randomOracle` is `randomOracle`.
Expectations are `∫⁻ r, r ∂𝒟[f <$> mx]`.

The main theorem, `QueryHistory.lintegral_le_of_potential`, is a supermartingale bound within a
query budget. Let a computation make at most `n` queries from the state `s`. At every fresh query
from a state whose cache, with one more entry, is at most `n` entries larger than `s`'s, let the
expected potential `Φ` after the uniform answer be at most the potential before plus `κ`. Then
the expected final potential is at most `Φ s + n * κ`. A step may thus pay in advance for a bad
event that a group of later queries completes, and the bound `κ` may hold only within the
budget, as a collision's charge `|c| / |Y|` does. It is VCVio's
`OracleComp.lintegral_run_le_of_isQueryBoundP` at the potential `Φ + m * κ` on the states with
room for the `m` queries left, and `⊤` on the others. Its consequences, in the namespace
`QueryHistory`:

* `prEvent_le_of_potential`: an event on the output and the final state on which `Φ ≥ 1` has
  probability at most `Φ s + n * κ`;
* `prEvent_bind_le_of_potential`: two runs in sequence, `oa >>= ob` with `oa` within the budget,
  the second run's probability from every reachable end of the first at most `Φ` there plus `ε`,
  give the event probability at most `Φ s + n * κ + ε`: the second run starts from the potential
  the first leaves, in expectation, not from its largest value;
* `enncard_le_of_mem_support`: a computation making at most `n` queries adds at most `n`
  entries to the cache.

**The fresh log of a logged run.** `QueryHistory.IsFreshLog s` says the log of a `freshLog` state
lists its cache's entries, each input once (`IsFreshLog.enncard_eq`: as many as the cache has).
`QueryHistory.withQueryLog_freshLog_support`: a run of `oa.withQueryLog` from such a state ends in
one whose log is the old log followed by the run's queries at their first occurrence
(`List.dedupKeys`) the old cache did not hold, with the old cache kept and every logged query
cached with its logged answer.
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

private theorem randomOracle_run_of_some {t : spec.Domain} {s : σ} {u : spec.Range t}
    (h : H.view s t = some u) : (H.randomOracle t).run s = pure (u, s) := by
  simp [randomOracle, h]

private theorem randomOracle_run_of_none {t : spec.Domain} {s : σ} (h : H.view s t = none) :
    (H.randomOracle t).run s = (fun u ↦ (u, H.record s t u)) <$> ($ᵗ spec.Range t) := by
  simp [randomOracle, h]

/-- On the cache alone, the oracle is `randomOracle`. -/
theorem randomOracle_cache :
    (cache : QueryHistory spec spec.QueryCache).randomOracle = spec.randomOracle :=
  funext fun t ↦ StateT.ext fun c ↦ by
    cases h : c t with
    | some u => rw [randomOracle_run_of_some cache h, QueryImpl.withCaching_run_some _ h]
    | none => rw [randomOracle_run_of_none cache h, QueryImpl.withCaching_run_none _ h]; rfl

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

/-- **Expected potential within a query budget.** Let `oa` make at most `n` queries, and at every
fresh query from a state whose cache, with one more entry, is at most `n` entries larger than
`s`'s, let the expected potential after the uniform answer be at most the potential before plus
`κ`. Then the expected final potential of a run from `s` is at most `Φ s + n * κ`. -/
theorem lintegral_le_of_potential (Φ : σ → ℝ≥0∞) {κ : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    (hn : IsTotalQueryBound oa n) (s : σ)
    (hstep : ∀ s' t, H.view s' t = none → (H.view s').enncard + 1 ≤ (H.view s).enncard + n →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (H.record s' t u)) <$> ($ᵗ spec.Range t)] ≤ Φ s' + κ) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ Φ z.2) <$> (simulateQ H.randomOracle oa).run s] ≤ Φ s + n * κ := by
  classical
  -- the potential and `m` steps' worth on the states with room for `m` more entries
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → σ → ℝ≥0∞, ∀ m s', Ψ m s' =
      if (H.view s').enncard + m ≤ (H.view s).enncard + n then Φ s' + m * κ else ⊤ :=
    ⟨_, fun _ _ ↦ rfl⟩
  have hmono : ∀ s', Monotone fun m ↦ Ψ m s' := fun s' a b hab ↦ by
    have hab' : (a : ℝ≥0∞) ≤ b := Nat.cast_le.mpr hab
    simp only [hΨ]
    split_ifs with ha hb hb
    · exact add_le_add le_rfl (mul_le_mul' hab' le_rfl)
    · exact le_top
    · exact absurd ((add_le_add le_rfl hab').trans hb) ha
    · exact le_rfl
  refine (lintegral_id_evalDist_map_mono _ fun z ↦ ?_).trans <|
    (lintegral_run_le_of_isQueryBoundP H.randomOracle (fun _ ↦ True) Ψ hmono
      (fun t s' m ↦ ?_) oa n ((isQueryBoundP_true_iff oa n).mpr hn) s).trans ?_
  · rw [hΨ]
    split_ifs <;> simp
  · rw [ite_eq_left trivial]
    cases h : H.view s' t with
    | some u =>
      rw [H.randomOracle_run_of_some h, map_pure, evalDist_pure, lintegral_dirac]
      exact hmono s' m.le_succ
    | none =>
      by_cases hb : (H.view s').enncard + ↑(m + 1) ≤ (H.view s).enncard + n
      · have hrec : ∀ u, Ψ m (H.record s' t u) = m * κ + Φ (H.record s' t u) := fun u ↦ by
          refine (hΨ _ _).trans ((ite_eq_left ?_).trans (add_comm _ _))
          rw [H.view_record _ _ _ h]
          refine (add_le_add (QueryCache.enncard_cacheQuery_le _ t u) le_rfl).trans
            (Eq.trans_le ?_ hb)
          push_cast
          ring
        rw [H.randomOracle_run_of_none h, Functor.map_map]
        simp only [hrec]
        rw [lintegral_id_evalDist_map_const_add _ (prEvent_true_eq_one _), hΨ, ite_eq_left hb]
        refine (add_le_add le_rfl (hstep s' t h ((add_le_add le_rfl ?_).trans hb))).trans_eq ?_
        · exact_mod_cast Nat.le_add_left 1 m
        · push_cast
          ring
      · rw [hΨ, ite_eq_right hb]
        exact le_top
  · rw [hΨ, ite_eq_left le_rfl]

/-- An event on the output and the final state on which the potential is at least `1` has
probability at most `Φ s + n * κ`, under the hypotheses of `lintegral_le_of_potential`. -/
theorem prEvent_le_of_potential (E : α × σ → Prop) (Φ : σ → ℝ≥0∞) (hE : ∀ z, E z → 1 ≤ Φ z.2)
    {κ : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ} (hn : IsTotalQueryBound oa n) (s : σ)
    (hstep : ∀ s' t, H.view s' t = none → (H.view s').enncard + 1 ≤ (H.view s).enncard + n →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (H.record s' t u)) <$> ($ᵗ spec.Range t)] ≤ Φ s' + κ) :
    Pr{let z ← (simulateQ H.randomOracle oa).run s}[E z] ≤ Φ s + n * κ :=
  (prEvent_le_lintegral_id_evalDist_map _ hE).trans (H.lintegral_le_of_potential Φ hn s hstep)

/-- **Two runs, one potential.** Run `oa` from `s` on `H`'s lazy random oracle, within the budget
of `lintegral_le_of_potential`, then `ob` on its output. If from every reachable end `z₁` of the
first run the second gives the event `E` probability at most `Φ z₁.2 + ε`, then `E` has
probability at most `Φ s + n * κ + ε`. -/
theorem prEvent_bind_le_of_potential {β γ : Type} (oa : OracleComp spec β)
    (ob : β → OracleComp spec γ) (s : σ) (E : γ × σ → Prop) (Φ : σ → ℝ≥0∞) {κ ε : ℝ≥0∞} {n : ℕ}
    (hn : IsTotalQueryBound oa n)
    (hstep : ∀ s' t, H.view s' t = none → (H.view s').enncard + 1 ≤ (H.view s).enncard + n →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (H.record s' t u)) <$> ($ᵗ spec.Range t)] ≤ Φ s' + κ)
    (hsecond : ∀ z₁ ∈ support ((simulateQ H.randomOracle oa).run s),
      Pr{let z₂ ← (simulateQ H.randomOracle (ob z₁.1)).run z₁.2}[E z₂] ≤ Φ z₁.2 + ε) :
    Pr{let z ← (simulateQ H.randomOracle (oa >>= ob)).run s}[E z] ≤ Φ s + n * κ + ε := by
  rw [simulateQ_bind, StateT.run_bind, prEvent_bind_eq_lintegral_id_evalDist_map]
  refine (lintegral_id_evalDist_map_mono_of_mem_support _ (g := fun z₁ ↦ Φ z₁.2 + ε)
    hsecond).trans ?_
  rw [lintegral_id_evalDist_map_add _ (fun z₁ : β × σ ↦ Φ z₁.2) fun _ ↦ ε]
  exact add_le_add (H.lintegral_le_of_potential Φ hn s hstep)
    (lintegral_id_evalDist_map_le_of_le _ fun _ ↦ le_rfl)

omit [∀ t, SampleableType (spec.Range t)] in
/-- A fresh query and at most `n - 1` more add at most `n` entries to the cache. -/
private theorem enncard_view_record_add_le {s : σ} {t : spec.Domain} (h : H.view s t = none)
    (u : spec.Range t) {n : ℕ} (hn : 0 < n) :
    (H.view (H.record s t u)).enncard + (n - 1 : ℕ) ≤ (H.view s).enncard + n := by
  rw [H.view_record _ _ _ h]
  calc _ ≤ (H.view s).enncard + 1 + (n - 1 : ℕ) :=
        add_le_add (QueryCache.enncard_cacheQuery_le _ t u) le_rfl
    _ = _ := by rw [add_assoc, add_comm (1 : ℝ≥0∞), ← Nat.cast_add_one, Nat.sub_add_cancel hn]

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
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hz
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
/-- A state whose fresh query's record has its log the cache's has its log the cache's. -/
theorem IsFreshLog.of_record {s : spec.QueryCache × spec.QueryLog} {t : spec.Domain}
    (ht : s.1 t = none) {u : spec.Range t} (h : IsFreshLog (freshLog.record s t u)) :
    IsFreshLog s := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  simp only [freshLog_record, List.map_append, List.map_cons, List.map_nil] at h₁ h₂ h₃
  have hne : ∀ e ∈ s.2, e.1 ≠ t := fun e he het ↦
    (List.nodup_append.mp h₃).2.2 _ (List.mem_map_of_mem he) t (by simp) het
  refine ⟨fun e he ↦ ?_, fun t' u' ht' ↦ ?_, (List.nodup_append.mp h₃).1⟩
  · have := h₁ e (List.mem_append_left _ he)
    rwa [QueryCache.cacheQuery_of_ne _ _ (hne e he)] at this
  · have htt : t' ≠ t := fun h ↦ by subst h; rw [ht] at ht'; cases ht'
    have := h₂ t' u' (by rwa [QueryCache.cacheQuery_of_ne _ _ htt])
    rcases List.mem_append.mp this with h | h
    · exact h
    · obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp (List.mem_singleton.mp h)
      exact absurd rfl htt

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
    z.2.2 = s.2 ++ (List.dedupKeys z.1.2).filter (fun e ↦ (s.1 e.1).isNone) ∧
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
    rw [hq, run_simulateQ_query_bind, mem_support_bind_iff] at hz
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
      · simp only [Prod.map_snd, QueryLog.dedupKeys_cons, h, Option.isNone_some, List.filter_cons,
          Bool.false_eq_true, ↓reduceIte, List.filter_filter, h₁]
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
      · simp only [Prod.map_snd, QueryLog.dedupKeys_cons, h, Option.isNone_none, List.filter_cons,
          ↓reduceIte, List.filter_filter, h₁, freshLog_record, List.append_assoc,
          List.singleton_append]
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

end

end LeanerVM.Protocol
