import XmssSecurity.Proof.Seeded.Erasure
import XmssSecurity.Proof.Seeded.AdaptiveSeedGuessing
import XmssSecurity.Proof.ExpectedQueryCount
import XmssSecurity.Proof.ExpectedTail
import XmssSecurity.Proof.QueryCounting

/-!
# Expected counts through the bridge's hops

The bridge moves the real game to the model's by hops that are equalities in distribution of
whole runs, erasures of known queries, and seed guesses. An expected count of selected calls
(`expectedSimulatedQueryCount`) is the mean of the count `QueryCounting.counted` returns
(`tsum_counted_eq_expectedSimulatedQueryCount`), so the equalities carry it as they carry any
output; an erasure only drops calls (`Erases.expectedSimulatedQueryCount_le`); and a seed guess
changes each tail probability `Pr[t < count]` by at most the guess bound, `q` tails for a count
bounded by `q` calls (`tsum_counted_random_cache_change_le`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem tsum_counted_run_eq_expectedSimulatedQueryCount {α : Type}
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    ∑' r, Pr{let x ← ((simulateQ romImpl (QueryCounting.counted predicate computation)).run
        cache)}[x = r] * (r.1.2 : ℝ≥0∞) =
      expectedSimulatedQueryCount romImpl predicate computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      have hrun : (simulateQ romImpl (QueryCounting.counted predicate (pure value))).run cache =
          pure ((value, 0), cache) := rfl
      rw [hrun, OracleComp.tsum_prEvent_pure_mul]
      simp
  | query_bind input next ih =>
      rw [expectedSimulatedQueryCount_query_bind, QueryCounting.counted_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
        StateT.run_pure]
      rw [OracleComp.tsum_prEvent_bind_mul]
      simp only [OracleComp.tsum_prEvent_bind_mul, OracleComp.tsum_prEvent_pure_mul,
        Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      calc
        _ = ∑' x, Pr{let y ← (romImpl input).run cache}[y = x] *
              ((if predicate input then 1 else 0) +
                expectedSimulatedQueryCount romImpl predicate (next x.1) x.2) := by
          refine tsum_congr fun x => ?_
          congr 1
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul,
            ih]
        _ = _ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul]

theorem tsum_counted_eq_expectedSimulatedQueryCount {α : Type}
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    ∑' r, Pr{let x ← ((simulateQ romImpl (QueryCounting.counted predicate computation)).run'
        cache)}[x = r] * (r.2 : ℝ≥0∞) =
      expectedSimulatedQueryCount romImpl predicate computation cache := by
  rw [← tsum_counted_run_eq_expectedSimulatedQueryCount, StateT.run'_eq,
    OracleComp.tsum_prEvent_map_mul]

/-- The selected calls are hash calls, so the count is at most a hash-call bound. -/
theorem counted_le_of_hashQueryBound {α : Type}
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (hpredicate : ∀ input, predicate input → input matches .inr _)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound computation cache q)
    (r : α × Nat)
    (hr : r ∈ support ((simulateQ romImpl (QueryCounting.counted predicate computation)).run'
      cache)) : r.2 ≤ q := by
  induction computation using OracleComp.inductionOn generalizing cache q r with
  | pure value =>
      rw [QueryCounting.counted_pure] at hr
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, support_pure,
        Set.mem_singleton_iff] at hr
      subst hr
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [QueryCounting.counted_query_bind] at hr
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run'_eq,
        StateT.run_bind, StateT.run_pure, map_bind, map_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨step, hstep, inner, hinner, rfl⟩ := hr
      have hq := hashQueryBound_query_bind input next cache q hbound step hstep
      have hrec := ih step.1 step.2 _ hq.2 inner.1 (by
        simp only [StateT.run'_eq, support_map]
        exact ⟨inner, hinner, rfl⟩)
      refine (Nat.add_le_add ?_ hrec).trans_eq (Nat.add_sub_cancel' hq.1)
      rcases input with n | x
      · have hp : ¬predicate (.inl n) := fun h => by simpa using hpredicate _ h
        simp [hp]
      · by_cases hp : predicate (.inr x) <;> simp [hp]

/-- The mean of a bounded natural component is the sum of its first `n` tail probabilities. -/
theorem tsum_snd_eq_sum_lt {α : Type} (mx : ProbComp (α × Nat)) (n : Nat)
    (hcount : ∀ r ∈ support mx, r.2 ≤ n) :
    ∑' r, Pr{let x ← mx}[x = r] * (r.2 : ℝ≥0∞) =
      ∑ t ∈ Finset.range n, Pr{let x ← mx}[t < x.2] := by
  rw [tsum_prEvent_mul_natCast_eq_tsum_lt (f := Prod.snd), tsum_eq_sum (s := Finset.range n)]
  intro t ht
  have hnt : n ≤ t := Nat.le_of_not_lt (by simpa using ht)
  apply prEvent_eq_zero_of_forall_mem_support
  intro r hr hlt
  have := hcount r hr
  omega

/-- The selected calls of a counted continuation are at most the whole run's hash calls. -/
theorem snd_le_of_mem_support_bind_counted {α β : Type} (first : OracleComp OracleWorld β)
    (predicate : β → OracleWorld.Domain → Prop) [∀ b, DecidablePred (predicate b)]
    (hpredicate : ∀ b input, predicate b input → input matches .inr _)
    (rest : β → OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (first >>= rest) cache q) (r : α × Nat)
    (hr : r ∈ support ((simulateQ romImpl (first >>= fun b =>
      QueryCounting.counted (predicate b) (rest b))).run' cache)) : r.2 ≤ q := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map, Set.mem_image] at hr
  obtain ⟨final, hfinal, rfl⟩ := hr
  rw [mem_support_bind_iff] at hfinal
  obtain ⟨head, hhead, htail⟩ := hfinal
  rw [← countHashQueries_run_forget, support_map] at hhead
  obtain ⟨counted, hcounted, rfl⟩ := hhead
  have hsplit := hashQueryBound_bind first rest cache q hbound counted hcounted
  have hle := counted_le_of_hashQueryBound (predicate counted.1.1) (hpredicate counted.1.1)
    (rest counted.1.1) counted.2 _ hsplit.2 final.1 (by
      rw [StateT.run'_eq, support_map]
      exact ⟨final, htail, rfl⟩)
  exact hle.trans (Nat.sub_le _ _)

theorem hashQueryBound_bind_counted_iff {α β : Type} (first : OracleComp OracleWorld β)
    (predicate : β → OracleWorld.Domain → Prop) [∀ b, DecidablePred (predicate b)]
    (rest : β → OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat) :
    HashQueryBound (first >>= fun b => QueryCounting.counted (predicate b) (rest b)) cache q ↔
      HashQueryBound (first >>= rest) cache q := by
  refine hashQueryBound_iff_of_map_eq (f := Prod.fst) ?_ cache q
  rw [map_bind]
  exact bind_congr fun b => QueryCounting.counted_forget _ _

open scoped Classical in
/-- A seed guess the other way: the run from the fixed cache is at most the runs from the seeded
caches plus the guess bound. -/
theorem probEvent_random_cache_change_le_rev {hit : HashInput → MasterSeed → Prop}
    (hhit : GuessBound hit) {α : Type} (computation : OracleComp OracleWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutside (fun input => hit input seed) (initial seed) cache)
    (q : Nat) (hbound : HashQueryBound computation cache q) (event : α → Prop) :
    Pr{let x ← (simulateQ romImpl computation).run' cache}[event x] ≤
      Pr{let x ← (sampleMasterSeed >>= fun seed =>
          (simulateQ romImpl computation).run' (initial seed))}[event x] +
        q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  let stopped := fun seed =>
    (simulateQ romImpl (stopBefore (hashBad (fun input => hit input seed)) computation)).run' cache
  calc
    _ = Pr{let x ← (sampleMasterSeed >>= fun _ =>
          (simulateQ romImpl computation).run' cache)}[event x] := by
      rw [OracleComp.prEvent_bind_eq_tsum, ENNReal.tsum_mul_right,
        OracleComp.tsum_prEvent_eq_one, one_mul]
    _ ≤ Pr{let x ← (sampleMasterSeed >>= fun seed =>
          (simulateQ romImpl computation).run' (initial seed))}[event x] +
        Pr{let x ← sampleMasterSeed >>= stopped}[x = none] := by
      simp only [OracleComp.prEvent_bind_eq_tsum, ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun seed => (mul_le_mul' le_rfl ?_).trans_eq (mul_add ..)
      refine (probEvent_le_stopBefore_add_failure (hashBad fun input => hit input seed)
        computation cache event).trans (add_le_add ?_ le_rfl)
      rw [← run'_stopBefore_eq (fun input => hit input seed) computation (initial seed) cache
        (hagree seed)]
      exact probEvent_stopBefore_le _ computation (initial seed) event
    _ ≤ _ := add_le_add le_rfl (probOutput_stopBefore_seed_le hhit computation cache q hbound)

/-- **Means through a seed guess.** A natural component bounded by `n` on the run from the fixed
cache has mean there at most its mean from the seeded caches plus `q` guesses for each of `n` tails. -/
theorem tsum_snd_random_cache_change_le {hit : HashInput → MasterSeed → Prop}
    (hhit : GuessBound hit) {α : Type} (computation : OracleComp OracleWorld (α × Nat))
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutside (fun input => hit input seed) (initial seed) cache)
    (q : Nat) (hbound : HashQueryBound computation cache q) (n : Nat)
    (hcount : ∀ r ∈ support ((simulateQ romImpl computation).run' cache), r.2 ≤ n) :
    ∑' r, Pr{let x ← ((simulateQ romImpl computation).run' cache)}[x = r] * (r.2 : ℝ≥0∞) ≤
      ∑' seed, Pr{let x ← sampleMasterSeed}[x = seed] *
          ∑' r, Pr{let x ← ((simulateQ romImpl computation).run' (initial seed))}[x = r] *
            (r.2 : ℝ≥0∞) +
        (n * q : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  rw [tsum_snd_eq_sum_lt _ n hcount]
  calc
    _ ≤ ∑ t ∈ Finset.range n, (Pr{let x ← (sampleMasterSeed >>= fun seed =>
          (simulateQ romImpl computation).run' (initial seed))}[t < x.2] +
            q / ((2 ^ 256 : Nat) : ℝ≥0∞)) :=
      Finset.sum_le_sum fun t _ => probEvent_random_cache_change_le_rev hhit computation initial
        cache hagree q hbound (fun x => t < x.2)
    _ ≤ ∑' t : ℕ, Pr{let x ← (sampleMasterSeed >>= fun seed =>
          (simulateQ romImpl computation).run' (initial seed))}[t < x.2] +
        (n * q : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
      rw [Finset.sum_add_distrib]
      gcongr
      · exact ENNReal.sum_le_tsum _
      · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_div_assoc]
        push_cast
        exact le_rfl
    _ = _ := by
      rw [← tsum_prEvent_mul_natCast_eq_tsum_lt (f := Prod.snd), OracleComp.tsum_prEvent_bind_mul]

/-- **Counts through a seed guess**, for a fixed predicate. -/
theorem tsum_counted_random_cache_change_le {hit : HashInput → MasterSeed → Prop}
    (hhit : GuessBound hit) {α : Type}
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (hpredicate : ∀ input, predicate input → input matches .inr _)
    (computation : OracleComp OracleWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutside (fun input => hit input seed) (initial seed) cache)
    (q : Nat) (hbound : HashQueryBound computation cache q) :
    expectedSimulatedQueryCount romImpl predicate computation cache ≤
      ∑' seed, Pr{let x ← sampleMasterSeed}[x = seed] *
          expectedSimulatedQueryCount romImpl predicate computation (initial seed) +
        (q * q : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hcounted : HashQueryBound (QueryCounting.counted predicate computation) cache q :=
    (hashQueryBound_iff_of_map_eq (QueryCounting.counted_forget predicate computation) cache q).mpr
      hbound
  have h := tsum_snd_random_cache_change_le hhit (QueryCounting.counted predicate computation)
    initial cache hagree q hcounted q
    (counted_le_of_hashQueryBound predicate hpredicate computation cache q hbound)
  simp only [tsum_counted_eq_expectedSimulatedQueryCount] at h
  exact h

/-- An erasure only drops calls. -/
theorem Erases.expectedSimulatedQueryCount_le {α : Type} {known : QueryCache HashSpec}
    {left right : OracleComp OracleWorld α} (h : Erases (worldKnown known) left right)
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (cache : QueryCache HashSpec) (hcache : known ≤ cache) :
    expectedSimulatedQueryCount romImpl predicate right cache ≤
      expectedSimulatedQueryCount romImpl predicate left cache := by
  induction h generalizing cache with
  | pure value => exact le_rfl
  | query input left right _ ih =>
      rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind]
      refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun result => ?_)
      by_cases hresult : result ∈ support ((romImpl input).run cache)
      · exact mul_le_mul' le_rfl (ih result.1 result.2
          (romImpl_preserves_known known cache hcache input result hresult))
      · rw [(prEvent_eq_zero_of_not_mem_support _) hresult, zero_mul, zero_mul]
  | skip input answer hknown next right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          have hrun : (romImpl (.inr input)).run cache = Pure.pure (answer, cache) :=
            QueryImpl.withCaching_run_some _ hc
          rw [expectedSimulatedQueryCount_query_bind, hrun, OracleComp.tsum_prEvent_pure_mul]
          exact (ih cache hcache).trans le_add_self
  | cached input answer hknown left right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          have hrun : (romImpl (.inr input)).run cache = Pure.pure (answer, cache) :=
            QueryImpl.withCaching_run_some _ hc
          rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind, hrun,
            OracleComp.tsum_prEvent_pure_mul, OracleComp.tsum_prEvent_pure_mul]
          exact add_le_add le_rfl (ih cache hcache)
  | trans _ _ first second => exact (second cache hcache).trans (first cache hcache)

end XmssSecurity.Seeded
