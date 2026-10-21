import XmssSecurity.Proof.MultiUser.Commute
import XmssSecurity.Proof.Seeded.HashTrace
import XmssSecurity.Proof.CappedExpectedFirstLane

/-!
# Hash traces

The multi-user counts are taken after the fact, on the list of hash inputs a run queried
(`Seeded.traceHashes`): a count of calls starting with a parameter is a count over the trace
(`counted_eq_traceHashes`), and the trace of a bind or of a sequence is the concatenation of the
traces of its parts (`traceHashes_bind`, `traceHashes_sequenceFin`). A trace taken after the fact may
count with a parameter generated later in the run, which a count taken during the run cannot.
-/

open OracleComp OracleSpec

namespace XmssSecurity.MultiUser

open Seeded

set_option backward.isDefEq.respectTransparency false

theorem traceHashes_bind {α β : Type} (computation : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) :
    traceHashes (computation >>= next) = (do
      let first ← traceHashes computation
      let second ← traceHashes (next first.1)
      pure (second.1, first.2 ++ second.2)) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [pure_bind, traceHashes_pure, List.nil_append, Prod.mk.eta, bind_pure]
  | query_bind input continuation ih =>
      simp only [bind_assoc, traceHashes_query_bind, ih, pure_bind]
      congr 1
      funext answer
      congr 1
      funext first
      congr 1
      funext second
      cases input <;> rfl

theorem traceHashes_forget {α : Type} (computation : OracleComp OracleWorld α) :
    Prod.fst <$> traceHashes computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [traceHashes_query_bind, map_bind, map_pure]
      congr 1
      funext answer
      conv_rhs => rw [← ih answer]
      rw [map_eq_bind_pure_comp]
      rfl

theorem traceHashes_map {α β : Type} (computation : OracleComp OracleWorld α) (f : α → β) :
    traceHashes (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> traceHashes computation := by
  rw [map_eq_bind_pure_comp, traceHashes_bind]
  simp only [Function.comp_apply, traceHashes_pure, pure_bind, List.append_nil,
    map_eq_bind_pure_comp]
  rfl

theorem traceHashes_lift_prob {α : Type} (computation : ProbComp α) :
    traceHashes (liftM computation : OracleComp OracleWorld α) =
      (fun value => (value, [])) <$> (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, traceHashes_pure, map_pure]
  | query_bind input next ih =>
      rw [liftM_bind]
      change traceHashes (liftM (OracleWorld.query (.inl input)) >>= _) = _
      simp only [traceHashes_query_bind, ih, map_bind, bind_pure_comp, Functor.map_map]
      rfl

/-- A count of calls attributable to a parameter is the count over the trace. -/
theorem counted_eq_traceHashes {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) :
    QueryCounting.counted (IsParameterQuery parameter) computation =
      (fun result => (result.1, result.2.countP fun input =>
        decide (IsParameterHashInput parameter input))) <$> traceHashes computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [QueryCounting.counted_query_bind, traceHashes_query_bind]
      simp only [ih, map_bind, map_pure, bind_map_left]
      congr 1
      funext answer
      congr 1
      funext result
      cases input with
      | inl n => simp [IsParameterQuery, prependHash]
      | inr x =>
          by_cases hx : IsParameterHashInput parameter x
          · simp [IsParameterQuery, prependHash, hx, Nat.add_comm]
          · simp [IsParameterQuery, prependHash, hx]

/-- The count of every hash call is the trace's length. -/
theorem countHashQueries_eq_traceHashes {α : Type} (computation : OracleComp OracleWorld α) :
    countHashQueries computation =
      (fun result => (result.1, result.2.length)) <$> traceHashes computation :=
  (traceHashes_length computation).symm

/-! ## Sequences -/

/-- The traces of a sequence's computations, in order. -/
def flatTrace {α : Type} : {n : Nat} → (Fin n → α × List HashInput) → List HashInput
  | 0, _ => []
  | _ + 1, parts => (parts 0).2 ++ flatTrace fun i => parts i.succ

theorem countP_flatTrace {α : Type} (p : HashInput → Bool) :
    ∀ {n : Nat} (parts : Fin n → α × List HashInput),
      (flatTrace parts).countP p = ∑ i, (parts i).2.countP p
  | 0, _ => rfl
  | n + 1, parts => by
      rw [flatTrace, List.countP_append, countP_flatTrace p (fun i => parts i.succ),
        Fin.sum_univ_succ]

theorem length_flatTrace {α : Type} :
    ∀ {n : Nat} (parts : Fin n → α × List HashInput),
      (flatTrace parts).length = ∑ i, (parts i).2.length
  | 0, _ => rfl
  | n + 1, parts => by
      rw [flatTrace, List.length_append, length_flatTrace (fun i => parts i.succ),
        Fin.sum_univ_succ]

theorem traceHashes_sequenceFin {α : Type} :
    ∀ {n : Nat} (computation : Fin n → OracleComp OracleWorld α),
      traceHashes (LeanXmss.Concrete.sequenceFin computation) =
        (fun parts => (fun i => (parts i).1, flatTrace parts)) <$>
          LeanXmss.Concrete.sequenceFin fun i => traceHashes (computation i)
  | 0, computation => by
      simp only [LeanXmss.Concrete.sequenceFin, traceHashes_pure, map_pure, flatTrace]
      congr 2
      funext i
      exact i.elim0
  | n + 1, computation => by
      simp only [LeanXmss.Concrete.sequenceFin, traceHashes_bind, traceHashes_pure,
        map_bind, map_pure, bind_assoc, pure_bind]
      congr 1
      funext head
      rw [traceHashes_sequenceFin (fun i => computation i.succ), bind_map_left]
      congr 1
      funext tail
      simp only [List.append_nil, flatTrace, Fin.cases_zero, Fin.cases_succ]
      congr 2
      funext i
      cases i using Fin.cases <;> rfl

/-! ## The cache of a run from the empty cache -/

/-- A run caches only inputs it queried. -/
theorem cache_mem_trace {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (result : (α × List HashInput) × QueryCache HashSpec)
    (hresult : result ∈ support (romRun (traceHashes computation) cache))
    (input : HashInput) (hinput : result.2 input ≠ none) :
    cache input ≠ none ∨ input ∈ result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [romRun, traceHashes_pure, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst hresult
      exact .inl hinput
  | query_bind query next ih =>
      rw [traceHashes_query_bind, romRun_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨answer, hanswer, hrest⟩ := hresult
      rw [romRun_bind, mem_support_bind_iff] at hrest
      obtain ⟨inner, hinner, hfinal⟩ := hrest
      simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
      subst hfinal
      rcases ih answer.1 answer.2 inner hinner hinput with hcached | hmem
      · cases query with
        | inl n =>
            rw [romImpl_uniform_run, support_map] at hanswer
            obtain ⟨sample, _, rfl⟩ := hanswer
            exact .inl hcached
        | inr x =>
            by_cases hx : input = x
            · subst hx
              exact .inr (List.mem_cons_self ..)
            · cases hc : cache x with
              | some value =>
                  rw [romImpl_hash_run_some x hc, support_pure, Set.mem_singleton_iff] at hanswer
                  subst hanswer
                  exact .inl hcached
              | none =>
                  rw [romImpl_hash_run_none x hc, support_map] at hanswer
                  obtain ⟨value, _, rfl⟩ := hanswer
                  left
                  simpa [QueryCache.cacheQuery, hx] using hcached
      · cases query with
        | inl n => exact .inr hmem
        | inr x => exact .inr (List.mem_cons_of_mem _ hmem)

end XmssSecurity.MultiUser
