import Sphincs.BridgeEager

/-! **The lazy random oracle with its cache, as an eager table.** A computation whose hash queries
are all short, run on the lazy random oracle from a cache, has the law of a uniformly sampled table
read through the cache (`extend`), the final cache being the initial one with every queried input
recorded at its answer (`fixedRec`). Under a fixed answer function a computation without private
draws is deterministic, and its final cache is the initial one overwritten by its own record:
two such computations commute. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.MultiEager

open Completeness Internalize Short Eager SeedCoupling

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Private draws are forwarded; a hash query reads a fixed answer function and records it. -/
noncomputable def fixedRec (answers : HashInput → HashOutput) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp)
  | .inl draw => (liftM (unifSpec.query draw) : StateT (QueryCache HashSpec) ProbComp (Fin (draw + 1)))
  | .inr input => modifyGet fun cache => (answers input, cache.cacheQuery input (answers input))

theorem fixedRec_inl_run (answers : HashInput → HashOutput) (draw : ℕ) (cache : QueryCache HashSpec) :
    (fixedRec answers (.inl draw)).run cache =
      (fun answer => (answer, cache)) <$> (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1))) := by
  simp [fixedRec]

theorem fixedRec_inr_run (answers : HashInput → HashOutput) (input : HashInput) (cache : QueryCache HashSpec) :
    (fixedRec answers (.inr input)).run cache = pure (answers input, cache.cacheQuery input (answers input)) := by
  simp [fixedRec]

theorem cacheQuery_of_eq (cache : QueryCache HashSpec) {input : HashInput} {answer : HashOutput}
    (h : cache input = some answer) : cache.cacheQuery input answer = cache := by
  ext query
  by_cases hq : query = input
  · subst hq
    rw [QueryCache.cacheQuery_self, h]
  · rw [QueryCache.cacheQuery_of_ne _ _ hq]

/-- **Lazy sampling with its final cache equals eager table sampling with recording**, from any
cache. -/
theorem evalDist_romImpl_run_eq_table {α : Type} (oa : OracleComp OracleWorld α) (h : OnlyW oa)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl oa).run cache =ᵈ
      (do let table ← $ᵗ Table; (simulateQ (fixedRec (extend cache table)) oa).run cache) := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | query_bind input next ih =>
      rw [OnlyW, isQueryBoundP_query_bind_iff] at h
      have hnext : ∀ answer, OnlyW (next answer) := fun answer => by
        have := h.2 answer
        split at this <;> simpa [OnlyW] using this
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      cases input with
      | inl draw =>
          change (unifFwdImpl HashSpec draw).run cache >>= _ =ᵈ _
          rw [show (unifFwdImpl HashSpec draw).run cache =
              (fun answer => (answer, cache)) <$> (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1))) by
            simpa using unifFwdImpl.simulateQ_run (hashSpec := HashSpec)
              (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1))) cache]
          simp_rw [fixedRec_inl_run]
          refine (evalDist_map_bind' (liftM (unifSpec.query draw) : ProbComp _)
            (fun answer => (answer, cache)) _).trans ?_
          refine EvalDistEq.trans (my := (liftM (unifSpec.query draw) : ProbComp _) >>= fun answer =>
            ($ᵗ Table) >>= fun table => (simulateQ (fixedRec (extend cache table)) (next answer)).run cache) ?_ ?_
          · exact EvalDistEq.bind_right _ fun answer => ih answer (hnext answer) cache
          · refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
            refine EvalDistEq.bind_right _ fun table => ?_
            rw [bind_map_left]
      | inr bytes =>
          have hshort : IsShort bytes := by
            rcases h.1 with hnot | hzero
            · simpa [LongQuery] using hnot
            · omega
          change (randomOracle (spec := HashSpec) bytes).run cache >>= _ =ᵈ _
          simp_rw [fixedRec_inr_run, pure_bind]
          cases hc : cache bytes with
          | some answer =>
              rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
              have hext : ∀ table, extend cache table bytes = answer := fun table => by
                simp [extend, hc]
              simp_rw [hext, cacheQuery_of_eq cache hc]
              exact ih answer (hnext answer) cache
          | none =>
              rw [QueryImpl.withCaching_run_none _ hc]
              refine (evalDist_map_bind' (uniformSampleImpl (spec := HashSpec) bytes)
                (fun answer => (answer, cache.cacheQuery bytes answer)) _).trans ?_
              let ψ : Table → ProbComp (α × QueryCache HashSpec) := fun table =>
                (simulateQ (fixedRec (extend cache table)) (next (extend cache table bytes))).run
                  (cache.cacheQuery bytes (extend cache table bytes))
              have hupdate : ∀ (answer : HashOutput) (table : Table),
                  (simulateQ (fixedRec (extend (cache.cacheQuery bytes answer) table)) (next answer)).run
                      (cache.cacheQuery bytes answer) =
                    ψ (Function.update table ⟨bytes, hshort⟩ answer) := by
                intro answer table
                have hval : extend cache (Function.update table ⟨bytes, hshort⟩ answer) bytes = answer := by
                  simp [extend, hc, hshort]
                simp only [ψ, hval, extend_cacheQuery cache table hshort hc answer]
              refine EvalDistEq.trans (my := (uniformSampleImpl (spec := HashSpec) bytes : ProbComp HashOutput) >>=
                fun answer => ($ᵗ Table) >>= fun table => ψ (Function.update table ⟨bytes, hshort⟩ answer)) ?_ ?_
              · refine EvalDistEq.bind_right _ (fun answer => ?_)
                refine (ih answer (hnext answer) (cache.cacheQuery bytes answer)).trans ?_
                simp only [hupdate, EvalDistEq.refl]
              · change ($ᵗ HashOutput : ProbComp HashOutput) >>= (fun answer =>
                  ($ᵗ Table) >>= fun table => ψ (Function.update table ⟨bytes, hshort⟩ answer)) =ᵈ
                    ($ᵗ Table) >>= ψ
                have hassoc : (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
                      ($ᵗ Table) >>= fun table => ψ (Function.update table ⟨bytes, hshort⟩ answer)) =
                    (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer => ($ᵗ Table) >>=
                      fun table => pure (Function.update table ⟨bytes, hshort⟩ answer)) >>= ψ := by
                  simp only [bind_assoc, pure_bind]
                rw [hassoc]
                exact (uniformSample_bind_update_evalDistEq (D := ShortIn) (R := HashOutput)
                  ⟨bytes, hshort⟩).bind_left ψ

/-! ### Computations without private draws under a fixed answer function -/

section Fixed

variable (answers : HashInput → HashOutput)

/-- The value of a hash computation under the answers. -/
def valF {α : Type} (oa : OracleComp HashSpec α) : α :=
  OracleComp.construct (C := fun _ => α) (fun a => a) (fun input _ next => next (answers input)) oa

/-- The number of hash calls of a hash computation under the answers. -/
def callsF {α : Type} (oa : OracleComp HashSpec α) : ℕ :=
  OracleComp.construct (C := fun _ => ℕ) (fun _ => 0) (fun input _ next => 1 + next (answers input)) oa

/-- The cache after a hash computation under the answers, from a given cache. -/
def recF {α : Type} (oa : OracleComp HashSpec α) : QueryCache HashSpec → QueryCache HashSpec :=
  OracleComp.construct (C := fun _ => QueryCache HashSpec → QueryCache HashSpec) (fun _ cache => cache)
    (fun input _ next cache => next (answers input) (cache.cacheQuery input (answers input))) oa

theorem valF_query_bind {α : Type} (input : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    valF answers (liftM (HashSpec.query input) >>= next) = valF answers (next (answers input)) := rfl

theorem callsF_query_bind {α : Type} (input : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    callsF answers (liftM (HashSpec.query input) >>= next) = 1 + callsF answers (next (answers input)) := rfl

theorem recF_query_bind {α : Type} (input : HashInput) (next : HashOutput → OracleComp HashSpec α)
    (cache : QueryCache HashSpec) :
    recF answers (liftM (HashSpec.query input) >>= next) cache =
      recF answers (next (answers input)) (cache.cacheQuery input (answers input)) := rfl

/-- **Under fixed answers a hash computation is deterministic**: its counted run gives its value,
its number of calls and its record. -/
theorem fixedRec_run_liftM {α : Type} (oa : OracleComp HashSpec α) (cache : QueryCache HashSpec) :
    (simulateQ (fixedRec answers) (countHashQueries (liftM oa : OracleComp OracleWorld α))).run cache =
      pure ((valF answers oa, callsF answers oa), recF answers oa cache) := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure value => rfl
  | query_bind input next ih =>
      rw [liftM_bind]
      change (simulateQ (fixedRec answers) (countHashQueries
        (liftM (OracleWorld.query (.inr input)) >>= fun answer => liftM (next answer)))).run cache = _
      rw [countHashQueries_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, fixedRec_inr_run,
        pure_bind, ih, StateT.run_pure]
      rfl

theorem valF_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    valF answers (oa >>= f) = valF answers (f (valF answers oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [bind_assoc, valF_query_bind, valF_query_bind, ih]

theorem callsF_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    callsF answers (oa >>= f) = callsF answers oa + callsF answers (f (valF answers oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure value => simp [callsF, valF]
  | query_bind input next ih =>
      rw [bind_assoc, callsF_query_bind, callsF_query_bind, ih, valF_query_bind]
      omega

theorem recF_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β)
    (cache : QueryCache HashSpec) :
    recF answers (oa >>= f) cache = recF answers (f (valF answers oa)) (recF answers oa cache) := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure value => rfl
  | query_bind input next ih =>
      rw [bind_assoc, recF_query_bind, recF_query_bind, ih, valF_query_bind]

/-- The record sets the queried inputs to their answers and keeps the rest of the cache. -/
theorem recF_apply {α : Type} (oa : OracleComp HashSpec α) (cache : QueryCache HashSpec) (input : HashInput) :
    recF answers oa cache input =
      if recF answers oa ∅ input = none then cache input else some (answers input) := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure value => simp [recF]
  | query_bind query next ih =>
      rw [recF_query_bind, recF_query_bind, ih (answers query) (cache.cacheQuery query (answers query)),
        ih (answers query) ((∅ : QueryCache HashSpec).cacheQuery query (answers query))]
      by_cases hq : input = query
      · subst hq
        simp
      · simp [QueryCache.cacheQuery_of_ne _ _ hq]

/-- **Two hash computations commute** under fixed answers: their records overwrite disjointly. -/
theorem recF_comm {α β : Type} (oa : OracleComp HashSpec α) (ob : OracleComp HashSpec β)
    (cache : QueryCache HashSpec) :
    recF answers oa (recF answers ob cache) = recF answers ob (recF answers oa cache) := by
  refine QueryCache.ext fun input => ?_
  rw [recF_apply answers oa (recF answers ob cache), recF_apply answers ob cache,
    recF_apply answers ob (recF answers oa cache), recF_apply answers oa cache]
  split_ifs <;> rfl

end Fixed

end Sphincs.Security.MultiEager
