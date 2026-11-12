/-
  LeanerVM.Protocol.ToVCVio.RandomOracleReplay

  A run of the lazy random oracle is the computation evaluated at any answer function that agrees
  with the run's final cache. Candidate for VCVio.
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# A lazy random oracle's run, replayed from its cache

VCVio's `exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support` says that an output of the lazy
random oracle from a cache `c₀` is `evalWithAnswerFn f oa` for *some* answer function `f` agreeing
with `c₀`. `evalWithAnswerFn_eq_of_mem_support_randomOracle` names one: every answer function
agreeing with the run's *final* cache, which extends `c₀`, evaluates the computation to the run's
output.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec

@[expose] public section

/-- **A lazy random oracle's run, replayed from its cache**: a run of `oa` against the lazy random
oracle from the cache `c₀`, ending at `(x, c)`, extends the cache, and every answer function that
agrees with `c` evaluates `oa` to `x`. -/
theorem evalWithAnswerFn_eq_of_mem_support_randomOracle {ι α : Type} [DecidableEq ι]
    {spec : OracleSpec ι} [∀ t, SampleableType (spec.Range t)] (oa : OracleComp spec α)
    (c₀ : spec.QueryCache) {z : α × spec.QueryCache}
    (hz : z ∈ support ((simulateQ spec.randomOracle oa).run c₀)) (f : QueryImpl spec Id)
    (hf : z.2.AgreesWithFn f) :
    c₀ ≤ z.2 ∧ evalWithAnswerFn f oa = z.1 := by
  induction oa using OracleComp.inductionOn generalizing c₀ with
  | pure a =>
    obtain rfl : z = (a, c₀) := by simpa using hz
    exact ⟨le_rfl, rfl⟩
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    have hstep : c₀ ≤ p.2 ∧ p.2 t = some p.1 := by
      cases h : c₀ t with
      | some u =>
        rw [QueryImpl.withCaching_run_some _ h, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact ⟨le_rfl, h⟩
      | none =>
        rw [QueryImpl.withCaching_run_none _ h, support_map] at hp
        obtain ⟨u, -, rfl⟩ := hp
        exact ⟨QueryCache.le_cacheQuery _ h, QueryCache.cacheQuery_self _ _ _⟩
    obtain ⟨hle, hrun⟩ := ih p.1 p.2 hz
    refine ⟨hstep.1.trans hle, ?_⟩
    have hq : evalWithAnswerFn f (liftM (spec.query t)) = p.1 := by
      rw [evalWithAnswerFn, simulateQ_spec_query]
      exact hf (hle hstep.2)
    rw [evalWithAnswerFn_bind, hq]
    exact hrun

end

end LeanerVM.Protocol
