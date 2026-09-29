/-
  LeanerVM.Protocol.ToArkLib.GuardedVerdict

  What a run says about a verifier that is a check followed by a verdict.
  Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
public import ArkLib.OracleReduction.Security.RoundByRound

/-!
# The verdict of a guarded verifier

ArkLib calls a verifier guarded when it is a Boolean check on the statement and the transcript
followed by a deterministic verdict: it outputs the verdict when the check passes and rejects
otherwise (`Verifier.GuardedForm`). Two facts follow for every such verifier, whatever its
schedule, and they are what a component's two proofs start from.

* `Verifier.GuardedForm.of_probEvent_pos`: if the verifier can output a statement satisfying a
  predicate, then the check passes and the verdict satisfies it. This is the last obligation of
  a knowledge state function.
* `Reduction.mem_support_run_of_guarded`: every outcome of a run is a transcript and output of
  the prover, together with the verdict when the check passes on that transcript, and a
  rejection otherwise. Perfect completeness is then a statement about the prover's runs.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

public section

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n}

/-- If a guarded verifier can output a statement satisfying `P`, its check passes and its
verdict satisfies `P`. -/
theorem Verifier.GuardedForm.of_probEvent_pos {V : Verifier oSpec StmtIn StmtOut pSpec}
    (G : V.GuardedForm) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (stmt : StmtIn) (tr : pSpec.FullTranscript)
    (P : StmtOut → Prop)
    (h : Pr[P | OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] > 0) :
    G.check stmt tr = true ∧ P (G.out stmt tr) := by
  have hv : V.run stmt tr = if G.check stmt tr then pure (G.out stmt tr) else failure :=
    G.verify_eq stmt tr
  rw [hv] at h
  by_cases hc : G.check stmt tr = true
  · refine ⟨hc, ?_⟩
    rw [if_pos hc] at h
    change Pr[_ | OptionT.mk (do let st ← init; (simulateQ impl (OptionT.run
      (pure (G.out stmt tr)))).run' st)] > 0 at h
    rw [OptionT.run_pure, simulateQ_pure] at h
    obtain ⟨z, hz, hp⟩ := probEvent_pos_iff.mp h
    simp only [StateT.run'_eq, StateT.run_pure, map_pure, bind_pure_comp,
      OptionT.mem_support_iff, OptionT.run_mk, support_map, Set.mem_image, Option.some.injEq,
      exists_and_right] at hz
    obtain ⟨_, rfl⟩ := hz
    exact hp
  · exfalso
    rw [if_neg hc] at h
    change Pr[_ | OptionT.mk (do let st ← init; (simulateQ impl (OptionT.run
      (failure : OptionT (OracleComp oSpec) StmtOut))).run' st)] > 0 at h
    rw [OptionT.run_failure, simulateQ_pure] at h
    obtain ⟨z, hz, -⟩ := probEvent_pos_iff.mp h
    simp only [StateT.run'_eq, StateT.run_pure, map_pure, bind_pure_comp,
      OptionT.mem_support_iff, OptionT.run_mk, support_map, Set.mem_image, reduceCtorEq,
      and_false, exists_false] at hz

/-- Every outcome of a run with a guarded verifier: a run of the prover, then the verdict if
the check passes on its transcript, a rejection otherwise. -/
theorem Reduction.mem_support_run_of_guarded
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (G : reduction.verifier.GuardedForm) (stmt : StmtIn) (wit : WitIn)
    {y : Option ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut)}
    (hy : y ∈ support (reduction.run stmt wit).run) :
    ∃ pr ∈ support (reduction.prover.run stmt wit),
      y = if G.check stmt pr.1 then some (pr, G.out stmt pr.1) else none := by
  unfold Reduction.run at hy
  simp only [OptionT.run_bind, Option.elimM] at hy
  rw [mem_support_bind_iff] at hy
  obtain ⟨prOpt, hprover, hy⟩ := hy
  cases prOpt with
  | none =>
    simp only [ChallengeIdx, Challenge, OptionT.run_monadLift, monadLift_self, support_map,
      Set.mem_image, reduceCtorEq, and_false, exists_false] at hprover
  | some pr =>
    have hpr : pr ∈ support (reduction.prover.run stmt wit) := by
      simpa only [ChallengeIdx, Challenge, OptionT.run_monadLift, monadLift_self, support_map,
        Set.mem_image, Option.some.injEq, exists_eq_right] using hprover
    refine ⟨pr, hpr, ?_⟩
    simp only [Option.elim_some] at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨sOpt, hs, hy⟩ := hy
    rw [Verifier.run, show reduction.verifier.verify stmt pr.1 = _ from G.verify_eq stmt pr.1]
      at hs
    by_cases hc : G.check stmt pr.1 = true
    · simp only [ChallengeIdx, Challenge, hc, ↓reduceIte, OptionT.run_pure, liftM_pure,
        support_pure, Set.mem_singleton_iff] at hs
      subst hs
      simp only [ChallengeIdx, Challenge, OptionT.run_pure, Option.elim_some, Option.getM_some,
        pure_bind, support_pure, Set.mem_singleton_iff, hc, ↓reduceIte] at hy ⊢
      exact hy
    · simp only [ChallengeIdx, Challenge, hc, Bool.false_eq_true, ↓reduceIte,
        OptionT.run_failure, liftM_pure, OptionT.run_pure, support_pure,
        Set.mem_singleton_iff] at hs
      subst hs
      simp only [ChallengeIdx, Challenge, OptionT.run_pure, Option.elim_some, Option.getM_none,
        OptionT.run_failure, pure_bind, Option.elim_none, support_pure, Set.mem_singleton_iff,
        hc, Bool.false_eq_true, ↓reduceIte] at hy ⊢
      exact hy

end
end LeanerVM.Protocol
