/-
  LeanerVM.Protocol.ToArkLib.GuardedVerdict

  What a run says about a verifier that is a check followed by a verdict.
  Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.LogicStep
public import ArkLib.OracleReduction.Security.GuardedRoundByRound

/-!
# The verdict of a guarded verifier

ArkLib calls a verifier guarded when it is a Boolean check on the statement and the transcript
followed by a deterministic verdict: it outputs the verdict when the check passes and rejects
otherwise (`Verifier.GuardedForm`). Two facts follow for every such verifier, whatever its
schedule, and they are what a component's two proofs start from.

* ArkLib's `Verifier.GuardedForm.check_and_of_prEvent_pos`: if the verifier can output a
  statement satisfying a predicate, then the check passes and the verdict satisfies it. This is
  the last obligation of a knowledge state function.
* `Reduction.mem_support_run_of_guarded`: every outcome of a run is a transcript and output of
  the prover, together with the verdict when the check passes on that transcript, and a
  rejection otherwise (ArkLib's `Reduction.run_eq_of_guarded_verifier`, read on the support).
  ArkLib's `Reduction.perfectCompleteness_of_guarded_prover_support` makes perfect completeness
  a statement about the prover's runs.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

public section

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n}

/-- Every outcome of a run with a guarded verifier: a run of the prover, then the verdict if
the check passes on its transcript, a rejection otherwise. -/
theorem Reduction.mem_support_run_of_guarded
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (G : reduction.verifier.GuardedForm) (stmt : StmtIn) (wit : WitIn)
    {y : Option ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut)}
    (hy : y ∈ support (reduction.run stmt wit).run) :
    ∃ pr ∈ support (reduction.prover.run stmt wit),
      y = if G.check stmt pr.1 then some (pr, G.out stmt pr.1) else none := by
  rw [Reduction.run_eq_of_guarded_verifier reduction G, mem_support_bind_iff] at hy
  obtain ⟨pr, hpr, hy⟩ := hy
  exact ⟨pr, hpr, by simpa only [support_pure, Set.mem_singleton_iff] using hy⟩

end
end LeanerVM.Protocol
