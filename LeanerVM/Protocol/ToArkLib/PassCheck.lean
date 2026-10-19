/-
  LeanerVM.Protocol.ToArkLib.PassCheck

  The component with no round that rejects unless the statement passes a check, maps the
  statement and leaves the oracles and the witness alone, with its completeness. Candidate for
  ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.PassThrough

/-!
# The pass-check component

`Component.passCheck OStmt check f` sends nothing: the verifier rejects unless `check s` holds of
the input statement, and outputs `f s` with the oracles it was given; the prover outputs the same
statement and keeps the oracles and the witness. It is `Component.passThrough` with a test on the
statement, the shape of a verifier's final comparison of values it already holds: the terminal
check of a sumcheck, which compares the running claim with the product of the weight and the
table at the challenge point.

Completeness (`passCheckComplete`): on the input relation the check passes and `f` carries the
relation into the output relation. Knowledge soundness is the consumer's.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  {StmtIn StmtOut W : Type} (check : StmtIn → Bool) (f : StmtIn → StmtOut)

/-- The verifier: rejects unless the statement passes the check, maps the statement, keeps the
oracles. -/
def passCheckVerifier : OracleVerifier []ₒ StmtIn OStmt StmtOut OStmt !p[] where
  verify := fun s _ ↦ if check s then pure (f s) else failure
  outputOracle := .inl (keepOracles OStmt !p[])

/-- The pass-check component: the pass-through prover, the pass-check verifier. -/
def passCheck : Def StmtIn OStmt W StmtOut OStmt W !p[] where
  red := ⟨passThroughProver OStmt f, passCheckVerifier OStmt check f⟩

/-- As an ordinary verifier: if the statement passes the check, the verdict is the mapped
statement and the oracles; otherwise it rejects. -/
theorem passCheckVerifier_verify (s : StmtIn) (o : ∀ i, OStmt i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    (passCheckVerifier OStmt check f).toVerifier.verify (s, o) tr =
      if check s then pure (f s, o) else failure := by
  simp only [OracleVerifier.toVerifier]
  rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl]
  simp only [passCheckVerifier]
  by_cases h : check s = true
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- The verifier is a check followed by a verdict, as data. -/
def passCheckGuarded : (passCheckVerifier OStmt check f).toVerifier.GuardedForm where
  check := fun p _ ↦ check p.1
  out := fun p _ ↦ (f p.1, p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ passCheckVerifier_verify OStmt check f s o tr

variable {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)} {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}

/-- Perfect completeness, whenever on the input relation the check passes and `f` carries the
relation into the output relation. -/
theorem passCheck_complete
    (h : ∀ s o w, ((s, o), w) ∈ relIn → check s = true ∧ ((f s, o), w) ∈ relOut)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (passCheck (W := W) OStmt check f).red.perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _
    (passCheckGuarded OStmt check f) (s, o) witIn hx
  have hrun : (passThroughProver OStmt f).run (s, o) witIn =
      pure ((show (!p[] : ProtocolSpec 0).FullTranscript from fun i ↦ Fin.elim0 i),
        (f s, o), witIn) := rfl
  have hpr' : pr ∈ support ((passThroughProver OStmt f).run (s, o) witIn) := hpr
  rw [hrun, support_pure, Set.mem_singleton_iff] at hpr'
  subst hpr'
  have hc : (passCheckGuarded OStmt check f).check (s, o) (fun i ↦ Fin.elim0 i) = true :=
    (h s o witIn hIn).1
  rw [ite_eq_left hc]
  exact ⟨_, rfl, (h s o witIn hIn).2, rfl⟩

/-- The completeness half. -/
def passCheckComplete
    (h : ∀ s o w, ((s, o), w) ∈ relIn → check s = true ∧ ((f s, o), w) ∈ relOut) :
    Complete (passCheck (W := W) OStmt check f) relIn relOut where
  guarded := passCheckGuarded OStmt check f
  complete := passCheck_complete OStmt check f h

end Component

end
end LeanerVM.Protocol
