/-
  LeanerVM.Protocol.ToArkLib.PassThrough

  The component with no round that maps the statement and leaves the oracles and the witness
  alone, with its completeness proof. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component

/-!
# The pass-through component

`Component.passThrough OStmt f` sends nothing and outputs `f` of the input statement, the same
oracles and the same witness. It is the shape of every bookkeeping step (relabelling claims,
dropping a clause the previous step consumed), and its two unfolding lemmas are the ones any
zero-round or pure component would otherwise prove again. Its completeness holds for any two
relations `f` carries one into the other.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  {StmtIn StmtOut W : Type}

/-- The prover: no message, the statement mapped, oracles and witness kept. -/
def passThroughProver (f : StmtIn → StmtOut) :
    OracleProver []ₒ StmtIn OStmt W StmtOut OStmt W !p[] where
  PrvState := fun _ ↦ (StmtIn × ∀ i, OStmt i) × W
  input := _root_.id
  sendMessage := fun i ↦ Fin.elim0 i.1
  receiveChallenge := fun i ↦ Fin.elim0 i.1
  output := fun p ↦ pure ((f p.1.1, p.1.2), p.2)

/-- The verifier: maps the statement and exposes the input oracles as the output oracles. -/
def passThroughVerifier (f : StmtIn → StmtOut) :
    OracleVerifier []ₒ StmtIn OStmt StmtOut OStmt !p[] where
  verify := fun s _ ↦ pure (f s)
  outputOracle := .inl
    { embed := Function.Embedding.inl
      hEq := fun _ ↦ rfl
      outputInterface_heq := fun _ ↦ HEq.rfl }

/-- The pass-through component: no round, no error. -/
def passThrough (f : StmtIn → StmtOut) : Def StmtIn OStmt W StmtOut OStmt W where
  n := 0
  pSpec := !p[]
  red := ⟨passThroughProver OStmt f, passThroughVerifier OStmt f⟩
  err := fun i ↦ Fin.elim0 i.1

/-- The output oracles are the input oracles. -/
theorem passThrough_materializeOutput (f : StmtIn → StmtOut) (challenges : (!p[]).Challenges)
    (o : ∀ i, OStmt i) (messages : (!p[]).Messages) :
    (passThroughVerifier OStmt f).materializeOutput challenges o messages = o := by
  funext i
  rfl

/-- As an ordinary verifier, the pass-through verifier returns the mapped statement and the
oracles. -/
theorem passThroughVerifier_toVerifier_run (f : StmtIn → StmtOut) (s : StmtIn)
    (o : ∀ i, OStmt i) (tr : (!p[]).FullTranscript) :
    (passThroughVerifier OStmt f).toVerifier.run (s, o) tr = pure (f s, o) := by
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [passThrough_materializeOutput]
  rfl

/-- The pass-through verifier is pure, as data. -/
def passThroughPure (f : StmtIn → StmtOut) :
    (passThroughVerifier OStmt f).toVerifier.PureForm where
  verify := fun p _ ↦ (f p.1, p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ passThroughVerifier_toVerifier_run OStmt f s o tr

/-- Completeness, for any two relations `f` carries one into the other. -/
def passThroughComplete (f : StmtIn → StmtOut)
    {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)} {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ((f s, o), w) ∈ relOut) :
    Complete (passThrough OStmt f) relIn relOut where
  outputPure := ⟨_, fun _ ↦ rfl⟩
  guarded := (passThroughPure OStmt f).toGuardedForm
  complete := fun init impl ↦ by
    apply Reduction.perfectCompleteness_of_run_support
    intro stmtIn witIn hIn x hx
    obtain ⟨s, o⟩ := stmtIn
    have hrun : ((passThrough OStmt f).red.toReduction.run (s, o) witIn).run =
        pure (some (((show (passThrough OStmt f).pSpec.FullTranscript from
          fun i ↦ Fin.elim0 i), (f s, o), witIn), (f s, o))) := rfl
    rw [hrun, support_pure, Set.mem_singleton_iff] at hx
    exact ⟨_, hx, h s o witIn hIn, rfl⟩

end Component

end
end LeanerVM.Protocol
