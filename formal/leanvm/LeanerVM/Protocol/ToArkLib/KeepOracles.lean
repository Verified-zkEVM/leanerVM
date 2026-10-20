/-
  LeanerVM.Protocol.ToArkLib.KeepOracles

  The output-oracle description of a verifier whose output oracles are its input oracles.
  Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.Basic

/-!
# Keeping the input oracles

An ArkLib oracle verifier says which oracles it hands on: each output oracle is one of the
input oracles or one of the prover's messages. `keepOracles` is the description "the output
oracles are exactly the input oracles, in the same order", the one every verifier uses that
adds claims about committed data without committing to anything new.
`OracleVerifier.materializeOutput_of_keepOracles` is its one fact: such a verifier outputs the
oracles it was given.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

variable {ι : Type} {oSpec : OracleSpec ι} {ιₛ : Type} (OStmt : ιₛ → Type)
  [∀ i, OracleInterface (OStmt i)] {n : ℕ} (pSpec : ProtocolSpec n)
  [∀ i, OracleInterface (pSpec.Message i)]

/-- The output oracles are the input oracles. -/
def keepOracles : OracleOutputEmbedding OStmt pSpec.Message OStmt where
  embed := Function.Embedding.inl
  hEq := fun _ ↦ rfl
  outputInterface_heq := fun _ ↦ HEq.rfl

variable {OStmt pSpec}

/-- A verifier that keeps the oracles outputs the oracles it was given. -/
theorem OracleVerifier.materializeOutput_of_keepOracles {StmtIn StmtOut : Type}
    (V : OracleVerifier oSpec StmtIn OStmt StmtOut OStmt pSpec)
    (h : V.outputOracle = .inl (keepOracles OStmt pSpec)) (challenges : pSpec.Challenges)
    (o : ∀ i, OStmt i) (messages : pSpec.Messages) :
    V.materializeOutput challenges o messages = o := by
  unfold OracleVerifier.materializeOutput
  rw [h]
  funext i
  rfl

end
end LeanerVM.Protocol
