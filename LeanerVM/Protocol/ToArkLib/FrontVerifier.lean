/-
  LeanerVM.Protocol.ToArkLib.FrontVerifier

  A verifier that never reads the input oracles, and how it becomes an ArkLib oracle verifier
  that keeps them. Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
public import LeanerVM.Protocol.ToArkLib.KeepOracles

/-!
# Front verifiers

An ArkLib oracle verifier may query the input oracles and the prover's messages. A *front*
verifier is one that never queries the input oracles: its computation runs over the shared
oracles and the messages alone, and it hands the input oracles on unchanged. A query to an
input oracle is then a type error, not a proof obligation.

`FrontVerifier.toOracleVerifier` lifts the computation past the input oracles and keeps them.
`FrontVerifier.toVerifier_verify` is the verdict of the resulting ordinary verifier: the
computation simulated with the transcript's messages, paired with the oracles it was given.
When that simulation is a check followed by a verdict, `FrontVerifier.guardedForm` is the
guarded form.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] {ιₛ : Type} {OStmt : ιₛ → Type}
  [∀ i, OracleInterface (OStmt i)]

/-- A query to the shared oracles or the messages, lifted past the input oracles and simulated
with the oracles and the messages, is the query simulated with the messages. -/
private theorem simulateQ_simOracle2_liftM_query (o : ∀ i, OStmt i) (msgs : pSpec.Messages)
    (t : (oSpec + [pSpec.Message]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec o msgs)
      (liftM (liftM ((oSpec + [pSpec.Message]ₒ).query t) :
          OracleComp (oSpec + [pSpec.Message]ₒ) _) :
        OracleComp (oSpec + ([OStmt]ₒ + [pSpec.Message]ₒ)) _) =
      OracleInterface.simOracle oSpec msgs t := by
  rw [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_liftM_query,
    OracleComp.liftM_eq_liftM_liftM]
  rcases t with t | t
  · simp only [OracleQuery.liftM_right_add_right_add_query, simulateQ_spec_query]
    rfl
  · simp only [OracleQuery.liftM_right_add_right_add_query, OracleQuery.liftM_add_right_query,
      simulateQ_spec_query]
    rfl

/-- Simulating a computation lifted past the input oracles with the oracles and the messages is
simulating the computation with the messages. -/
theorem OracleInterface.simulateQ_simOracle2_liftM_run (o : ∀ i, OStmt i)
    (msgs : pSpec.Messages) {α : Type} (mx : OptionT (OracleComp (oSpec + [pSpec.Message]ₒ)) α) :
    simulateQ (OracleInterface.simOracle2 oSpec o msgs)
      (liftM mx : OptionT (OracleComp (oSpec + ([OStmt]ₒ + [pSpec.Message]ₒ))) α).run =
      simulateQ (OracleInterface.simOracle oSpec msgs) mx.run := by
  have hrun : (liftM mx : OptionT (OracleComp (oSpec + ([OStmt]ₒ + [pSpec.Message]ₒ))) α).run =
      (liftM mx.run : OracleComp (oSpec + ([OStmt]ₒ + [pSpec.Message]ₒ)) (Option α)) := by
    rw [OracleComp.liftM_OptionT_eq, ← OracleComp.liftComp_eq_liftM]
    rfl
  rw [hrun]
  exact QueryImpl.simulateQ_liftM_eq_of_query _ _ (simulateQ_simOracle2_liftM_query o msgs) mx.run

/-- A verifier whose computation reads the shared oracles and the prover's messages, never the
input oracles. -/
structure FrontVerifier {ι : Type} (oSpec : OracleSpec ι) (StmtIn StmtOut : Type) {n : ℕ}
    (pSpec : ProtocolSpec n) [∀ i, OracleInterface (pSpec.Message i)] where
  /-- The verdict, from the statement and the challenges. -/
  verify : StmtIn → pSpec.Challenges → OptionT (OracleComp (oSpec + [pSpec.Message]ₒ)) StmtOut

namespace FrontVerifier

variable {StmtIn StmtOut : Type} (V : FrontVerifier oSpec StmtIn StmtOut pSpec) (OStmt)

/-- As an oracle verifier over the input oracles `OStmt`: the computation lifted past them, and
the input oracles kept. -/
def toOracleVerifier : OracleVerifier oSpec StmtIn OStmt StmtOut OStmt pSpec where
  verify := fun s c ↦ liftM (V.verify s c)
  outputOracle := .inl (keepOracles OStmt pSpec)

variable {OStmt}

/-- The verdict of the ordinary verifier: the computation simulated with the transcript's
messages, paired with the oracles it was given. -/
theorem toVerifier_verify (s : StmtIn) (o : ∀ i, OStmt i) (tr : pSpec.FullTranscript) :
    (V.toOracleVerifier OStmt).toVerifier.verify (s, o) tr =
      (fun t ↦ (t, o)) <$> OptionT.mk (simulateQ (OracleInterface.simOracle oSpec tr.messages)
        (V.verify s tr.challenges).run) := by
  simp only [OracleVerifier.toVerifier]
  rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl,
    show (V.toOracleVerifier OStmt).verify s tr.challenges = liftM (V.verify s tr.challenges)
      from rfl,
    OracleInterface.simulateQ_simOracle2_liftM_run]
  apply OptionT.ext
  rw [OptionT.run_map]
  rfl

/-- If the simulated computation is a check followed by a verdict, the ordinary verifier is that
check followed by the verdict and the oracles. -/
theorem toVerifier_verify_of_check (check : StmtIn → pSpec.FullTranscript → Bool)
    (out : StmtIn → pSpec.FullTranscript → StmtOut)
    (h : ∀ s tr, OptionT.mk (simulateQ (OracleInterface.simOracle oSpec tr.messages)
        (V.verify s tr.challenges).run) = if check s tr then pure (out s tr) else failure)
    (s : StmtIn) (o : ∀ i, OStmt i) (tr : pSpec.FullTranscript) :
    (V.toOracleVerifier OStmt).toVerifier.verify (s, o) tr =
      if check s tr then pure (out s tr, o) else failure := by
  rw [toVerifier_verify, h]
  by_cases hc : check s tr = true
  · rw [ite_eq_left hc, ite_eq_left hc, map_pure]
  · rw [ite_eq_right hc, ite_eq_right hc]
    rfl

variable (OStmt)

/-- A front verifier whose simulated computation is a check followed by a verdict, as a guarded
ordinary verifier: the check on the statement, the verdict paired with the oracles. -/
def guardedForm (check : StmtIn → pSpec.FullTranscript → Bool)
    (out : StmtIn → pSpec.FullTranscript → StmtOut)
    (h : ∀ s tr, OptionT.mk (simulateQ (OracleInterface.simOracle oSpec tr.messages)
        (V.verify s tr.challenges).run) = if check s tr then pure (out s tr) else failure) :
    (V.toOracleVerifier OStmt).toVerifier.GuardedForm where
  check := fun p tr ↦ check p.1 tr
  out := fun p tr ↦ (out p.1 tr, p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ toVerifier_verify_of_check V check out h s o tr

/-- The front verifier that queries nothing and outputs `f` of the statement. -/
def pure (f : StmtIn → StmtOut) : FrontVerifier oSpec StmtIn StmtOut pSpec where
  verify := fun s _ ↦ Pure.pure (f s)

end FrontVerifier

/-! The pure front verifier, through the verdict lemma: its ordinary verifier returns `f` of the
statement and the oracles, and it is guarded at the check that always passes. -/

variable {StmtIn StmtOut : Type} (f : StmtIn → StmtOut) (s : StmtIn) (o : ∀ i, OStmt i)
  (tr : pSpec.FullTranscript)

example :
    ((FrontVerifier.pure (oSpec := oSpec) f).toOracleVerifier OStmt).toVerifier.verify (s, o) tr =
      pure (f s, o) := by
  rw [FrontVerifier.toVerifier_verify]
  rfl

example :
    ((FrontVerifier.pure (oSpec := oSpec) (pSpec := pSpec) f).toOracleVerifier
      OStmt).toVerifier.GuardedForm :=
  (FrontVerifier.pure f).guardedForm OStmt (fun _ _ ↦ true) (fun s _ ↦ f s) fun _ _ ↦ rfl

end
end LeanerVM.Protocol
