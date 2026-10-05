/-
  LeanerVM.Protocol.ToArkLib.SendChecked

  The component with one round, a prover message: the verifier reads the message, rejects
  unless the statement and the message pass a check, and outputs a function of both, leaving
  the oracles and the witness alone. Its completeness proof. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.GuardedVerdict
public import LeanerVM.Protocol.ToArkLib.KeepOracles
public import LeanerVM.Protocol.ToArkLib.Schedule

/-!
# The send-checked component

`Component.sendChecked OStmt M honest check out` is the one-message schedule `say M`: the prover
sends `honest` of its input (the statement, the oracles' contents and the witness), the verifier
reads the message `msg` whole, rejects unless `check s msg` passes, and outputs `out s msg` with
the same oracles and the same witness. It is the shape of every step in which the prover
announces values the verifier tests or records: the values at the descendants of a product
tree, the polynomial of a sumcheck round (recorded, the check left to the challenge that
follows), the values at a final point. With `check := fun _ _ ↦ true` the verifier is pure.

Completeness (`sendCheckedComplete`): on the input relation the honest message passes the check
and `out` of it lands in the output relation. Knowledge soundness is the step's own: a message
has no challenge, so its error is zero whenever the check and the output relation together
imply the input relation.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  {StmtIn StmtOut W : Type} (M : Type)
  (honest : (StmtIn × ∀ i, OStmt i) × W → M) (check : StmtIn → M → Bool)
  (out : StmtIn → M → StmtOut)

/-- The prover: sends the honest message, outputs `out` of it, keeps the oracles and the
witness. -/
def sendCheckedProver : OracleProver []ₒ StmtIn OStmt W StmtOut OStmt W (say M) where
  PrvState := fun _ ↦ (StmtIn × ∀ i, OStmt i) × W
  input := _root_.id
  sendMessage | ⟨0, _⟩ => fun st ↦ pure (honest st, st)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st ↦ pure ((out st.1.1 (honest st), st.1.2), st.2)

/-- The verifier reads the message whole. -/
def queryMessage : OracleComp [(say M).Message]ₒ M :=
  liftM <| OracleSpec.query
    (show [(say M).Message]ₒ.Domain from ⟨⟨0, rfl⟩, (by change Unit; exact ())⟩)

/-- The verifier: reads the message, rejects unless the statement and the message pass the
check, outputs `out` of them, keeps the oracles. -/
def sendCheckedVerifier : OracleVerifier []ₒ StmtIn OStmt StmtOut OStmt (say M) where
  verify := fun s _ ↦ do
    let msg ← liftM (queryMessage M)
    if check s msg then pure (out s msg) else failure
  outputOracle := .inl (keepOracles OStmt (say M))

/-- The send-checked component. -/
def sendChecked : Def StmtIn OStmt W StmtOut OStmt W (say M) where
  red := ⟨sendCheckedProver OStmt M honest out, sendCheckedVerifier OStmt M check out⟩

/-- Reading the message returns the transcript's entry. -/
private theorem simulateQ_queryMessage (o : ∀ i, OStmt i) (tr : (say M).FullTranscript) :
    simulateQ (OracleInterface.simOracle2 []ₒ o tr.messages)
      (OptionT.lift (liftM (queryMessage M) :
        OracleComp ([]ₒ + ([OStmt]ₒ + [(say M).Message]ₒ)) M)).run =
      (pure (tr 0) : OptionT (OracleComp []ₒ) M) := by
  have h : simulateQ (OracleInterface.simOracle2 []ₒ o tr.messages)
      (liftM (queryMessage M) : OracleComp ([]ₒ + ([OStmt]ₒ + [(say M).Message]ₒ)) M) =
      pure (tr 0) := rfl
  rw [OptionT.run_lift, simulateQ_bind, h, pure_bind, simulateQ_pure]
  rfl

/-- As an ordinary verifier: if the transcript's message passes the check, the verdict is `out`
of the statement and the message, with the oracles; otherwise it rejects. -/
theorem sendCheckedVerifier_verify (s : StmtIn) (o : ∀ i, OStmt i)
    (tr : (say M).FullTranscript) :
    (sendCheckedVerifier OStmt M check out).toVerifier.verify (s, o) tr =
      if check s (tr 0) then pure (out s (tr 0), o) else failure := by
  simp only [OracleVerifier.toVerifier]
  rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl]
  simp only [sendCheckedVerifier]
  rw [show (liftM (queryMessage M) :
        OptionT (OracleComp ([]ₒ + ([OStmt]ₒ + [(say M).Message]ₒ))) M) =
      OptionT.lift (liftM (queryMessage M) :
        OracleComp ([]ₒ + ([OStmt]ₒ + [(say M).Message]ₒ)) M) from
    (OracleComp.monadLift_liftM_OptionT _).symm]
  rw [simulateQ_optionT_bind_run, simulateQ_queryMessage, pure_bind]
  by_cases h : check s (tr 0) = true
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- The send-checked verifier is a check followed by a verdict, as data. -/
def sendCheckedGuarded : (sendCheckedVerifier OStmt M check out).toVerifier.GuardedForm where
  check := fun p tr ↦ check p.1 (tr 0)
  out := fun p tr ↦ (out p.1 (tr 0), p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ sendCheckedVerifier_verify OStmt M check out s o tr

/-- The send-checked component is front: the check and the verdict read the message off the
transcript. -/
def sendCheckedFront : Front (sendChecked OStmt M honest check out) :=
  ⟨fun s tr ↦ check s (tr 0), fun s tr ↦ out s (tr 0),
    fun ⟨s, o⟩ tr ↦ sendCheckedVerifier_verify OStmt M check out s o tr⟩

omit [∀ i, OracleInterface (OStmt i)] in
/-- The run of the prover: its message is the honest one, its output `out` of it. -/
private theorem sendCheckedProver_run (s : StmtIn) (o : ∀ i, OStmt i) (w : W) :
    (sendCheckedProver OStmt M honest out).run (s, o) w =
      pure ((show (say M).FullTranscript from
          ProtocolSpec.Transcript.concat (m := 0) (honest ((s, o), w))
            (default : (say M).Transcript 0)),
        ((out s (honest ((s, o), w)), o), w)) :=
  rfl

variable {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)} {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}

/-- Perfect completeness, whenever on the input relation the honest message passes the check
and `out` of it lands in the output relation. -/
theorem sendChecked_complete
    (h : ∀ s o w, ((s, o), w) ∈ relIn →
      check s (honest ((s, o), w)) = true ∧ ((out s (honest ((s, o), w)), o), w) ∈ relOut)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (sendChecked OStmt M honest check out).red.perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _
    (sendCheckedGuarded OStmt M check out) (s, o) witIn hx
  replace hpr : pr ∈ support ((sendCheckedProver OStmt M honest out).run (s, o) witIn) := hpr
  rw [sendCheckedProver_run, support_pure, Set.mem_singleton_iff] at hpr
  subst hpr
  have hc : (sendCheckedGuarded OStmt M check out).check (s, o)
      (ProtocolSpec.Transcript.concat (m := 0) (honest ((s, o), witIn))
        (default : (say M).Transcript 0)) = true :=
    (h s o witIn hIn).1
  rw [ite_eq_left hc]
  exact ⟨_, rfl, (h s o witIn hIn).2, rfl⟩

/-- The completeness half. -/
def sendCheckedComplete
    (h : ∀ s o w, ((s, o), w) ∈ relIn →
      check s (honest ((s, o), w)) = true ∧ ((out s (honest ((s, o), w)), o), w) ∈ relOut) :
    Complete (sendChecked OStmt M honest check out) relIn relOut where
  guarded := sendCheckedGuarded OStmt M check out
  complete := sendChecked_complete OStmt M honest check out h

end Component

end
end LeanerVM.Protocol
