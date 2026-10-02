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

/-! ## Knowledge soundness -/

variable (h : ∀ s o w msg, check s msg = true → ((out s msg, o), w) ∈ relOut → ((s, o), w) ∈ relIn)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function of a checked message: the input relation, before and after the
message; the message cannot make it true. -/
def sendCheckedStateFunction :
    (sendCheckedVerifier OStmt M check out).toVerifier.KnowledgeStateFunction init impl relIn
      relOut (keepExtractor _ W (say M)) where
  toFun := fun _ stmt _ w ↦ (stmt, w) ∈ relIn
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun _ _ _ _ _ _ hw ↦ hw
  toFun_full := fun stmt tr w hpos ↦
    have hv := Verifier.GuardedForm.of_probEvent_pos (sendCheckedGuarded OStmt M check out) init
      impl stmt tr _ hpos
    h stmt.1 stmt.2 w (tr ⟨0, Nat.zero_lt_one⟩) hv.1 hv.2

/-- The security half of a checked message, at error zero: no challenge, the witness kept,
whenever the check and the output relation together imply the input relation. -/
def sendCheckedSecurity :
    Security (sendChecked OStmt M honest check out) relIn relOut (sayError M) where
  guarded := sendCheckedGuarded OStmt M check out
  witMid := fun _ ↦ W
  extractor := keepExtractor _ W (say M)
  kSF := sendCheckedStateFunction OStmt M check out h
  rbr := fun _ _ _ i ↦ (IsEmpty.false i).elim

omit h in
/-- No knowledge state function at all when some message that passes the check carries a
statement with no witness into the output relation: the verifier accepts it, so the state is
true after the message, and a message cannot have made it true. -/
theorem sendChecked_no_stateFunction {W' : Fin 2 → Type}
    {E : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (StmtIn × ∀ i, OStmt i) W W
      (say M) W'}
    (K : (sendCheckedVerifier OStmt M check out).toVerifier.KnowledgeStateFunction init impl
      relIn relOut E)
    (s : StmtIn) (o : ∀ i, OStmt i) (hin : ∀ w, ((s, o), w) ∉ relIn) (msg : M)
    (hc : check s msg = true) (w : W) (hout : ((out s msg, o), w) ∈ relOut) : False := by
  let tr : (say M).FullTranscript :=
    ProtocolSpec.Transcript.concat (m := 0) msg (default : (say M).Transcript 0)
  have hc' : (sendCheckedGuarded OStmt M check out).check (s, o) tr = true := hc
  have hpos := Verifier.guarded_accepting_of_mem init impl _ _ _
    (sendCheckedGuarded OStmt M check out).verify_eq (s, o) tr hc' {t | (t, w) ∈ relOut} hout
  have hfull := K.toFun_full (s, o) tr w (lt_of_lt_of_eq zero_lt_one hpos.symm)
  have hnext := K.toFun_next 0 rfl (s, o) (default : (say M).Transcript 0) msg _ hfull
  exact hin _ ((K.toFun_empty (s, o) _).mpr hnext)

end Component

end
end LeanerVM.Protocol
