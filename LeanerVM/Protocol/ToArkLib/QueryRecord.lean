/-
  LeanerVM.Protocol.ToArkLib.QueryRecord

  The component with no round whose verifier asks the input oracles one question, checks the
  answer, records a function of it in the statement and hands on some of the input oracles.
  Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.QueryCheck

/-!
# The query-record component

`Component.queryRecord OStmt keep query check out` sends nothing: the verifier asks the input
oracles the question `query s`, rejects unless `check s a` holds of the answer `a`, and outputs
`out s a`. It hands on the input oracles `keep` selects, `OStmt ∘ keep` (`keep` an injection of
the output index set into the input's). Its prover computes the same answer from the oracle
data it holds.

It is `Component.queryCheck` with the output statement allowed to depend on the answer, and with
the oracles that the question was about allowed to be dropped. It is the shape of a step that
*reads* committed data and *records* what it read: the verifier of one level of an
interleaved-code opening reads the rows of the previous level's word at the sampled positions and
records the folded symbols as claims, and the previous word is then of no further use.

Completeness (`queryRecordComplete`): on the input relation the check passes and `out` of the
answer carries the relation into the output relation, read on the oracles handed on. Security
(`queryRecordSecurity`, at the empty error, with the extractor that keeps the witness): a statement
that passes the check into the output relation is in the input relation; what the answer may be
is the consumer's to show.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Component

variable {ι ι' : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  (keep : ι' ↪ ι)
  {StmtIn StmtOut W : Type} (query : StmtIn → [OStmt]ₒ.Domain)
  (check : (s : StmtIn) → [OStmt]ₒ.Range (query s) → Bool)
  (out : (s : StmtIn) → [OStmt]ₒ.Range (query s) → StmtOut)

/-- A question to the input oracles, lifted past the shared oracles and the messages and
simulated with the oracles and the messages, is answered by the oracles. -/
private theorem simulateQ_askInput' {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, OracleInterface (pSpec.Message i)] (o : ∀ i, OStmt i) (msgs : pSpec.Messages)
    (t : [OStmt]ₒ.Domain) :
    simulateQ (OracleInterface.simOracle2 []ₒ o msgs)
      (liftM (askInput OStmt t) : OracleComp ([]ₒ + ([OStmt]ₒ + [pSpec.Message]ₒ)) _) =
      pure (answerOf OStmt o t) :=
  rfl

/-- The oracles handed on: the input oracles at `keep`. -/
abbrev keptOracles (i : ι') : Type := OStmt (keep i)

/-- The kept oracles are queried as the input oracles are. -/
instance keptInterface (i : ι') : OracleInterface (keptOracles OStmt keep i) := inferInstance

/-- The output-oracle description: each output oracle is the input oracle `keep` selects. -/
def keepSome : OracleOutputEmbedding OStmt (!p[] : ProtocolSpec 0).Message
    (keptOracles OStmt keep) where
  embed := keep.trans Function.Embedding.inl
  hEq := fun _ ↦ rfl
  outputInterface_heq := fun _ ↦ HEq.rfl

/-- The prover: sends nothing, records the answer it computes from the oracle data, hands on the
kept oracles and the witness. -/
def queryRecordProver :
    OracleProver []ₒ StmtIn OStmt W StmtOut (keptOracles OStmt keep) W !p[] where
  PrvState := fun _ ↦ (StmtIn × ∀ i, OStmt i) × W
  input := _root_.id
  sendMessage := fun i ↦ Fin.elim0 i.1
  receiveChallenge := fun i ↦ Fin.elim0 i.1
  output := fun p ↦
    pure ((out p.1.1 (answerOf OStmt p.1.2 (query p.1.1)), fun i ↦ p.1.2 (keep i)), p.2)

/-- The verifier: asks the input oracles the question, rejects unless the check holds of the
answer, records `out` of the answer, hands on the kept oracles. -/
def queryRecordVerifier :
    OracleVerifier []ₒ StmtIn OStmt StmtOut (keptOracles OStmt keep) !p[] where
  verify := fun s _ ↦ do
    let a ← liftM (askInput OStmt (query s))
    if check s a then pure (out s a) else failure
  outputOracle := .inl (keepSome OStmt keep)

/-- The query-record component. -/
def queryRecord : Def StmtIn OStmt W StmtOut (keptOracles OStmt keep) W !p[] where
  red := ⟨queryRecordProver OStmt keep query out,
    queryRecordVerifier OStmt keep query check out⟩

/-- The output oracles are the kept input oracles. -/
private theorem queryRecord_materializeOutput (challenges : (!p[] : ProtocolSpec 0).Challenges)
    (o : ∀ i, OStmt i) (messages : (!p[] : ProtocolSpec 0).Messages) :
    (queryRecordVerifier OStmt keep query check out).materializeOutput challenges o messages =
      fun i ↦ o (keep i) := by
  unfold OracleVerifier.materializeOutput
  change OracleVerifier.materializeOutputOracle (Sum.inl (keepSome OStmt keep)) challenges o
    messages = _
  simp only [OracleVerifier.materializeOutputOracle]
  funext i
  rfl

/-- As an ordinary verifier: if the check holds of the oracles' answer, the verdict is `out` of
the answer and the kept oracles; otherwise it rejects. -/
theorem queryRecordVerifier_verify (s : StmtIn) (o : ∀ i, OStmt i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    (queryRecordVerifier OStmt keep query check out).toVerifier.verify (s, o) tr =
      if check s (answerOf OStmt o (query s)) then
        pure (out s (answerOf OStmt o (query s)), fun i ↦ o (keep i))
      else failure := by
  simp only [OracleVerifier.toVerifier]
  rw [queryRecord_materializeOutput]
  simp only [queryRecordVerifier]
  rw [show (liftM (askInput OStmt (query s)) :
      OptionT (OracleComp ([]ₒ + ([OStmt]ₒ + [(!p[] : ProtocolSpec 0).Message]ₒ))) _) =
      OptionT.lift (liftM (askInput OStmt (query s)) :
        OracleComp ([]ₒ + ([OStmt]ₒ + [(!p[] : ProtocolSpec 0).Message]ₒ)) _) from
    (OracleComp.monadLift_liftM_OptionT _).symm]
  rw [simulateQ_optionT_bind_elimM, OptionT.run_lift, simulateQ_bind, simulateQ_askInput',
    pure_bind, simulateQ_pure]
  simp only [Option.elimM, pure_bind, Option.elim]
  by_cases h : check s (answerOf OStmt o (query s)) = true
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- The verifier is a check followed by a verdict, as data. -/
def queryRecordGuarded :
    (queryRecordVerifier OStmt keep query check out).toVerifier.GuardedForm where
  check := fun p _ ↦ check p.1 (answerOf OStmt p.2 (query p.1))
  out := fun p _ ↦ (out p.1 (answerOf OStmt p.2 (query p.1)), fun i ↦ p.2 (keep i))
  verify_eq := fun ⟨s, o⟩ tr ↦ queryRecordVerifier_verify OStmt keep query check out s o tr

variable {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)}
  {relOut : Set ((StmtOut × ∀ i, keptOracles OStmt keep i) × W)}

/-- Perfect completeness, whenever on the input relation the check passes and `out` of the answer
carries the relation into the output relation. -/
theorem queryRecord_complete
    (h : ∀ s o w, ((s, o), w) ∈ relIn →
      check s (answerOf OStmt o (query s)) = true ∧
        ((out s (answerOf OStmt o (query s)), fun i ↦ o (keep i)), w) ∈ relOut)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryRecord OStmt keep query check out).red.perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _
    (queryRecordGuarded OStmt keep query check out) (s, o) witIn hx
  have hrun : (queryRecordProver OStmt keep query out).run (s, o) witIn =
      pure ((show (!p[] : ProtocolSpec 0).FullTranscript from fun i ↦ Fin.elim0 i),
        (out s (answerOf OStmt o (query s)), fun i ↦ o (keep i)), witIn) := rfl
  have hpr' : pr ∈ support ((queryRecordProver OStmt keep query out).run (s, o) witIn) := hpr
  rw [hrun, support_pure, Set.mem_singleton_iff] at hpr'
  subst hpr'
  have hc : (queryRecordGuarded OStmt keep query check out).check (s, o)
      (fun i ↦ Fin.elim0 i) = true := (h s o witIn hIn).1
  rw [ite_eq_left hc]
  exact ⟨_, rfl, (h s o witIn hIn).2, rfl⟩

/-- The completeness half. -/
def queryRecordComplete
    (h : ∀ s o w, ((s, o), w) ∈ relIn →
      check s (answerOf OStmt o (query s)) = true ∧
        ((out s (answerOf OStmt o (query s)), fun i ↦ o (keep i)), w) ∈ relOut) :
    Complete (queryRecord OStmt keep query check out) relIn relOut where
  guarded := queryRecordGuarded OStmt keep query check out
  complete := queryRecord_complete OStmt keep query check out h


/-! ## Security -/

section Security

variable (h : ∀ s o w, check s (answerOf OStmt o (query s)) = true →
    ((out s (answerOf OStmt o (query s)), fun i ↦ o (keep i)), w) ∈ relOut →
      ((s, o), w) ∈ relIn)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function of the query-record component: the input relation, at the only
round. -/
def queryRecordStateFunction :
    (queryRecordVerifier OStmt keep query check out).toVerifier.KnowledgeStateFunction init impl
      relIn relOut (keepExtractor (StmtIn × ∀ i, OStmt i) W !p[]) where
  toFun := fun _ stmt _ w ↦ (stmt, w) ∈ relIn
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ Fin.elim0 m
  toFun_full := fun stmt tr w hpos ↦
    have hg := Verifier.GuardedForm.of_probEvent_pos
      (queryRecordGuarded OStmt keep query check out) init impl stmt tr _ hpos
    h stmt.1 stmt.2 w hg.1 hg.2

/-- The security half of the query-record component, at the empty error, with the extractor that
keeps the witness: a statement that passes the check into the output relation is in the input
relation. -/
def queryRecordSecurity :
    Security (queryRecord OStmt keep query check out) relIn relOut (fun i ↦ Fin.elim0 i.1) where
  guarded := queryRecordGuarded OStmt keep query check out
  witMid := fun _ ↦ W
  extractor := keepExtractor (StmtIn × ∀ i, OStmt i) W !p[]
  kSF := queryRecordStateFunction OStmt keep query check out h
  rbr := fun _ _ _ i ↦ Fin.elim0 i.1

end Security

end Component

end
end LeanerVM.Protocol
