/-
  LeanerVM.Protocol.ToArkLib.QueryCheck

  The component with no round whose verifier asks the input oracles one question and checks the
  answer, with its completeness and knowledge-soundness proofs, and the refutation of a batching
  followed by such a check. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Batch
public import LeanerVM.Protocol.ToArkLib.PassThrough

/-!
# The query-check component

`Component.queryCheck OStmt query check f` sends nothing: the verifier asks the input oracles
the question `query s` (an index and a query to that oracle), rejects unless `check s` holds of
the answer, and outputs `f s` with the same oracles and the same witness. Its prover is the
pass-through's. It is the last step of a protocol that reduces its claims on an oracle to one
claim and then reads the oracle once, as after `Component.batch`; unlike a front component, it
reads the oracles.

Completeness (`queryCheckComplete`): on the input relation the check passes and `f` carries
the relation into the output relation. Knowledge soundness (`queryCheckSecurity`, at the empty
error, with the extractor that keeps the witness): whenever a statement that passes the check
into the output relation is in the input relation. A batching followed by a query check is not
knowledge sound below error one, whatever the extractor and the state function, when a
statement outside the input relation passes the check into the output relation at every
challenge (`batch_append_queryCheck_not_rbr`).
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]

/-- The answer of the oracles `o` to a question: the queried oracle's answer to the query. -/
def answerOf (o : ∀ i, OStmt i) (t : [OStmt]ₒ.Domain) : [OStmt]ₒ.Range t :=
  OracleInterface.answer (o t.1) t.2

/-- The verifier asks the input oracles one question. -/
def askInput (t : [OStmt]ₒ.Domain) : OracleComp [OStmt]ₒ ([OStmt]ₒ.Range t) :=
  liftM (OracleSpec.query t)

/-- A question to the input oracles, lifted past the shared oracles and the messages and
simulated with the oracles and the messages, is answered by the oracles. -/
private theorem simulateQ_askInput {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, OracleInterface (pSpec.Message i)] (o : ∀ i, OStmt i) (msgs : pSpec.Messages)
    (t : [OStmt]ₒ.Domain) :
    simulateQ (OracleInterface.simOracle2 []ₒ o msgs)
      (liftM (askInput OStmt t) : OracleComp ([]ₒ + ([OStmt]ₒ + [pSpec.Message]ₒ)) _) =
      pure (answerOf OStmt o t) :=
  rfl

variable {StmtIn StmtOut W : Type} (query : StmtIn → [OStmt]ₒ.Domain)
  (check : (s : StmtIn) → [OStmt]ₒ.Range (query s) → Bool) (f : StmtIn → StmtOut)

/-- The verifier: asks the input oracles the question, rejects unless the check holds of the
answer, maps the statement, keeps the oracles. -/
def queryCheckVerifier : OracleVerifier []ₒ StmtIn OStmt StmtOut OStmt !p[] where
  verify := fun s _ ↦ do
    let a ← liftM (askInput OStmt (query s))
    if check s a then pure (f s) else failure
  outputOracle := .inl (keepOracles OStmt !p[])

/-- The query-check component: the pass-through prover, the query-check verifier. -/
def queryCheck : Def StmtIn OStmt W StmtOut OStmt W !p[] where
  red := ⟨passThroughProver OStmt f, queryCheckVerifier OStmt query check f⟩

/-- As an ordinary verifier: if the check holds of the oracles' answer, the verdict is the mapped
statement and the oracles; otherwise it rejects. -/
theorem queryCheckVerifier_verify (s : StmtIn) (o : ∀ i, OStmt i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    (queryCheckVerifier OStmt query check f).toVerifier.verify (s, o) tr =
      if check s (answerOf OStmt o (query s)) then pure (f s, o) else failure := by
  simp only [OracleVerifier.toVerifier]
  rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl]
  simp only [queryCheckVerifier]
  rw [show (liftM (askInput OStmt (query s)) :
      OptionT (OracleComp ([]ₒ + ([OStmt]ₒ + [(!p[] : ProtocolSpec 0).Message]ₒ))) _) =
      OptionT.lift (liftM (askInput OStmt (query s)) :
        OracleComp ([]ₒ + ([OStmt]ₒ + [(!p[] : ProtocolSpec 0).Message]ₒ)) _) from
    (OracleComp.monadLift_liftM_OptionT _).symm]
  rw [simulateQ_optionT_bind_elimM, OptionT.run_lift, simulateQ_bind, simulateQ_askInput,
    pure_bind, simulateQ_pure]
  simp only [Option.elimM, pure_bind, Option.elim]
  by_cases h : check s (answerOf OStmt o (query s)) = true
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- The query-check verifier is a check followed by a verdict, as data: the check reads the
statement and the oracles' answer. -/
def queryCheckGuarded : (queryCheckVerifier OStmt query check f).toVerifier.GuardedForm where
  check := fun p _ ↦ check p.1 (answerOf OStmt p.2 (query p.1))
  out := fun p _ ↦ (f p.1, p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ queryCheckVerifier_verify OStmt query check f s o tr

variable {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)} {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}

/-- Perfect completeness, whenever on the input relation the check passes and `f` carries the
relation into the output relation. -/
theorem queryCheck_complete
    (h : ∀ s o w, ((s, o), w) ∈ relIn →
      check s (answerOf OStmt o (query s)) = true ∧ ((f s, o), w) ∈ relOut)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryCheck OStmt query check f).red.perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _
    (queryCheckGuarded OStmt query check f) (s, o) witIn hx
  have hrun : (passThroughProver OStmt f).run (s, o) witIn =
      pure ((show (!p[] : ProtocolSpec 0).FullTranscript from fun i ↦ Fin.elim0 i),
        (f s, o), witIn) := rfl
  have hpr' : pr ∈ support ((passThroughProver OStmt f).run (s, o) witIn) := hpr
  rw [hrun, support_pure, Set.mem_singleton_iff] at hpr'
  subst hpr'
  have hc : (queryCheckGuarded OStmt query check f).check (s, o)
      (fun i ↦ Fin.elim0 i) = true := (h s o witIn hIn).1
  rw [ite_eq_left hc]
  exact ⟨_, rfl, (h s o witIn hIn).2, rfl⟩

/-- The completeness half. -/
def queryCheckComplete
    (h : ∀ s o w, ((s, o), w) ∈ relIn →
      check s (answerOf OStmt o (query s)) = true ∧ ((f s, o), w) ∈ relOut) :
    Complete (queryCheck OStmt query check f) relIn relOut where
  guarded := queryCheckGuarded OStmt query check f
  complete := queryCheck_complete OStmt query check f h

/-! ## Knowledge soundness -/

variable (h : ∀ s o w, check s (answerOf OStmt o (query s)) = true →
    ((f s, o), w) ∈ relOut → ((s, o), w) ∈ relIn)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function: the input relation, at the only round. -/
def queryCheckStateFunction :
    (queryCheckVerifier OStmt query check f).toVerifier.KnowledgeStateFunction init impl relIn
      relOut (keepExtractor (StmtIn × ∀ i, OStmt i) W !p[]) where
  toFun := fun _ stmt _ w ↦ (stmt, w) ∈ relIn
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ Fin.elim0 m
  toFun_full := fun stmt tr w hpos ↦
    have hg := Verifier.GuardedForm.of_probEvent_pos (queryCheckGuarded OStmt query check f)
      init impl stmt tr _ hpos
    h stmt.1 stmt.2 w hg.1 hg.2

/-- Round-by-round knowledge soundness at the empty error: no challenge, the witness is kept. -/
theorem queryCheck_rbr :
    (queryCheckVerifier OStmt query check f).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init
      impl relIn relOut (fun _ ↦ W) (keepExtractor (StmtIn × ∀ i, OStmt i) W !p[])
      (queryCheckStateFunction OStmt query check f h init impl) (fun i ↦ Fin.elim0 i.1) :=
  fun _ i ↦ Fin.elim0 i.1

/-- The security half, at the empty error, with the extractor that keeps the witness, whenever a
statement that passes the check into the output relation is in the input relation. -/
def queryCheckSecurity :
    Security (queryCheck OStmt query check f) relIn relOut (fun i ↦ Fin.elim0 i.1) where
  guarded := queryCheckGuarded OStmt query check f
  witMid := fun _ ↦ W
  extractor := keepExtractor (StmtIn × ∀ i, OStmt i) W !p[]
  kSF := queryCheckStateFunction OStmt query check f h
  rbr := fun init impl ↦ queryCheck_rbr OStmt query check f h init impl

end Component

/-! ## A batching followed by a query check -/

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  {StmtIn Mid StmtOut W : Type} (F : Type) [Field F] [SampleableType F] {k : ℕ}
  (value : StmtIn → Fin k → F) (out : StmtIn → F → F → Mid) (query : Mid → [OStmt]ₒ.Domain)
  (check : (m : Mid) → [OStmt]ₒ.Range (query m) → Bool) (f : Mid → StmtOut)

/-- Batching by powers followed by a query check, at the schedule of the batching's one
challenge: the claims are combined by the powers of a challenge, then the oracles are asked the
combined claim's question. -/
abbrev batchQuery : Def StmtIn OStmt W StmtOut OStmt W (draw F) :=
  (batch OStmt F value out).append (queryCheck OStmt query check f)

variable {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)} {relMid : Set ((Mid × ∀ i, OStmt i) × W)}
  {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}

/-- Its completeness, from the two parts' through a relation between them. -/
def batchQueryComplete
    (h₁ : ∀ s o w, ((s, o), w) ∈ relIn →
      ∀ ρ, ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relMid)
    (h₂ : ∀ m o w, ((m, o), w) ∈ relMid →
      check m (answerOf OStmt o (query m)) = true ∧ ((f m, o), w) ∈ relOut) :
    Complete (batchQuery OStmt F value out query check f) relIn relOut :=
  (batchComplete OStmt F value out h₁).append (queryCheckComplete OStmt query check f h₂)

variable [Finite F]

/-- Its security at `(k - 1) / |F|`, from the two parts' through a relation between them: the
batching's hypothesis, and that passing the check into the output relation is the relation
between them. -/
def batchQuerySecurity
    (h₁ : ∀ s o, ∃ a : Fin k → F, ∀ w ρ, ((s, o), w) ∉ relIn →
      ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relMid →
        a ≠ value s ∧ powerBatch (value s) ρ = powerBatch a ρ)
    (h₂ : ∀ m o w, check m (answerOf OStmt o (query m)) = true →
      ((f m, o), w) ∈ relOut → ((m, o), w) ∈ relMid) :
    Security (batchQuery OStmt F value out query check f) relIn relOut
      (drawError F (((k - 1 : ℕ) : ℝ≥0) / (Nat.card F : ℝ≥0))) :=
  Security.mono (fun i ↦ le_of_eq (by
      simp only [errAppend, Function.comp_apply]
      cases (ChallengeIdx.sumEquiv (pSpec₁ := draw F) (pSpec₂ := !p[])).symm i with
      | inl j => rfl
      | inr j => exact Fin.elim0 j.1))
    ((batchSecurity OStmt F value out h₁).append (queryCheckSecurity OStmt query check f h₂))

omit [Finite F] in
/-- A batching followed by a query check is not knowledge sound below error one, whatever the
extractor and the state function, from a statement outside the input relation that passes the
check into the output relation at every challenge. -/
theorem batchQuery_not_rbr {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl []ₒ (StateT σ ProbComp)} {WitMid : Fin 2 → Type}
    {E : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (StmtIn × ∀ i, OStmt i) W W
      (draw F) WitMid}
    {kSF : (batchQuery (W := W) OStmt F value out query check f).red.verifier.toVerifier
      |>.KnowledgeStateFunction init impl relIn relOut E}
    {ε : (draw F).ChallengeIdx → ℝ≥0}
    (h : (batchQuery (W := W) OStmt F value out query check f).red.verifier.toVerifier
      |>.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut WitMid E kSF ε)
    (s : StmtIn) (o : ∀ i, OStmt i) (hin : ∀ w, ((s, o), w) ∉ relIn) (w : W)
    (hesc : ∀ ρ, check (out s ρ (powerBatch (value s) ρ))
        (answerOf OStmt o (query (out s ρ (powerBatch (value s) ρ)))) = true ∧
      ((f (out s ρ (powerBatch (value s) ρ)), o), w) ∈ relOut) :
    1 ≤ ε ⟨0, rfl⟩ := by
  refine Verifier.not_rbr_zero h ⟨0, rfl⟩ rfl (fun j hj ↦ absurd hj (by have := j.isLt; omega))
    (s, o) (fun w' hw' ↦ hin w' hw') (default : (draw F).Transcript 0) fun c ↦ ?_
  refine ⟨Transcript.concat c (default : (draw F).Transcript 0), rfl, w, ?_⟩
  apply Verifier.GuardedForm.probEvent_pos_of_check
    (guardedAppend (D₁ := batch OStmt F value out) (D₂ := queryCheck OStmt query check f)
      (sampleGuarded OStmt F _ _) (queryCheckGuarded OStmt query check f))
    init impl (s, o) _ (fun t ↦ (t, w) ∈ relOut)
  · exact (guardedAppend_check _ _ _ _).trans (hesc _).1
  · exact (congrArg (fun t ↦ (t, w) ∈ relOut) (guardedAppend_out _ _ _ _)).mpr (hesc _).2

end Component

end
end LeanerVM.Protocol
