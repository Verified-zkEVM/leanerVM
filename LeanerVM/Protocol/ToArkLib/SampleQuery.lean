/-
  LeanerVM.Protocol.ToArkLib.SampleQuery

  The component with one round, a verifier challenge, whose verifier then asks the input
  oracles one question and checks the answer. Its completeness and its round-by-round knowledge
  soundness. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.SampleChallenge

/-!
# The sample-query component

`Component.sampleQuery OStmt C query check f` is the one-challenge schedule `draw C`: the
verifier draws `c : C`, asks the input oracles the question `query s c` (an index and a query to
that oracle), rejects unless `check s c` holds of the answer, and outputs `f s c` with the same
oracles and the same witness. Its prover is the sample-challenge component's: it receives the
challenge and maps the statement. It is the shape of a step that ends in an oracle query whose
question depends on the challenge, such as the opening of a batch of claims at a random linear
combination. Unlike `Component.sampleChallenge`, whose check reads the statement before the
challenge, the check here reads the challenge and the oracle's answer, so the verifier is not
front: it reads the oracles.

Completeness (`sampleQueryComplete`): on the input relation every challenge passes the check and
`f` carries the relation into the output relation. Knowledge soundness (`sampleQuerySecurity`):
at `N / |C|`, with the extractor that keeps the witness, when every statement has at most `N`
bad challenges, those at which a witness outside the input relation passes the check and lands
in the output relation. A statement with no witness at which every challenge passes the check
into the output relation leaves no knowledge error below one, whatever the extractor and the
state function (`sampleQuery_not_rbr`).
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

@[expose] public section

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  {StmtIn StmtOut W : Type} (C : Type) [SampleableType C]
  (query : StmtIn → C → [OStmt]ₒ.Domain)
  (check : (s : StmtIn) → (c : C) → [OStmt]ₒ.Range (query s c) → Bool)
  (f : StmtIn → C → StmtOut)

/-- The answer of the oracles `o` to a question: the queried oracle's answer to the query. -/
def answerOf (o : ∀ i, OStmt i) (t : [OStmt]ₒ.Domain) : [OStmt]ₒ.Range t :=
  OracleInterface.answer (o t.1) t.2

/-- The verifier asks the input oracles one question. -/
def askInput (t : [OStmt]ₒ.Domain) : OracleComp [OStmt]ₒ ([OStmt]ₒ.Range t) :=
  liftM (OracleSpec.query t)

/-- The verifier: asks the input oracles the question at the challenge, rejects unless the check
holds of the answer, maps the statement by the challenge, keeps the oracles. -/
def queryVerifier : OracleVerifier []ₒ StmtIn OStmt StmtOut OStmt (draw C) where
  verify := fun s chals ↦ do
    let a ← liftM (askInput OStmt (query s (chals ⟨0, rfl⟩)))
    if check s (chals ⟨0, rfl⟩) a then pure (f s (chals ⟨0, rfl⟩)) else failure
  outputOracle := .inl (keepOracles OStmt (draw C))

/-- The sample-query component: the sample-challenge prover, the query verifier. -/
def sampleQuery : Def StmtIn OStmt W StmtOut OStmt W (draw C) where
  red := ⟨sampleProver OStmt C f, queryVerifier OStmt C query check f⟩

omit [SampleableType C] in
/-- A question to the input oracles, lifted past the shared oracles and the messages and
simulated with the oracles and the messages, is answered by the oracles. -/
theorem simulateQ_askInput {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, OracleInterface (pSpec.Message i)] (o : ∀ i, OStmt i) (msgs : pSpec.Messages)
    (t : [OStmt]ₒ.Domain) :
    simulateQ (OracleInterface.simOracle2 []ₒ o msgs)
      (liftM (askInput OStmt t) : OracleComp ([]ₒ + ([OStmt]ₒ + [pSpec.Message]ₒ)) _) =
      pure (answerOf OStmt o t) :=
  rfl

omit [SampleableType C] in
/-- As an ordinary verifier: if the check holds of the oracles' answer at the transcript's
challenge, the verdict is the mapped statement at it and the oracles; otherwise it rejects. -/
theorem queryVerifier_verify (s : StmtIn) (o : ∀ i, OStmt i) (tr : (draw C).FullTranscript) :
    (queryVerifier OStmt C query check f).toVerifier.verify (s, o) tr =
      if check s (tr 0) (answerOf OStmt o (query s (tr 0))) then pure (f s (tr 0), o)
      else failure := by
  simp only [OracleVerifier.toVerifier]
  rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl]
  simp only [queryVerifier]
  rw [show (liftM (askInput OStmt (query s (tr.challenges ⟨0, rfl⟩))) :
      OptionT (OracleComp ([]ₒ + ([OStmt]ₒ + [(draw C).Message]ₒ))) _) =
      OptionT.lift (liftM (askInput OStmt (query s (tr.challenges ⟨0, rfl⟩))) :
        OracleComp ([]ₒ + ([OStmt]ₒ + [(draw C).Message]ₒ)) _) from
    (OracleComp.monadLift_liftM_OptionT _).symm]
  rw [simulateQ_optionT_bind_elimM, OptionT.run_lift, simulateQ_bind, simulateQ_askInput,
    pure_bind, simulateQ_pure]
  simp only [Option.elimM, pure_bind, Option.elim]
  show OptionT.mk ((Option.map fun stmtOut ↦ (stmtOut, o)) <$>
      simulateQ (OracleInterface.simOracle2 []ₒ o tr.messages)
        (if check s (tr 0) (answerOf OStmt o (query s (tr 0))) = true then
          (pure (f s (tr 0)) : OptionT (OracleComp ([]ₒ + ([OStmt]ₒ + [(draw C).Message]ₒ))) _)
          else failure).run) = _
  by_cases h : check s (tr 0) (answerOf OStmt o (query s (tr 0))) = true
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- The query verifier is a check followed by a verdict, as data: the check reads the statement,
the challenge and the oracles' answer. -/
def queryGuarded : (queryVerifier OStmt C query check f).toVerifier.GuardedForm where
  check := fun p tr ↦ check p.1 (tr 0) (answerOf OStmt p.2 (query p.1 (tr 0)))
  out := fun p tr ↦ (f p.1 (tr 0), p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ queryVerifier_verify OStmt C query check f s o tr

omit [∀ i, OracleInterface (OStmt i)] [SampleableType C] in
/-- For every challenge, some run of the prover receives it and outputs the mapped statement at
it, with the oracles and the witness. -/
theorem exists_mem_support_sampleProver_run (s : StmtIn) (o : ∀ i, OStmt i) (w : W) (c : C) :
    ∃ pr ∈ support ((sampleProver OStmt C f).run (s, o) w),
      pr.1 0 = c ∧ pr.2 = ((f s c, o), w) := by
  have h0 : (draw C).dir 0 = .V_to_P := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_one,
    Prover.processRound_of_dir_eq_V_to_P 0 h0]
  simp only [ChallengeIdx, Nat.reduceAdd, Challenge, Fin.reduceLast, sampleProver, Fin.isValue,
    Fin.castSucc_zero, Fin.succ_zero_eq_one, id_eq, HasQuery.instOfMonadLift_query,
    toPFunctor_emptySpec, liftM_pure, bind_pure_comp, map_pure, pure_bind, Functor.map_map,
    support_map, Set.mem_image]
  refine ⟨_, ⟨c, ?_, rfl⟩, rfl, rfl⟩
  apply mem_support_query

variable {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)} {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}

/-- Perfect completeness, whenever on the input relation every challenge passes the check and
`f` carries the relation into the output relation. -/
theorem sampleQuery_complete
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ∀ c,
      check s c (answerOf OStmt o (query s c)) = true ∧ ((f s c, o), w) ∈ relOut)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (sampleQuery OStmt C query check f).red.perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _
    (queryGuarded OStmt C query check f) (s, o) witIn hx
  have hout := sampleProver_run_support OStmt C f s o witIn pr hpr
  have hc : (queryGuarded OStmt C query check f).check (s, o) pr.1 = true :=
    (h s o witIn hIn (pr.1 0)).1
  rw [ite_eq_left hc]
  refine ⟨_, rfl, ?_, congrArg Prod.fst hout⟩
  show ((f s (pr.1 0), o), pr.2.2) ∈ relOut
  rw [congrArg Prod.snd hout]
  exact (h s o witIn hIn (pr.1 0)).2

/-- The completeness half. -/
def sampleQueryComplete
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ∀ c,
      check s c (answerOf OStmt o (query s c)) = true ∧ ((f s c, o), w) ∈ relOut) :
    Complete (sampleQuery OStmt C query check f) relIn relOut where
  guarded := queryGuarded OStmt C query check f
  complete := sampleQuery_complete OStmt C query check f h

/-- A check that some challenge fails on the input relation breaks perfect completeness: the
prover's run that receives that challenge is rejected. -/
theorem sampleQuery_not_complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) {s : StmtIn} {o : ∀ i, OStmt i} {w : W}
    (hin : ((s, o), w) ∈ relIn) (c : C) (hc : check s c (answerOf OStmt o (query s c)) = false) :
    ¬ (sampleQuery OStmt C query check f).red.perfectCompleteness init impl relIn relOut := by
  obtain ⟨pr, hpr, hc0, -⟩ := exists_mem_support_sampleProver_run OStmt C f s o w c
  refine Reduction.not_perfectCompleteness_of_reject' _ (queryGuarded OStmt C query check f) init
    impl relIn relOut hin ⟨pr, hpr, Or.inl ?_⟩
  show check s (pr.1 0) (answerOf OStmt o (query s (pr.1 0))) = false
  rw [hc0]
  exact hc

/-! ## Knowledge soundness -/

variable [Finite C] {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function of a checked query: the input relation before the challenge;
after it, that the check holds of the oracles' answer and the mapped statement is in the output
relation. -/
def queryStateFunction :
    (queryVerifier OStmt C query check f).toVerifier.KnowledgeStateFunction init impl relIn relOut
      (keepExtractor _ W (draw C)) where
  toFun := fun m stmt tr w ↦
    if h0 : m.val = 0 then (stmt, w) ∈ relIn
    else check stmt.1 (tr ⟨0, by omega⟩)
        (answerOf OStmt stmt.2 (query stmt.1 (tr ⟨0, by omega⟩))) = true ∧
      ((f stmt.1 (tr ⟨0, by omega⟩), stmt.2), w) ∈ relOut
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m hm ↦ nomatch hm
  toFun_full := fun stmt tr _ hpos ↦
    Verifier.GuardedForm.of_probEvent_pos (queryGuarded OStmt C query check f) init impl stmt tr _
      hpos

/-- A bad challenge: some witness fails the input relation at the statement, passes the check
and meets the output relation at the mapped statement. -/
def badQuery (s : StmtIn) (o : ∀ i, OStmt i) (c : C) : Prop :=
  ∃ w, ((s, o), w) ∉ relIn ∧ check s c (answerOf OStmt o (query s c)) = true ∧
    ((f s c, o), w) ∈ relOut

/-- Round-by-round knowledge soundness of a checked query at `N / |C|`, when every statement has
at most `N` bad challenges. -/
theorem sampleQuery_rbr (N : ℕ)
    (hN : ∀ s o,
      Nat.card {c // badQuery OStmt C query check f (relIn := relIn) (relOut := relOut) s o c} ≤
        N) :
    (queryVerifier OStmt C query check f).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      relIn relOut (fun _ ↦ W) (keepExtractor _ W (draw C))
      (queryStateFunction OStmt C query check f init impl)
      (drawError C ((N : ℝ≥0) / (Nat.card C : ℝ≥0))) := by
  have := Fintype.ofFinite C
  classical
  intro stmtIn i tr
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨⟨i, hi⟩, hdir⟩ := i
  have hi0 : i = 0 := by omega
  subst hi0
  show _ ≤ (((N : ℝ≥0) / (Nat.card C : ℝ≥0) : ℝ≥0) : ℝ≥0∞)
  rw [Nat.card_eq_fintype_card, ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
    ENNReal.coe_natCast, ENNReal.coe_natCast]
  refine le_trans (prEvent_mono _ _ _ ?_)
    ((SampleableType.prEvent_uniformSample_le_div_iff
      (p := fun c ↦ badQuery OStmt C query check f (relIn := relIn) (relOut := relOut) s o c)).mpr
      ((natCard_subtype_eq_card_filter _).symm.trans_le (hN s o)))
  rintro c ⟨w, hin, hc, hout⟩
  exact ⟨w, hin, hc, hout⟩

/-- The security half of a checked query at `N / |C|`, with the extractor that keeps the
witness, when every statement has at most `N` bad challenges. -/
def sampleQuerySecurity (N : ℕ)
    (hN : ∀ s o,
      Nat.card {c // badQuery OStmt C query check f (relIn := relIn) (relOut := relOut) s o c} ≤
        N) :
    Security (sampleQuery OStmt C query check f) relIn relOut
      (drawError C ((N : ℝ≥0) / (Nat.card C : ℝ≥0))) where
  guarded := queryGuarded OStmt C query check f
  witMid := fun _ ↦ W
  extractor := keepExtractor _ W (draw C)
  kSF := queryStateFunction OStmt C query check f
  rbr := fun init impl ↦ sampleQuery_rbr OStmt C query check f init impl N hN

omit [Finite C] in
/-- The checked query is not knowledge sound below error one, whatever the extractor and the
state function, from a statement with no witness at which every challenge passes the check into
the output relation. -/
theorem sampleQuery_not_rbr {WitMid : Fin 2 → Type}
    {E : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (StmtIn × ∀ i, OStmt i) W W
      (draw C) WitMid}
    {kSF : (queryVerifier OStmt C query check f).toVerifier.KnowledgeStateFunction init impl relIn
      relOut E}
    {ε : (draw C).ChallengeIdx → ℝ≥0}
    (h : (queryVerifier OStmt C query check f).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init
      impl relIn relOut WitMid E kSF ε)
    (s : StmtIn) (o : ∀ i, OStmt i) (hin : ∀ w, ((s, o), w) ∉ relIn) (w : W)
    (hesc : ∀ c, check s c (answerOf OStmt o (query s c)) = true ∧ ((f s c, o), w) ∈ relOut) :
    1 ≤ ε ⟨0, rfl⟩ :=
  Verifier.not_rbr_zero h ⟨0, rfl⟩ rfl (fun j hj ↦ absurd hj (by have := j.isLt; omega))
    (s, o) (fun w' hw' ↦ hin w' hw') (default : (draw C).Transcript 0) fun c ↦
      ⟨Transcript.concat c (default : (draw C).Transcript 0), rfl, w,
        Verifier.GuardedForm.probEvent_pos_of_check (queryGuarded OStmt C query check f) init impl
          (s, o) _ (fun t ↦ (t, w) ∈ relOut) (hesc c).1 (hesc c).2⟩

end Component

end
end LeanerVM.Protocol
