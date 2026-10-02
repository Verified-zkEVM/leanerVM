/-
  LeanerVM.Protocol.ToArkLib.SampleChallenge

  The component with one round, a verifier challenge: the verifier checks the statement, draws
  the challenge and maps the statement by it, leaving the oracles and the witness alone. Its
  completeness proof. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.GuardedVerdict
public import LeanerVM.Protocol.ToArkLib.KeepOracles
public import LeanerVM.Protocol.ToArkLib.Schedule
public import LeanerVM.Protocol.ToArkLib.Refutation

/-!
# The sample-challenge component

`Component.sampleChallenge OStmt C check f` is the one-challenge schedule `draw C`: the verifier
rejects unless the input statement `s` passes `check`, draws `c : C`, and outputs `f s c` with
the same oracles and the same witness. It is the shape of every step that records a random
value in the statement: a batching combiner, a fingerprint, an evaluation point, the challenge
of a sumcheck round once its polynomial has been received. The check is on the statement
alone, so a check that reads a message checks the message the previous component recorded in
the statement. With `check := fun _ ↦ true` the verifier is pure.

Completeness (`sampleChallengeComplete`): on the input relation the check passes and `f`
carries the relation into the output relation at every challenge. Knowledge soundness is the
step's own, since it depends on what `f` records.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

@[expose] public section

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  {StmtIn StmtOut W : Type} (C : Type) [SampleableType C]
  (check : StmtIn → Bool) (f : StmtIn → C → StmtOut)

/-- The prover: receives the challenge, maps the statement, keeps the oracles and the
witness. -/
def sampleProver : OracleProver []ₒ StmtIn OStmt W StmtOut OStmt W (draw C) where
  PrvState
    | ⟨0, _⟩ => (StmtIn × ∀ i, OStmt i) × W
    | _ => ((StmtIn × ∀ i, OStmt i) × W) × C
  input := _root_.id
  sendMessage | ⟨0, h⟩ => nomatch h
  receiveChallenge | ⟨0, _⟩ => fun st ↦ pure fun c ↦ (st, c)
  output := fun st ↦ pure ((f st.1.1.1 st.2, st.1.1.2), st.1.2)

/-- The verifier: rejects unless the statement passes the check, maps the statement by the
challenge, keeps the oracles. -/
def sampleVerifier : OracleVerifier []ₒ StmtIn OStmt StmtOut OStmt (draw C) where
  verify := fun s chals ↦ if check s then pure (f s (chals ⟨0, rfl⟩)) else failure
  outputOracle := .inl (keepOracles OStmt (draw C))

/-- The sample-challenge component. -/
def sampleChallenge : Def StmtIn OStmt W StmtOut OStmt W (draw C) where
  red := ⟨sampleProver OStmt C f, sampleVerifier OStmt C check f⟩

omit [SampleableType C] in
/-- As an ordinary verifier: if the statement passes the check, the verdict is the mapped
statement at the transcript's challenge and the oracles; otherwise it rejects. -/
theorem sampleVerifier_verify (s : StmtIn) (o : ∀ i, OStmt i) (tr : (draw C).FullTranscript) :
    (sampleVerifier OStmt C check f).toVerifier.verify (s, o) tr =
      if check s then pure (f s (tr 0), o) else failure := by
  simp only [OracleVerifier.toVerifier]
  rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl]
  simp only [sampleVerifier]
  by_cases h : check s = true
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- The sample verifier is a check followed by a verdict, as data. -/
def sampleGuarded : (sampleVerifier OStmt C check f).toVerifier.GuardedForm where
  check := fun p _ ↦ check p.1
  out := fun p tr ↦ (f p.1 (tr 0), p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ sampleVerifier_verify OStmt C check f s o tr

omit [∀ i, OracleInterface (OStmt i)] [SampleableType C] in
/-- In every run of the prover, the output is the mapped statement at the transcript's
challenge, with the oracles and the witness. -/
private theorem sampleProver_run_support (s : StmtIn) (o : ∀ i, OStmt i) (w : W)
    (pr : (draw C).FullTranscript × (StmtOut × ∀ i, OStmt i) × W)
    (hpr : pr ∈ support ((sampleProver OStmt C f).run (s, o) w)) :
    pr.2 = ((f s (pr.1 0), o), w) := by
  have h0 : (draw C).dir 0 = .V_to_P := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_one,
    Prover.processRound_of_dir_eq_V_to_P 0 h0] at hpr
  simp only [ChallengeIdx, Nat.reduceAdd, Challenge, Fin.reduceLast, sampleProver, Fin.isValue,
    Fin.castSucc_zero, Fin.succ_zero_eq_one, id_eq, HasQuery.instOfMonadLift_query,
    toPFunctor_emptySpec, liftM_pure, bind_pure_comp, map_pure, pure_bind, Functor.map_map,
    support_map, Set.mem_image] at hpr
  obtain ⟨c, -, rfl⟩ := hpr
  rfl

variable {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)} {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}

/-- Perfect completeness, whenever on the input relation the check passes and `f` carries the
relation into the output relation at every challenge. -/
theorem sampleChallenge_complete
    (h : ∀ s o w, ((s, o), w) ∈ relIn → check s = true ∧ ∀ c, ((f s c, o), w) ∈ relOut)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (sampleChallenge OStmt C check f).red.perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _
    (sampleGuarded OStmt C check f) (s, o) witIn hx
  have hout := sampleProver_run_support OStmt C f s o witIn pr hpr
  have hc : (sampleGuarded OStmt C check f).check (s, o) pr.1 = true := (h s o witIn hIn).1
  rw [ite_eq_left hc]
  refine ⟨_, rfl, ?_, congrArg Prod.fst hout⟩
  show ((f s (pr.1 0), o), pr.2.2) ∈ relOut
  rw [congrArg Prod.snd hout]
  exact (h s o witIn hIn).2 (pr.1 0)

/-- The completeness half. -/
def sampleChallengeComplete
    (h : ∀ s o w, ((s, o), w) ∈ relIn → check s = true ∧ ∀ c, ((f s c, o), w) ∈ relOut) :
    Complete (sampleChallenge OStmt C check f) relIn relOut where
  guarded := sampleGuarded OStmt C check f
  complete := sampleChallenge_complete OStmt C check f h

/-! ## Knowledge soundness -/

variable [Fintype C] {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function of a checked challenge: the input relation before the challenge;
after it, that the check passed and the mapped statement is in the output relation. -/
def sampleStateFunction :
    (sampleVerifier OStmt C check f).toVerifier.KnowledgeStateFunction init impl relIn relOut
      (keepExtractor _ W (draw C)) where
  toFun := fun m stmt tr w ↦
    if h0 : m.val = 0 then (stmt, w) ∈ relIn
    else check stmt.1 = true ∧ ((f stmt.1 (tr ⟨0, by omega⟩), stmt.2), w) ∈ relOut
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m hm ↦ nomatch hm
  toFun_full := fun stmt tr w hpos ↦
    Verifier.GuardedForm.of_probEvent_pos (sampleGuarded OStmt C check f) init impl stmt tr _ hpos

/-- A bad challenge: some witness fails the input relation at the statement and meets the output
relation at the mapped statement. -/
def badChallenge (s : StmtIn) (o : ∀ i, OStmt i) (c : C) : Prop :=
  ∃ w, ((s, o), w) ∉ relIn ∧ ((f s c, o), w) ∈ relOut

omit [∀ i, OracleInterface (OStmt i)] [SampleableType C] in
open scoped Classical in
/-- With a trivial witness, the bad challenges are those carrying a statement outside the input
relation into the output relation. -/
theorem card_filter_badChallenge_le_of_unit {relIn : Set ((StmtIn × ∀ i, OStmt i) × Unit)}
    {relOut : Set ((StmtOut × ∀ i, OStmt i) × Unit)} (N : ℕ) (s : StmtIn) (o : ∀ i, OStmt i)
    (h : ((s, o), ()) ∉ relIn →
      (Finset.univ.filter fun c ↦ ((f s c, o), ()) ∈ relOut).card ≤ N) :
    (Finset.univ.filter fun c ↦ badChallenge OStmt C f (relIn := relIn) (relOut := relOut)
      s o c).card ≤ N := by
  by_cases hin : ((s, o), ()) ∈ relIn
  · refine le_trans (le_of_eq ?_) (Nat.zero_le N)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro c - ⟨w, hw, -⟩
    exact hw hin
  · refine (Finset.card_le_card fun c hc ↦ ?_).trans (h hin)
    rw [Finset.mem_filter] at hc ⊢
    obtain ⟨-, w, -, hw⟩ := hc
    exact ⟨Finset.mem_univ _, hw⟩

open scoped Classical in
/-- Round-by-round knowledge soundness of a checked challenge at `N / |C|`, when a statement
passing the check has at most `N` bad challenges. -/
theorem sample_rbr (N : ℕ)
    (hN : ∀ s o, check s = true →
      (Finset.univ.filter fun c ↦ badChallenge OStmt C f (relIn := relIn) (relOut := relOut)
        s o c).card ≤ N) :
    (sampleVerifier OStmt C check f).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      relIn relOut (fun _ ↦ W) (keepExtractor _ W (draw C))
      (sampleStateFunction OStmt C check f init impl)
      (drawError C ((N : ℝ≥0) / (Fintype.card C : ℝ≥0))) := by
  intro stmtIn i tr
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨⟨i, hi⟩, hdir⟩ := i
  have hi0 : i = 0 := by omega
  subst hi0
  show _ ≤ (((N : ℝ≥0) / (Fintype.card C : ℝ≥0) : ℝ≥0) : ℝ≥0∞)
  rw [ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_natCast,
    ENNReal.coe_natCast]
  by_cases hc : check s = true
  · refine le_trans (prEvent_mono _ _ _ ?_)
      ((SampleableType.prEvent_uniformSample_le_div_iff
        (p := fun c ↦ badChallenge OStmt C f (relIn := relIn) (relOut := relOut) s o c)).mpr
        (hN s o hc))
    rintro c ⟨w, hin, -, hout⟩
    exact ⟨w, hin, hout⟩
  · refine le_trans (le_of_eq ?_) zero_le
    refine (OracleComp.prEvent_eq_zero_iff _ _).mpr ?_
    rintro c - ⟨w, -, hcheck, -⟩
    exact hc hcheck

open scoped Classical in
/-- The security half of a checked challenge at `N / |C|`, with the extractor that keeps the
witness, when a statement passing the check has at most `N` bad challenges. -/
noncomputable def sampleChallengeSecurity (N : ℕ)
    (hN : ∀ s o, check s = true →
      (Finset.univ.filter fun c ↦ badChallenge OStmt C f (relIn := relIn) (relOut := relOut)
        s o c).card ≤ N) :
    Security (sampleChallenge OStmt C check f) relIn relOut
      (drawError C ((N : ℝ≥0) / (Fintype.card C : ℝ≥0))) where
  guarded := sampleGuarded OStmt C check f
  witMid := fun _ ↦ W
  extractor := keepExtractor _ W (draw C)
  kSF := sampleStateFunction OStmt C check f
  rbr := fun init impl ↦ sample_rbr OStmt C check f init impl N hN

omit [Fintype C] in
/-- The challenge is not knowledge sound below error one for its state function from a statement
with no witness that passes the check and that every challenge carries into the output
relation. -/
theorem sampleChallenge_not_rbr {ε : (draw C).ChallengeIdx → ℝ≥0}
    (h : (sampleVerifier OStmt C check f).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      relIn relOut (fun _ ↦ W) (keepExtractor _ W (draw C))
      (sampleStateFunction OStmt C check f init impl) ε)
    (s : StmtIn) (o : ∀ i, OStmt i) (hin : ∀ w, ((s, o), w) ∉ relIn) (hc : check s = true)
    (w : W) (hesc : ∀ c, ((f s c, o), w) ∈ relOut) : 1 ≤ ε ⟨0, rfl⟩ :=
  Verifier.not_rbr_of_escape h ⟨0, rfl⟩ (s, o) (default : (draw C).Transcript 0)
    (fun w' hw' ↦ hin w' hw') fun c ↦ ⟨w, hc, hesc c⟩

end Component

end
end LeanerVM.Protocol
