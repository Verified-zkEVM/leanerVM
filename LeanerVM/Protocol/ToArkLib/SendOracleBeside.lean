/-
  LeanerVM.Protocol.ToArkLib.SendOracleBeside

  The component whose one message becomes a new oracle beside the input oracles, with its
  completeness. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.SendOracle
public import LeanerVM.Protocol.ToArkLib.Schedule

/-!
# The send-oracle-beside component

`Component.sendOracleBeside OStmt M honest out` has the one-message schedule `sayO M`: the
prover sends `honest s o w`, computed from the statement, the oracles' contents and the witness,
and the verifier maps the statement by `out` and exposes the input oracles *and* the message as
oracles: the family `besideOracles OStmt M` on `ι ⊕ Unit`, the inputs on the left and the message
on the right. `Component.sendOracle` is the case of no input oracle.

It is the shape of a commitment made while an earlier commitment is still to be read: one level of
an interleaved-code opening commits the next level's word and then reads the previous one at the
sampled positions (`Component.queryRecord`, which hands on the new word only).

Completeness (`sendOracleBesideComplete`): on the input relation the output relation holds of
the output statement, the oracles beside the honest message, and the witness. Security
(`sendOracleBesideSecurity`): no challenge, no error, whenever the output relation on the oracles
beside any message implies the input relation.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  (M : Type) [OracleInterface M]

/-- One prover message of type `M`, to be queried through `M`'s own oracle interface. It is
`say M` in all but name: a definition, not an abbreviation, so that instance search does not take
it for `say M`, whose message interface is the trivial one. -/
def sayO : ProtocolSpec 1 := ⟨fun _ ↦ .P_to_V, !v[M]⟩

/-- The message of `sayO M` is queried as `M` is. -/
instance instOracleInterfaceSayO : ∀ i, OracleInterface ((sayO M).Message i)
  | ⟨0, _⟩ => inferInstanceAs (OracleInterface M)

instance instSampleableTypeSayO : ∀ i, SampleableType ((sayO M).Challenge i)
  | ⟨0, h⟩ => nomatch h

/-- The input oracles with the message beside them. -/
abbrev besideOracles : ι ⊕ Unit → Type := Sum.elim OStmt fun _ ↦ M

instance besideInterface : ∀ i, OracleInterface (besideOracles OStmt M i)
  | .inl j => inferInstanceAs (OracleInterface (OStmt j))
  | .inr _ => inferInstanceAs (OracleInterface M)

/-- The oracle data of the output: the inputs, and the message beside them. -/
def besideData (o : ∀ i, OStmt i) (m : M) : ∀ i, besideOracles OStmt M i
  | .inl j => o j
  | .inr _ => m

/-- The output-oracle description: the inputs stay, and the one message is the new oracle. -/
def besideEmbedding :
    OracleOutputEmbedding OStmt (sayO M).Message (besideOracles OStmt M) where
  embed := ⟨fun i ↦ i.elim .inl fun _ ↦ .inr ⟨0, rfl⟩, by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;> simp_all⟩
  hEq := fun i ↦ by cases i <;> rfl
  outputInterface_heq := fun i ↦ by cases i <;> exact HEq.rfl

variable {S S' W : Type} (honest : (S × ∀ i, OStmt i) × W → M) (out : S → S')

/-- The prover: sends the message it computes, maps the statement, exposes the oracles and the
message, keeps the witness. -/
def sendBesideProver :
    OracleProver []ₒ S OStmt W S' (besideOracles OStmt M) W (sayO M) where
  PrvState := fun _ ↦ ((S × ∀ i, OStmt i) × W) × M
  input := fun p ↦ (p, honest p)
  sendMessage | ⟨0, _⟩ => fun st ↦ pure (st.2, st)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st ↦ pure ((out st.1.1.1, besideData OStmt M st.1.1.2 st.2), st.1.2)

/-- The verifier: maps the statement, exposes the inputs and the message as oracles. -/
def sendBesideVerifier :
    OracleVerifier []ₒ S OStmt S' (besideOracles OStmt M) (sayO M) where
  verify := fun s _ ↦ pure (out s)
  outputOracle := .inl (besideEmbedding OStmt M)

/-- The send-oracle-beside component. -/
def sendOracleBeside : Def S OStmt W S' (besideOracles OStmt M) W (sayO M) where
  red := ⟨sendBesideProver OStmt M honest out, sendBesideVerifier OStmt M out⟩

/-- The output oracles are the inputs and the message. -/
private theorem sendBeside_materializeOutput (challenges : (sayO M).Challenges) (o : ∀ i, OStmt i)
    (messages : (sayO M).Messages) :
    (sendBesideVerifier OStmt M out).materializeOutput challenges o messages =
      besideData OStmt M o (messages ⟨0, rfl⟩) := by
  unfold OracleVerifier.materializeOutput sendBesideVerifier
  change OracleVerifier.materializeOutputOracle (Sum.inl (besideEmbedding OStmt M)) challenges o
    messages = _
  simp only [OracleVerifier.materializeOutputOracle]
  funext i
  cases i <;> rfl

/-- As an ordinary verifier, the verifier returns the mapped statement, the oracles and the
message. -/
theorem sendBesideVerifier_toVerifier_run (s : S) (o : ∀ i, OStmt i)
    (tr : (sayO M).FullTranscript) :
    (sendBesideVerifier OStmt M out).toVerifier.run (s, o) tr =
      pure (out s, besideData OStmt M o (tr 0)) := by
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [sendBeside_materializeOutput]
  rfl

/-- The verifier is pure, as data. -/
def sendBesideVerifierPure : (sendBesideVerifier OStmt M out).toVerifier.PureForm where
  verify := fun p tr ↦ (out p.1, besideData OStmt M p.2 (tr 0))
  verify_eq := fun ⟨s, o⟩ tr ↦ sendBesideVerifier_toVerifier_run OStmt M out s o tr

variable {relIn : Set ((S × ∀ i, OStmt i) × W)}
  {relOut : Set ((S' × ∀ i, besideOracles OStmt M i) × W)}

/-- Perfect completeness: on the input relation the honest message, beside the inputs, lands in
the output relation. -/
theorem sendOracleBeside_complete
    (h : ∀ s o w, ((s, o), w) ∈ relIn →
      ((out s, besideData OStmt M o (honest ((s, o), w))), w) ∈ relOut)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (sendOracleBeside OStmt M honest out).red.perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _
    (sendBesideVerifierPure OStmt M out).toGuardedForm (s, o) witIn hx
  have hrun : (sendBesideProver OStmt M honest out).run (s, o) witIn =
      pure (show (sayO M).FullTranscript from
        ProtocolSpec.Transcript.concat (m := 0) (honest ((s, o), witIn))
          (default : (sayO M).Transcript 0),
        (out s, besideData OStmt M o (honest ((s, o), witIn))), witIn) := rfl
  have hpr' : pr ∈ support ((sendBesideProver OStmt M honest out).run (s, o) witIn) := hpr
  rw [hrun, support_pure, Set.mem_singleton_iff] at hpr'
  subst hpr'
  have hc : (sendBesideVerifierPure OStmt M out).toGuardedForm.check (s, o)
      (ProtocolSpec.Transcript.concat (m := 0) (honest ((s, o), witIn))
        (default : (sayO M).Transcript 0)) = true := rfl
  rw [ite_eq_left hc]
  exact ⟨_, rfl, h s o witIn hIn, rfl⟩

/-- The completeness half. -/
def sendOracleBesideComplete
    (h : ∀ s o w, ((s, o), w) ∈ relIn →
      ((out s, besideData OStmt M o (honest ((s, o), w))), w) ∈ relOut) :
    Complete (sendOracleBeside OStmt M honest out) relIn relOut where
  guarded := (sendBesideVerifierPure OStmt M out).toGuardedForm
  complete := sendOracleBeside_complete OStmt M honest out h

/-! ## Security -/

section Security

/-- A message queried through its own interface has no challenge. -/
instance instIsEmptySayOChallengeIdx : IsEmpty (sayO M).ChallengeIdx :=
  ⟨fun i ↦ by
    have h := i.2
    change Direction.P_to_V = Direction.V_to_P at h
    cases h⟩

/-- The error of a message: none. -/
def sayOError : (sayO M).ChallengeIdx → ℝ≥0 := fun i ↦ (IsEmpty.false i).elim

variable (h : ∀ s o w m, ((out s, besideData OStmt M o m), w) ∈ relOut → ((s, o), w) ∈ relIn)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function of the send-oracle-beside component: the input relation, before
and after the message. -/
def sendOracleBesideStateFunction :
    (sendBesideVerifier OStmt M out).toVerifier.KnowledgeStateFunction init impl relIn relOut
      (keepExtractor (S × ∀ i, OStmt i) W (sayO M)) where
  toFun := fun _ stmt _ w ↦ (stmt, w) ∈ relIn
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun _ _ _ _ _ _ hw ↦ hw
  toFun_full := fun stmt tr w hpos ↦
    have hv := Verifier.GuardedForm.of_probEvent_pos
      (sendBesideVerifierPure OStmt M out).toGuardedForm init impl stmt tr _ hpos
    h stmt.1 stmt.2 w (tr ⟨0, Nat.zero_lt_one⟩) hv.2

/-- The security half of the send-oracle-beside component: no challenge, no error, whenever
whatever message is sent, the output relation on the oracles beside it implies the input
relation. -/
def sendOracleBesideSecurity :
    Security (sendOracleBeside OStmt M honest out) relIn relOut (sayOError M) where
  guarded := (sendBesideVerifierPure OStmt M out).toGuardedForm
  witMid := fun _ ↦ W
  extractor := keepExtractor (S × ∀ i, OStmt i) W (sayO M)
  kSF := sendOracleBesideStateFunction OStmt M out h
  rbr := fun _ _ _ i ↦ (IsEmpty.false i).elim

end Security

end Component

end
end LeanerVM.Protocol
