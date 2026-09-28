/-
  LeanerVM.Protocol.ToArkLib.SendOracle

  The component whose one message becomes the one oracle every later component queries, with
  its completeness and its zero-error knowledge soundness. Candidate for ArkLib, whose
  `SendSingleWitness` has the same shape with its completeness admitted.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.Oracles

/-!
# The send-oracle component

`Component.sendOracle S M` starts from a statement of type `S` and no oracle, with the witness
an `M`; the prover sends the witness as its one message, the verifier keeps the statement and
exposes the message as the one oracle. Its output relation `sendOracle_relOut rel` is the input
relation `rel` read on the oracle instead of the witness, so the oracle is pinned to the
witness of record. There is no challenge: the knowledge error is zero, and the extractor reads
the message.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Component

variable (S M : Type) [OracleInterface M]

/-- The schedule: one prover message of type `M`. -/
@[reducible]
def sendSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[M]⟩

/-- The prover: sends the witness, keeps the statement. -/
def sendProver : OracleProver []ₒ S NoOracle M S (OneOracle M) Unit (sendSpec M) where
  PrvState := fun _ ↦ S × M
  input := fun p ↦ (p.1.1, p.2)
  sendMessage | ⟨0, _⟩ => fun st ↦ pure (st.2, st)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st ↦ pure ((st.1, fun _ ↦ st.2), ())

/-- The one message is the one output oracle. -/
def sendEmbedding : OracleOutputEmbedding NoOracle (sendSpec M).Message (OneOracle M) where
  embed := ⟨fun _ ↦ Sum.inr ⟨0, rfl⟩, fun a b _ ↦ Subsingleton.elim a b⟩
  hEq := fun _ ↦ rfl
  outputInterface_heq := fun _ ↦ HEq.rfl

/-- The verifier: keeps the statement, exposes the message. -/
def sendVerifier : OracleVerifier []ₒ S NoOracle S (OneOracle M) (sendSpec M) where
  verify := fun s _ ↦ pure s
  outputOracle := .inl (sendEmbedding M)

/-- The send-oracle component: no challenge, error zero. -/
def sendOracle : Def S NoOracle M S (OneOracle M) Unit where
  n := 1
  pSpec := sendSpec M
  red := ⟨sendProver S M, sendVerifier S M⟩
  err := fun _ ↦ 0

variable {S M}

/-- The input relation read on the oracle: `((s, oracle), ())` is in it when `(s, oracle 0)` was
in `rel`. -/
def sendOracle_relOut (rel : Set ((S × ∀ i, NoOracle i) × M)) :
    Set ((S × ∀ i, OneOracle M i) × Unit) :=
  {p | ((p.1.1, fun i ↦ i.elim0), p.1.2 0) ∈ rel}

/-! ## Completeness -/

/-- The prover's output makes no oracle query. -/
theorem sendOracle_outputPure : (sendOracle S M).red.prover.OutputIsPure := ⟨_, fun _ ↦ rfl⟩

/-- The output oracle is the message. -/
theorem send_materializeOutput (challenges : (sendSpec M).Challenges) (o : ∀ i, NoOracle i)
    (messages : (sendSpec M).Messages) :
    (sendVerifier S M).materializeOutput challenges o messages = fun _ ↦ messages ⟨0, rfl⟩ := by
  unfold OracleVerifier.materializeOutput sendVerifier
  change OracleVerifier.materializeOutputOracle (Sum.inl (sendEmbedding M)) challenges o
    messages = _
  simp only [OracleVerifier.materializeOutputOracle]
  funext i
  fin_cases i
  rfl

/-- As an ordinary verifier, the send verifier returns the statement and the message. -/
theorem sendVerifier_toVerifier_run (s : S) (o : ∀ i, NoOracle i)
    (tr : (sendSpec M).FullTranscript) :
    (sendVerifier S M).toVerifier.run (s, o) tr = pure (s, fun _ ↦ tr 0) := by
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [send_materializeOutput]
  rfl

/-- The send verifier is pure, as data. -/
def sendVerifierPure : (sendVerifier S M).toVerifier.PureForm where
  verify := fun p tr ↦ (p.1, fun _ ↦ tr 0)
  verify_eq := fun ⟨s, o⟩ tr ↦ sendVerifier_toVerifier_run s o tr

/-- Perfect completeness: sending a witness of `rel` lands in `rel` read on the oracle. -/
theorem sendOracle_complete (rel : Set ((S × ∀ i, NoOracle i) × M)) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (sendOracle S M).red.perfectCompleteness init impl rel (sendOracle_relOut rel) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  have hrun : ((sendOracle S M).red.toReduction.run (s, o) witIn).run =
      pure (some (((show (sendOracle S M).pSpec.FullTranscript from
        ProtocolSpec.Transcript.concat (m := 0) witIn (default : (sendSpec M).Transcript 0)),
        (s, fun _ ↦ witIn), ()), (s, fun _ ↦ witIn))) := rfl
  rw [hrun, support_pure, Set.mem_singleton_iff] at hx
  rw [noOracle_eq o (fun i ↦ i.elim0)] at hIn
  exact ⟨_, hx, hIn, rfl⟩

/-- The completeness half. -/
def sendOracleComplete (rel : Set ((S × ∀ i, NoOracle i) × M)) :
    Complete (sendOracle S M) rel (sendOracle_relOut rel) where
  outputPure := sendOracle_outputPure
  guarded := (sendVerifierPure (S := S) (M := M)).toGuardedForm
  complete := sendOracle_complete rel

/-! ## Knowledge soundness -/

/-- The intermediate witness at every round: an `M`. -/
abbrev sendWitMid (M : Type) : Fin 2 → Type := fun _ ↦ M

/-- The extractor reads the message. The shared oracle is written `OracleSpec.emptySpec.{0, 0}`
rather than `[]ₒ` to pin a universe `Extractor.RoundByRound` leaves free. -/
def sendExtractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (S × ∀ i, NoOracle i) M
    Unit (sendSpec M) (sendWitMid M) where
  eqIn := rfl
  extractMid := fun m _ tr _ ↦ tr ⟨0, Nat.succ_pos m.val⟩
  extractOut := fun _ tr _ ↦ tr 0

/-- The run of the send verifier, at the transcript type a state function sees. -/
theorem sendVerifier_toVerifier_run' (s : S) (o : ∀ i, NoOracle i)
    (tr : (sendSpec M).Transcript (Fin.last 1)) :
    Verifier.run (s, o) tr (sendVerifier S M).toVerifier =
      pure (s, fun _ ↦ tr ⟨0, Nat.succ_pos 0⟩) :=
  sendVerifier_toVerifier_run s o tr

variable (rel : Set ((S × ∀ i, NoOracle i) × M))
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function: before the message, `rel` of the intermediate witness; after
it, `rel` of the message. -/
def sendStateFunction :
    (sendVerifier S M).toVerifier.KnowledgeStateFunction init impl rel (sendOracle_relOut rel)
      (sendExtractor (S := S) (M := M)) where
  toFun := fun m stmt tr w ↦
    if h : m.val = 0 then (stmt, w) ∈ rel else (stmt, tr ⟨0, Nat.pos_of_ne_zero h⟩) ∈ rel
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m _ stmt tr msg w h ↦ by
    have hm : m.val = 0 := by omega
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, dite_false] at h
    simp only [Fin.val_castSucc, hm, dite_true]
    exact h
  toFun_full := fun stmt tr _ h ↦ by
    obtain ⟨s, o⟩ := stmt
    simp only [Fin.val_last, one_ne_zero, dite_false]
    rw [sendVerifier_toVerifier_run'] at h
    change Pr[_ | OptionT.mk (do let st ← init; (simulateQ impl
      (OptionT.run (pure (s, fun _ ↦ tr ⟨0, Nat.succ_pos 0⟩)))).run' st)] > 0 at h
    rw [OptionT.run_pure, simulateQ_pure] at h
    obtain ⟨y, hy, hp⟩ := probEvent_pos_iff.mp h
    simp [OptionT.mem_support_iff] at hy
    obtain ⟨_, rfl⟩ := hy
    rw [noOracle_eq o (fun i ↦ i.elim0)]
    exact hp

/-- Round-by-round knowledge soundness at error zero: no challenge, the extractor reads the
message. -/
theorem sendOracle_rbr :
    (sendVerifier S M).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl rel
      (sendOracle_relOut rel) (sendWitMid M) sendExtractor (sendStateFunction rel init impl)
      (fun _ ↦ 0) :=
  fun _ i ↦ (IsEmpty.false i).elim

/-- The security half, with the extractor that reads the message. -/
def sendOracleSecurity : Security (sendOracle S M) rel (sendOracle_relOut rel) where
  toComplete := sendOracleComplete rel
  witMid := sendWitMid M
  extractor := sendExtractor
  kSF := sendStateFunction rel
  rbr := sendOracle_rbr rel

end Component

end
end LeanerVM.Protocol
