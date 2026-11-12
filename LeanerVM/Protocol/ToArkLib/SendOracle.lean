/-
  LeanerVM.Protocol.ToArkLib.SendOracle

  The component whose one message becomes the one oracle every later component queries, with
  its completeness and its zero-error knowledge soundness: ArkLib's one-message
  `SendSingleWitness.Adapter` at the identity, packaged as a component.
-/

module

public import ArkLib.OracleReduction.Security.GuardedRoundByRound
public import ArkLib.ProofSystem.Component.SendWitness
public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.ExtractIn
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
abbrev sendSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[M]⟩

/-- The one message is the one output oracle. -/
def sendEmbedding : OracleOutputEmbedding NoOracle (sendSpec M).Message (OneOracle M) where
  embed := ⟨fun _ ↦ Sum.inr ⟨0, rfl⟩, fun a b _ ↦ Subsingleton.elim a b⟩
  hEq := fun _ ↦ rfl
  outputInterface_heq := fun _ ↦ HEq.rfl

/-- The one-message stage: the statement kept, the witness sent as it is and exposed as the one
oracle. -/
def sendAdapter : SendSingleWitness.Adapter []ₒ S NoOracle M S (OneOracle M) M where
  stmtOut := id
  encode := id
  decode := id
  outputOracle := .inl (sendEmbedding M)

/-- The verifier: keeps the statement, exposes the message. -/
def sendVerifier : OracleVerifier []ₒ S NoOracle S (OneOracle M) (sendSpec M) :=
  (sendAdapter S M).oracleVerifier

/-- The send-oracle component: the prover sends the witness, no challenge. -/
def sendOracle : Def S NoOracle M S (OneOracle M) Unit (sendSpec M) where
  red := ⟨(sendAdapter S M).oracleProver, sendVerifier S M⟩

variable {S M}

/-- The input relation read on the oracle: `((s, oracle), ())` is in it when `(s, oracle 0)` was
in `rel`. -/
def sendOracle_relOut (rel : Set ((S × ∀ i, NoOracle i) × M)) :
    Set ((S × ∀ i, OneOracle M i) × Unit) :=
  {p | ((p.1.1, fun i ↦ i.elim0), p.1.2 0) ∈ rel}

/-- The send verifier is pure, as data. -/
def sendVerifierPure : (sendVerifier S M).toVerifier.PureForm where
  verify := fun p tr ↦ (p.1, fun _ ↦ tr 0)
  verify_eq := (sendAdapter S M).verifier_run

/-- The output relation read back on the message is the input relation. -/
private theorem send_relOut_iff (rel : Set ((S × ∀ i, NoOracle i) × M)) (s : S × ∀ i, NoOracle i)
    (w : M) : ((sendAdapter S M).output s w, ()) ∈ sendOracle_relOut rel ↔ (s, w) ∈ rel := by
  obtain ⟨s, o⟩ := s
  rw [noOracle_eq o (fun i ↦ i.elim0)]
  rfl

/-- The completeness half: sending a witness of `rel` lands in `rel` read on the oracle. -/
def sendOracleComplete (rel : Set ((S × ∀ i, NoOracle i) × M)) :
    Complete (sendOracle S M) rel (sendOracle_relOut rel) where
  guarded := (sendVerifierPure (S := S) (M := M)).toGuardedForm
  complete := fun init impl ↦ (sendAdapter S M).perfectCompleteness init impl rel _
    fun s w ↦ by exact (send_relOut_iff rel s w).mpr

/-! ## Knowledge soundness -/

/-- The extractor reads the message. The shared oracle is written `OracleSpec.emptySpec.{0, 0}`
rather than `[]ₒ` to pin a universe `Extractor.RoundByRound` leaves free. -/
def sendExtractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (S × ∀ i, NoOracle i) M
    Unit (sendSpec M) (fun _ ↦ M) :=
  SendSingleWitness.transcriptExtractor _ id

omit [OracleInterface M] in
/-- Its fold from round `1` is the message. -/
theorem sendExtractor_readsFirst :
    Extractor.RoundByRound.ReadsFirst (sendExtractor (S := S) (M := M)) :=
  fun _ _ _ _ ↦ HEq.rfl

/-- The security half, at error zero, with the extractor that reads the message. -/
def sendOracleSecurity (rel : Set ((S × ∀ i, NoOracle i) × M)) :
    Security (sendOracle S M) rel (sendOracle_relOut rel) (fun _ ↦ 0) where
  guarded := (sendVerifierPure (S := S) (M := M)).toGuardedForm
  witMid := fun _ ↦ M
  extractor := sendExtractor
  kSF := fun init impl ↦ (sendAdapter S M).knowledgeStateFunction init impl rel _
    fun s w ↦ by exact (send_relOut_iff rel s w).mp
  rbr := fun init impl ↦ (sendAdapter S M).rbrKnowledgeSoundnessWith init impl rel _ _

end Component

end
end LeanerVM.Protocol
