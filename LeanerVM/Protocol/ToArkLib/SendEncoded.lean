/-
  LeanerVM.Protocol.ToArkLib.SendEncoded

  The component whose one message, an encoding of the witness, becomes the one oracle, with an
  extractor that decodes the message: its completeness and its zero-error knowledge soundness.
  Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.SendOracle

/-!
# Sending an encoding

`Component.sendEncoded S M W enc` starts from a statement of type `S` and no oracle, with the
witness a `W`; the prover sends `enc w` as its one message and keeps the witness, the verifier keeps
the statement and exposes the message as the one oracle (the verifier of `Component.sendOracle`).
It is the commitment of a word that encodes the witness, when the oracle protocol after it reads
the word and not the witness.

Its output relation is the consumer's. Knowledge soundness (`sendEncodedSecurity`, at error zero)
asks of it only that a message in the output relation can be decoded: `pick s m` returns a witness
of the input relation for the statement `s` whenever `s` and the message `m` are in the output
relation. The extractor runs `pick` on the message. Completeness (`sendEncodedComplete`) asks that
the encoding of a witness of the input relation is in the output relation.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Component

variable (S M W : Type) [OracleInterface M] (enc : W → M)

/-- The prover: sends the encoding of the witness, keeps the statement and the witness. -/
def sendEncodedProver : OracleProver []ₒ S NoOracle W S (OneOracle M) W (sendSpec M) where
  PrvState := fun _ ↦ S × W
  input := fun p ↦ (p.1.1, p.2)
  sendMessage | ⟨0, _⟩ => fun st ↦ pure (enc st.2, st)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st ↦ pure ((st.1, fun _ ↦ enc st.2), st.2)

/-- The send-encoded component: no challenge. -/
def sendEncoded : Def S NoOracle W S (OneOracle M) W (sendSpec M) where
  red := ⟨sendEncodedProver S M W enc, sendVerifier S M⟩

variable {S M W enc}

/-- Perfect completeness, whenever the encoding of a witness of the input relation is in the
output relation. -/
theorem sendEncoded_complete {relIn : Set ((S × ∀ i, NoOracle i) × W)}
    {relOut : Set ((S × ∀ i, OneOracle M i) × W)}
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ((s, fun _ ↦ enc w), w) ∈ relOut) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (sendEncoded S M W enc).red.perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  have hrun : ((sendEncoded S M W enc).red.toReduction.run (s, o) witIn).run =
      pure (some (((show (sendSpec M).FullTranscript from
        ProtocolSpec.Transcript.concat (m := 0) (enc witIn) (default : (sendSpec M).Transcript 0)),
        (s, fun _ ↦ enc witIn), witIn), (s, fun _ ↦ enc witIn))) := rfl
  rw [hrun, support_pure, Set.mem_singleton_iff] at hx
  exact ⟨_, hx, h s o witIn hIn, rfl⟩

/-- The completeness half. -/
def sendEncodedComplete {relIn : Set ((S × ∀ i, NoOracle i) × W)}
    {relOut : Set ((S × ∀ i, OneOracle M i) × W)}
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ((s, fun _ ↦ enc w), w) ∈ relOut) :
    Complete (sendEncoded S M W enc) relIn relOut where
  guarded := (sendVerifierPure (S := S) (M := M)).toGuardedForm
  complete := sendEncoded_complete h

/-! ## Knowledge soundness -/

variable (pick : S → M → Option W)

/-- The extractor decodes the message: the witness `pick` returns, or the witness it is handed
when `pick` fails. The shared oracle is written `OracleSpec.emptySpec.{0, 0}` rather than `[]ₒ` to
pin a universe `Extractor.RoundByRound` leaves free. -/
def decodeExtractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
    (S × ∀ i, NoOracle i) W W (sendSpec M) (fun _ ↦ W) where
  eqIn := rfl
  extractMid := fun m s tr w ↦ (pick s.1 (tr ⟨0, Nat.succ_pos m.val⟩)).getD w
  extractOut := fun _ _ w ↦ w

variable {relIn : Set ((S × ∀ i, NoOracle i) × W)} {relOut : Set ((S × ∀ i, OneOracle M i) × W)}
  (hpick : ∀ s m w, ((s, fun _ ↦ m), w) ∈ relOut →
    ∃ q, pick s m = some q ∧ ∀ o, ((s, o), q) ∈ relIn)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function: before the message, the input relation of the intermediate
witness; after it, the output relation of the message. -/
def sendEncodedStateFunction :
    (sendVerifier S M).toVerifier.KnowledgeStateFunction init impl relIn relOut
      (decodeExtractor pick) where
  toFun := fun m stmt tr w ↦
    if h : m.val = 0 then (stmt, w) ∈ relIn
    else ((stmt.1, fun _ ↦ tr ⟨0, Nat.pos_of_ne_zero h⟩), w) ∈ relOut
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m _ stmt tr msg w h ↦ by
    have hm : m.val = 0 := by omega
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, dite_false] at h
    simp only [Fin.val_castSucc, hm, dite_true]
    obtain ⟨q, hq, hrel⟩ := hpick _ _ w h
    simp only [decodeExtractor]
    rw [hq, Option.getD_some]
    exact hrel stmt.2
  toFun_full := fun stmt tr w h ↦ by
    simp only [Fin.val_last, one_ne_zero, dite_false]
    exact (Verifier.GuardedForm.of_probEvent_pos
      (sendVerifierPure (S := S) (M := M)).toGuardedForm init impl stmt tr _ h).2

/-- The security half, at error zero, with the extractor that decodes the message. -/
def sendEncodedSecurity :
    Security (sendEncoded S M W enc) relIn relOut (fun _ ↦ 0) where
  guarded := (sendVerifierPure (S := S) (M := M)).toGuardedForm
  witMid := fun _ ↦ W
  extractor := decodeExtractor pick
  kSF := sendEncodedStateFunction pick hpick
  rbr := fun _ _ _ i ↦ (IsEmpty.false i).elim

end Component

end
end LeanerVM.Protocol
