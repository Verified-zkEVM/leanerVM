import LeanerVM.Protocol.Prove
import LeanerVMTests.Arithmetization.Statement

/-!
# The honest prover's wire

The whole prover runs compiled, in the `leanervm-prove` executable (`bench/LeanerVMProve.lean`),
which writes the test vectors and checks that `verify` accepts them. Here, interpreted:

* **The run against a wire.** A two-round toy component, a checked message and a challenge, run by
  `Prover.runWith` on the transcript writer: the stream is the honest message, the challenge is the
  chain's squeeze after it, which the reader reads back, and the output is the honest prover's on
  that challenge.
* **The committed rows.** The verifier reads the level-0 rows `Prove.level0Rows` stores and the
  later rows `Prove.laterRows` stores back to the word's lanes (`Verify.laneRow`).
* **The setup.** The prover returns no proof at a rate outside its window, before any hash.
-/

namespace LeanerVMTests.Protocol.Prove

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.Prove LeanerVM.Protocol.Verify OracleComp OracleSpec ProtocolSpec
open LeanerVMTests.Arithmetization.Statement

/-! ## The run against a wire -/

instance : ∀ i, OracleInterface ((say E ++ₚ draw E).Message i) :=
  msgAppend (instOracleInterfaceSay E) (instOracleInterfaceDraw E)

instance : ∀ i, SampleableType ((say E ++ₚ draw E).Challenge i) :=
  chalAppend (instSampleableTypeSay E) (instSampleableTypeDraw E)

/-- A toy component: the prover sends `s + 1`, the statement becomes `s + m`, then a challenge
`x` makes it `(s + m) · x`. -/
def toy : Component.Def E NoOracle Unit E NoOracle Unit (say E ++ₚ draw E) :=
  (Component.sendChecked (StmtIn := E) (StmtOut := E) (W := Unit) NoOracle E
    (fun p ↦ p.1.1 + 1) (fun _ _ ↦ true) (fun s m ↦ s + m)).append
  (Component.sampleChallenge (StmtIn := E) (StmtOut := E) (W := Unit) NoOracle E
    (fun _ ↦ true) (fun s x ↦ s * x))

/-- The toy's wire: the message as a scalar, the challenge a squeeze. -/
def toyCodec : RoundCodec (WriteM Id PrunedMerklePaths) (say E ++ₚ draw E) :=
  (RoundCodec.msg (Writer.addScalar blake2sBytes)).append
    (RoundCodec.chal (Writer.sample blake2sBytes))

/-- The chain the toy starts from. -/
def s0 : FsState := FsState.seed fillProg mulInput

/-- The statement. -/
def stmt : E := E.ofLimbs (K.ofBits 5) (K.ofBits 7) 0

/-- The toy run on the writer. -/
def toyRun : Option (((say E ++ₚ draw E).FullTranscript × (E × (∀ i, NoOracle i)) × Unit) ×
    WriterState PrunedMerklePaths) :=
  Id.run (runWrite (Prover.runWith toyCodec toy.red.prover (stmt, fun i ↦ i.elim0) ()) s0)

/-- The challenge the reader squeezes after reading the stream back. -/
def readBack (stream : List E) : Except ReadError (E × E) :=
  ((do let m ← Reader.nextScalar blake2sBytes; let x ← Reader.sample blake2sBytes; return (m, x) :
    ReadM Id PrunedMerklePaths (E × E)).run' ⟨s0, stream, []⟩).run

#guard match toyRun with
  | some ((_, (out, _), ()), st) =>
    st.stream.toList == [stmt + 1] &&
      match readBack st.stream.toList with
      | .ok (m, x) => m == stmt + 1 && out == (stmt + (stmt + 1)) * x
      | .error _ => false
  | none => false

/-! ## The committed rows -/

/-- A word of four lanes whose last lane is zero, on two positions. -/
def kword : Whir.KWord 2 1 1 :=
  ⟨fun y ↦ #v[K.ofBits (y.val + 3), K.ofBits (5 * y.val + 1), K.ofBits 9, 0]⟩

-- The verifier reads a stored level-0 row of three lanes back to the word's row.
#guard (List.finRange 2).all fun y ↦
  (Verify.laneRow true 2 (leafImage 4 ((level0Rows 3 kword)[y]))).map (·.toList) ==
    some ((kword.lift.row y).toList)

/-- A word of two lanes in `E` on two positions. -/
def eword : Whir.Word 1 1 1 :=
  ⟨fun y ↦ #v[E.ofLimbs (K.ofBits y.val) (K.ofBits 2) (K.ofBits 3), E.ofLimbs 1 (K.ofBits 5) 0]⟩

-- The verifier reads a stored later row back to the word's row.
#guard (List.finRange 2).all fun y ↦
  (Verify.laneRow false 1 (leafImage 6 ((laterRows eword)[y]))).map (·.toList) ==
    some ((eword.row y).toList)

/-! ## The setup -/

-- A rate outside its window: no proof.
#guard (prove 1 fillProg mulInput (fillW 1 g memCnt) 0).isNone
#guard (prove 1 fillProg mulInput (fillW 1 g memCnt) 5).isNone

end LeanerVMTests.Protocol.Prove
