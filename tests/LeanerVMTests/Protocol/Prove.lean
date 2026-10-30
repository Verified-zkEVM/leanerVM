import LeanerVM.Protocol.Prove
import LeanerVM.Protocol.Compile.Agree
import LeanerVM.Protocol.Prove.Complete
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
* **Completeness.** `baseProver_complete_of_agree` as stated, given `PhasesAgree`, and
  `baseProver_complete` with it proved (`Compile.phasesAgree`); a stored level-0 row is read as
  the word's row exactly when the lanes past the stored ones vanish.
* **When the prover returns no proof.** `proveWith_eq_none` and `proveWith_ne_none` as stated, the
  grind's failure at a chain state the run reaches (`RunReaches`); at a rate outside its window the
  prover returns no proof, before any hash.
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

-- Its last lane being zero, the stored row of three lanes has the full row, in reverse, as its
-- leaf image (`leafImage_level0Rows`); stored with two lanes, the third, nonzero, is lost.
#guard (List.finRange 2).all fun y ↦
  leafImage 4 ((level0Rows 3 kword)[y]) == (kword.row y).toList.reverse
#guard (List.finRange 2).all fun y ↦
  leafImage 4 ((level0Rows 2 kword)[y]) != (kword.row y).toList.reverse

/-- A word of two lanes in `E` on two positions. -/
def eword : Whir.Word 1 1 1 :=
  ⟨fun y ↦ #v[E.ofLimbs (K.ofBits y.val) (K.ofBits 2) (K.ofBits 3), E.ofLimbs 1 (K.ofBits 5) 0]⟩

-- The verifier reads a stored later row back to the word's row.
#guard (List.finRange 2).all fun y ↦
  (Verify.laneRow false 1 (leafImage 6 ((laterRows eword)[y]))).map (·.toList) ==
    some ((eword.row y).toList)

/-! ## Completeness -/

/-- The honest prover's completeness given the phases' agreement: for every hash and fuel, a proof
the prover returns for a satisfying witness is accepted, given the phases' agreement at every
admissible size and valid rate. -/
example (H : List UInt8 → Digest) (fuel : ℕ) {prog : Program} {input : PublicInput}
    {κ : ℕ} {w : Air.Flat.EnsembleWitness (LeanerVM.Arithmetization.leanIsaEnsemble prog κ)} {ρ : ℕ}
    {proof : Proof PrunedMerklePaths} (hsat : LeanerVM.Arithmetization.SatisfiedBy prog input w)
    (hagree : ∀ s hs hρ, PhasesAgree prog s hs ρ hρ input)
    (hp : proveWith (m := Id) H fuel Blake2sFlock.blake2sFlockSpec prog input w ρ = some proof) :
    verifyWith (m := Id) H prog input proof = true :=
  baseProver_complete_of_agree H fuel hsat hagree hp

/-- The honest prover's completeness, the phases' agreement proved: for every hash and fuel, a
proof the prover returns for a satisfying witness is accepted. -/
example (H : List UInt8 → Digest) (fuel : ℕ) {prog : Program} {input : PublicInput}
    {κ : ℕ} {w : Air.Flat.EnsembleWitness (LeanerVM.Arithmetization.leanIsaEnsemble prog κ)} {ρ : ℕ}
    {proof : Proof PrunedMerklePaths} (hsat : LeanerVM.Arithmetization.SatisfiedBy prog input w)
    (hp : proveWith (m := Id) H fuel Blake2sFlock.blake2sFlockSpec prog input w ρ = some proof) :
    verifyWith (m := Id) H prog input proof = true :=
  baseProver_complete H fuel hsat hp

open LeanerVM.Protocol.LeanIsa in
/-- When the honest prover returns no proof, as stated: the witness gives no sizes, or they are
not admissible, or the rate is not valid, or a grind runs out of fuel at a chain state the run
reaches; never the openings. -/
example (H : List UInt8 → Digest) (fuel : ℕ) (F : FlockSpec) {prog : Program}
    {input : PublicInput}
    {κ : ℕ} {w : Air.Flat.EnsembleWitness (LeanerVM.Arithmetization.leanIsaEnsemble prog κ)} {ρ : ℕ}
    (h : proveWith (m := Id) H fuel F prog input w ρ = none) :
    Sizes.ofWitness w = none ∨ ∃ s, Sizes.ofWitness w = some s ∧
      (¬ s.Admissible prog ∨ ¬ validRate ρ ∨
        ∃ fs, RunReaches H (FsState.seedWith H prog input) fuel F prog input w ρ fs ∧
          Id.run (fs.grind H fuel Whir.queryGrindingBits) = none) :=
  proveWith_eq_none H fuel F h

open LeanerVM.Protocol.LeanIsa in
/-- When the honest prover returns a proof, as stated: at admissible sizes and a valid rate, when
no grind runs out of fuel at a chain state its run reaches. -/
example (H : List UInt8 → Digest) (fuel : ℕ) (F : FlockSpec) {prog : Program}
    {input : PublicInput}
    {κ : ℕ} {w : Air.Flat.EnsembleWitness (LeanerVM.Arithmetization.leanIsaEnsemble prog κ)} {ρ : ℕ}
    {s : Sizes} (hws : Sizes.ofWitness w = some s) (hs : s.Admissible prog) (hρ : validRate ρ)
    (hg : ∀ fs, RunReaches H (FsState.seedWith H prog input) fuel F prog input w ρ fs →
      Id.run (fs.grind H fuel Whir.queryGrindingBits) ≠ none) :
    proveWith (m := Id) H fuel F prog input w ρ ≠ none :=
  proveWith_ne_none H fuel F hws hs hρ hg

/-! ## The setup -/

-- A rate outside its window: no proof (the third case of `proveWith_eq_none`).
#guard (prove 1 fillProg mulInput (fillW 1 g memCnt) 0).isNone
#guard (prove 1 fillProg mulInput (fillW 1 g memCnt) 5).isNone

end LeanerVMTests.Protocol.Prove
