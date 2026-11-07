/-
  LeanVM.Wire.Statements

  Knowledge soundness and completeness of leanVM on the wire: the verifier on bytes decodes them
  (`Proof.fromBytes`) and verifies the proof, the honest prover on bytes encodes its proof
  (`Proof.toBytes`). Not end statements: the end statements (`Statement/LeanVm.lean`) are about the
  structured proof, and these carry them over the compression layer (`LeanVM.Wire.Sound`,
  `LeanVM.Wire.Complete`).
-/

module

public import LeanVM.Wire.Encoding
public import Statement.LeanVm

@[expose] public section

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open Common
  (RandomPermutationOracles OracleQueryLog PermutationQuery PermutationEdges queryPermutation)
open scoped ENNReal

/-! ### The proof on the wire

The proof travels as one byte string, its one encoding `Proof.toBytes` (`LeanVM.Wire.Encoding`,
`Proof::to_bytes` of `crates/fiat_shamir/src/wire.rs`), which the verifier decodes,
`Proof.fromBytes` (`LeanVM.Wire.Encoding`, `Proof::from_bytes`), before it verifies the proof.
Decoding hashes the Merkle nodes the encoding leaves out, over `π`, at most `73728` permutation
calls (eight phases of at most `256` leaves of at most `64` words, four calls each, and `32` levels
of at most `256` nodes, one call each). -/

/-- **The leanVM verifier on bytes**, over a permutation `π` in any monad `m`: the proof the bytes
encode (`Proof.fromBytes`), verified (`leanVmVerifier`); bytes that encode no proof are rejected. -/
def leanVmVerifierOnBytes {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (program : LeanIsaProgram) (input : PublicInput) (bytes : Bytes) : m Bool := do
  match ← Proof.fromBytes π bytes with
  | none => pure false
  | some proof => leanVmVerifier π program input proof

/-- **The honest prover on bytes**: `leanVmHonestProver`'s proof, as its one encoding
(`Proof.toBytes`). -/
def leanVmHonestProverOnBytes {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (program : LeanIsaProgram) (input : PublicInput) (execution : Execution program)
    (ρ nonceAttemptsPerProofOfWork : ℕ) : m (Option Bytes) := do
  let proof ← leanVmHonestProver π program input execution ρ nonceAttemptsPerProofOfWork
  pure (proof.map Proof.toBytes)

/-- An adversary on the wire: as `RandomPermutationAdversary`, but it outputs a statement and
bytes. -/
abbrev RandomPermutationAdversaryOnBytes : Type :=
  OracleComp RandomPermutationOracles (ProgramAndInput × Bytes)

/-- **An outcome of the experiment on the wire**: the statement and bytes the adversary outputs,
the proof they decode to, if any, the verifier's verdict, and the transcript of the adversary
followed by the decoding of its bytes. -/
structure ExperimentOutcomeOnBytes where
  /-- The adversary's program. -/
  program : LeanIsaProgram
  /-- Its public input. -/
  input : PublicInput
  /-- Its bytes. -/
  bytes : Bytes
  /-- The proof they decode to (`Proof.fromBytes`), `none` if they encode none. -/
  decodedProof : Option Proof
  /-- The verifier accepted the decoded proof. -/
  accepted : Bool
  /-- The adversary's queries and their answers, in order, then the decoding's. -/
  transcript : OracleQueryLog

/-- **The random-permutation experiment on the wire**: the adversary, then the decoding of its
bytes (`Proof.fromBytes` over `π`), both recorded in one transcript (`Common.loggedOracles`); then
the verifier over `π` on the decoded proof, rejecting if there is none; the whole game run against
the lazily sampled permutation from no edge. The transcript is that of the adversary that decodes
its own bytes: decoding is a public deterministic computation of the bytes, and the extractor
reads its queries as it reads the adversary's. -/
noncomputable def knowledgeSoundnessExperimentOnBytes
    (adversary : RandomPermutationAdversaryOnBytes) : ProbComp ExperimentOutcomeOnBytes :=
  Common.runWithRandomPermutation do
    let ((((program, input), bytes), decodedProof), transcript) ←
      (simulateQ Common.loggedOracles (do
        let (statement, bytes) ← adversary
        let decodedProof ← Proof.fromBytes queryPermutation bytes
        return ((statement, bytes), decodedProof))).run []
    let accepted ← match decodedProof with
      | none => pure false
      | some proof => leanVmVerifier queryPermutation program input proof
    return ⟨program, input, bytes, decodedProof, accepted, transcript⟩

/-- **The adversary breaks soundness on the wire** for the extractor `extractor`: the verifier
accepts the proof its bytes decode to, and the execution `extractor` extracts from the transcript
(the adversary's and the decoding's) and that proof is not a valid execution of the program on the
public input. -/
def BreaksKnowledgeSoundnessOnBytes (extractor : StraightLineExtractor)
    (outcome : ExperimentOutcomeOnBytes) : Prop :=
  outcome.accepted ∧ ∀ proof, outcome.decodedProof = some proof → ¬ ∃ execution,
    extractor outcome.program outcome.input outcome.transcript proof = some execution ∧
      ValidExecution outcome.program outcome.input execution

/-- **Knowledge soundness on the wire in the random-permutation model**, for the extractor
`extractor`: an adversary of at most `Q ≤ 2^128` queries to `π` and `π⁻¹` that outputs bytes, which
the verifier decodes and then verifies, breaks soundness with probability at most
`(Q + 2^17) · 2^-128 + 5 (Q + 2^17)² · 2^-256`. This is `KnowledgeSoundness` for the adversary that
decodes its own bytes: the extractor reads the transcript of the adversary followed by the
decoding (`knowledgeSoundnessExperimentOnBytes`) and the decoded proof. The `2^17` covers
`KnowledgeSoundness`'s `2^14` and the decoding's at most `73728` permutation calls. -/
def KnowledgeSoundnessOnBytes (extractor : StraightLineExtractor) : Prop :=
  ∀ (adversary : RandomPermutationAdversaryOnBytes) (Q : ℕ),
    Common.QueryCostAtMost adversary Common.permutationCallCost Q → Q ≤ 2 ^ 128 →
    Pr{let outcome ← knowledgeSoundnessExperimentOnBytes adversary}[
        BreaksKnowledgeSoundnessOnBytes extractor outcome] ≤
      (Q + 2 ^ 17 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        5 * (Q + 2 ^ 17 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-- **The completeness experiment on the wire**: the honest prover's bytes
(`leanVmHonestProverOnBytes`), then the verifier's verdict on them (`leanVmVerifierOnBytes`), both
over `π`, run against the lazily sampled permutation; no proof is a failure. -/
noncomputable def completenessExperimentOnBytes (program : LeanIsaProgram) (input : PublicInput)
    (execution : Execution program) (ρ nonceAttemptsPerProofOfWork : ℕ) : ProbComp Bool :=
  Common.runWithRandomPermutation do
    match ← leanVmHonestProverOnBytes queryPermutation program input execution ρ
        nonceAttemptsPerProofOfWork with
    | none => pure false
    | some bytes => leanVmVerifierOnBytes queryPermutation program input bytes

/-- **Completeness on the wire in the random-permutation model**: trying `2^25` nonces per proof of
work, the honest prover's bytes for an execution within the verifier's size cap are rejected by
the verifier on bytes with probability at most `2^-256`. -/
def CompletenessOnBytes : Prop :=
  ∀ (program : LeanIsaProgram) (input : PublicInput) (execution : Execution program) (ρ : ℕ),
    ValidExecution program input execution → execution.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← completenessExperimentOnBytes program input execution ρ (2 ^ 25)}[v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 256


end LeanVM

end
