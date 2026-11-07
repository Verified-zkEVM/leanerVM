module

public import Statement.Prover.Prove
public import Statement.RandomPermutation
public import VCVio.OracleComp.OracleComp
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.ProbabilityNotation

/-!
# leanVM: knowledge soundness and completeness

A statement (a program and a public input), the verifier on it, and the end statements in the
random-permutation model (`RandomPermutation.lean`; `Statement/README.md`, **The model**),
`LeanVM.KnowledgeSoundness` and `LeanVM.Completeness`, proved by `LeanVM.knowledgeSoundness_holds`
and `completeness_holds` (`lean_vm/README.md` says how they reach this model).

The verifier (`leanVmVerifier π`) and the honest prover are written over a permutation `π` in any
monad, Keccak-256 the sponge over `π` (`keccak256With π`); in the model `π` is
`Common.queryPermutation`, and with Keccak-f[1600] in `Id` they are the deployed ones. The
adversary (`RandomPermutationAdversary`) flips private coins and queries `π` and `π⁻¹`, every query
and its answer recorded in order (`Common.loggedOracles`, `Common.OracleQueryLog`), its coins not
counted (`Common.permutationCallCost`); a Keccak-256 evaluation is a sequence of forward queries,
which it makes itself. The experiment (`knowledgeSoundnessExperiment`) is one game: the adversary,
then the verifier on its statement and proof, run against the lazily sampled permutation from no
edge (`Common.runWithRandomPermutation`).

**Knowledge soundness** is stated for a straight-line extractor (`StraightLineExtractor`), which
reads the statement, the proof and the adversary's transcript, and nothing else (it neither queries
`π` nor rewinds the adversary); `Statement.Theorems` states it for the extractor a cost-machine
program of bounded size computes within its budget (`LeanVM.extractorComputedBy`,
`CostMachine.lean`, which gives the bound and the budget). **Completeness** is stated for one honest
prover, `leanVmHonestProver`: `LeanVM.Prover.prove` (`Statement/Prover/Prove.lean`), an executable
program (`Statement/README.md` says what a reviewer checks of it).

**Scope and trust**, beyond the model's assumption (`Statement/README.md`):

* A proof is the Rust verifier's `Proof`: the scalar stream and one full Merkle path per query, with
  its position, grouped in phases. It travels as bytes, its one encoding (`wire.rs`), with the
  paths pruned; the verifier on bytes (`leanVmVerifierOnBytes`) decodes them (`Proof.fromBytes`, a
  transcription of `Proof::from_bytes`) and verifies the proof, and `KnowledgeSoundnessOnBytes` and
  `CompletenessOnBytes` are stated for it. That `Proof.fromBytes` and `Proof.toBytes` are the Rust's
  is test evidence (`lean_vm`'s wire differential against the Rust decoder); that each decodes the
  other, and that the encoding is the only one of its proof, is proved (`lean_vm`).
* That `verifier` is the Python and Rust verifiers is test evidence: it is a transcription of the
  Python, it accepts the Rust prover's proofs, and on mutated proofs it gives the Rust verifier's
  verdict every time (`scripts/fuzz-verifier.py`).
-/

@[expose] public section

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open Common
  (RandomPermutationOracles OracleQueryLog PermutationQuery PermutationEdges queryPermutation)
open scoped ENNReal

/-! ### The verifier on a statement -/

-- The bytecode the verifier reads (`bytecodeWords`) and the public input as it reads it
-- (`publicInputDigest`) are `LeanIsa.lean`'s, where the encoding is.

/-- **The leanVM verifier** over a permutation `π` in any monad `m`, Keccak-256 the sponge over
`π`: does `proof` show that `program` runs on `input`? -/
def leanVmVerifier {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (program : LeanIsaProgram) (input : PublicInput) (proof : Proof) : m Bool :=
  verifyWith π (bytecodeWords program) (publicInputDigest input) proof

/-- A statement: a program and a public input. -/
abbrev ProgramAndInput : Type := LeanIsaProgram × PublicInput

/-! ### The honest prover and the committed size -/

/-- An honest prover: over a permutation `π` in any monad, from a statement, an execution, the
commitment's rate exponent `ρ` and a fuel of nonces per proof of work, a proof, or `none` when it
makes none. -/
abbrev HonestProver : Type 1 :=
  {m : Type → Type} → [Monad m] → (KeccakState → m KeccakState) → (program : LeanIsaProgram) →
    (input : PublicInput) → Execution program → (ρ nonceAttemptsPerProofOfWork : ℕ) →
    m (Option Proof)

/-- **The honest prover**: `LeanVM.Prover.prove` (`Statement/Prover/Prove.lean`). From the
execution it computes the witness (`witness?`, no proof unless the execution is valid and within
`2^28` committed cells), and, at a valid rate, runs the honest script against the verifier's own
program `leanVmVerifierProgram`, trying `nonceAttemptsPerProofOfWork` nonces per proof of work. -/
def leanVmHonestProver : HonestProver :=
  fun π program input execution ρ nonceAttemptsPerProofOfWork ↦
    Prover.prove π program input execution ρ nonceAttemptsPerProofOfWork

/-- **The committed size of an execution**: the number of cells the honest prover commits to, every
committed column at its table's height, the least power of two holding the table's rows (`1` for no
row), and at least `2^9` for the `KECCAK` table (`TABLE_LOG_FLOORS`, `verifier.py:971`). The memory
has four columns of `2^κ` rows, and the bytecode's counts (`BFCNT`) one of `2^logSize` rows. Each
opcode has a table of one row per instruction of that opcode the execution executes
(`Execution.opcodeCount`), with `15, 15, 8, 15, 14, 26` committed columns for `XOR`, `MUL_NATIVE`,
`SET_CONSTANT`, `DEREF`, `JUMP`, `KECCAK` (of the `KECCAK` table's `90` columns, the `25` input
lanes and `14` more ride `q_keccak`'s slots and the `25` output lanes are not committed,
`verifier.py:932-954`); and `q_keccak` has `2^6` rows per row of the `KECCAK` table. -/
noncomputable def Semantics.Execution.committedSize {program : LeanIsaProgram}
    (execution : Execution program) : ℕ :=
  let height (op : Opcode) : ℕ := 2 ^ Nat.clog 2 (execution.opcodeCount op)
  let keccakHeight : ℕ := 2 ^ max (Nat.clog 2 (execution.opcodeCount .keccak)) 9
  4 * 2 ^ execution.logMemorySize + 2 ^ program.logSize +
    15 * height .xor + 15 * height .mulNative + 8 * height .setConstant + 15 * height .deref +
    14 * height .jump + 26 * keccakHeight + 2 ^ 6 * keccakHeight

/-! ### The experiment -/

/-- An adversary in the random-permutation model: a computation with private coins and oracle
access to `π` and `π⁻¹` that outputs a statement and a proof. -/
abbrev RandomPermutationAdversary : Type :=
  OracleComp RandomPermutationOracles (ProgramAndInput × Proof)

/-- **An outcome of the experiment**: the statement and proof the adversary outputs, the
verifier's verdict, and the adversary's transcript. -/
structure ExperimentOutcome where
  /-- The adversary's program. -/
  program : LeanIsaProgram
  /-- Its public input. -/
  input : PublicInput
  /-- Its proof. -/
  proof : Proof
  /-- The verifier accepted the proof. -/
  accepted : Bool
  /-- The adversary's queries and their answers, in order. -/
  transcript : OracleQueryLog

/-- **The random-permutation experiment**: the adversary, its queries recorded
(`Common.loggedOracles`), then the verifier over `π` (`Common.queryPermutation`) on its statement
and proof, the whole game run against the lazily sampled permutation from no edge
(`Common.runWithRandomPermutation`). -/
noncomputable def knowledgeSoundnessExperiment (adversary : RandomPermutationAdversary) :
    ProbComp ExperimentOutcome :=
  Common.runWithRandomPermutation do
    let (((program, input), proof), transcript) ← (simulateQ Common.loggedOracles adversary).run []
    let accepted ← leanVmVerifier queryPermutation program input proof
    return ⟨program, input, proof, accepted, transcript⟩

/-! ### The extractor -/

/-- The permutation queries of a transcript and their answers, oldest first: its coins left out. -/
def permutationQueries (transcript : OracleQueryLog) : List
    (PermutationQuery KeccakState × KeccakState) :=
  transcript.filterMap fun
    | ⟨.inl _, _⟩ => none
    | ⟨.inr q, y⟩ => some (q, y)

/-- **A straight-line extractor**: from the statement (a program and a public input), the
adversary's transcript and the proof, an execution of the program, or none. It reads nothing
else: it neither queries `π` nor runs the adversary again. -/
abbrev StraightLineExtractor : Type :=
  (program : LeanIsaProgram) → PublicInput → OracleQueryLog → Proof → Option (Execution program)

/-! ### Knowledge soundness -/

/-- **The adversary breaks soundness** for the extractor `extractor`: the verifier accepts its
statement and proof, and the execution `extractor` extracts from the transcript and the proof is
not a valid execution of the program on the public input (no execution, `none`, is a break). -/
def BreaksKnowledgeSoundness (extractor : StraightLineExtractor) (outcome : ExperimentOutcome) :
    Prop :=
  outcome.accepted ∧ ¬ ∃ execution,
    extractor outcome.program outcome.input outcome.transcript outcome.proof = some execution ∧
      ValidExecution outcome.program outcome.input execution

/-- **Knowledge soundness in the random-permutation model**, for the extractor `extractor`: an
adversary of at most `Q ≤ 2^128` queries to `π` and `π⁻¹` (its coins free) breaks soundness with
probability at most `(Q + 2^14) · 2^-128 + 5 (Q + 2^14)² · 2^-256`. The `2^14` covers the verifier's
own Keccak-256 evaluations and duplex permutations, at most `12006` (the `Q + 12006` of `lean_vm`'s
`soundnessError`; as calls of `π` they are up to `12006 · 2^32`, the IV hashing a bytecode of up to
`2^32` instructions, which the transfer below pays), its `12006 · 2^-256` for a fresh hash answer
equal to a stack root the adversary announced without computing it, and the transfer from two
random oracles to one permutation. `Statement.Theorems`
states it for the extractor a cost-machine program computes within its budget
(`LeanVM.extractorComputedBy`, `CostMachine.lean`). The extractor must output some valid execution
of the program on the input; nothing requires it to be the execution the proof commits to (its
committed word). For a program with several valid executions on one input, the one extracted may
differ, and `AggregateSound` (`Corollaries.lean`) then decodes that one. -/
def KnowledgeSoundness (extractor : StraightLineExtractor) : Prop :=
  ∀ (adversary : RandomPermutationAdversary) (Q : ℕ),
    Common.QueryCostAtMost adversary Common.permutationCallCost Q → Q ≤ 2 ^ 128 →
    Pr{let outcome ← knowledgeSoundnessExperiment adversary}[
        BreaksKnowledgeSoundness extractor outcome] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-! ### Completeness -/

/-- **The completeness experiment in the random-permutation model**: the honest prover's proof,
then the verifier's verdict on it, both over `π`, run against the lazily sampled permutation; no
proof is a failure. -/
noncomputable def completenessExperiment (honestProver : HonestProver) (program : LeanIsaProgram)
    (input : PublicInput) (execution : Execution program) (ρ nonceAttemptsPerProofOfWork : ℕ) :
    ProbComp Bool :=
  Common.runWithRandomPermutation do
    match ← honestProver queryPermutation program input execution ρ nonceAttemptsPerProofOfWork with
    | none => pure false
    | some proof => leanVmVerifier queryPermutation program input proof

/-- **Completeness in the random-permutation model**: trying `2^25` nonces per proof of work, the
honest prover's (`leanVmHonestProver`) proof of an execution within the verifier's size cap is
rejected with probability at most `2^-256`. -/
def Completeness : Prop :=
  ∀ (program : LeanIsaProgram) (input : PublicInput) (execution : Execution program) (ρ : ℕ),
    ValidExecution program input execution → execution.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← completenessExperiment leanVmHonestProver program input execution ρ (2 ^ 25)}[
        v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 256


/-! ### The proof on the wire

The proof travels as one byte string, its one encoding `Proof.toBytes` (`Prover/Prove.lean`,
`Proof::to_bytes` of `crates/fiat_shamir/src/wire.rs`), which the verifier decodes,
`Proof.fromBytes` (`LeanVmVerifier.lean`, `Proof::from_bytes`), before it verifies the proof.
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
