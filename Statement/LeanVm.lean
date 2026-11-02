module

public import Statement.Prover.Prove
public import Statement.RandomPermutation
public import VCVio.OracleComp.OracleComp
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.ProbabilityNotation

/-!
# leanVM: knowledge soundness and completeness

A statement (a program and a public input), the verifier on it, and the end statements in the
random-permutation model (`RandomPermutation.lean`), `LeanVM.KnowledgeSoundness` and
`LeanVM.Completeness`, proved by `LeanVM.knowledgeSoundness_holds` and `completeness_holds`
(`lean_vm/README.md` says how they reach this model).

The model has one random object, the permutation `π` of the Keccak state, lazily sampled
(`Common.lazyRandomPermutation`); its oracles are coins, `π` and `π⁻¹`
(`Common.RandomPermutationOracles`), and nothing else. The verifier (`leanVmVerifier π`) and the
honest prover are written over a permutation `π` in any monad, Keccak-256 the sponge over `π`
(`keccak256With π`); in the model `π` is `Common.queryPermutation`, with Keccak-f[1600] in `Id`
they are the deployed ones. The adversary (`RandomPermutationAdversary`) flips private coins
and queries `π` and `π⁻¹`, every query and its answer recorded in order (`Common.loggedOracles`,
`Common.OracleQueryLog`), its coins not counted (`Common.permutationCallCost`); a Keccak-256
evaluation is a sequence of forward queries, which it makes itself. The experiment
(`knowledgeSoundnessExperiment`) is one game: the adversary, then the verifier on its statement and
proof, run against the lazily sampled permutation from no edge (`Common.runWithRandomPermutation`).

**Knowledge soundness** is stated for a straight-line extractor (`StraightLineExtractor`), which
reads the statement, the proof and the adversary's transcript, and nothing else (it neither queries
`π` nor rewinds the adversary): `KnowledgeSoundness extractor`. `Statement.Theorems` states it for
the extractor that a cost-machine program of bounded size computes within a budget in the number of
permutation queries (`LeanVM.extractorComputedBy`, `CostMachine.lean`). The statement does not name
the program (`lean_vm` supplies its extractor, compiled); it constrains it only by its size bound,
which leaves no room for a useful table of witnesses beside the compiled extractor's code, and its
budget, `leanVmKnowledgeExtractorBudget` (the most its run may cost, so also the most steps it may
execute), `2^81 + O(N·log³N)` for `N` permutation queries (about `2^81` for `N ≤ 2^50`), `lean_vm`'s
proved price of the compiled extractor being about `2^80.49 + 2^14.85·N·log²N`. A run out of budget
extracts nothing, which counts as a break.

**Completeness** is stated for one honest prover, `leanVmHonestProver`: `LeanVM.Prover.prove`
(`Statement/Prover/Prove.lean`), an executable program (over Keccak-f[1600] it is
`lake exe leanvm-prove`; `Statement/README.md` says what a reviewer checks of it). Given a valid
execution whose committed size is at most `2^28`, the most the verifier admits, at an inverse rate
`2^ρ` with `1 ≤ ρ ≤ 4`, trying `2^25` nonces per proof of work, its proof is rejected with
probability at most `2^-256`.

**Scope and trust.**

* The deployed Keccak-f[1600] is a fixed permutation; that it behaves as a random one is the
  assumption of this model. Inside the executed program the `KECCAK` instruction computes the
  deployed Keccak-f[1600], not `π`: in the model the transcript's permutation and the one a proved
  program computes are independent, while deployed they are the same function. The model so
  excludes, by construction, programs that evaluate their own proof's Fiat-Shamir duplex, the
  setting of the known attacks on Fiat-Shamir for GKR-based systems (Khovratovich, Rothblum and
  Soukhanov, 2025): the assumption is that the deployed Keccak-f[1600] behaves as a random
  permutation even to programs that compute it. The adversary's code is fixed before `π` is sampled
  (no advice that depends on the permutation).
* The adversary is classical: no statement covers quantum adversaries (a quantum random-permutation
  model).
* A proof is the Python verifier's format: the scalar stream and one full Merkle path per query. The
  Rust prover ships pruned paths, which the deployed Rust verifier expands into these paths; that
  expansion is not formalized.
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
own oracle calls, at most `12006` (in the `Q + 12006` of `lean_vm`'s `soundnessError`), its
`12006 · 2^-256` for a fresh hash answer equal to a stack root the adversary announced without
computing it, and the transfer from two random oracles to one permutation. `Statement.Theorems`
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

end LeanVM

end
