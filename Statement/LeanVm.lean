module

public import Statement.Extractor
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
(`Common.RandomPermutationOracles`), and nothing else. The verifier (`verifier F`) and the honest
prover are written over a permutation `F` in any monad, Keccak-256 the sponge over `F`
(`keccak256With F`); in the model `F` is `π` (`Common.queryPermutation`), with Keccak-f[1600] in
`Id` they are the deployed ones. The adversary (`RandomPermutationAdversary`) flips private coins
and queries `π` and `π⁻¹`, every query and its answer recorded in order (`Common.loggedOracles`,
`Common.OracleQueryLog`), its coins not counted (`Common.permutationCallCost`); a Keccak-256
evaluation is a sequence of forward queries, which it makes itself. The experiment
(`soundnessExperiment`) is one game: the adversary, then the verifier on its statement and proof,
run against the lazily sampled permutation from no edge (`Common.runWithRandomPermutation`).

**Knowledge soundness** is stated for one extractor, `transcriptExtractor`, which is straight-line:
it reads the statement, the proof and the adversary's transcript, and nothing else (it neither
queries `π` nor rewinds the adversary). It is `Extractor.lean`'s `extract` on the Keccak-256
evaluations the transcript's permutation queries hold (`keccakEvaluationsOfTranscript`; the coins
left out, `permutationQueries`). An accepted proof thus commits,
except with the bound's probability, to a stack whose memory columns hold a valid execution, among
the at most `2^18` stacks the word the adversary hashed is close to (proved for every admissible
shape and word: `LeanVM.candidates_ncard_le`).

**Completeness** is stated for one honest prover, `prover`: `LeanVM.Prover.prove`
(`Statement/Prover/Prove.lean`), an executable program (over Keccak-f[1600] it is
`lake exe leanvm-prove`; `Statement/README.md` says what a reviewer checks of
it). Given a valid execution whose committed size is at most `2^28`, the most the verifier admits,
at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4`, trying `2^25` nonces per proof of work, its proof is
rejected with probability at most `2^-256`.

**Scope and trust.**

* The deployed Keccak-f[1600] is a fixed permutation; that it behaves as a random one is the
  assumption of this model. Inside the executed program the `KECCAK` instruction computes the
  deployed Keccak-f[1600], not `π`: in the model the transcript's permutation and the one a
  proved program computes are independent, while deployed they are the same function. The model
  so excludes, by construction, programs that evaluate their own proof's Fiat-Shamir duplex, the
  setting of the known attacks on Fiat-Shamir for GKR-based systems (Khovratovich, Rothblum and
  Soukhanov, 2025): the assumption is that the deployed Keccak-f[1600] behaves as a random
  permutation even to programs that compute it. The adversary's code is fixed before `π` is
  sampled (no advice that depends on the permutation).
* The adversary is classical: no statement covers quantum adversaries (a quantum
  random-permutation model).
* A proof is the Python verifier's format: the scalar stream and one full Merkle path per query.
  The Rust prover ships pruned paths, which the deployed Rust verifier expands into these paths;
  that expansion is not formalized.
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
-- (`publicDigest`) are `LeanIsa.lean`'s, where the encoding is.

/-- **The leanVM verifier** over a permutation `F` in any monad `m`, Keccak-256 the sponge over
`F`: does `proof` show that `prog` runs on `input`? -/
def verifier {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (prog : Program)
    (input : PublicInput) (proof : Proof) : m Bool :=
  verifyWith F (bytecodeWords prog) (publicDigest input) proof

/-- A statement: a program and a public input. -/
abbrev ProgramAndInput : Type := Program × PublicInput

/-! ### The honest prover and the committed size -/

/-- An honest prover: over a permutation `F` in any monad, from a statement, an execution, the
commitment's rate exponent `ρ` and a fuel of nonces per proof of work, a proof, or `none` when it
makes none. -/
abbrev HonestProver : Type 1 :=
  {m : Type → Type} → [Monad m] → (KeccakState → m KeccakState) → (prog : Program) →
    (input : PublicInput) → Execution prog → (ρ fuel : ℕ) → m (Option Proof)

/-- **The honest prover**: `LeanVM.Prover.prove` (`Statement/Prover/Prove.lean`). From the
execution `t` it computes the witness (`witness?`, no proof unless `t` is a valid execution within
`2^28` committed cells), and, at a valid rate, runs the honest script against the verifier's
own program `leanVmProgram`, trying `fuel` nonces per proof of work. -/
def prover : HonestProver :=
  fun F prog input t ρ fuel ↦ Prover.prove F prog input t ρ fuel

/-- **The committed size of an execution**: the number of cells the honest prover commits to,
every committed column at its table's height, the least power of two holding the table's rows
(`1` for no row), and at least `2^9` for the `KECCAK` table (`TABLE_LOG_FLOORS`,
`verifier.py:971`). The memory has four columns of `2^κ` rows, and the bytecode's counts (`BFCNT`)
one of `2^logSize` rows. Each opcode has a table of one row per instruction of that opcode the
execution executes (`Execution.count`), with `15, 15, 8, 15, 14, 26` committed columns for `XOR`,
`MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP`, `KECCAK` (of the `KECCAK` table's `90` columns, the
`25` input lanes and `14` more ride `q_keccak`'s slots and the `25` output lanes are not committed,
`verifier.py:932-954`); and `q_keccak` has `2^6` rows per row of the `KECCAK` table. -/
noncomputable def Semantics.Execution.committedSize {prog : Program} (t : Execution prog) : ℕ :=
  let height (op : Opcode) : ℕ := 2 ^ Nat.clog 2 (t.count op)
  let keccakHeight : ℕ := 2 ^ max (Nat.clog 2 (t.count .keccak)) 9
  4 * 2 ^ t.logMemorySize + 2 ^ prog.logSize +
    15 * height .xor + 15 * height .mulNative + 8 * height .setConstant + 15 * height .deref +
    14 * height .jump + 26 * keccakHeight + 2 ^ 6 * keccakHeight

/-! ### The experiment -/

/-- An adversary in the random-permutation model: a computation with private coins and oracle
access to `π` and `π⁻¹` that outputs a statement and a proof. -/
abbrev RandomPermutationAdversary : Type :=
  OracleComp RandomPermutationOracles (ProgramAndInput × Proof)

/-- An outcome of the experiment: the statement (`program`, `input`) and the `proof`, the
verdict (`accepted`), and the adversary's `transcript`, its queries and their answers in order. -/
abbrev ExperimentOutcome : Type := ((ProgramAndInput × Proof) × Bool) × OracleQueryLog

abbrev ExperimentOutcome.program (z : ExperimentOutcome) : Program := z.1.1.1.1
abbrev ExperimentOutcome.input (z : ExperimentOutcome) : PublicInput := z.1.1.1.2
abbrev ExperimentOutcome.proof (z : ExperimentOutcome) : Proof := z.1.1.2
abbrev ExperimentOutcome.accepted (z : ExperimentOutcome) : Prop := z.1.2 = true
abbrev ExperimentOutcome.transcript (z : ExperimentOutcome) : OracleQueryLog := z.2

/-- **The random-permutation experiment**: the adversary, its queries recorded
(`Common.loggedOracles`), then the verifier over `π` (`Common.queryPermutation`) on its statement
and proof, the whole game run against the lazily sampled permutation from no edge
(`Common.runWithRandomPermutation`). -/
noncomputable def soundnessExperiment (A : RandomPermutationAdversary) :
    ProbComp ExperimentOutcome :=
  Common.runWithRandomPermutation do
    let (z, transcript) ← (simulateQ Common.loggedOracles A).run []
    let accepted ← verifier queryPermutation z.1.1 z.1.2 z.2
    return ((z, accepted), transcript)

/-! ### The extractor -/

/-- The bytes Keccak-256 absorbs for the message `m`: its whole blocks of `136` bytes, then the
padded last block (`padBlock`, as `keccak256With` absorbs them). -/
def keccakPadded (m : Bytes) : Bytes :=
  m.take (rate * (m.length / rate)) ++ padBlock (m.drop (rate * (m.length / rate)))

/-- The message whose padding is `bs`, if any: the prefix of `bs` short of `1` to `136` bytes
that pads to `bs` (there is at most one). -/
def keccakUnpadded (bs : Bytes) : Option Bytes :=
  ((List.range rate).map fun k ↦ bs.take (bs.length - 1 - k)).find? (keccakPadded · = bs)

/-- The extractor's bookkeeping of a transcript: the edges `(x, π x)` fixed so far, newest first,
and the states that a chain of forward queries reaches from the zero state, each with the bytes
its path absorbed, newest first. -/
structure TranscriptReplay where
  /-- The edges `(x, π x)` fixed so far, newest first. -/
  edges : PermutationEdges KeccakState
  /-- The states reached from the zero state, with the bytes their paths absorbed. -/
  spongePaths : List (KeccakState × Bytes)

/-- One query and its answer. A forward query `π x` that fixes a new edge extends the chain of a
state `s` with the capacity of `x` (lanes `17 … 24`), if there is one, by the block that takes
`s` to `x`: the bytes of their rates' XOR, lanes `0 … 16`. An inverse query extends no chain. -/
def TranscriptReplay.step (σ : TranscriptReplay) :
    PermutationQuery KeccakState × KeccakState → TranscriptReplay
  | (.forward x, y) =>
    match Common.forwardLookup σ.edges x with
    | some _ => σ
    | none =>
      match σ.spongePaths.find? (fun p ↦ p.1.toList.drop 17 = x.toList.drop 17) with
      | some (s, bs) =>
        ⟨(x, y) :: σ.edges, (y, bs ++ (List.range 17).flatMap fun i ↦
          wordBytes (Keccak.lane s i ^^^ Keccak.lane x i)) :: σ.spongePaths⟩
      | none => ⟨(x, y) :: σ.edges, σ.spongePaths⟩
  | (.inverse y, x) =>
    match Common.inverseLookup σ.edges y with
    | some _ => σ
    | none => ⟨(x, y) :: σ.edges, σ.spongePaths⟩

/-- **The Keccak-256 evaluations a transcript holds**: the byte strings whose whole padded sponge
path the transcript (oldest first) holds as a chain of forward queries from the zero state, each
query absorbing the next block into the answer of the one before and each the query that first
fixed its edge (an edge first fixed by an inverse query extends no path), with the first four lanes
of the path's last answer. -/
def keccakEvaluationsOfTranscript (T : List (PermutationQuery KeccakState × KeccakState)) :
    List (Bytes × Digest) :=
  (T.foldl TranscriptReplay.step ⟨[], [(Vector.replicate 25 0, [])]⟩).spongePaths.filterMap fun p ↦
    (keccakUnpadded p.2).map fun m ↦ (m, #v[p.1[0], p.1[1], p.1[2], p.1[3]])

/-- The permutation queries of a transcript and their answers, oldest first: its coins left out. -/
def permutationQueries (T : OracleQueryLog) : List (PermutationQuery KeccakState × KeccakState) :=
  T.filterMap fun
    | ⟨.inl _, _⟩ => none
    | ⟨.inr q, y⟩ => some (q, y)

/-- The Keccak-256 evaluation of `x` among the paths `P`, if `P` holds one. -/
def lookupEvaluation (P : List (Bytes × Digest)) (x : Bytes) : Option Digest :=
  (P.find? (·.1 = x)).map (·.2)

/-- **The extractor in the random-permutation model**: from the statement, the adversary's
transcript and the proof, an execution of the program: the extractor of `Extractor.lean`
(`LeanVM.Extraction.extract`) on the Keccak-256 evaluations of the transcript's permutation queries
(`lookupEvaluation (keccakEvaluationsOfTranscript (permutationQueries T))`), the byte strings they
answer being those of the transcript's paths. The paths are computed once. -/
def transcriptExtractor (prog : Program) (input : PublicInput) (T : OracleQueryLog)
    (proof : Proof) : Option (Execution prog) :=
  let paths := keccakEvaluationsOfTranscript (permutationQueries T)
  Extraction.extract prog input (bytecodeWords prog) (lookupEvaluation paths)
    (paths.map (·.1)) proof

/-! ### Knowledge soundness -/

/-- **The adversary breaks soundness**: the verifier accepts its statement and proof, and the
execution `transcriptExtractor` extracts from the transcript and the proof is not a valid execution
of the program on the public input. -/
def BreaksKnowledgeSoundness (z : ExperimentOutcome) : Prop :=
  z.accepted ∧ ¬ ∃ t, transcriptExtractor z.program z.input z.transcript z.proof = some t ∧
    ValidExecution z.program z.input t

/-- **Knowledge soundness in the random-permutation model**, for the extractor
`transcriptExtractor`: an adversary of at most `Q ≤ 2^128` queries to `π` and `π⁻¹` (its coins free)
breaks soundness with probability at most `(Q + 2^14) · 2^-128 + 5 (Q + 2^14)² · 2^-256`, the `2^14`
covering the verifier's own `12006` oracle calls and two terms of `2^-128` (a guessed stack root,
the transfer from two random oracles to one permutation). -/
def KnowledgeSoundness : Prop :=
  ∀ (A : RandomPermutationAdversary) (Q : ℕ),
    Common.QueryCostAtMost A Common.permutationCallCost Q → Q ≤ 2 ^ 128 →
    Pr{let z ← soundnessExperiment A}[BreaksKnowledgeSoundness z] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-! ### Completeness -/

/-- **The completeness experiment in the random-permutation model**: the honest prover's proof,
then the verifier's verdict on it, both over `π`, run against the lazily sampled permutation; no
proof is a failure. -/
noncomputable def verifierCompletenessExperiment (prover : HonestProver) (prog : Program)
    (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) : ProbComp Bool :=
  Common.runWithRandomPermutation do
    match ← prover queryPermutation prog input t ρ fuel with
    | none => pure false
    | some proof => verifier queryPermutation prog input proof

/-- **Completeness in the random-permutation model**: trying `2^25` nonces per proof of work, the
honest prover's (`prover`) proof of an execution within the verifier's size cap is rejected with
probability at most `2^-256`. -/
def Completeness : Prop :=
  ∀ (prog : Program) (input : PublicInput) (t : Execution prog) (ρ : ℕ),
    ValidExecution prog input t → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← verifierCompletenessExperiment prover prog input t ρ (2 ^ 25)}[v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM

end
