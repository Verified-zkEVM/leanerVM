module

public import Statement.Extractor
public import Statement.RandomPermutation
public import VCVio.OracleComp.OracleComp
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.ProbabilityNotation

/-!
# leanVM: knowledge soundness and completeness

The statement the verifier reads, its errors, and the end statements in the random-permutation
model: `LeanVM.KnowledgeSoundness`, `LeanVM.Completeness` and `LeanVM.KnowledgeSoundnessBits`.
Proved by `LeanVM.knowledgeSoundness_holds`, `completeness_holds` and `knowledgeSoundness_bits`
(`lean_vm`).
-/

section

/-!
## The verifier on a statement

The verifier receives a statement (a program and a public input, `Statement`) as the program's
bytecode and the public input's digest (`bytecodeWords`, `publicDigest`), and a proof. It is
written for any hash function `H` and permutation `F` in any monad (`verifier H F`); with
Keccak-256 and Keccak-f[1600] it is the deployed verifier (`verify`).

The verifier and the honest prover call Keccak-256 and Keccak-f[1600] as oracle queries, `.inl x`
the hash of the bytes `x` and `.inr s` the permutation of the state `s` (`HashSpec`, `queryH`,
`queryF`). This file does not say what answers them: the model is `LeanVM/Spec/Rpm.lean`'s, the
random-permutation model, in which both are built from one uniformly random permutation `π` of the
Keccak state (Keccak-256 the sponge over `π`, Keccak-f[1600] `π` itself), and the adversary
queries `π` and `π⁻¹`. The statements, `KnowledgeSoundness` and `Completeness`, are there.

Here are the parts they are stated with: the verifier's query bound (`verifierQueries`), the
soundness error at `Q` queries (`soundnessError`), the honest prover's type (`HonestProver`), the
completeness error (`completenessError`), and the committed size of an execution
(`Trace.committedSize`), which the verifier caps at `2^28`.

**Scope and trust.**

* A proof is the Python verifier's format: the scalar stream and one full Merkle path per query.
  The Rust prover ships pruned paths, which the deployed Rust verifier expands into these paths;
  that expansion is not formalized.
* That `verifier` is the Python and Rust verifiers is test evidence: it is a transcription of the
  Python, it accepts the Rust prover's proofs, and on mutated proofs it gives the Rust verifier's
  verdict every time (`scripts/fuzz-verifier.py`).
* The definitions rest on Mathlib, CompPoly (the fields) and VCVio (oracle computations, query
  bounds).
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-! ### The verifier on a statement -/

/-- A proof: the scalar stream and the Merkle openings. -/
abbrev Proof := Compile.Proof

/-- The bytecode the verifier reads: the sixteen slots of every instruction (`encodeSlots`),
slot by slot: word `i + 2^logSize · s` is slot `s` of instruction `i`. -/
def bytecodeWords (prog : Program) : List K :=
  (List.finRange 16).flatMap fun s ↦
    (List.finRange (2 ^ prog.logSize)).map fun i ↦ (encodeSlots (prog.code i))[s]

/-- The public input as the verifier reads it: its four lanes, the digest's four words
(`public_input_bytes`, `crates/leanvm_core/src/cpu/mod.rs:723-730`; `Digest.halves`,
`verifier.py:225-228`). -/
def publicDigest (input : PublicInput) : Digest :=
  #v[(input.lanes 0).lane, (input.lanes 1).lane, (input.lanes 2).lane, (input.lanes 3).lane]

/-- **The leanVM verifier**, for a hash function `H` and a permutation `F` in any monad `m`: does
`proof` show that `prog` runs on `input`? -/
def verifier {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KState → m KState)
    (prog : Program) (input : PublicInput) (proof : Proof) : m Bool :=
  verifyWith H F (bytecodeWords prog) (publicDigest input) proof

/-- **The deployed verifier**: `verifier` with Keccak-256 and Keccak-f[1600]. -/
def verify (prog : Program) (input : PublicInput) (proof : Proof) : Bool :=
  Id.run (verifier (m := Id) keccak256 keccakF prog input proof)

/-! ### The oracle calls -/

/-- The verifier's and the honest prover's calls: Keccak-256, a function from byte strings to
digests (queries `.inl x`), and Keccak-f[1600], a function from states to states (queries
`.inr s`). What answers them is the model's (`LeanVM/Spec/Rpm.lean`: the sponge over a random
permutation, and the permutation). -/
abbrev HashSpec : OracleSpec (Bytes ⊕ KState) := (Bytes →ₒ Digest) + (KState →ₒ KState)

/-- A call to the hash. -/
def queryH (x : Bytes) : OracleComp HashSpec Digest := liftM (HashSpec.query (.inl x))

/-- A call to the permutation. -/
def queryF (s : KState) : OracleComp HashSpec KState := liftM (HashSpec.query (.inr s))

/-- A statement: a program and a public input. -/
abbrev Statement : Type := Program × PublicInput

/-! ### The soundness error -/

/-- The verifier's oracle queries, at most, on every statement and proof: `12008` queries to
Keccak-256 and Keccak-f together (the bytecode, the relation label, the IV, the seed's
permutation, the sponge's permutations, one per challenge and one per four absorbed scalars, and
every Merkle hash of the openings), the bound the proof establishes over every admissible shape
(`LeanVM.Protocol.Verifier.leanVmQueryBound`). The bound is not tight: it charges every WHIR
opening at the largest commitment height, and bounds the bus depth, the table heights and the
Keccak reduction's point by the window of the announced sizes. -/
def verifierQueries : ℕ := 12008

/-- **The soundness error** at `Q` queries, the first term of the bound of `KnowledgeSoundness`
(`Rpm.lean`; the second, `rpmError`, is the cost of building both functions from one
permutation). It is the error the proof obtains with Keccak-256 and Keccak-f[1600] two independent
random functions, counting the hash and permutation calls of the adversary (`Q`) and of the
verifier (at most `verifierQueries = V`; in `KnowledgeSoundness` the adversary's `Q` are its `π` and
`π⁻¹` queries): one `2^-128` per call, plus, per call,
`7 · (Q + V) / 2^256` for a fresh answer that collides with or predicts a value the answers
already refer to (a digest, or a state's capacity), plus one `2^-256` per call of the verifier, for
a fresh hash answer that is the stack's root the adversary announced without computing it (the
extractor, reading the adversary's evaluations only, would then miss the root's preimage). -/
noncomputable def soundnessError (Q : ℕ) : ℝ≥0∞ :=
  ((Q + verifierQueries : ℕ) : ℝ≥0∞) *
      ((2 : ℝ≥0∞)⁻¹ ^ 128 + ((7 * (Q + verifierQueries) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    (verifierQueries : ℝ≥0∞) / 2 ^ 256

/-! ### The honest prover, the completeness error and the committed size -/

/-- An honest prover: from a statement, an execution, the commitment's rate exponent `ρ` and a
fuel of nonces per proof of work, a proof, computed with calls to Keccak-256 and Keccak-f[1600]
(`HashSpec`), which the model answers. -/
abbrev HonestProver : Type :=
  (prog : Program) → (input : PublicInput) → Trace prog → (ρ fuel : ℕ) → OracleComp HashSpec Proof

/-- **The completeness error** at a fuel of `fuel` nonces per proof of work, the first term of the
bound of `Completeness` (`Rpm.lean`), the error with two independent random functions: each of the
`Q` queries of the honest prover and the verifier may complete a proof of work whose nonces all
failed, a nonce failing a proof of work of `17` bits with probability `1 - 2^-17`. -/
noncomputable def completenessError (fuel : ℕ) : ℝ≥0∞ :=
  let Q : ℕ := 12012 + 48017 * (2 ^ 27 + 2 * fuel + 2)
  Q * (1 - (2 : ℝ≥0∞)⁻¹ ^ 17) ^ fuel

/-- **The committed size of an execution**: the number of cells the honest prover commits to,
every committed column at its table's height, the least power of two holding the table's rows
(`1` for no row), and at least `2^9` for the `KECCAK` table (`TABLE_LOG_FLOORS`,
`verifier.py:970`). The memory has four columns of `2^κ` rows, and the bytecode's counts (`BFCNT`)
one of `2^logSize` rows. Each opcode has a table of one row per instruction of that opcode the
execution executes (`Trace.count`), with `15, 15, 8, 15, 14, 26` committed columns for `XOR`,
`MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP`, `KECCAK` (of the `KECCAK` table's `90` columns, the
fifty value lanes are committed in `q_keccak`, or not at all, and fourteen more in `q_keccak`'s
spare slots); and `q_keccak` has `2^6` rows per row of the `KECCAK` table. -/
noncomputable def Semantics.Trace.committedSize {prog : Program} (t : Trace prog) : ℕ :=
  let height (op : Opcode) : ℕ := 2 ^ Nat.clog 2 (t.count op)
  let keccakHeight : ℕ := 2 ^ max (Nat.clog 2 (t.count .keccak)) 9
  4 * 2 ^ t.κ + 2 ^ prog.logSize +
    15 * height .xor + 15 * height .mulNative + 8 * height .setConstant + 15 * height .deref +
    14 * height .jump + 26 * keccakHeight + 2 ^ 6 * keccakHeight

end
end LeanVM

end

@[expose] public section

/-!
## The statements, in the random-permutation model

The model: one permutation `π` of the Keccak state (`KState`, 1600 bits), sampled uniformly and
queried forward (`π x`) and inverse (`π⁻¹ y`), the random-permutation model (RPM). Keccak-256
and Keccak-f[1600], which the verifier calls (`verifier H F`, `LeanVM/Spec/Statement.lean`), are
both built from it.

* **The permutation** is `Common.lazyPerm`, the lazily sampled uniform permutation of
  `common` (`common/Common/Model.lean`): its state is the list of edges `(x, π x)` fixed so
  far (`PermLog`); a fresh forward query draws `π x` uniformly among the states that are not yet
  the output of an edge, a fresh inverse query `π⁻¹ y` uniformly among the states that are not yet
  the input of an edge.
* **Keccak-256** (`keccak256With π`) is `keccak256` (`LeanVM/Spec/Keccak.lean`, `keccak_hash`,
  `verifier.py:191-209`) with `π` in place of Keccak-f[1600]: the sponge of rate 136 bytes and
  capacity 512 bits, the padding `0x01 ‖ 0^* ‖ 0x80`, the zero initial state, the first four lanes
  as the digest. **Keccak-f[1600]**, the Fiat-Shamir duplex's permutation, is `π` itself. The
  verifier's and the honest prover's calls (`HashSpec`, `Statement.lean`) are answered so
  (`rpmImpl`).
* **The adversary** (`RpmAdversary`) queries `π` and `π⁻¹` only, and outputs a statement and a
  proof; a Keccak-256 evaluation is a sequence of forward queries, which it makes itself. Every
  query and its answer is recorded, in order (`Transcript`, `loggedPerm`).
* **The experiment** (`rpmExperiment`): the adversary against the lazily sampled permutation from
  no edge, then the verifier on its statement and proof against the same permutation (`H` the
  sponge over `π`, `F = π`); the outcome is the statement and the proof, the verdict, and the
  adversary's transcript.

**Knowledge soundness** (`KnowledgeSoundness`) is stated for one extractor, `extractorRpm`, which
is straight-line: it reads the proof and the adversary's transcript, and nothing else (not the
verifier's queries, not the permutation's other values; it neither queries `π` nor rewinds the
adversary). It is the extractor of `Extractor.lean` (`LeanVM.Extraction.extract`) run on the
Keccak-256 evaluations the transcript contains (`transcriptHashes`): a byte string `m` has digest
`d` when the transcript holds the whole padded sponge path of `m`, a chain of forward queries from
the zero state, each one absorbing the next block into the answer of the one before and each the
query that first fixed its edge (an edge first fixed by an inverse query extends no path), as the
indifferentiability simulator of `common` books it (`Common.pathsOf`, on the bytes of the
states, `KState.toRpm`); `d` is the first four lanes of the path's last answer. It reads the
announced sizes and the stack's Merkle root off the proof; reads the word the root commits to off
those evaluations (each leaf the preimage, among them, of a path climbing to the root); and
returns the halting run of the memory image of a stack in the word's Johnson list (a stack whose
Reed–Solomon encoding agrees with the word on at least the Johnson threshold of columns), one that
is a valid execution if there is one. For every adversary of at most `Q` queries to `π` and `π⁻¹`,
the probability that the verifier accepts while the extractor does not return a valid execution
of the program on the public input is at most `soundnessError Q + rpmError (Q + verifierPermCalls)`: `soundnessError Q`
(`Statement.lean`) plus `q² / 2^508` for `q` the permutation calls of the whole experiment, the
adversary's `Q` and at most `verifierPermCalls` of the verifier. So an accepted proof commits,
except with that probability, to a stack whose memory columns hold a valid execution, among the at
most `2^18` stacks the word the adversary hashed is close to (proved, for every admissible shape
and word: `LeanVM.candidates_ncard_le`). The choice among them is classical: the extractor is a
definition, not an algorithm with a running time.

**Completeness** (`Completeness`): there is an honest prover (an oracle computation over the
calls of `Statement.lean`, answered here with both functions built from `π`) which, given a valid
execution whose committed size is at most `2^28`, the most the verifier admits
(`Trace.committedSize`), at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4`, trying at most `fuel ≤ 2^64`
nonces per proof of work, makes the verifier reject with probability at most
`completenessError fuel` plus `q² / 2^508`, `q` the permutation calls of the prover and the
verifier (`completenessPermCalls`). The honest prover is not required to be efficient.

**Scope and trust.** The permutation is uniformly random; the deployed Keccak-f[1600] is a fixed
permutation, and that it behaves as a random one is the assumption of this model. Inside the
executed program the `KECCAK` instruction computes the deployed Keccak-f[1600], not `π`. The
definitions rest on `common` (the lazily sampled permutation, the sponge's padding and
`pathsOf`), VCVio and the files of `LeanVM/Spec/`. The `common` definitions they use are in
`Model.lean` (`lazyPerm`, `uniformAvoiding`, the edge lookups), `Sponge.lean` (the byte state,
`ofBytes`, `zero`, `keccakPadding`, `blockTo`, `rxor`), `Indiff/Defs.lean` (`SimState.init`,
`chainOf`) and `Transfer.lean` (`replayStep`, `replay`, `simPaths`, `pathsOf`); the rest of
`common` is proof.

**How the proofs reach this model** (not part of the statement). The proofs first prove both
statements with Keccak-256 and Keccak-f[1600] two independent random oracles
(`LeanVM/Protocol/Rom/Statement.lean`, `LeanVM.knowledgeSoundnessRom_holds`,
`LeanVM.completenessRom_holds`), then move them here with `common`'s indifferentiability of the
sponge from a random oracle, with the duplex's direct permutation calls
(`Common.keccak256_transfer2`, `q² / 2^508`).

The proofs are `LeanVM.knowledgeSoundness_holds` and `LeanVM.completeness_holds`
(`LeanVM/Protocol/LeanVMRpm.lean`).
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

/-! ### Keccak-256 over a permutation -/

namespace Rpm

section With

variable {m : Type → Type} [Monad m] (π : KState → m KState)

/-- `absorbBlock` with `π` for Keccak-f[1600]: XOR the block's `17` little-endian lanes into the
rate, then permute. -/
def absorbBlockWith (state : KState) (block : List UInt8) : m KState :=
  π (Vector.ofFn fun i ↦
    if i.val < 17 then Keccak.lane state i ^^^ leLane block i else Keccak.lane state i)

/-- `KeccakHash.absorb` with `π` for Keccak-f[1600]: `blocks` whole blocks of `136` bytes, then
the padded last block. -/
def absorbWith : ℕ → KState → List UInt8 → m KState
  | 0, state, data => absorbBlockWith π state (padBlock data)
  | blocks + 1, state, data => do
    let state ← absorbBlockWith π state (data.take rate)
    absorbWith blocks state (data.drop rate)

end With

end Rpm

/-- **Keccak-256 over a permutation `π`**, in any monad: `keccak256` (`LeanVM/Spec/Keccak.lean`)
with `π` for Keccak-f[1600]. At `π = keccakF` it is `keccak256`
(`LeanVM.Rpm.keccak256With_keccakF`). -/
def keccak256With {m : Type → Type} [Monad m] (π : KState → m KState) (data : Bytes) :
    m Digest := do
  let state ← Rpm.absorbWith π (data.length / rate) (Vector.replicate 25 0) data
  pure #v[Keccak.lane state 0, Keccak.lane state 1, Keccak.lane state 2, Keccak.lane state 3]

/-! ### The random permutation -/

/-- The oracle of the random-permutation model: `π` and `π⁻¹` on Keccak states
(`Common.permSpec`; a query is `.fwd x` or `.inv y`). -/
abbrev PermSpec : OracleSpec (Common.PermQuery KState) := Common.permSpec KState

/-- The state of the lazily sampled permutation: the edges `(x, π x)` fixed so far, newest
first. -/
abbrev PermLog : Type := Common.PermLog KState

/-- `π x`: a forward query to the lazily sampled uniform permutation (`Common.lazyPerm`). -/
noncomputable def perm (x : KState) : StateT PermLog ProbComp KState :=
  Common.lazyPerm (.fwd x)

/-- **The verifier's calls (`Statement.lean`) in the random-permutation model**: Keccak-256 is the
sponge over the random permutation, Keccak-f[1600] is the random permutation. -/
noncomputable def rpmImpl : QueryImpl HashSpec (StateT PermLog ProbComp)
  | .inl x => keccak256With perm x
  | .inr s => perm s

/-! ### The experiment -/

/-- An adversary in the random-permutation model: a computation with oracle access to `π` and
`π⁻¹` that outputs a statement and a proof. It has no coins of its own: the extractor is fixed,
so a randomized adversary's probability of breaking it is an average of deterministic
adversaries' probabilities, and one of them does at least as well. -/
abbrev RpmAdversary : Type := OracleComp PermSpec (Statement × Proof)

/-- A transcript: queries to `π` and `π⁻¹` with their answers, oldest first. -/
abbrev Transcript : Type := List (Common.PermQuery KState × KState)

/-- The adversary's oracle: the lazily sampled permutation, each query and its answer appended
to the transcript. -/
noncomputable def loggedPerm : QueryImpl PermSpec (StateT (PermLog × Transcript) ProbComp) :=
  fun q ↦ StateT.mk fun s ↦
    (fun r ↦ (r.1, (r.2, s.2 ++ [(q, r.1)]))) <$> (Common.lazyPerm q).run s.1

/-- An outcome of the experiment: the statement and the proof, the verdict, and the adversary's
transcript. -/
abbrev RpmOutcome : Type := ((Statement × Proof) × Bool) × Transcript

/-- The outcome's program. -/
abbrev RpmOutcome.program (z : RpmOutcome) : Program := z.1.1.1.1

/-- The outcome's public input. -/
abbrev RpmOutcome.input (z : RpmOutcome) : PublicInput := z.1.1.1.2

/-- The outcome's proof. -/
abbrev RpmOutcome.proof (z : RpmOutcome) : Proof := z.1.1.2

/-- The verifier accepted. -/
abbrev RpmOutcome.accepted (z : RpmOutcome) : Prop := z.1.2 = true

/-- The adversary's transcript. -/
abbrev RpmOutcome.transcript (z : RpmOutcome) : Transcript := z.2

/-- **The random-permutation experiment**: the adversary against the lazily sampled permutation
from no edge, its queries recorded; then the verifier on its statement and proof, with
Keccak-256 the sponge over the same permutation and Keccak-f[1600] the permutation. -/
noncomputable def rpmExperiment (A : RpmAdversary) : ProbComp RpmOutcome := do
  let (z, perms, transcript) ← (simulateQ loggedPerm A).run ([], [])
  let verdict ← (simulateQ rpmImpl (verifier queryH queryF z.1.1 z.1.2 z.2)).run' perms
  return ((z, verdict), transcript)

/-! ### The extractor -/

/-- The 200 bytes of a Keccak state, as `common` splits them (32 digest bytes, 104 more bytes
of the rate, 64 bytes of capacity): byte `8i + k` is byte `k` of lane `i`, little-endian
(`keccak_hash`'s `unpack("<17Q", ...)`, `verifier.py:207`). -/
def KState.toRpm (s : KState) : Common.KState :=
  Common.KState.ofBytes (s.toList.flatMap wordBytes)

/-- A digest of 32 bytes as four little-endian words (`Digest.words`, `verifier.py:221-223`). -/
def Digest.ofRpm (d : Common.KDigest) : Digest :=
  #v[leLane d.toList 0, leLane d.toList 1, leLane d.toList 2, leLane d.toList 3]

/-- A query on the bytes of the states. -/
def permQueryToRpm : Common.PermQuery KState → Common.PermQuery Common.KState
  | .fwd x => .fwd (KState.toRpm x)
  | .inv y => .inv (KState.toRpm y)

/-- **The Keccak-256 evaluations a transcript contains**: the byte strings whose whole padded
sponge path the transcript holds as a chain of forward queries from the zero state, each the query
that first fixed its edge, each with the
first four lanes of the path's last answer, as `common` reads them (`Common.pathsOf`, the
indifferentiability simulator's bookkeeping replayed on the transcript, on the bytes of the
states). -/
noncomputable def transcriptHashes (T : Transcript) (x : Bytes) : Option Digest :=
  ((Common.pathsOf Common.keccakPadding Common.KState.zero
      (T.map fun e ↦ (permQueryToRpm e.1, KState.toRpm e.2))).find? (·.1 = x)).map
    fun p ↦ Digest.ofRpm p.2

/-- An extractor in the random-permutation model: from the adversary's transcript and the
proof, an execution of the program. -/
abbrev RpmExtractor : Type :=
  (prog : Program) → PublicInput → Transcript → Proof → Option (Trace prog)

/-- **The extractor in the random-permutation model**: the extractor of `Extractor.lean`
(`LeanVM.Extraction.extract`) on the Keccak-256 evaluations of the adversary's transcript. -/
noncomputable def extractorRpm : RpmExtractor := fun prog input T proof ↦
  Extraction.extract prog input (bytecodeWords prog) (transcriptHashes T) proof

/-! ### Knowledge soundness -/

/-- **The adversary breaks soundness**: the verifier accepts its statement and proof, and the
execution extracted from the transcript and the proof is not a valid execution of the program on
the public input. -/
def BreaksRpm (extract : RpmExtractor) (z : RpmOutcome) : Prop :=
  z.accepted ∧ ¬ ∃ t, extract z.program z.input z.transcript z.proof = some t ∧
    ValidExecution z.program z.input t

/-- The permutation calls of the verifier, at most, on every statement and proof: its
`verifierQueries = 12008` queries, each a permutation or a Keccak-256 hash of at most `2^39`
bytes (the bytecode: `16` words of `8` bytes per instruction, at most `2^32` instructions), which
is at most `⌊2^39 / 136⌋ + 1 ≤ 2^32` blocks, one permutation each. -/
def verifierPermCalls : ℕ := verifierQueries * 2 ^ 32

/-- The second term of the bounds, for an experiment of `q` permutation calls: `q² / 2^508`, the
cost of building Keccak-256 and Keccak-f[1600] from one random permutation rather than taking them
independent random functions (`Common.keccak256_transfer2`). -/
noncomputable def rpmError (q : ℕ) : ℝ≥0∞ := (q ^ 2 : ℝ≥0∞) / 2 ^ 508

/-- **Knowledge soundness in the random-permutation model**, for the extractor `extractorRpm`:
an adversary of at most `Q` queries to `π` and `π⁻¹` breaks soundness with probability at most
`soundnessError Q` plus `rpmError` of the experiment's permutation calls. -/
def KnowledgeSoundness : Prop :=
  ∀ (A : RpmAdversary) (Q : ℕ), A.IsTotalQueryBound Q →
    Pr{let z ← rpmExperiment A}[BreaksRpm extractorRpm z] ≤
      soundnessError Q + rpmError (Q + verifierPermCalls)

/-! ### Completeness -/

/-- **The completeness experiment in the random-permutation model**: the honest prover's proof,
then the verifier's verdict on it, both with Keccak-256 the sponge over the lazily sampled
permutation and Keccak-f[1600] the permutation. -/
noncomputable def rpmCompletenessExperiment (prover : HonestProver) (prog : Program)
    (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ) : ProbComp Bool :=
  (simulateQ rpmImpl (do
    let proof ← prover prog input t ρ fuel
    verifier queryH queryF prog input proof)).run' []

/-- The permutation calls of the honest prover and the verifier together, at most: the
`12012 + 48017 · (2^27 + 2·fuel + 2)` queries of `completenessError`, each at most `2^32`
blocks. -/
def completenessPermCalls (fuel : ℕ) : ℕ := (12012 + 48017 * (2 ^ 27 + 2 * fuel + 2)) * 2 ^ 32

/-- **Completeness in the random-permutation model.** -/
def Completeness : Prop :=
  ∃ prover : HonestProver, ∀ (prog : Program) (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ),
    ValidExecution prog input t →
    t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 → fuel ≤ 2 ^ 64 →
    Pr{let v ← rpmCompletenessExperiment prover prog input t ρ fuel}[v = false] ≤
      completenessError fuel + rpmError (completenessPermCalls fuel)

end LeanVM

end

@[expose] public section

/-! ### Knowledge soundness in bits -/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open OracleComp OracleSpec
open scoped ENNReal

/-- **Knowledge soundness, in bits**: an adversary of at most `Q ≤ 2^120` queries to `π` and
`π⁻¹` breaks soundness (`BreaksRpm extractorRpm`, as in `KnowledgeSoundness`) with probability at
most `(Q + 2^14) · 2^-127`. Proved by `LeanVM.knowledgeSoundness_bits`. -/
abbrev KnowledgeSoundnessBits : Prop :=
  ∀ (A : RpmAdversary) (Q : ℕ), A.IsTotalQueryBound Q →
    Q ≤ 2 ^ 120 →
      Pr{let z ← rpmExperiment A}[BreaksRpm extractorRpm z] ≤
        (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 127

end LeanVM

end
