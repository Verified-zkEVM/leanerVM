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
random-permutation model, `LeanVM.KnowledgeSoundness` and `LeanVM.Completeness`, proved by
`LeanVM.knowledgeSoundness_holds` and `completeness_holds` (`LeanVM/Protocol/LeanVMRpm.lean`;
`lean_vm/README.md` says how they reach this model).

The verifier receives a statement as the program's bytecode and the public input's digest, and a
proof. It is written for any hash function `H` and permutation `F` in any monad (`verifier H F`).
It and the honest prover call Keccak-256 and Keccak-f[1600] as oracle queries (`HashSpec`), which
the random-permutation model answers: one uniformly random permutation `π` of the Keccak state,
queried forward and inverse, Keccak-256 the sponge over `π` and Keccak-f[1600] `π` itself.

* **The permutation** is `Common.lazyPerm`, the lazily sampled uniform permutation
  (`RandomPermutation.lean`): its state is the list of edges `(x, π x)` fixed so far (`PermLog`);
  a fresh forward query draws `π x` uniformly among the states that are not yet the output of an
  edge, a fresh inverse query `π⁻¹ y` uniformly among the states that are not yet the input of
  an edge.
* **Keccak-256** (`keccak256With π`, `RandomPermutation.lean`) is `keccak_hash`
  (`verifier.py:191-209`) with `π` in place of Keccak-f[1600]: the sponge of rate 136 bytes and
  capacity 512 bits, the padding `0x01 ‖ 0^* ‖ 0x80`, the zero initial state, the first four lanes
  as the digest.
* **The adversary** (`RpmAdversary`) queries `π` and `π⁻¹` only, and outputs a statement and a
  proof; a Keccak-256 evaluation is a sequence of forward queries, which it makes itself. Every
  query and its answer is recorded, in order (`Transcript`, `loggedPerm`).
* **The experiment** (`rpmExperiment`): the adversary against the lazily sampled permutation from
  no edge, then the verifier on its statement and proof against the same permutation.

**Knowledge soundness** is stated for one extractor, `extractorRpm`, which is straight-line: it
reads the proof and the adversary's transcript, and nothing else (it neither queries `π` nor
rewinds the adversary). It is `Extractor.lean`'s `extract` on the Keccak-256 evaluations the
transcript contains: a byte string `m` has digest `d` when the transcript holds the whole padded
sponge path of `m`, a chain of forward queries from the zero state, each one absorbing the next
block into the answer of the one before and each the query that first fixed its edge (an edge
first fixed by an inverse query extends no path), as the indifferentiability simulator books it
(`transcriptPaths`); `d` is the first four lanes of the path's last answer. An accepted proof thus commits, except with the bound's probability, to a stack whose
memory columns hold a valid execution, among the at most `2^18` stacks the word the adversary
hashed is close to (proved for every admissible shape and word: `LeanVM.candidates_ncard_le`).
The extractor is deterministic and computable, with running time polynomial in the announced
committed size `2^μ` and the number of evaluations, not in the proof's size, and infeasible at
deployed sizes; its cost (`Extractor.lean`) is read off its loops, not proved.

**Completeness** is stated for one honest prover, `prover`: `LeanVM.Prover.prove`
(`Statement/Prover/Prove.lean`) with the oracle calls, an executable program (with Keccak-256 and
Keccak-f[1600] it is `lake exe leanvm-prove`). Given a valid execution whose committed size is at
most `2^28`, the most the verifier admits, at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4`, trying
`2^25` nonces per proof of work, its proof is rejected with probability at most `2^-127`. The
prover's definitions are in `Statement/Prover/`, which a reviewer need not read line by line: it
is proved to make the moves of the honest prover the completeness proof follows; a reviewer only
checks that it is a genuine prover (it computes from the execution, its only search is the nonce
search within the fuel, and it branches on no hash or permutation answer other than through the
challenges the verifier's program samples).

**Scope and trust.**

* The permutation is uniformly random; the deployed Keccak-f[1600] is a fixed permutation, and
  that it behaves as a random one is the assumption of this model. Inside the executed program the
  `KECCAK` instruction computes the deployed Keccak-f[1600], not `π`.
* A proof is the Python verifier's format: the scalar stream and one full Merkle path per query.
  The Rust prover ships pruned paths, which the deployed Rust verifier expands into these paths;
  that expansion is not formalized.
* That `verifier` is the Python and Rust verifiers is test evidence: it is a transcription of the
  Python, it accepts the Rust prover's proofs, and on mutated proofs it gives the Rust verifier's
  verdict every time (`scripts/fuzz-verifier.py`).
* The definitions rest on Mathlib, CompPoly (the fields), VCVio (oracle computations, query
  bounds) and the statement's own files; the model's definitions (namespace `Common`) are
  `RandomPermutation.lean`'s, and the proof project `common` proves about them.
-/

@[expose] public section

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

/-! ### The verifier on a statement -/

/-- A proof: the scalar stream and the Merkle openings. -/
abbrev Proof := Compile.Proof

-- The bytecode the verifier reads (`bytecodeWords`) and the public input as it reads it
-- (`publicDigest`) are `LeanIsa.lean`'s, where the encoding is.

/-- **The leanVM verifier**, for a hash function `H` and a permutation `F` in any monad `m`: does
`proof` show that `prog` runs on `input`? -/
def verifier {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KState → m KState)
    (prog : Program) (input : PublicInput) (proof : Proof) : m Bool :=
  verifyWith H F (bytecodeWords prog) (publicDigest input) proof

/-! ### The oracle calls -/

/-- The verifier's and the honest prover's calls: Keccak-256, a function from byte strings to
digests (queries `.inl x`), and Keccak-f[1600], a function from states to states (queries
`.inr s`). What answers them is the model's (`rpmImpl`, below: the sponge over a random
permutation, and the permutation). -/
abbrev HashSpec : OracleSpec (Bytes ⊕ KState) := (Bytes →ₒ Digest) + (KState →ₒ KState)

/-- A call to the hash. -/
def queryH (x : Bytes) : OracleComp HashSpec Digest := liftM (HashSpec.query (.inl x))

/-- A call to the permutation. -/
def queryF (s : KState) : OracleComp HashSpec KState := liftM (HashSpec.query (.inr s))

/-- A statement: a program and a public input. -/
abbrev Statement : Type := Program × PublicInput

/-! ### The honest prover and the committed size -/

/-- An honest prover: from a statement, an execution, the commitment's rate exponent `ρ` and a
fuel of nonces per proof of work, a proof, computed with calls to Keccak-256 and Keccak-f[1600]
(`HashSpec`), which the model answers. -/
abbrev HonestProver : Type :=
  (prog : Program) → (input : PublicInput) → Trace prog → (ρ fuel : ℕ) → OracleComp HashSpec Proof

/-- **The honest prover**: `LeanVM.Prover.prove` (`Statement/Prover/Prove.lean`) with Keccak-256 and
Keccak-f[1600] the oracle calls. From the execution `t` it computes the witness (`witness?`, the
empty proof unless `t` is a valid execution within `2^28` committed cells), and, at a valid rate,
runs the honest script against the verifier's own program `leanVmProgram`, trying `fuel` nonces
per proof of work. -/
def prover : HonestProver := fun prog input t ρ fuel ↦ Prover.prove queryH queryF prog input t ρ fuel

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

/-- **The verifier's calls (`HashSpec`) in the random-permutation model**: Keccak-256 is the
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

/-- An outcome of the experiment: the statement (`program`, `input`) and the `proof`, the
verdict (`accepted`), and the adversary's `transcript`. -/
abbrev RpmOutcome : Type := ((Statement × Proof) × Bool) × Transcript

abbrev RpmOutcome.program (z : RpmOutcome) : Program := z.1.1.1.1
abbrev RpmOutcome.input (z : RpmOutcome) : PublicInput := z.1.1.1.2
abbrev RpmOutcome.proof (z : RpmOutcome) : Proof := z.1.1.2
abbrev RpmOutcome.accepted (z : RpmOutcome) : Prop := z.1.2 = true
abbrev RpmOutcome.transcript (z : RpmOutcome) : Transcript := z.2

/-- **The random-permutation experiment**: the adversary against the lazily sampled permutation
from no edge, its queries recorded; then the verifier on its statement and proof, with
Keccak-256 the sponge over the same permutation and Keccak-f[1600] the permutation. -/
noncomputable def rpmExperiment (A : RpmAdversary) : ProbComp RpmOutcome := do
  let (z, perms, transcript) ← (simulateQ loggedPerm A).run ([], [])
  let verdict ← (simulateQ rpmImpl (verifier queryH queryF z.1.1 z.1.2 z.2)).run' perms
  return ((z, verdict), transcript)

/-! ### The extractor -/

/-- The bytes Keccak-256 absorbs for the message `m`: its whole blocks of `136` bytes, then the
padded last block (`padBlock`, as `keccak256With` absorbs them). -/
def padded (m : Bytes) : Bytes :=
  m.take (rate * (m.length / rate)) ++ padBlock (m.drop (rate * (m.length / rate)))

/-- The message whose padding is `bs`, if any: the prefix of `bs` short of `1` to `136` bytes
that pads to `bs` (there is at most one). -/
def unpad (bs : Bytes) : Option Bytes :=
  ((List.range rate).map fun k ↦ bs.take (bs.length - 1 - k)).find? (padded · = bs)

/-- The extractor's bookkeeping of a transcript: the edges `(x, π x)` fixed so far, newest first,
and the states that a chain of forward queries reaches from the zero state, each with the bytes
its path absorbed, newest first. -/
structure Replay where
  /-- The edges `(x, π x)` fixed so far, newest first. -/
  edges : PermLog
  /-- The states reached from the zero state, with the bytes their paths absorbed. -/
  chains : List (KState × Bytes)

/-- One query and its answer. A forward query `π x` that fixes a new edge extends the chain of a
state `s` with the capacity of `x` (lanes `17 … 24`), if there is one, by the block that takes
`s` to `x`: the bytes of their rates' XOR, lanes `0 … 16`. An inverse query extends no chain. -/
def Replay.step (σ : Replay) : Common.PermQuery KState × KState → Replay
  | (.fwd x, y) =>
    match Common.fwdLookup σ.edges x with
    | some _ => σ
    | none =>
      match σ.chains.find? (fun p ↦ p.1.toList.drop 17 = x.toList.drop 17) with
      | some (s, bs) =>
        ⟨(x, y) :: σ.edges, (y, bs ++ (List.range 17).flatMap fun i ↦
          wordBytes (Keccak.lane s i ^^^ Keccak.lane x i)) :: σ.chains⟩
      | none => ⟨(x, y) :: σ.edges, σ.chains⟩
  | (.inv y, x) =>
    match Common.invLookup σ.edges y with
    | some _ => σ
    | none => ⟨(x, y) :: σ.edges, σ.chains⟩

/-- **The Keccak-256 evaluations a transcript holds**: the byte strings whose whole padded sponge
path the transcript (oldest first) holds as a chain of forward queries from the zero state, each
query absorbing the next block into the answer of the one before and each the query that first
fixed its edge, with the first four lanes of the path's last answer (the indifferentiability
simulator's bookkeeping, replayed). -/
def transcriptPaths (T : Transcript) : List (Bytes × Digest) :=
  (T.foldl Replay.step ⟨[], [(Vector.replicate 25 0, [])]⟩).chains.filterMap fun p ↦
    (unpad p.2).map fun m ↦ (m, #v[p.1[0], p.1[1], p.1[2], p.1[3]])

/-- The Keccak-256 evaluation of `x` among the paths `P`, if `P` holds one. -/
def hashesOf (P : List (Bytes × Digest)) (x : Bytes) : Option Digest :=
  (P.find? (·.1 = x)).map (·.2)

/-- An extractor in the random-permutation model: from the adversary's transcript and the
proof, an execution of the program. -/
abbrev RpmExtractor : Type :=
  (prog : Program) → PublicInput → Transcript → Proof → Option (Trace prog)

/-- **The extractor in the random-permutation model**: the extractor of `Extractor.lean`
(`LeanVM.Extraction.extract`) on the Keccak-256 evaluations of the adversary's transcript
(`hashesOf (transcriptPaths T)`), the byte strings they answer being those of the transcript's
paths. The paths are computed once. -/
def extractorRpm : RpmExtractor := fun prog input T proof ↦
  let paths := transcriptPaths T
  Extraction.extract prog input (bytecodeWords prog) (hashesOf paths) (paths.map (·.1)) proof

/-! ### Knowledge soundness -/

/-- **The adversary breaks soundness**: the verifier accepts its statement and proof, and the
execution extracted from the transcript and the proof is not a valid execution of the program on
the public input. -/
def BreaksRpm (extract : RpmExtractor) (z : RpmOutcome) : Prop :=
  z.accepted ∧ ¬ ∃ t, extract z.program z.input z.transcript z.proof = some t ∧
    ValidExecution z.program z.input t

/-- **Knowledge soundness in the random-permutation model**, for the extractor `extractorRpm`:
an adversary of at most `Q ≤ 2^128` queries to `π` and `π⁻¹` breaks soundness with probability at
most `(Q + 2^14) · 2^-128 + 7 (Q + 2^14)² · 2^-256`. -/
def KnowledgeSoundness : Prop :=
  ∀ (A : RpmAdversary) (Q : ℕ), A.IsTotalQueryBound Q → Q ≤ 2 ^ 128 →
    Pr{let z ← rpmExperiment A}[BreaksRpm extractorRpm z] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        7 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-! ### Completeness -/

/-- **The completeness experiment in the random-permutation model**: the honest prover's proof,
then the verifier's verdict on it, both with Keccak-256 the sponge over the lazily sampled
permutation and Keccak-f[1600] the permutation. -/
noncomputable def rpmCompletenessExperiment (prover : HonestProver) (prog : Program)
    (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ) : ProbComp Bool :=
  (simulateQ rpmImpl (do
    let proof ← prover prog input t ρ fuel
    verifier queryH queryF prog input proof)).run' []

/-- **Completeness in the random-permutation model**: trying `2^25` nonces per proof of work, the
honest prover's (`prover`) proof of an execution within the verifier's size cap is rejected with
probability at most `2^-127`. -/
def Completeness : Prop :=
  ∀ (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ),
    ValidExecution prog input t → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← rpmCompletenessExperiment prover prog input t ρ (2 ^ 25)}[v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 127

/-- **The random-permutation experiment of an adversary and a computation**: `rpmExperiment`
with any computation `V` over the verifier's calls in place of the verifier, without the
transcript; the experiment of the batching's end statement (`LeanVmGuest.lean`). -/
noncomputable def Rpm.rpmRun {α β : Type} (A : OracleComp PermSpec α)
    (V : α → OracleComp HashSpec β) : ProbComp (α × β) := do
  let (z, perms, _) ← (simulateQ loggedPerm A).run ([], [])
  let v ← (simulateQ rpmImpl (V z)).run' perms
  return (z, v)

/-- The public input a digest gives the instance: its four `u64` lanes as `K` words, the memory's
first two words being the digest's halves (`Digest.halves`, `verifier.py:225-228`;
`public_input_bytes`, `crates/leanvm_core/src/cpu/mod.rs:723-730`). -/
def Protocol.EndToEnd.Front.publicInputOfDigest (d : Digest) : PublicInput :=
  ⟨![K.ofLane d[0], K.ofLane d[1], K.ofLane d[2], K.ofLane d[3]]⟩

end LeanVM

end
