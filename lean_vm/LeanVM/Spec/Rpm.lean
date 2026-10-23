/-
  LeanVM.Spec.Rpm

  What is proved about the leanVM verifier in the random-permutation model: knowledge soundness
  and completeness, stated as two propositions, with Keccak-256 and Keccak-f[1600] both built from
  one uniformly random permutation of the Keccak state.
-/

import LeanVM.Spec.Statement
import LeanRpm.Transfer

/-!
# The statements in the random-permutation model

`LeanVM/Spec/Statement.lean` states knowledge soundness and completeness with Keccak-256 and
Keccak-f[1600] as two independent random oracles. Here both are built from one permutation `π` of
the Keccak state (`KState`, 1600 bits), sampled uniformly and queried forward (`π x`) and inverse
(`π⁻¹ y`): the random-permutation model (RPM).

* **The permutation** is `LeanRpm.lazyPerm`, the lazily sampled uniform permutation of
  `lean_rpm` (`lean_rpm/LeanRpm/Model.lean`): its state is the list of edges `(x, π x)` fixed so
  far (`PermLog`); a fresh forward query draws `π x` uniformly among the states that are not yet
  the output of an edge, a fresh inverse query `π⁻¹ y` uniformly among the states that are not yet
  the input of an edge.
* **Keccak-256** (`keccak256With π`) is `keccak256` (`LeanVM/Spec/Keccak.lean`, `keccak_hash`,
  `verifier.py:191-207`) with `π` in place of Keccak-f[1600]: the sponge of rate 136 bytes and
  capacity 512 bits, the padding `0x01 ‖ 0^* ‖ 0x80`, the zero initial state, the first four lanes
  as the digest. **Keccak-f[1600]**, the Fiat-Shamir duplex's permutation, is `π` itself. The two
  oracles of `Statement.lean` are implemented so (`rpmImpl`), and the verifier and the honest
  prover run against this implementation.
* **The adversary** (`RpmAdversary`) queries `π` and `π⁻¹` only, and outputs a statement and a
  proof; a Keccak-256 evaluation is a sequence of forward queries, which it makes itself. Every
  query and its answer is recorded, in order (`Transcript`, `loggedPerm`).
* **The experiment** (`rpmExperiment`): the adversary against the lazily sampled permutation from
  no edge, then the verifier on its statement and proof against the same permutation (`H` the
  sponge over `π`, `F = π`); the outcome is the statement and the proof, the verdict, and the
  adversary's transcript.

**Knowledge soundness** (`KnowledgeSoundnessRpm`) is stated for one extractor, `extractorRpm`,
which is straight-line: it reads the proof and the adversary's transcript, and nothing else (not
the verifier's queries, not the permutation's other values; it neither queries `π` nor rewinds the
adversary). It is the extractor of `Statement.lean` (`LeanVM.Extraction.extract`) run on the
Keccak-256 evaluations the transcript contains (`transcriptHashes`): a byte string `m` has digest
`d` when the transcript holds the whole padded sponge path of `m`, a chain of forward queries from
the zero state, each one absorbing the next block into the answer of the one before and each the
query that first fixed its edge (an edge first fixed by an inverse query extends no path), as the
indifferentiability simulator of `lean_rpm` books it (`LeanRpm.pathsOf`, on the bytes of the
states, `KState.toRpm`); `d` is the first four lanes of the path's last answer. The bound is the
random-oracle bound at the adversary's query count, plus `q² / 2^508` for `q` the permutation
calls of the whole experiment (`rpmError`): the adversary's `Q`, and at most `verifierPermCalls`
of the verifier.

**Completeness** (`CompletenessRpm`): there is an honest prover (an oracle computation over the
two oracles of `Statement.lean`, run here with both built from `π`) which, given a valid
execution within the verifier's size cap, makes the verifier reject with probability at most the
random-oracle error plus `q² / 2^508`, `q` the permutation calls of the prover and the verifier
(`completenessPermCalls`).

**Scope and trust.** The permutation is uniformly random; the deployed Keccak-f[1600] is a fixed
permutation, and that it behaves as a random one is the assumption of this model. Inside the
executed program the `KECCAK` instruction computes the deployed Keccak-f[1600], not `π`, as in
`Statement.lean`. The definitions rest on `lean_rpm` (the lazily sampled permutation, the sponge's
padding and `pathsOf`), VCVio and the files of `LeanVM/Spec/`. The `lean_rpm` definitions they
use are in `Model.lean` (`lazyPerm`, `uniformAvoiding`, the edge lookups), `Sponge.lean` (the byte
state, `ofBytes`, `zero`, `keccakPadding`, `blockTo`, `rxor`), `Indiff/Defs.lean`
(`SimState.init`, `chainOf`) and `Transfer.lean` (`replayStep`, `replay`, `simPaths`,
`pathsOf`); the rest of `lean_rpm` is proof.

The proofs are `LeanVM.knowledgeSoundnessRpm_holds` and `LeanVM.completenessRpm_holds`
(`LeanVM/Protocol/LeanVMRpm.lean`).
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

/-! ## Keccak-256 over a permutation -/

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

/-! ## The random permutation -/

/-- The oracle of the random-permutation model: `π` and `π⁻¹` on Keccak states
(`LeanRpm.permSpec`; a query is `.fwd x` or `.inv y`). -/
abbrev PermSpec : OracleSpec (LeanRpm.PermQuery KState) := LeanRpm.permSpec KState

/-- The state of the lazily sampled permutation: the edges `(x, π x)` fixed so far, newest
first. -/
abbrev PermLog : Type := LeanRpm.PermLog KState

/-- `π x`: a forward query to the lazily sampled uniform permutation (`LeanRpm.lazyPerm`). -/
noncomputable def perm (x : KState) : StateT PermLog ProbComp KState :=
  LeanRpm.lazyPerm (.fwd x)

/-- **The two oracles of `Statement.lean` in the random-permutation model**: Keccak-256 is the
sponge over the random permutation, Keccak-f[1600] is the random permutation. -/
noncomputable def rpmImpl : QueryImpl HashSpec (StateT PermLog ProbComp)
  | .inl x => keccak256With perm x
  | .inr s => perm s

/-! ## The experiment -/

/-- An adversary in the random-permutation model: a computation with oracle access to `π` and
`π⁻¹` that outputs a statement and a proof. It has no coins of its own: the extractor is fixed,
so a randomized adversary's probability of breaking it is an average of deterministic
adversaries' probabilities, and one of them does at least as well. -/
abbrev RpmAdversary : Type := OracleComp PermSpec (Statement × Proof)

/-- A transcript: queries to `π` and `π⁻¹` with their answers, oldest first. -/
abbrev Transcript : Type := List (LeanRpm.PermQuery KState × KState)

/-- The adversary's oracle: the lazily sampled permutation, each query and its answer appended
to the transcript. -/
noncomputable def loggedPerm : QueryImpl PermSpec (StateT (PermLog × Transcript) ProbComp) :=
  fun q ↦ StateT.mk fun s ↦
    (fun r ↦ (r.1, (r.2, s.2 ++ [(q, r.1)]))) <$> (LeanRpm.lazyPerm q).run s.1

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

/-! ## The extractor -/

/-- The 200 bytes of a Keccak state, as `lean_rpm` splits them (32 digest bytes, 104 more bytes
of the rate, 64 bytes of capacity): byte `8i + k` is byte `k` of lane `i`, little-endian
(`keccak_hash`'s `unpack("<17Q", ...)`, `verifier.py:205`). -/
def KState.toRpm (s : KState) : LeanRpm.KState :=
  LeanRpm.KState.ofBytes (s.toList.flatMap wordBytes)

/-- A digest of 32 bytes as four little-endian words (`Digest.words`, `verifier.py:219-221`). -/
def Digest.ofRpm (d : LeanRpm.KDigest) : Digest :=
  #v[leLane d.toList 0, leLane d.toList 1, leLane d.toList 2, leLane d.toList 3]

/-- A query on the bytes of the states. -/
def permQueryToRpm : LeanRpm.PermQuery KState → LeanRpm.PermQuery LeanRpm.KState
  | .fwd x => .fwd (KState.toRpm x)
  | .inv y => .inv (KState.toRpm y)

/-- **The Keccak-256 evaluations a transcript contains**: the byte strings whose whole padded
sponge path the transcript holds as a chain of forward queries from the zero state, each the query
that first fixed its edge, each with the
first four lanes of the path's last answer, as `lean_rpm` reads them (`LeanRpm.pathsOf`, the
indifferentiability simulator's bookkeeping replayed on the transcript, on the bytes of the
states). -/
noncomputable def transcriptHashes (T : Transcript) (x : Bytes) : Option Digest :=
  ((LeanRpm.pathsOf LeanRpm.keccakPadding LeanRpm.KState.zero
      (T.map fun e ↦ (permQueryToRpm e.1, KState.toRpm e.2))).find? (·.1 = x)).map
    fun p ↦ Digest.ofRpm p.2

/-- An extractor in the random-permutation model: from the adversary's transcript and the
proof, an execution of the program. -/
abbrev RpmExtractor : Type :=
  (prog : Program) → PublicInput → Transcript → Proof → Option (Trace prog)

/-- **The extractor in the random-permutation model**: the extractor of `Statement.lean`
(`LeanVM.Extraction.extract`, `LeanVM/Spec/Extractor.lean`) on the Keccak-256 evaluations of the
adversary's transcript. -/
noncomputable def extractorRpm : RpmExtractor := fun prog input T proof ↦
  Extraction.extract prog input (bytecodeWords prog) (transcriptHashes T) proof

/-! ## Knowledge soundness -/

/-- **The adversary breaks soundness**: the verifier accepts its statement and proof, the
program's last instruction is not a `JUMP`, and the execution extracted from the transcript and
the proof is not a valid execution of the program on the public input. -/
def BreaksRpm (extract : RpmExtractor) (z : RpmOutcome) : Prop :=
  z.accepted ∧ SentinelSafe z.program ∧
    ¬ ∃ t, extract z.program z.input z.transcript z.proof = some t ∧
      ValidExecution z.program z.input t

/-- The permutation calls of the verifier, at most, on every statement and proof: its
`verifierQueries = 12008` queries, each a permutation or a Keccak-256 hash of at most `2^39`
bytes (the bytecode: `16` words of `8` bytes per instruction, at most `2^32` instructions), which
is at most `⌊2^39 / 136⌋ + 1 ≤ 2^32` blocks, one permutation each. -/
def verifierPermCalls : ℕ := verifierQueries * 2 ^ 32

/-- The cost of replacing the two random oracles by one random permutation, for an experiment of
`q` permutation calls (`LeanRpm.keccak256_transfer2`). -/
noncomputable def rpmError (q : ℕ) : ℝ≥0∞ := (q ^ 2 : ℝ≥0∞) / 2 ^ 508

/-- **Knowledge soundness in the random-permutation model**, for the extractor `extractorRpm`:
an adversary of at most `Q` queries to `π` and `π⁻¹` breaks soundness with probability at most
the random-oracle error at `Q` queries plus `rpmError` of the experiment's permutation calls. -/
def KnowledgeSoundnessRpm : Prop :=
  ∀ (A : RpmAdversary) (Q : ℕ), A.IsTotalQueryBound Q →
    Pr{let z ← rpmExperiment A}[BreaksRpm extractorRpm z] ≤
      soundnessError Q + rpmError (Q + verifierPermCalls)

/-! ## Completeness -/

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
def CompletenessRpm : Prop :=
  ∃ prover : HonestProver, ∀ (prog : Program) (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ),
    ValidExecution prog input t →
    t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 → fuel ≤ 2 ^ 64 →
    Pr{let v ← rpmCompletenessExperiment prover prog input t ρ fuel}[v = false] ≤
      completenessError fuel + rpmError (completenessPermCalls fuel)

end LeanVM
