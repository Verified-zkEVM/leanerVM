/-
  LeanVM.Spec.Statement

  What is proved about the leanVM verifier: knowledge soundness and completeness in the
  random-oracle model, stated as two propositions.
-/

module

public import LeanVM.Spec.Isa
public import LeanVM.Spec.Verifier
public import LeanVM.Spec.Extractor
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.ProbabilityNotation

/-!
# The statements

The verifier receives a statement (a program and a public input) as the program's bytecode and
the public input's digest (`bytecodeWords`, `publicDigest`), and a proof. With BLAKE2s it is the
deployed verifier (`verify`). In the random-oracle model, the hash is a lazily sampled random
function from byte strings to digests (`HashSpec`, `queryH`), and an adversary is any
computation with access to it that outputs a statement and a proof, choosing both after querying
(`Adversary`). The experiment runs the adversary, then the verifier on its output, against one
oracle, and records the verdict, the oracle's answers at the end, and the oracle's answers to the
adversary's queries, as they stood when the adversary output its proof (`experiment`).

**Knowledge soundness** (`KnowledgeSoundness`): for every adversary of at most `Q` queries, the
probability that the verifier accepts while the program's last instruction is not a `JUMP`
(`SentinelSafe`) and the extractor does not return a valid execution of the program on the public
input is at most `soundnessError Q`. The extractor (`extractor`, `LeanVM/Spec/Extractor.lean`) is
fixed, and straight-line: it reads only the proof and the oracle's answers to the adversary's own
queries (not the verifier's), and neither queries the oracle nor rewinds the adversary. It reads
the announced sizes and the stack's Merkle root off the proof; reads the word the root commits to
off the adversary's answers (each leaf the preimage, among them, of a path climbing to the root);
and returns the halting run of the memory image of a stack in the word's Johnson list (a stack
whose Reed–Solomon encoding agrees with the word on at least the Johnson threshold of columns),
one that is a valid execution if there is one. So an accepted proof commits, except with
probability `soundnessError Q`, to a stack whose memory columns hold a valid execution, among the
at most `2^18` stacks the word the adversary hashed is close to (proved, for every admissible
shape and word: `LeanVM.candidates_ncard_le`, from level 0's list bound `listMax ≤ 2^18`). The
choice among them is classical: the extractor is a definition, not an algorithm with a running
time.

**Completeness** (`Completeness`): there is an honest prover which, given a valid execution whose
committed size is at most `2^28`, the most the verifier admits (`Trace.committedSize`: the cells
of the memory, of the bytecode's counts and of one table per opcode, a row per instruction of that
opcode the execution executes, `Trace.count`), at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4`, trying at most `fuel ≤ 2^64`
nonces per proof of work, makes the verifier reject with probability at most
`completenessError fuel`. The honest prover is not required to be efficient.

**Scope and trust.**

* BLAKE2s is modelled as a random oracle.
* A proof is the Python verifier's format: the scalar stream and one full Merkle path per query.
  The Rust prover ships pruned paths, which the deployed Rust verifier expands into these paths;
  that expansion is not formalized.
* That `verifier` is the Python and Rust verifiers is test evidence: it is a transcription of the
  Python, it accepts the Rust prover's proofs, and on mutated proofs it gives the Rust verifier's
  verdict every time (`scripts/fuzz-verifier.py`).
* The definitions rest on Mathlib, CompPoly (the fields) and VCVio (oracle computations, the
  random oracle, `Pr`, query bounds).

The proofs are `LeanVM.knowledgeSoundness_holds` and `LeanVM.completeness_holds`
(`LeanVM/Protocol/LeanVM.lean`).
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-! ## The verifier on a statement -/

/-- A proof: the scalar stream and the Merkle openings. -/
abbrev Proof := Compile.Proof

/-- The bytecode the verifier reads: the sixteen slots of every instruction (`encodeSlots`),
slot by slot: word `i + 2^logSize · s` is slot `s` of instruction `i`. -/
def bytecodeWords (prog : Program) : List K :=
  (List.finRange 16).flatMap fun s ↦
    (List.finRange (2 ^ prog.logSize)).map fun i ↦ (encodeSlots (prog.code i))[s]

/-- The public input as the verifier reads it: the low and high 32-bit words of its four lanes,
in order (`hash_to_scalars`, `crates/fiat_shamir/src/merkle.rs:8-19`, read backwards). -/
def publicDigest (input : PublicInput) : Digest :=
  #v[lowWord (input.lanes 0), highWord (input.lanes 0), lowWord (input.lanes 1),
    highWord (input.lanes 1), lowWord (input.lanes 2), highWord (input.lanes 2),
    lowWord (input.lanes 3), highWord (input.lanes 3)]

/-- **The leanVM verifier**, for a hash function `H` in any monad `m`: does `proof` show that
`prog` runs on `input`? -/
def verifier {m : Type → Type} [Monad m] (H : Bytes → m Digest) (prog : Program)
    (input : PublicInput) (proof : Proof) : m Bool :=
  verifyWith H (bytecodeWords prog) (publicDigest input) proof

/-- **The deployed verifier**: `verifier` with BLAKE2s-256. -/
def verify (prog : Program) (input : PublicInput) (proof : Proof) : Bool :=
  Id.run (verifier blake2sBytes prog input proof)

/-! ## The random-oracle model -/

/-- The random oracle: a function from byte strings to digests. -/
abbrev HashSpec : OracleSpec Bytes := Bytes →ₒ Digest

/-- A query to the random oracle. -/
def queryH (x : Bytes) : OracleComp HashSpec Digest := liftM (HashSpec.query x)

/-- A statement: a program and a public input. -/
abbrev Statement : Type := Program × PublicInput

/-- An adversary: a computation with oracle access to the hash function that outputs a statement
and a proof. -/
abbrev Adversary : Type := OracleComp HashSpec (Statement × Proof)

/-- An outcome of the experiment: the statement and the proof, the verdict, the oracle's answers
at the end (to the adversary's queries and the verifier's; no statement reads them, the proofs
relate them to the adversary's), and the oracle's answers when the adversary returned (to the
adversary's queries). -/
abbrev Outcome : Type :=
  ((Statement × Proof) × Bool) × HashSpec.QueryCache × HashSpec.QueryCache

/-- The outcome's program. -/
abbrev Outcome.program (z : Outcome) : Program := z.1.1.1.1

/-- The outcome's public input. -/
abbrev Outcome.input (z : Outcome) : PublicInput := z.1.1.1.2

/-- The outcome's proof. -/
abbrev Outcome.proof (z : Outcome) : Proof := z.1.1.2

/-- The verifier accepted. -/
abbrev Outcome.accepted (z : Outcome) : Prop := z.1.2 = true

/-- The verifier rejected. -/
abbrev Outcome.rejected (z : Outcome) : Prop := z.1.2 = false

/-- The oracle's answers to the adversary's queries: the cache when the adversary returned,
before the verifier ran. -/
abbrev Outcome.adversaryCache (z : Outcome) : HashSpec.QueryCache := z.2.2

/-- **The random-oracle experiment**: the adversary from the empty cache, then the verifier on its
statement and proof, continuing from the cache the adversary left: one lazily sampled random
oracle. -/
noncomputable def experiment (A : Adversary) : ProbComp Outcome := do
  let (z, adversaryCache) ← (simulateQ HashSpec.randomOracle A).run ∅
  let (verdict, cache) ←
    (simulateQ HashSpec.randomOracle (verifier queryH z.1.1 z.1.2 z.2)).run adversaryCache
  return ((z, verdict), cache, adversaryCache)

/-! ## Knowledge soundness -/

/-- An extractor: from the oracle's answers to the adversary's queries and the proof, an
execution of the program. -/
abbrev Extractor : Type :=
  (prog : Program) → PublicInput → HashSpec.QueryCache → Proof → Option (Trace prog)

/-- **The extractor** (`LeanVM.Extraction.extract`, `LeanVM/Spec/Extractor.lean`): from the
adversary's answers and the proof, the announced sizes and the word the stack's root commits to,
and a valid execution of the program on the public input that is the halting run of the memory
image of a stack in the word's Johnson list, if there is one. -/
noncomputable def extractor : Extractor := fun prog input answers proof ↦
  Extraction.extract prog input (bytecodeWords prog) (fun x ↦ answers x) proof

/-- **The adversary breaks soundness**: the verifier accepts its statement and proof, the
program's last instruction is not a `JUMP`, and the execution extracted from the adversary's
answers and the proof is not a valid execution of the program on the public input. -/
def Breaks (extract : Extractor) (z : Outcome) : Prop :=
  z.accepted ∧ SentinelSafe z.program ∧
    ¬ ∃ t, extract z.program z.input z.adversaryCache z.proof = some t ∧
      ValidExecution z.program z.input t

/-- **The soundness error** of an adversary of `Q` queries: one `2^-128` per query of the
adversary and the verifier (at most `13213`), plus collisions, plus one `2^-256` per query of the
verifier, for a fresh answer that is the stack's root the adversary announced without computing
it (the extractor, reading the adversary's answers only, would then miss the root's preimage). -/
noncomputable def soundnessError (Q : ℕ) : ℝ≥0∞ :=
  ((Q + 13213 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + ((5 * (Q + 13213) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    (13213 : ℝ≥0∞) / 2 ^ 256

/-- **Knowledge soundness in the random-oracle model**, for the extractor `extractor`. -/
def KnowledgeSoundness : Prop :=
  ∀ (A : Adversary) (Q : ℕ), A.IsTotalQueryBound Q →
    Pr{let z ← experiment A}[Breaks extractor z] ≤ soundnessError Q

/-! ## Completeness -/

/-- An honest prover: from a statement, an execution, the commitment's rate exponent `ρ` and a
fuel of nonces per proof of work, a proof, computed with oracle access to the hash function. -/
abbrev HonestProver : Type :=
  (prog : Program) → (input : PublicInput) → Trace prog → (ρ fuel : ℕ) → OracleComp HashSpec Proof

/-- **The completeness error** at a fuel of `fuel` nonces per proof of work: each of the
`Q` queries of the honest prover and the verifier may complete a proof of work whose nonces all
failed, or meet a digest the oracle already gave. -/
noncomputable def completenessError (fuel : ℕ) : ℝ≥0∞ :=
  let Q : ℕ := 13216 + 13210 * (2 ^ 27 + fuel + 1)
  Q * ((1 - (2 : ℝ≥0∞)⁻¹ ^ 17) ^ fuel + Q / 2 ^ 256)

/-- **The committed size of an execution**: the number of cells the honest prover commits to,
every committed column at its table's height, the least power of two holding the table's rows
(`1` for no row). The memory has four columns of `2^κ` rows, and the bytecode's counts (`BFCNT`)
one of `2^logSize` rows. Each opcode has a table of one row per instruction of that opcode the execution
executes (`Trace.count`), with `15, 15, 8, 15, 14, 19` committed columns for `XOR`, `MUL_NATIVE`,
`SET_CONSTANT`, `DEREF`, `JUMP`, `BLAKE2S`; and Flock's region has `2^8` rows per row of the
`BLAKE2S` table. -/
noncomputable def Semantics.Trace.committedSize {prog : Program} (t : Trace prog) : ℕ :=
  let height (op : Opcode) : ℕ := 2 ^ Nat.clog 2 (t.count op)
  4 * 2 ^ t.κ + 2 ^ prog.logSize +
    15 * height .xor + 15 * height .mulNative + 8 * height .setConstant + 15 * height .deref +
    14 * height .jump + 19 * height .blake2s + 2 ^ 8 * height .blake2s

/-- **Completeness in the random-oracle model.** -/
def Completeness : Prop :=
  ∃ prover : HonestProver, ∀ (prog : Program) (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ),
    ValidExecution prog input t →
    t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 → fuel ≤ 2 ^ 64 →
    Pr{let z ← experiment ((fun proof ↦ ((prog, input), proof)) <$> prover prog input t ρ fuel)}[
      z.rejected] ≤ completenessError fuel

end
end LeanVM
