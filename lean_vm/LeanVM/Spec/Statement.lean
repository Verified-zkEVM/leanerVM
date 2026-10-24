/-
  LeanVM.Spec.Statement

  The statement the leanVM verifier reads (a program and a public input), the verifier on it, its
  calls to Keccak-256 and Keccak-f[1600] as oracle queries, and the errors and the committed size
  that the statements of `LeanVM/Spec/Rpm.lean` are stated with.
-/

module

public import LeanVM.Spec.Isa
public import LeanVM.Spec.Verifier
public import LeanVM.Spec.Extractor
public import VCVio.OracleComp.OracleComp
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.ProbabilityNotation

/-!
# The verifier on a statement

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

/-! ## The verifier on a statement -/

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

/-! ## The oracle calls -/

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

/-! ## The soundness error -/

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
verifier (at most `verifierQueries = V`): one `2^-128` per call, plus, per call,
`7 · (Q + V) / 2^256` for a fresh answer that collides with or predicts a value the answers
already refer to (a digest, or a state's capacity), plus one `2^-256` per call of the verifier, for
a fresh hash answer that is the stack's root the adversary announced without computing it (the
extractor, reading the adversary's evaluations only, would then miss the root's preimage). -/
noncomputable def soundnessError (Q : ℕ) : ℝ≥0∞ :=
  ((Q + verifierQueries : ℕ) : ℝ≥0∞) *
      ((2 : ℝ≥0∞)⁻¹ ^ 128 + ((7 * (Q + verifierQueries) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    (verifierQueries : ℝ≥0∞) / 2 ^ 256

/-! ## The honest prover, the completeness error and the committed size -/

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
