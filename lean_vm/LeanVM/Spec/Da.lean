/-
  LeanVM.Spec.Da

  What an aggregate's DA claim on a root says, in terms of LeanDA as `lean_da` defines it, on
  Keccak-256 and Keccak-f[1600].
-/

module

public import LeanDa.Scheme
public import LeanVM.Spec.Keccak
public import LeanVM.Spec.Fast.Da
public import LeanVM.Spec.Fast.Keccak

/-!
# The DA claim

LeanDA, the commitment to a blob matrix and the Reed-Solomon membership vector its root
determines, is `lean_da`'s, imported from its `Scheme` module: the security of the scheme is
proved there, and its deployed algorithms (`LeanDa.commitCodewords`, `LeanDa.membershipVector`,
`LeanDa.vectorDigest`) are transcribed there, generic in the hash `H` and in the permutation `P`
of the challenges' duplex sponge. Here the hash is this project's Keccak-256 (`keccak`, from
`keccak256`), its digest read as LeanDA's 32 bytes (`toBytes`), and the permutation is this
project's Keccak-f[1600] on LeanDA's lanes (`keccakLanes`, from `keccakF`): the crate's, at leanVM
`94ee12ff6b2a3d42ba8328e22d09443692e4800b` (`crates/lean_da`, `crates/verifier/src/da.rs`).
`Fast.Da` compiles the membership vector with this project's field arithmetic, and `Fast.Keccak`
Keccak-f[1600] and Keccak-256 with their lanes written out.

An aggregate's DA claim is a pair of a root and a vector digest; it is held by a matrix committed
to the root whose rows are orthogonal to a vector of that digest (`Witness.Opens`: the guest's
`da_verify`, `crates/rec_aggregation/guests/lean_ethereum.py:3920-4060`). The guest takes the
vector digest from the statement; the outer verifier derives it from the root (`vectorDigestOf`;
`verifier::da::list_digest`, `crates/verifier/src/da.rs:99-104`, called by
`EthereumProof::verify`, `crates/rec_aggregation/src/aggregation.rs:697-719`). The vector digest
is two-level at this pin: the hash of the `128` column digests of `256` entries each
(`LeanDa.vectorDigest`; the guest's `da_vector_cell`, `lean_ethereum.py:4048-4060`).
Orthogonality to the one vector the root determines makes the rows codewords except with the
membership test's soundness error (`lean_da`'s `checker_sound`); that vector is the code's dual
codeword (`lean_da`'s `membershipVector_eq_dual`). The link from this check to `lean_da`'s code
binding is not proved. The prover's copy of the membership vector
(`crates/lean_da/src/membership.rs`) is not transcribed; that it agrees with
`crates/verifier/src/da.rs` is an implementation fact, which honest aggregates rely on.
-/

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- A digest as LeanDA's 32 bytes: its words, little-endian (`Digest.value`). -/
def toBytes (d : Digest) : LeanDa.Digest :=
  ⟨(digestBytes d).toArray, by
    obtain ⟨⟨l⟩, hl⟩ := d
    match l, hl with
    | [_, _, _, _], _ => rfl⟩

/-- Keccak-256 as LeanDA's hash. -/
def keccak (input : List UInt8) : LeanDa.Digest := toBytes (keccak256 input)

/-- LeanDA's sponge lanes as a Keccak state: each `K` word as its 64-bit lane. -/
def lanesState (l : LeanDa.Lanes) : KState := l.map K.lane

/-- A Keccak state as LeanDA's sponge lanes: each 64-bit lane as its `K` word. -/
def stateLanes (s : KState) : LeanDa.Lanes := s.map K.ofLane

/-- Keccak-f[1600] as LeanDA's sponge permutation. -/
def keccakLanes (l : LeanDa.Lanes) : LeanDa.Lanes := stateLanes (keccakF (lanesState l))

/-- **The vector digest of a root**, as the outer verifier derives it
(`vector_digest(membership_vector(root))`, `crates/verifier/src/da.rs:83-104`). -/
def vectorDigestOf (root : Digest) : LeanDa.Digest :=
  LeanDa.vectorDigest keccak (LeanDa.membershipVector keccak keccakLanes (toBytes root))

/-- What holds a DA claim: a matrix of codewords and the vector its rows are orthogonal to. -/
structure Witness where
  /-- The codewords. -/
  rows : List (List K)
  /-- The vector. -/
  vector : List E

/-- **The witness holds the DA claim `(root, vd)`** (`da_verify`): `1` to `1024` codewords of
`2^15` symbols commit to `root`, and every one is orthogonal to the vector, whose digest is
`vd`. -/
def Witness.Opens (root vd : Digest) (w : Witness) : Prop :=
  1 ≤ w.rows.length ∧ w.rows.length ≤ LeanDa.maxRows ∧
    (∀ row ∈ w.rows, row.length = 2 ^ LeanDa.logM) ∧
    LeanDa.commitCodewords keccak w.rows = toBytes root ∧ w.vector.length = 2 ^ LeanDa.logM ∧
    LeanDa.vectorDigest keccak w.vector = toBytes vd ∧
    ∀ row ∈ w.rows, LeanDa.dot (fun b ↦ w.vector.getD b 0) (fun b ↦ row.getD b 0) = 0

end
end LeanVM.Da
