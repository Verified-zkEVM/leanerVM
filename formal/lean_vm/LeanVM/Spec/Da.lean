/-
  LeanVM.Spec.Da

  LeanDA: the commitment to a blob matrix, the Reed-Solomon membership vector its root
  determines, and what an aggregate's DA claim on a root says.
-/

module

public import LeanVM.Spec.Verifier

/-!
# LeanDA

Transcribed from leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`,
`crates/lean_da/src/lib.rs:23-46` and `commit.rs:55-145` (the commitment), and
`crates/verifier/src/da.rs:15-96` (the membership vector, as the outer verifier derives it). The
prover's copy of the membership vector (`lean_da/src/{encode,membership}.rs`) is not transcribed;
that it agrees with `da.rs` is an implementation fact, which honest aggregates rely on.

A blob is `2^14` symbols of `K`, systematically encoded into a codeword of `2^15` symbols, cut
into `128` cells of `256` symbols. A matrix of `1` to `1024` codewords is committed by two Merkle
trees over the cells' digests, its row count padded to a power of two with zero codewords: the
row tree over each row's digest of its first `64` cells (the payload), and the column tree over
all the cells, column by column. The root is the hash of the two roots (`commitCodewords`).

A row is a codeword when it is orthogonal to the dual codeword `L` of challenges drawn from the
root (`membershipVector`), with high probability over the challenges. An aggregate's DA claim is
a pair of a root and a vector digest; it is held by a matrix committed to the root whose rows are
orthogonal to a vector of that digest (`Witness.Opens`, `lean_ethereum.py:3159-3353` at `a0ca7858`). The guest
takes the vector digest from the statement; the outer verifier derives it from the root
(`vectorDigest (membershipVector root)`), so that the rows are codewords given that BLAKE2s, here
and in the statement's digests, has no collision.
-/

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile

@[expose] public section

/-! ## Shapes (`lean_da/src/lib.rs:23-41`) -/

/-- Payload symbols per blob, as a logarithm (`DA_LOG_K`). -/
def logK : ℕ := 14

/-- Codeword symbols per blob, as a logarithm: rate one half (`LOG_M`). -/
def logM : ℕ := logK + 1

/-- Symbols per cell (`CELL_SYMBOLS`). -/
def cellSymbols : ℕ := 2 ^ 8

/-- Cells per codeword (`CELLS_PER_ROW`). -/
def cellsPerRow : ℕ := 2 ^ logM / cellSymbols

/-- Cells per payload (`PAYLOAD_CELLS`). -/
def payloadCells : ℕ := 2 ^ logK / cellSymbols

/-- The most codewords in one commitment (`DA_MAX_ROWS`). -/
def maxRows : ℕ := 1024

/-! ## The commitment (`lean_da/src/commit.rs`) -/

/-- The root of a Merkle tree over a power-of-two number of digests, each level hashing
neighbours in pairs (`tree_from_leaves`; on other lengths, which `commitCodewords` never passes,
the Rust panics). -/
def merkleRoot (leaves : List Digest) : Digest :=
  if h : leaves.length ≤ 1 then leaves.headD default
  else merkleRoot ((List.range (leaves.length / 2)).map fun i ↦
    hashPair (leaves.getD (2 * i) default) (leaves.getD (2 * i + 1) default))
termination_by leaves.length
decreasing_by simp only [List.length_map, List.length_range]; omega

/-- Cell `j` of a codeword. -/
def cell (row : List K) (j : ℕ) : List K := (row.drop (j * cellSymbols)).take cellSymbols

/-- A cell's digest, BLAKE2s of its symbols' bytes (`hash_cells`). -/
def cellDigest (row : List K) (j : ℕ) : Digest := hashWords (cell row j)

/-- A row's digest, BLAKE2s of its payload cells' digests. -/
def rowDigest (row : List K) : Digest :=
  blake2sBytes ((List.range payloadCells).flatMap fun j ↦ digestBytes (cellDigest row j))

/-- The digest of the zero cell, which pads the columns (`padding_digests`). -/
def paddingCell : Digest := hashWords (List.replicate cellSymbols 0)

/-- The digest of the zero row, which pads the row tree (`padding_digests`). -/
def paddingRow : Digest :=
  blake2sBytes ((List.replicate payloadCells paddingCell).flatMap digestBytes)

/-- **The root of a matrix of codewords** (`commit_codewords`): the rows padded to a power of
two, the hash of the row tree's root and the column tree's. -/
def commitCodewords (rows : List (List K)) : Digest :=
  let nPad := rows.length.nextPowerOfTwo
  let rowRoot := merkleRoot (rows.map rowDigest ++ List.replicate (nPad - rows.length) paddingRow)
  let columnRoot := merkleRoot ((List.range cellsPerRow).flatMap fun j ↦
    (List.range nPad).map fun i ↦ if h : i < rows.length then cellDigest rows[i] j else paddingCell)
  hashPair rowRoot columnRoot

/-! ## The membership vector (`verifier/src/da.rs`) -/

/-- `leanDA/rs-membership/v1`, the label of the challenges' transcript (`LABEL`). -/
def label : List UInt8 := "leanDA/rs-membership/v1".toUTF8.toList

/-- `n` challenges squeezed out of the chain from `cv` (`sample`). -/
def squeezes : ℕ → Digest → List E
  | 0, _ => []
  | n + 1, cv =>
    let cv := blake2sBytes (digestBytes cv ++ blockOf 0 2)
    challengeOf cv :: squeezes n cv

/-- The challenges `z_0 … z_13` of a root: a chain from the label's hash absorbs the root's two
halves, then squeezes (`membership_challenges`). -/
def membershipChallenges (root : Digest) : List E :=
  let cv := blake2sBytes label
  let cv := blake2sBytes (digestBytes cv ++ blockOf (digestScalars root).1 1)
  let cv := blake2sBytes (digestBytes cv ++ blockOf (digestScalars root).2 1)
  squeezes logK cv

/-- Row `i` of the subspace evaluations before scaling: `s_i` at the basis elements `x^j`,
`j ≥ i`. -/
def subspaceRow : ℕ → List K
  | 0 => (List.range logM).map fun j ↦ K.ofBits (2 ^ j)
  | i + 1 =>
    let previous := subspaceRow i
    (previous.drop 1).map fun value ↦ value * (value + previous.headD 0)

/-- Row `i` of the subspace evaluations, scaled so that its first entry is one
(`subspace_evaluations`). -/
def subspaceEvaluations (i : ℕ) : List K :=
  (subspaceRow i).map (· * ((subspaceRow i).headD 0)⁻¹)

/-- One butterfly block: `u += v·t`, then `v += u`. -/
def butterfly (twiddle : K) (block : List E) : List E :=
  let top := block.take (block.length / 2)
  let bottom := block.drop (block.length / 2)
  let top := List.zipWith (fun u v ↦ u + v * ofK twiddle) top bottom
  top ++ List.zipWith (· + ·) bottom top

/-- Layer `layer` of the additive NTT: blocks of `2^(logM - layer)` points, block `b`'s twiddle
the subset sum of the row's entries that `b`'s bits pick. -/
def encodeLayer (layer : ℕ) (codeword : List E) : List E :=
  let row := (subspaceEvaluations (logM - layer - 1)).drop 1
  let size := 2 ^ (logM - layer)
  (List.range (codeword.length / size)).flatMap fun b ↦
    let twiddle := ((List.range layer).filter b.testBit).foldl (fun t bit ↦ t + row.getD bit 0) 0
    butterfly twiddle ((codeword.drop (b * size)).take size)

/-- The codeword of the `2^14` novel-basis coefficients `message`: the message twice, then the
layers `1 … 14` (`encode`). -/
def encode (message : List E) : List E :=
  (List.range' 1 (logM - 1)).foldl (fun codeword layer ↦ encodeLayer layer codeword)
    (message ++ message)

/-- The dual codeword: the tensor of the `(1, z_j)`, encoded (`dual_codeword`). -/
def dualCodeword (z : List E) : List E :=
  encode (z.foldl (fun t challenge ↦ t ++ t.map (· * challenge)) [1])

/-- **The membership vector of a root** (`membership_vector`). -/
def membershipVector (root : Digest) : List E := dualCodeword (membershipChallenges root)

/-- BLAKE2s of a vector's limbs, three little-endian `K` words an entry (`vector_digest`). -/
def vectorDigest (vector : List E) : Digest :=
  hashWords (vector.flatMap fun e ↦ [e.limb 0, e.limb 1, e.limb 2])

/-! ## The claim -/

/-- The inner product of a row with a vector. -/
def dot (row : List K) (vector : List E) : E :=
  (List.zipWith (fun a b ↦ ofK a * b) row vector).foldl (· + ·) 0

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
  1 ≤ w.rows.length ∧ w.rows.length ≤ maxRows ∧ (∀ row ∈ w.rows, row.length = 2 ^ logM) ∧
    commitCodewords w.rows = root ∧ w.vector.length = 2 ^ logM ∧ vectorDigest w.vector = vd ∧
    ∀ row ∈ w.rows, dot row w.vector = 0

end
end LeanVM.Da
