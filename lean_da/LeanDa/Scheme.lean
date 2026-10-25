module

public import LeanDa.Field
public import Mathlib.LinearAlgebra.Lagrange
public import Statement.LeanDa

/-!
# LeanDA

The erasure code commitment of `crates/lean_da` at leanVM `main` `4af2cdddd`, specified in
`doc/leanvm/body/10-ethereum.tex` §sec:leanda, for a matrix of `r` rows.

* **The code** (`encode.rs:12-36`). A row's payload is `2^14` symbols of `K`, the evaluations on
  the domain points `0 … 2^14 - 1` of the polynomial of degree below `2^14` they determine. Its
  codeword is that polynomial's evaluations on all `2^15` points (`encodeRow`): the inverse
  additive NTT interpolates, the forward one evaluates, so the payload is the codeword's first
  half. Both transforms compute these maps (Annex D, Proposition prop:ntt); they are not
  transcribed here.
* **Cells** (`lib.rs:23-39`). A codeword is `128` cells of `256` symbols, cell `j` its symbols
  `256 j … 256 j + 255`. A matrix of `r` codewords has `128 r` cells, cell `j` of row `i` at
  position `128 i + j`: the positions of the erasure code commitment are the cells sampling
  opens.
* **The commitment** (`commit.rs:55-151`). The rows are padded to `2^⌈log₂ r⌉` with zero
  codewords. A cell's digest is the hash of its symbols' little-endian bytes (`hash_cells`). The
  row tree is the Merkle tree over each row's digest of its first `64` cell digests (the payload),
  the column tree the one over all cell digests in column-major order, and the root is
  `H(rowRoot ‖ colRoot)`. A tree hashes neighbours in pairs, level by level (`tree_from_leaves`).
  The padding digests of `padding_digests` are the digests of zero cells and rows, so the root is
  the commitment to the padded matrix.
* **Openings.** A cell is opened by its authentication path in the column tree and the row root.
  The crate keeps the column tree for this (`DaWitness::column_tree`, `commit.rs:23-45`), whose
  level `⌈log₂ r⌉` holds the column roots (`column_roots`), but verifies no sample:
  `verifyCell` is the check this path determines.
* **Membership** (`membership.rs:33-83`, `verifier/src/da.rs:15-85`). Challenges `z ∈ E^14` give
  the dual codeword `L`, the tensor `⊗_j (1, z_j)` read as novel-basis coefficients and encoded,
  that is `L(x) = ∏_j (1 + z_j Ŵ_j(x))` on the domain (Annex D, eq. dual-product), with
  `Ŵ_j` the normalized subspace polynomial of the span of `e_0 … e_(j-1)`. A matrix passes when
  every row is orthogonal to `L` (`check_membership`, `membership.rs:94-103`; the guest's
  `da_verify`). The challenges are drawn from the root by a duplex sponge over Keccak-f[1600]
  seeded with the label's hash (`membership_challenges`); the security game models them as one
  random oracle on the root.
* **The deployed algorithms** (`commit.rs:55-145`, `verifier/src/da.rs:15-96`,
  `verifier/src/transcript.rs:32-95`). The crate's computations, transcribed computably on lists,
  for `lean_vm` to state the aggregation node's DA claim with: `commitCodewords`, the commitment
  level by level, which is `commitCells` of the matrix (`commitCodewords_eq_commitCells`,
  `LeanDa.Commitment`); the challenges' sponge (`Sponge`, `membershipChallenges`); the dual
  codeword by the additive NTT (`membershipVector`), which computes `dual`
  (`membershipVector_eq_dual`, `LeanDa.Dual`); and the vector's digest, the hash of its `128`
  columns' hashes (`vectorDigest`).

The row count `r` is a parameter. The crate takes `1 ≤ r ≤ 1024` (`row_count`, `lib.rs:41-46`);
the statements hold for every `r ≥ 1`. So are the hash `H` and the sponge's permutation `P`: the
crate's are Keccak-256 (Ethereum's: rate `136` bytes, padding `0x01 ‖ 0^* ‖ 0x80`,
`verifier/src/hash.rs:79-97`) and the Keccak-f[1600] it is built on, which `lean_vm` supplies,
and the statements hold for every `H` and `P`.

Part of `lean_da`, which instantiates Benedikt Wagner's framework for erasure code commitments
(`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

open Polynomial

namespace LeanDa

@[expose] public section

/-! ## Shapes (`lib.rs:23-39`) -/

/-! ## The code (`encode.rs`) -/

/-! ## The commitment (`commit.rs`) -/

variable (H : List UInt8 → Digest)

/-! ## Openings -/

/-! ## Membership (`membership.rs`, `verifier/src/da.rs`) -/

/-- The tensor `⊗_j (1, z_j)`: coefficient `u` is the product of the `z_j` over the bits of `u`
(`dual_codeword`'s first loop). -/
def tensor (z : Fin 14 → E) (u : Fin (2 ^ 14)) : E :=
  ∏ j : Fin 14, if (u : ℕ).testBit j then z j else 1

/-! ## The deployed commitment (`commit.rs:55-145`)

The commitment as the crate computes it, on codewords given as lists of symbols: the leaves in
the crate's order, each tree built level by level. It is `commitCells` of the matrix the rows
form (`commitCodewords_eq_commitCells`, `LeanDa.Commitment`). -/

/-- The cells of the matrix whose rows are `rows`: cell `j` of row `i` at position `128 i + j`. -/
def cellsOfRows (rows : List (List K)) : Fin (rows.length * 128) → Cell :=
  fun p s ↦ (rows.getD (p / 128) []).getD (256 * (p % 128) + s) 0

/-! ## The deployed membership vector (`verifier/src/da.rs:15-96`)

The challenges, drawn from the root by the duplex sponge the security game models as a random
oracle, and the dual codeword as the crate computes it, by the additive NTT, which computes `dual`
(`membershipVector_eq_dual`, `LeanDa.Dual`). -/

/-! ### The sponge (`verifier/src/transcript.rs:32-95`)

A duplex sponge in overwrite mode over a permutation `P` of `25` lanes. The crate's is
Keccak-f[1600] (`keccak_f`, `verifier/src/hash.rs:50-69`), which `lean_vm` supplies; the
definitions hold for every `P`. A lane is a `u64`, read as the element of `K` with its bits, so
a scalar's limbs are lanes as they are. The rate is lanes `0 … 15`, the capacity lanes
`16 … 24`. -/

variable (P : Lanes → Lanes)

/-! ### The challenges and the vector -/

end

end LeanDa
