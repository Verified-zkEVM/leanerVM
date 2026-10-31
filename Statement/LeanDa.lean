module

public import Statement.Field
public import CompPoly.Fields.Binary.BF64
public import CompPoly.Fields.Binary.AdditiveNTT.NovelPolynomialBasis
public import VCVio.OracleComp.Constructions.SampleableType
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Lagrange
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.Coercions.Add.Basic
public import VCVio.OracleComp.EvalDist.Sum
public import Statement.Fast.FieldWords
public import Statement.Fast.CubicExt
public import Statement.Fast.Keccak

/-!
# LeanDA

LeanDA as `crates/lean_da` computes it, and its security in Benedikt Wagner's framework for erasure
code commitments, moved to the random-permutation model.

**Credit.** The framework (erasure codes and their consistency, arguments of knowledge and their
knowledge-soundness game, the code-binding game) is Benedikt Wagner's formalization,
https://github.com/b-wagn/fv-pq-da at `4475179c19296acf3469d7d552a3186ad1feda74` (his post:
https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746), ported and modified
to build on VCVio `afa6593f` and Lean v4.34.1, under the Apache License 2.0 (`lean_da/LICENSE`,
`lean_da/NOTICE`); the definitions the end statements need are here, the rest of his framework
(vector commitments, code checkers, his oracle-free arguments, the scheme in the random-oracle
model and its games, his reductions) and his proofs in `lean_da/PqDas/`. The instantiation with
LeanDA (`LeanDa`) follows his framework, and the end statements are his completeness and binding
notions moved to the random-permutation model, where the argument's prover and verifier query
the model's oracles (`OracleArgument`) and its extractor reads the adversary's transcript.

The file: Wagner's framework (`PqDas`: erasure codes and the consistency of opened cells),
LeanDA (`LeanDa`: the code, the commitment, the membership test, the deployed algorithms), the
relation of LeanDA's argument (the root's challenges drawn by the deployed duplex), arguments in
the random-permutation model, the games there (the hash Keccak-256 over `π`, the membership
challenges the deployed duplex over `π`; no random oracle), and the end statements (last
section).
-/

@[expose] public section

open Polynomial OracleComp OracleSpec ENNReal Common MeasureTheory

set_option linter.unusedSectionVars false

/-! ## Wagner's framework: erasure codes -/

namespace PqDas

/-- An erasure code with message alphabet `Γ`, code alphabet `Λ`, message
length `k`, and code length `n`, given by its encoding function. -/
structure ErasureCode (Γ Λ : Type) (k n : ℕ) where
  /-- The encoding function of the code. -/
  encode : (Fin k → Γ) → (Fin n → Λ)

namespace ErasureCode

variable {Γ Λ : Type} {k n : ℕ}

/-- A list of position/symbol pairs is *consistent* with the code if some
codeword agrees with all of them. The winning condition of the code-binding
game is the negation of this, for the pairs the adversary opened. -/
def Consistent (C : ErasureCode Γ Λ k n) (openings : List (Fin n × Λ)) : Prop :=
  ∃ m : Fin k → Γ, ∀ p ∈ openings, C.encode m p.1 = p.2

/-- Consistency is decidable for finite alphabets. -/
instance decidableConsistent (C : ErasureCode Γ Λ k n) [Fintype Γ] [DecidableEq Λ]
    (openings : List (Fin n × Λ)) : Decidable (C.Consistent openings) :=
  decidable_of_iff (∃ m : Fin k → Γ, ∀ p ∈ openings, C.encode m p.1 = p.2) Iff.rfl

end ErasureCode

end PqDas

/-! ## LeanDA's fields -/

namespace LeanDa

open PqDas

export LeanVM.Parameters (K E K.ofBits K.ofLane K.lane)
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (keccak256With)

/-- An enumeration of `K` through its bits, for proofs only: compiled, it would list `2^64`
elements when a program starts. -/
noncomputable instance : Fintype K := Fintype.ofEquiv (Fin (2 ^ 64)) BF64.equivFin.symm

/-- `K` is a `GF(2)`-algebra, being of characteristic two. -/
instance : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The embedding `K ↪ E` as the `y^0` limb. -/
abbrev ι : K →+* E := algebraMap K E

/-- The point of index `b` of an additive domain: `Σ_c b_c e_c` with `e_c = x^c`. -/
def point (b : ℕ) : K := K.ofBits b

/-- `e_c = x^c` for `c < 16`, the start of the basis of Annex D. -/
def basis (c : Fin 16) : K := K.ofBits (2 ^ (c : ℕ))

/-!
## LeanDA

The erasure code commitment of `crates/lean_da` at leanVM
`c445e3d51a5a85031df47240595698f3b24897bf`, specified in `doc/leanvm/body/10-ethereum.tex`
§sec:leanda, for a matrix of `r` rows.

* **The code** (`encode.rs:12-36`). A row's payload is `2^14` symbols of `K`, the evaluations on
  the domain points `0 … 2^14 - 1` of the polynomial of degree below `2^14` they determine. Its
  codeword is that polynomial's evaluations on all `2^15` points (`encodeRow`): the inverse
  additive NTT interpolates, the forward one evaluates, so the payload is the codeword's first
  half. Both transforms compute these maps (Annex D, Proposition prop:ntt); they are not
  transcribed here.
* **Cells** (`lib.rs:23-39`). A codeword is `128` cells of `256` symbols; cell `j` of row `i` is
  at position `128 i + j`, the positions of the erasure code commitment.
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
  `verifyCellM` is the check this path determines.
* **Membership** (`membership.rs:33-83`, `verifier/src/da.rs:15-85`). Challenges `z ∈ E^14` give
  the dual codeword `L`, the tensor `⊗_j (1, z_j)` read as novel-basis coefficients and encoded,
  that is `L(x) = ∏_j (1 + z_j Ŵ_j(x))` on the domain (Annex D, eq. dual-product), with
  `Ŵ_j` the normalized subspace polynomial of the span of `e_0 … e_(j-1)`. A matrix passes when
  every row is orthogonal to `L` (`check_membership`, `membership.rs:94-103`; the guest program's
  `da_verify`). The challenges are drawn from the root by a duplex sponge over Keccak-f[1600]
  seeded with the label's hash (`membership_challenges`); the end statements draw them by this
  duplex over the permutation (`membershipChallengesM`).

The row count `r` is a parameter: the crate takes `1 ≤ r ≤ 1024` (`row_count`, `lib.rs:41-46`);
completeness and position binding hold for every `r`, code binding for `1 ≤ r ≤ 1024`
(`maxRows`). The algorithms take a permutation `π` of the Keccak state as a parameter and hash with
Keccak-256 over it (`keccakDigestBytes`, the hash `H` below): the crate's is Keccak-f[1600], the
hash Keccak-256 (`verifier/src/hash.rs:79-97`); in the end statements `π` is the random
permutation. A digest is 32 bytes, `DigestBytes` (`fiat_shamir::merkle::Hash`).
-/

/-! ### Shapes (`lib.rs:23-39`) -/

/-- Payload symbols per row, as a logarithm (`DA_LOG_K`). -/
def logK : ℕ := 14

/-- Codeword symbols per row, as a logarithm: rate one half (`LOG_M`). -/
def logM : ℕ := 15

/-- Symbols per cell (`CELL_SYMBOLS`). -/
def cellSymbols : ℕ := 256

/-- Cells per codeword (`CELLS_PER_ROW`). -/
def cellsPerRow : ℕ := 128

/-- Cells per payload (`PAYLOAD_CELLS`). -/
def payloadCells : ℕ := 64

/-- The most rows the crate commits to (`DA_MAX_ROWS`). -/
def maxRows : ℕ := 1024

/-- A row's payload. -/
abbrev Payload := Fin (2 ^ 14) → K

/-- A codeword, in domain order. -/
abbrev Row := Fin (2 ^ 15) → K

/-- A sampling cell. -/
abbrev Cell := Fin 256 → K

/-! ### The code (`encode.rs`) -/

/-- The polynomial of degree below `2^14` taking the payload's values on the points
`0 … 2^14 - 1` (`inverse_transform`). -/
noncomputable def interpolate (p : Payload) : K[X] :=
  Lagrange.interpolate Finset.univ (fun a : Fin (2 ^ 14) ↦ point a) p

/-- **The systematic encoding of a payload** (`encode_rows`): its polynomial's values on all
`2^15` points (`encode_interleaved_in_place`). -/
noncomputable def encodeRow (p : Payload) : Row := fun b ↦ (interpolate p).eval (point b)

/-- Cell `j` of a codeword: its symbols `256 j … 256 j + 255`. -/
def rowCell (w : Row) (j : Fin 128) : Cell := fun s ↦ w ⟨256 * j + s, by omega⟩

/-- The position of cell `j` of row `i`. -/
def pos {r : ℕ} (i : Fin r) (j : Fin 128) : Fin (r * 128) := ⟨128 * i + j, by omega⟩

/-- The row of a position. -/
def posRow {r : ℕ} (p : Fin (r * 128)) : Fin r := ⟨p / 128, by omega⟩

/-- The cell of a position within its row. -/
def posCell {r : ℕ} (p : Fin (r * 128)) : Fin 128 := ⟨p % 128, by omega⟩

/-- The cells of a matrix of encoded payloads. -/
noncomputable def encodeMatrix {r : ℕ} (msg : Fin r → Payload) : Fin (r * 128) → Cell :=
  fun p ↦ rowCell (encodeRow (msg (posRow p))) (posCell p)

/-- Row `i` of a matrix given by its cells. -/
def rowOf {r : ℕ} (c : Fin (r * 128) → Cell) (i : Fin r) : Row :=
  fun b ↦ c (pos i ⟨b / 256, by omega⟩) ⟨b % 256, by omega⟩

/-- **LeanDA's hash** over a permutation `π` of the Keccak state in any monad: Keccak-256 over `π`
(`keccak256With`), its digest's 32 bytes (`Digest.toBytes`). The crate's is Keccak-256 over
Keccak-f[1600] (`verifier/src/hash.rs`); the end statements' is over the random permutation. -/
def keccakDigestBytes {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (bytes : List UInt8) : m DigestBytes :=
  LeanVM.Protocol.Digest.toBytes <$> keccak256With π bytes

/-! ### The commitment (`commit.rs`) -/

section Pure

variable (π : KeccakState → KeccakState)

/-- The eight little-endian bytes of a symbol (`as_bytes`). -/
def kBytes (a : K) : List UInt8 := (List.range 8).map fun t ↦ (a.toBitVec.toNat >>> (8 * t)).toUInt8

/-- A cell's bytes: its symbols' bytes in order. -/
def cellBytes (x : Cell) : List UInt8 := (List.ofFn x).flatMap kBytes

/-- The 64 bytes of a pair of digests (`hash_pair`, `tree_from_leaves`). -/
def pairBytes (a b : DigestBytes) : List UInt8 := a.toList ++ b.toList

/-- The digest of a cell (`hash_cells`). -/
def cellDigest (x : Cell) : DigestBytes := Id.run (keccakDigestBytes π (cellBytes x))

/-- `⌈log₂ r⌉`: the padded row count `2^⌈log₂ r⌉` is `r.next_power_of_two()`. -/
def logPad (r : ℕ) : ℕ := Nat.clog 2 r

/-- The padded row count. -/
def nPad (r : ℕ) : ℕ := 2 ^ logPad r

/-- Cell `j` of row `i` of the padded matrix: zero below the `r` rows. -/
def paddedCell {r : ℕ} (c : Fin (r * 128) → Cell) (i j : ℕ) : Cell :=
  if h : i < r ∧ j < 128 then c (pos ⟨i, h.1⟩ ⟨j, h.2⟩) else 0

/-- One level up a Merkle tree: node `i` hashes nodes `2i` and `2i + 1`. -/
def up (f : ℕ → DigestBytes) (i : ℕ) : DigestBytes :=
  Id.run (keccakDigestBytes π (pairBytes (f (2 * i)) (f (2 * i + 1))))

/-- The root of the Merkle tree over the leaves `f 0 … f (2^d - 1)` (`tree_from_leaves`). -/
def merkleRoot : ℕ → (ℕ → DigestBytes) → DigestBytes
  | 0, f => f 0
  | d + 1, f => merkleRoot d (up π f)

/-- The other node of the pair of node `idx`. -/
def sibling (idx : ℕ) : ℕ := if idx % 2 = 0 then idx + 1 else idx - 1

/-- The authentication path of leaf `idx`, siblings from the bottom. -/
def merklePath : ℕ → (ℕ → DigestBytes) → ℕ → List DigestBytes
  | 0, _, _ => []
  | d + 1, f, idx => f (sibling idx) :: merklePath d (up π f) (idx / 2)

/-- The row tree's leaves: each padded row's digest of its first `64` cell digests. -/
def rowLeaves {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) : DigestBytes :=
  Id.run (keccakDigestBytes π
    ((List.ofFn fun j : Fin 64 ↦ cellDigest π (paddedCell c i j)).flatMap Vector.toList))

/-- The column tree's leaves: leaf `j · 2^⌈log₂ r⌉ + i` is cell `j` of padded row `i`. -/
def colLeaves {r : ℕ} (c : Fin (r * 128) → Cell) (l : ℕ) : DigestBytes :=
  cellDigest π (paddedCell c (l % nPad r) (l / nPad r))

/-- The row root (`root_row`). -/
def rowRoot {r : ℕ} (c : Fin (r * 128) → Cell) : DigestBytes :=
  merkleRoot π (logPad r) (rowLeaves π c)

/-- The column root (`root_col`). -/
def colRoot {r : ℕ} (c : Fin (r * 128) → Cell) : DigestBytes :=
  merkleRoot π (7 + logPad r) (colLeaves π c)

/-- **The root of a matrix** (`commit_codewords`): `H(rowRoot ‖ colRoot)`. -/
def commitCells {r : ℕ} (c : Fin (r * 128) → Cell) : DigestBytes :=
  Id.run (keccakDigestBytes π (pairBytes (rowRoot π c) (colRoot π c)))

/-! ### Openings -/

/-- The opening of a cell: the row root and the cell's path in the column tree. -/
structure Opening where
  /-- The row root. -/
  rowRoot : DigestBytes
  /-- The siblings from the cell's leaf up to the column root. -/
  path : List DigestBytes
deriving Inhabited

/-- The column tree index of a position: cell `j` of row `i` is leaf `j · 2^⌈log₂ r⌉ + i`. -/
def colIndex {r : ℕ} (p : Fin (r * 128)) : ℕ := (posCell p : ℕ) * nPad r + posRow p

/-- The honest opening of a position. -/
def openCell {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) : Opening :=
  ⟨rowRoot π c, merklePath π (7 + logPad r) (colLeaves π c) (colIndex p)⟩

/-! ### Membership (`membership.rs`, `verifier/src/da.rs`) -/

/-- The normalized subspace polynomial `Ŵ_j`, vanishing on the span of `e_0 … e_(j-1)` and one
at `e_j` (CompPoly's `normalizedW`; `subspace_evaluations` tabulates it on the basis). -/
noncomputable def normW (j : Fin 14) : K[X] :=
  AdditiveNTT.normalizedW (ZMod 2) basis (Fin.castLE (by omega) j)

/-- **The dual codeword of challenges `z`** (`dual_codeword`): `L(x) = ∏_j (1 + z_j Ŵ_j(x))` on
the domain, the encoding of `tensor z` (`lean_da`'s `dual_eq_sum`). -/
noncomputable def dual (z : Fin 14 → E) (b : Fin (2 ^ 15)) : E :=
  ∏ j : Fin 14, (1 + z j * ι ((normW j).eval (point b)))

/-- The inner product of the dual codeword with a row: `Σ_x L(x) w(x)` (`check_membership`). -/
noncomputable def dot (L : Fin (2 ^ 15) → E) (w : Row) : E := ∑ b, L b * ι (w b)

/-- **The membership check**: every row is orthogonal to the dual codeword. -/
noncomputable def membershipCheck {r : ℕ} (z : Fin 14 → E) (c : Fin (r * 128) → Cell) : Bool :=
  decide (∀ i : Fin r, dot (dual z) (rowOf c i) = 0)

/-! ### The deployed commitment (`commit.rs:55-145`)

The commitment as the crate computes it, on codewords given as lists of symbols: the leaves in
the crate's order, each tree built level by level. It is `commitCells` of the matrix the rows
form (`commitCodewords_eq_commitCells`, `LeanDa.Commitment`). -/

/-- One level of a Merkle tree: the digests of neighbouring pairs (`tree_from_leaves`). -/
def treeLevel (nodes : List DigestBytes) : List DigestBytes :=
  (List.range (nodes.length / 2)).map (up π fun i ↦ nodes.getD i default)

/-- The root of the Merkle tree over a power-of-two number of digests (`tree_from_leaves`; on
other lengths, which `commitCodewords` never passes, the crate panics). -/
def treeRoot (nodes : List DigestBytes) : DigestBytes :=
  if nodes.length ≤ 1 then nodes.headD default else treeRoot (treeLevel π nodes)
termination_by nodes.length
decreasing_by simp only [treeLevel, List.length_map, List.length_range]; omega

/-- Cell `j` of a codeword. -/
def listCell (row : List K) (j : ℕ) : List K := (row.drop (j * cellSymbols)).take cellSymbols

/-- The digest of cell `j` of a codeword (`hash_cells`). -/
def listCellDigest (row : List K) (j : ℕ) : DigestBytes :=
  Id.run (keccakDigestBytes π ((listCell row j).flatMap kBytes))

/-- A row's digest: the hash of its payload cells' digests. -/
def rowDigest (row : List K) : DigestBytes :=
  Id.run (keccakDigestBytes π
    ((List.range payloadCells).flatMap fun j ↦ (listCellDigest π row j).toList))

/-- The digest of the zero cell, which pads the columns (`padding_digests`). -/
def paddingCell : DigestBytes :=
  Id.run (keccakDigestBytes π ((List.replicate cellSymbols 0).flatMap kBytes))

/-- The digest of the zero row, which pads the row tree (`padding_digests`). -/
def paddingRow : DigestBytes :=
  Id.run (keccakDigestBytes π ((List.replicate payloadCells (paddingCell π)).flatMap Vector.toList))

/-- **The root of a matrix of codewords, as the crate computes it** (`commit_codewords`): the
rows padded to a power of two, the hash of the row tree's root and the column tree's. -/
def commitCodewords (rows : List (List K)) : DigestBytes :=
  let n := nPad rows.length
  let rowTree := treeRoot π
    (rows.map (rowDigest π) ++ List.replicate (n - rows.length) (paddingRow π))
  let columnTree := treeRoot π ((List.range cellsPerRow).flatMap fun j ↦ (List.range n).map fun i ↦
    if h : i < rows.length then listCellDigest π rows[i] j else paddingCell π)
  Id.run (keccakDigestBytes π (pairBytes rowTree columnTree))

/-! ### The membership challenges (`verifier/src/da.rs:15-22`)

The challenges, drawn from the root by the duplex sponge (over the permutation `π` in the end
statements). The crate's membership vector, their dual codeword by the additive NTT, is `lean_da`'s
(`membershipVector`, which computes `dual`: `membershipVector_eq_dual`). -/

/-- `leanDA/rs-membership/v1`, the label of the challenges' transcript (`LABEL`). -/
def label : List UInt8 := "leanDA/rs-membership/v1".toUTF8.toList

/-- The symbol of eight little-endian bytes (`u64::from_le_bytes`). -/
def ofBytes (bytes : List UInt8) : K := K.ofBits (bytes.foldr (fun b acc ↦ b.toNat + 256 * acc) 0)

/-- Word `i` of a digest, its bytes `8 i … 8 i + 7` (`Digest::words`). -/
def word (d : DigestBytes) (i : ℕ) : K := ofBytes ((d.toList.drop (8 * i)).take 8)

/-- The element `c0 + c1·y + c2·y²` (`E::new`). -/
def ofLimbs (c0 c1 c2 : K) : E := CompPoly.Extension.Ext.ofVector #v[c0, c1, c2]

/-- Limb `i` of an element, the coefficient of `y^i`. -/
def limb (x : E) (i : Fin 3) : K := CompPoly.Extension.Ext.coeff x i

end Pure

/-! #### The sponge (`verifier/src/transcript.rs:32-95`)

A duplex sponge in overwrite mode over a permutation `P` of the Keccak state (`KeccakState`, `25`
lanes, `[u64; STATE_LANES]`). The crate's is Keccak-f[1600] (`keccak_f`,
`verifier/src/hash.rs:50-69`), which `lean_vm` supplies; the definitions hold for every `P`. A
lane is a `u64`, read as the element of `K` with its bits (`K.ofLane`, `K.lane`), so a scalar's
limbs are lanes as they are. The rate is lanes `0 … 15`, the capacity lanes `16 … 24`. -/

/-- Lanes of the rate. -/
def rateLanes : ℕ := 16

/-- Scalars that wait to be absorbed, four rate lanes each (`RATE_SCALARS`). -/
def rateScalars : ℕ := 4

/-- The tag of an observed scalar (`DS_OBSERVE = 1`). -/
def dsObserve : K := K.ofBits 1

/-- **The sponge** (`Sponge`): the lanes the last permutation left, and the scalars absorbed
since with their tags, at most `rateScalars` (`pending[..n_pending]`). -/
structure Sponge where
  /-- The lanes the last permutation left (`state`). -/
  state : KeccakState
  /-- The waiting scalars and their tags, in order. -/
  pending : List (E × K)

/-- The rate lanes the waiting scalars fill: scalar `i`'s three limbs and tag in lanes
`4 i … 4 i + 3`. -/
def rateWords (pending : List (E × K)) : List K :=
  pending.flatMap fun x ↦ [limb x.1 0, limb x.1 1, limb x.1 2, x.2]

/-! The sponge, the challenges and the openings' check over a permutation `P` in any monad, the hash
Keccak-256 over `P`: the games' oracles, or pure functions over `Id`. -/

section Monadic

variable {m : Type → Type} [Monad m] (P : KeccakState → m KeccakState)

/-- The lanes a duplexing permutes: the waiting scalars over the rate, the rest of the rate zero,
the capacity kept. -/
def duplexInput (s : Sponge) : KeccakState :=
  Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < rateLanes then ((rateWords s.pending).getD i 0).lane else s.state[i]

/-- The lanes of a fresh sponge: the IV's words in lanes `0 … 3`, the public input's in `4 … 7`. -/
def newInput (iv publicInput : DigestBytes) : KeccakState :=
  Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < 4 then (word iv i).lane else if (i : ℕ) < 8 then (word publicInput (i - 4)).lane
    else 0

/-- A sponge seeded with one permutation of `newInput` (`Sponge::new`). -/
def Sponge.newM (iv publicInput : DigestBytes) : m Sponge := do
  let state ← P (newInput iv publicInput)
  pure ⟨state, []⟩

/-- A sponge with no public input of its own, seeded from the hash of `label`
(`Sponge::from_label`). -/
def Sponge.fromLabelM (label : List UInt8) : m Sponge := do
  let iv ← keccakDigestBytes P label
  Sponge.newM P iv (Vector.replicate 32 0)

/-- Permute `duplexInput` (`duplex`). -/
def Sponge.duplexM (s : Sponge) : m Sponge := do
  let state ← P (duplexInput s)
  pure ⟨state, []⟩

/-- Absorb a scalar with a tag, permuting first when `rateScalars` wait (`absorb`). -/
def Sponge.absorbM (s : Sponge) (x : E) (tag : K) : m Sponge :=
  (if s.pending.length = rateScalars then Sponge.duplexM P s else pure s) >>= fun s ↦
    pure ⟨s.state, s.pending ++ [(x, tag)]⟩

/-- Observe a scalar (`observe`). -/
def Sponge.observeM (s : Sponge) (x : E) : m Sponge := Sponge.absorbM P s x dsObserve

/-- Draw a challenge: a permutation of its own, whose lanes `0 … 2` are its limbs (`sample`). -/
def Sponge.sampleM (s : Sponge) : m (E × Sponge) := do
  let s ← Sponge.duplexM P s
  pure (ofLimbs (K.ofLane s.state[0]) (K.ofLane s.state[1]) (K.ofLane s.state[2]), s)

/-- `n` challenges, in order. -/
def Sponge.samplesM : ℕ → Sponge → m (List E)
  | 0, _ => pure []
  | n + 1, s => do
    let (z, s) ← Sponge.sampleM P s
    let zs ← Sponge.samplesM n s
    pure (z :: zs)

/-- **The challenges `z_0 … z_13` of a root** (`membership_challenges`, `verifier/src/da.rs:15-22`):
a sponge from the label, the root's words observed as two scalars `(w_0, w_1, 0)` and
`(w_2, w_3, 0)`, then `14` samples. -/
def membershipChallengesM (root : DigestBytes) : m (List E) := do
  let s ← Sponge.fromLabelM P label
  let s ← Sponge.observeM P s (ofLimbs (word root 0) (word root 1) 0)
  let s ← Sponge.observeM P s (ofLimbs (word root 2) (word root 3) 0)
  Sponge.samplesM P logK s

/-- Climb from `node` at index `idx` along the siblings `path`. -/
def walkM : ℕ → DigestBytes → List DigestBytes → m DigestBytes
  | _, node, [] => pure node
  | idx, node, s :: rest => do
    let d ← keccakDigestBytes P (if idx % 2 = 0 then pairBytes node s else pairBytes s node)
    walkM (idx / 2) d rest

/-- **Verification of a cell opening**: a path of the column tree's height that climbs from the
cell's digest to a column root, which hashed after the row root gives the commitment. -/
def verifyCellM (r : ℕ) (com : DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : Opening) : m Bool :=
  do
  let d ← keccakDigestBytes P (cellBytes x)
  let w ← walkM P (colIndex p) d τ.path
  let root ← keccakDigestBytes P (pairBytes τ.rowRoot w)
  pure (decide (τ.path.length = 7 + logPad r) && decide (root = com))

/-- One level up a Merkle tree over an oracle (`up`). -/
def upM (f : ℕ → m DigestBytes) (i : ℕ) : m DigestBytes := do
  let a ← f (2 * i)
  let b ← f (2 * i + 1)
  keccakDigestBytes P (pairBytes a b)

/-- The root of a Merkle tree over an oracle (`merkleRoot`). -/
def merkleRootM : ℕ → (ℕ → m DigestBytes) → m DigestBytes
  | 0, f => f 0
  | d + 1, f => merkleRootM d (upM P f)

/-- The row tree's leaves over an oracle (`rowLeaves`). -/
def rowLeavesM {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) : m DigestBytes := do
  let ds ← (List.range 64).mapM fun j ↦ keccakDigestBytes P (cellBytes (paddedCell c i j))
  keccakDigestBytes P (ds.flatMap Vector.toList)

/-- The column tree's leaves over an oracle (`colLeaves`). -/
def colLeavesM {r : ℕ} (c : Fin (r * 128) → Cell) (l : ℕ) : m DigestBytes :=
  keccakDigestBytes P (cellBytes (paddedCell c (l % nPad r) (l / nPad r)))

/-- The row root over an oracle (`rowRoot`). -/
def rowRootM {r : ℕ} (c : Fin (r * 128) → Cell) : m DigestBytes :=
  merkleRootM P (logPad r) (rowLeavesM P c)

/-- The column root over an oracle (`colRoot`). -/
def colRootM {r : ℕ} (c : Fin (r * 128) → Cell) : m DigestBytes :=
  merkleRootM P (7 + logPad r) (colLeavesM P c)

/-- **The root of a matrix over an oracle** (`commitCells`). -/
def commitCellsM {r : ℕ} (c : Fin (r * 128) → Cell) : m DigestBytes := do
  let a ← rowRootM P c
  let b ← colRootM P c
  keccakDigestBytes P (pairBytes a b)

end Monadic

/-! #### The vector's digest -/

variable (π : KeccakState → KeccakState)

/-- The bytes of entries: three little-endian limbs each. -/
def limbBytes (entries : List E) : List UInt8 :=
  (entries.flatMap fun e ↦ [limb e 0, limb e 1, limb e 2]).flatMap kBytes

/-- The digest of column `j` of a vector, its entries `256 j … 256 j + 255`. -/
def columnDigest (vector : List E) (j : ℕ) : DigestBytes :=
  Id.run (keccakDigestBytes π (limbBytes ((vector.drop (j * cellSymbols)).take cellSymbols)))

/-- **The digest of a vector** (`vector_digest`, `verifier/src/da.rs:87-96`): the hash of its
`128` columns' digests, in order. The crate takes vectors of `2^15` entries and panics on others. -/
def vectorDigest (vector : List E) : DigestBytes :=
  Id.run (keccakDigestBytes π
    ((List.range cellsPerRow).flatMap fun j ↦ (columnDigest π vector j).toList))

/-! ## LeanDA's code and the argument's relation -/

/-- **LeanDA's erasure code**: `r` payloads, encoded row by row and cut into cells. -/
noncomputable def code (r : ℕ) : ErasureCode Payload Cell r (r * 128) := ⟨encodeMatrix⟩

/-- The challenges of the membership test. -/
abbrev Challenges := Fin 14 → E

/-- The challenges of the sponge's list. -/
def toChallenges (zs : List E) : Challenges := fun j ↦ zs.getD j 0

/-- **The relation the argument proves**, over a permutation `P` in any monad: the cells commit to
the root and pass the membership test on the root's challenges, drawn by the deployed duplex
(`membershipChallengesM`), the hash Keccak-256 over `P`. In the games `P` is `π`
(`queryPermutation`). -/
noncomputable def relationM {m : Type → Type} [Monad m] (P : KeccakState → m KeccakState) {r : ℕ}
    (root : DigestBytes) (c : Fin (r * 128) → Cell) : m Bool := do
  let zs ← membershipChallengesM P root
  let d ← commitCellsM P c
  pure (decide (d = root) && membershipCheck (toChallenges zs) c)

/-! ## Arguments in the random-permutation model -/

/-- **An argument in the random-permutation model** (Wagner's arguments of knowledge, Foundations
Definition 18, with oracle access): its prover and verifier query the model's oracles
(`RandomPermutationOracles`: coins, `π` and `π⁻¹`), the oracles the adversary and LeanDA's verifier
query. -/
structure OracleArgument (Stmt Wit Crs Proof : Type) where
  /-- Sample a common reference string. -/
  setup : ProbComp Crs
  /-- Produce a proof for `stmt` from witness `wit`, querying the oracles. -/
  prove : Crs → Stmt → Wit → OracleComp RandomPermutationOracles Proof
  /-- Verify a proof, querying the oracles. -/
  verify : Crs → Stmt → Proof → OracleComp RandomPermutationOracles Bool

/-- **A straight-line extractor in the random-permutation model**: a witness from the crs, the
statement, the proof and the transcript of the adversary's queries. -/
abbrev StraightLineExtractor (Stmt Wit Crs Proof : Type) :=
  Crs → Stmt → Proof → OracleQueryLog → Wit

/-- **The model's oracles answered by a permutation `π`**: coins uniform, `π` and `π⁻¹`. -/
noncomputable def oraclesFromPermutation (π : Equiv.Perm KeccakState) :
    QueryImpl RandomPermutationOracles ProbComp
  | .inl n => (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.forward x) => pure (π x)
  | .inr (.inverse y) => pure (π.symm y)

/-- **Perfect completeness for every permutation**: with the oracles answered by any permutation
`π`, an honest proof of a statement the relation `rel π` holds for verifies with probability
one. -/
def OracleArgument.PerfectlyComplete {Stmt Wit Crs Proof : Type}
    (ps : OracleArgument Stmt Wit Crs Proof)
    (rel : Equiv.Perm KeccakState → Stmt → Wit → Bool) : Prop :=
  ∀ (π : Equiv.Perm KeccakState), ∀ crs ∈ support ps.setup, ∀ stmt wit, rel π stmt wit = true →
    Pr{let b ← simulateQ (oraclesFromPermutation π)
         (ps.prove crs stmt wit >>= ps.verify crs stmt)}[b = true] = 1

/-- **LeanDA's relation for a permutation `π`**: `relationM` over `π`. -/
noncomputable def relationForPermutation (r : ℕ) (π : Equiv.Perm KeccakState) (root : DigestBytes)
    (c : Fin (r * 128) → Cell) : Bool :=
  Id.run (relationM (fun x ↦ pure (π x)) root c)

/-- An argument for LeanDA's relation: the statement a root, the witness the cells. -/
abbrev LeanDaArgument (r : ℕ) (Crs Proof : Type) :=
  OracleArgument DigestBytes (Fin (r * 128) → Cell) Crs Proof

/-! ## The games in the random-permutation model

Every party queries the same oracles (`RandomPermutationOracles`: coins, `π` and `π⁻¹`) and hashes
with Keccak-256 over `π` (`keccakDigestBytes queryPermutation`): the adversary, the argument's
prover and verifier, and LeanDA's verifier. A game is run against the lazily sampled permutation
(`runWithRandomPermutation`), and its cost counts every party's calls of `π` and `π⁻¹`
(`permutationCallCost`). LeanDA's verifier verifies the argument's proof for the commitment's root
once, and each opening's path. -/

variable (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
  (ext : StraightLineExtractor DigestBytes (Fin (r * 128) → Cell) Crs Proof)

/-- A position-binding adversary: from the commitment key, a commitment, a position, and two cells
with their openings. -/
abbrev PositionBindingAdversary (Crs Proof : Type) :=
  Unit × Crs →
    OracleComp RandomPermutationOracles
      ((DigestBytes × Proof) × Fin (r * 128) × Cell × Opening × Cell × Opening)

/-- **The position-binding game**: the argument's setup, the adversary, then the verifications:
the argument's of the root's proof and the two openings'; it wins when all verify, at two
different cells. -/
def positionBindingGame (A : PositionBindingAdversary r Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM ps.setup
  let (com, p, x, τ, x', τ') ← A ((), crs)
  let ok ← ps.verify crs com.1 com.2
  let b ← verifyCellM queryPermutation r com.1 p x τ
  let b' ← verifyCellM queryPermutation r com.1 p x' τ'
  pure (decide (x ≠ x') && ok && b && b')

/-- A code-binding adversary: from the commitment key, a commitment and a list of opened
positions. -/
abbrev CodeBindingAdversary (Crs Proof : Type) :=
  Unit × Crs →
    OracleComp RandomPermutationOracles
      ((DigestBytes × Proof) × List (Fin (r * 128) × Cell × Opening))

/-- **The code-binding game**: the argument's setup, the adversary, then the verifications; it wins
when the root's proof and every opening verify and no codeword agrees with the opened cells. -/
noncomputable def codeBindingGame (A : CodeBindingAdversary r Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM ps.setup
  let (com, opened) ← A ((), crs)
  let ok ← ps.verify crs com.1 com.2
  let verdicts ← opened.mapM fun o ↦ verifyCellM queryPermutation r com.1 o.1 o.2.1 o.2.2
  pure (ok && verdicts.all id && !decide ((code r).Consistent (opened.map fun o ↦ (o.1, o.2.1))))

/-- A knowledge-soundness adversary: from the crs, a root and a proof. -/
abbrev KnowledgeSoundnessAdversary (Crs Proof : Type) :=
  Crs → OracleComp RandomPermutationOracles (DigestBytes × Proof)

/-- **The argument's knowledge-soundness game** (Wagner's, Foundations Definition 18, in the
random-permutation model with a straight-line extractor): the argument's setup, the adversary with
its queries logged, the argument's verification, then the relation's check on the cells the
extractor reads off the proof and the adversary's transcript; it wins when the proof verifies and
the extracted cells do not satisfy the relation (`relationM` over `π`). -/
noncomputable def knowledgeSoundnessGame (B : KnowledgeSoundnessAdversary Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM ps.setup
  let ((root, proof), log) ← (simulateQ loggedOracles (B crs)).run []
  let v ← ps.verify crs root proof
  let ok ← relationM queryPermutation root (ext crs root proof log)
  pure (v && !ok)

/-- **The completeness experiment for a permutation `π`** (Wagner's, Foundations Definition 8,
with the hash and the oracles answered by `π`): the argument's setup; the honest commitment to the
message `msg`, the root of its encoding's cells hashed with Keccak-256 over `π`; the argument's
honest proof for the root and its verification, both with the oracles answered by `π`; and the
verification of the encoding's cell at `p` with its honest opening. -/
noncomputable def completenessExperiment (π : Equiv.Perm KeccakState)
    (ps : LeanDaArgument r Crs Proof)
    (msg : Fin r → Payload) (p : Fin (r * 128)) : ProbComp Bool := do
  let crs ← ps.setup
  let c := (code r).encode msg
  let root := commitCells π c
  let ok ← simulateQ (oraclesFromPermutation π) (ps.prove crs root c >>= ps.verify crs root)
  pure (ok && Id.run (verifyCellM (fun x ↦ pure (π x)) r root p (c p) (openCell π c p)))

/-! ### The end statements -/

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation.**
For any number `r` of rows, every permutation `π` of the Keccak state, and every argument `ps`
perfectly complete for LeanDA's relation for every permutation (`relationForPermutation`, the hash
Keccak-256 over `π` and the challenges the deployed duplex over `π`; the argument's prover and
verifier answered by `π`): every position `p` of the honest commitment to every message `msg`
opens and verifies with probability one (`completenessExperiment`). Holding for each `π`, it holds
for every outcome of the binding statements' uniformly random permutation. The proof is Wagner's
completeness proof, transferred. Proved by `LeanDa.leanDa_perfectlyComplete_rpm`. -/
abbrev PerfectlyCompleteRpm : Prop :=
  ∀ (r : ℕ) (π : Equiv.Perm KeccakState) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof),
    ps.PerfectlyComplete (relationForPermutation r) →
      ∀ (msg : Fin r → Payload) (p : Fin (r * 128)),
        Pr{let b ← completenessExperiment r π ps msg p}[b = true] = 1

/-- **LeanDA is position binding in the random-permutation model.** For every argument `ps` (any
prover and verifier) and every adversary whose game, verifications included, makes at most `Q`
calls of `π` and `π⁻¹` on every path (`permutationCallCost`; a hash of `n` bytes, Keccak-256 over
`π`, makes `⌊n / 136⌋ + 1`; the argument's verifier's included), the probability of opening a
position to two different cells is at most `(Q + 1)² · 2^-256`, for every `Q` (past `2^128` the
bound exceeds one). Proved by
`LeanDa.leanDa_positionBinding_rpm`. -/
abbrev PositionBindingRpm : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
    (A : PositionBindingAdversary r Crs Proof)
    (Q : ℕ), QueryCostAtMost (positionBindingGame r ps A) permutationCallCost Q →
      Pr{let b ← runWithRandomPermutation (positionBindingGame r ps A)}[b = true] ≤
        ((Q : ℝ≥0∞) + 1) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-- **LeanDA is code binding in the random-permutation model, for an argument knowledge sound in
it** (Benedikt Wagner's framework and games, moved to the random-permutation model, with a
straight-line argument in place of his forking lemma). For `1 ≤ r ≤ 1024` rows (`maxRows`, the
crate's bound), every argument `ps` (its prover and verifier querying the model's oracles) and
straight-line extractor `ext` (reading the adversary's transcript): if every adversary whose
knowledge-soundness game (`knowledgeSoundnessGame`, the argument's verifier and the relation's check
included) makes at most `q ≤ 2^128` permutation calls (`permutationCallCost`) wins it with
probability at most `(q + c) · 2^-k`, then every adversary whose code-binding game, verifications
included, makes at most `Q` calls breaks code binding with probability at most

`(Q + c + 2^22) · 2^-k + (Q + 2^22) · 2^-188 + (Q + 2^22)² · 2^-247`.

The first term is the argument's knowledge soundness against the code-binding adversary itself,
its transcript handed to the extractor (at most `Q + 2^22` calls with the relation's check). The
second is the membership test's soundness, `14 / 2^192` for each of at most `Q + 14` roots whose
challenges are drawn. The third gathers the transfer to the two-oracle model and the duplex
lemma, of the two games, and the hash's bad events among at most `2 Q + 2^20` hash and challenge
queries: a collision, or a fresh answer that is a digest an earlier input or a root with drawn
challenges already carries; it exceeds one before `Q = 2^124`.

The argument queries the oracles the adversary does, so its knowledge soundness here is the
usual one of an argument in the random-permutation model, with a straight-line extractor reading
the adversary's queries, as leanVM's (`LeanVM.KnowledgeSoundness`); an argument may satisfy it and
be perfectly complete for every permutation (`PerfectlyCompleteRpm`). Proved by
`LeanDa.leanDa_codeBinding_rpm_bound`. -/
abbrev CodeBindingRpm : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
    (ext : StraightLineExtractor DigestBytes (Fin (r * 128) → Cell) Crs Proof) (c k : ℕ),
    (∀ (B : KnowledgeSoundnessAdversary Crs Proof) (q : ℕ),
      QueryCostAtMost (knowledgeSoundnessGame r ps ext B) permutationCallCost q →
      q ≤ 2 ^ 128 →
        Pr{let b ← runWithRandomPermutation (knowledgeSoundnessGame r ps ext B)}[b = true] ≤
        ((q : ℝ≥0∞) + c) * (2 : ℝ≥0∞)⁻¹ ^ k) →
    1 ≤ r → r ≤ maxRows →
    ∀ (A : CodeBindingAdversary r Crs Proof) (Q : ℕ),
      QueryCostAtMost (codeBindingGame r ps A) permutationCallCost Q →
        Pr{let b ← runWithRandomPermutation (codeBindingGame r ps A)}[b = true] ≤
          ((Q : ℝ≥0∞) + c + 2 ^ 22) * (2 : ℝ≥0∞)⁻¹ ^ k + ((Q : ℝ≥0∞) + 2 ^ 22) * (2 : ℝ≥0∞)⁻¹ ^ 188 +
            ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247

end LeanDa

end
