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
knowledge-soundness game) and the code-binding bound are Benedikt Wagner's formalization,
https://github.com/b-wagn/fv-pq-da at `4475179c19296acf3469d7d552a3186ad1feda74` (his post:
https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746), ported and modified
to build on VCVio `afa6593f` and Lean v4.34.1, under the Apache License 2.0 (`lean_da/LICENSE`,
`lean_da/NOTICE`); the definitions the end statements need are here, the rest of his framework
(vector commitments, code checkers, the scheme in the random-oracle model and its games, his
reductions) and his proofs in `lean_da/PqDas/`. The instantiation with LeanDA (`LeanDa`) follows
his framework, and the end statements are his completeness and binding notions moved to the
random-permutation model.

The file: Wagner's framework (`PqDas`: erasure codes and the consistency of opened cells,
arguments of knowledge), LeanDA (`LeanDa`: the code, the commitment, the membership test, the
deployed algorithms), the verifier over a permutation, the games in the random-permutation model
(`H` Keccak-256 over `π`, the membership challenges the deployed duplex over `π`; no random
oracle), and the end statements (last section).
-/

@[expose] public section

open Polynomial OracleComp OracleSpec ENNReal Common MeasureTheory

set_option linter.unusedSectionVars false

/-! ## Wagner's framework: erasure codes and arguments of knowledge -/

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

/-- A non-interactive argument (of knowledge) for the `Bool`-valued relation
`rel`, with statement type `Stmt`, witness type `Wit`, common reference string
type `Crs`, and proof type `Proof` (Foundations Definition 18, with
deterministic `prove`). -/
structure Nark (Stmt Wit Crs Proof : Type) (rel : Stmt → Wit → Bool) where
  /-- Sample a common reference string. -/
  setup : ProbComp Crs
  /-- Produce a proof for `stmt` from witness `wit` (deterministic). -/
  prove : Crs → Stmt → Wit → Proof
  /-- Verify a proof (deterministic). -/
  verify : Crs → Stmt → Proof → Bool

namespace Nark

variable {Stmt Wit Crs Proof : Type} {rel : Stmt → Wit → Bool}

/-- Perfect completeness: honestly generated proofs for true statements verify. -/
def PerfectlyComplete (ps : Nark Stmt Wit Crs Proof rel) : Prop :=
  ∀ crs ∈ support ps.setup, ∀ stmt wit, rel stmt wit = true →
    ps.verify crs stmt (ps.prove crs stmt wit) = true

/-- A straightline knowledge extractor: computes a witness from the crs, the
statement, and the proof alone (Foundations Definition 18). -/
def Extractor (Stmt Wit Crs Proof : Type) := Crs → Stmt → Proof → Wit

end Nark

end PqDas

/-! ## LeanDA's fields -/

namespace LeanDa

open PqDas

export LeanVM.Parameters (K E K.ofBits)

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
`94ee12ff6b2a3d42ba8328e22d09443692e4800b`, specified in `doc/leanvm/body/10-ethereum.tex`
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
  every row is orthogonal to `L` (`check_membership`, `membership.rs:94-103`; the guest's
  `da_verify`). The challenges are drawn from the root by a duplex sponge over Keccak-f[1600]
  seeded with the label's hash (`membership_challenges`); the end statements draw them by this
  duplex over the permutation (`membershipChallengesM`).

The row count `r` is a parameter: the crate takes `1 ≤ r ≤ 1024` (`row_count`, `lib.rs:41-46`);
completeness and position binding hold for every `r`, code binding for `1 ≤ r ≤ 1024`
(`maxRows`). The deployed algorithms (last of this part, for `lean_vm`'s DA claims) take the hash
`H` and the sponge's permutation `P` as parameters: the crate's are Keccak-256
(`verifier/src/hash.rs:79-97`) and Keccak-f[1600]; in the end statements `H` is Keccak-256 over
`π` and `P` is `π` itself.
-/

/-- A digest of the hash, 32 bytes (`fiat_shamir::merkle::Hash`, `[u8; 32]`). -/
abbrev Digest := Vector UInt8 32

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

/-! ### The commitment (`commit.rs`) -/

section Pure

variable (H : List UInt8 → Digest)

/-- The eight little-endian bytes of a symbol (`as_bytes`). -/
def kBytes (a : K) : List UInt8 := (List.range 8).map fun t ↦ (a.toBitVec.toNat >>> (8 * t)).toUInt8

/-- A cell's bytes: its symbols' bytes in order. -/
def cellBytes (x : Cell) : List UInt8 := (List.ofFn x).flatMap kBytes

/-- The 64 bytes of a pair of digests (`hash_pair`, `tree_from_leaves`). -/
def pairBytes (a b : Digest) : List UInt8 := a.toList ++ b.toList

/-- The digest of a cell (`hash_cells`). -/
def cellDigest (x : Cell) : Digest := H (cellBytes x)

/-- `⌈log₂ r⌉`: the padded row count `2^⌈log₂ r⌉` is `r.next_power_of_two()`. -/
def logPad (r : ℕ) : ℕ := Nat.clog 2 r

/-- The padded row count. -/
def nPad (r : ℕ) : ℕ := 2 ^ logPad r

/-- Cell `j` of row `i` of the padded matrix: zero below the `r` rows. -/
def paddedCell {r : ℕ} (c : Fin (r * 128) → Cell) (i j : ℕ) : Cell :=
  if h : i < r ∧ j < 128 then c (pos ⟨i, h.1⟩ ⟨j, h.2⟩) else 0

/-- One level up a Merkle tree: node `i` hashes nodes `2i` and `2i + 1`. -/
def up (f : ℕ → Digest) (i : ℕ) : Digest := H (pairBytes (f (2 * i)) (f (2 * i + 1)))

/-- The root of the Merkle tree over the leaves `f 0 … f (2^d - 1)` (`tree_from_leaves`). -/
def merkleRoot : ℕ → (ℕ → Digest) → Digest
  | 0, f => f 0
  | d + 1, f => merkleRoot d (up H f)

/-- The other node of the pair of node `idx`. -/
def sibling (idx : ℕ) : ℕ := if idx % 2 = 0 then idx + 1 else idx - 1

/-- The authentication path of leaf `idx`, siblings from the bottom. -/
def merklePath : ℕ → (ℕ → Digest) → ℕ → List Digest
  | 0, _, _ => []
  | d + 1, f, idx => f (sibling idx) :: merklePath d (up H f) (idx / 2)

/-- The row tree's leaves: each padded row's digest of its first `64` cell digests. -/
def rowLeaves {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) : Digest :=
  H ((List.ofFn fun j : Fin 64 ↦ cellDigest H (paddedCell c i j)).flatMap Vector.toList)

/-- The column tree's leaves: leaf `j · 2^⌈log₂ r⌉ + i` is cell `j` of padded row `i`. -/
def colLeaves {r : ℕ} (c : Fin (r * 128) → Cell) (l : ℕ) : Digest :=
  cellDigest H (paddedCell c (l % nPad r) (l / nPad r))

/-- The row root (`root_row`). -/
def rowRoot {r : ℕ} (c : Fin (r * 128) → Cell) : Digest := merkleRoot H (logPad r) (rowLeaves H c)

/-- The column root (`root_col`). -/
def colRoot {r : ℕ} (c : Fin (r * 128) → Cell) : Digest :=
  merkleRoot H (7 + logPad r) (colLeaves H c)

/-- **The root of a matrix** (`commit_codewords`): `H(rowRoot ‖ colRoot)`. -/
def commitCells {r : ℕ} (c : Fin (r * 128) → Cell) : Digest :=
  H (pairBytes (rowRoot H c) (colRoot H c))

/-! ### Openings -/

/-- The opening of a cell: the row root and the cell's path in the column tree. -/
structure Opening where
  /-- The row root. -/
  rowRoot : Digest
  /-- The siblings from the cell's leaf up to the column root. -/
  path : List Digest
deriving Inhabited

/-- The column tree index of a position: cell `j` of row `i` is leaf `j · 2^⌈log₂ r⌉ + i`. -/
def colIndex {r : ℕ} (p : Fin (r * 128)) : ℕ := (posCell p : ℕ) * nPad r + posRow p

/-- The honest opening of a position. -/
def openCell {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) : Opening :=
  ⟨rowRoot H c, merklePath H (7 + logPad r) (colLeaves H c) (colIndex p)⟩

/-! ### Membership (`membership.rs`, `verifier/src/da.rs`) -/

/-- The normalized subspace polynomial `Ŵ_j`, vanishing on the span of `e_0 … e_(j-1)` and one
at `e_j` (CompPoly's `normalizedW`; `subspace_evaluations` tabulates it on the basis). -/
noncomputable def normW (j : Fin 14) : K[X] :=
  AdditiveNTT.normalizedW (ZMod 2) basis (Fin.castLE (by omega) j)

/-- **The dual codeword of challenges `z`** (`dual_codeword`): `L(x) = ∏_j (1 + z_j Ŵ_j(x))` on
the domain, the encoding of `tensor z` (`dual_eq_encode_tensor`). -/
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
def treeLevel (nodes : List Digest) : List Digest :=
  (List.range (nodes.length / 2)).map (up H fun i ↦ nodes.getD i default)

/-- The root of the Merkle tree over a power-of-two number of digests (`tree_from_leaves`; on
other lengths, which `commitCodewords` never passes, the crate panics). -/
def treeRoot (nodes : List Digest) : Digest :=
  if nodes.length ≤ 1 then nodes.headD default else treeRoot (treeLevel H nodes)
termination_by nodes.length
decreasing_by simp only [treeLevel, List.length_map, List.length_range]; omega

/-- Cell `j` of a codeword. -/
def listCell (row : List K) (j : ℕ) : List K := (row.drop (j * cellSymbols)).take cellSymbols

/-- The digest of cell `j` of a codeword (`hash_cells`). -/
def listCellDigest (row : List K) (j : ℕ) : Digest := H ((listCell row j).flatMap kBytes)

/-- A row's digest: the hash of its payload cells' digests. -/
def rowDigest (row : List K) : Digest :=
  H ((List.range payloadCells).flatMap fun j ↦ (listCellDigest H row j).toList)

/-- The digest of the zero cell, which pads the columns (`padding_digests`). -/
def paddingCell : Digest := H ((List.replicate cellSymbols 0).flatMap kBytes)

/-- The digest of the zero row, which pads the row tree (`padding_digests`). -/
def paddingRow : Digest := H ((List.replicate payloadCells (paddingCell H)).flatMap Vector.toList)

/-- **The root of a matrix of codewords, as the crate computes it** (`commit_codewords`): the
rows padded to a power of two, the hash of the row tree's root and the column tree's. -/
def commitCodewords (rows : List (List K)) : Digest :=
  let n := nPad rows.length
  let rowTree := treeRoot H
    (rows.map (rowDigest H) ++ List.replicate (n - rows.length) (paddingRow H))
  let columnTree := treeRoot H ((List.range cellsPerRow).flatMap fun j ↦ (List.range n).map fun i ↦
    if h : i < rows.length then listCellDigest H rows[i] j else paddingCell H)
  H (pairBytes rowTree columnTree)

/-! ### The deployed membership vector (`verifier/src/da.rs:15-96`)

The challenges, drawn from the root by the duplex sponge (over the permutation `π` in the end
statements), and the dual codeword as the crate computes it, by the additive NTT, which computes `dual`
(`membershipVector_eq_dual`, `LeanDa.Dual`). -/

/-- `leanDA/rs-membership/v1`, the label of the challenges' transcript (`LABEL`). -/
def label : List UInt8 := "leanDA/rs-membership/v1".toUTF8.toList

/-- The symbol of eight little-endian bytes (`u64::from_le_bytes`). -/
def ofBytes (bytes : List UInt8) : K := K.ofBits (bytes.foldr (fun b acc ↦ b.toNat + 256 * acc) 0)

/-- Word `i` of a digest, its bytes `8 i … 8 i + 7` (`Digest::words`). -/
def word (d : Digest) (i : ℕ) : K := ofBytes ((d.toList.drop (8 * i)).take 8)

/-- The element `c0 + c1·y + c2·y²` (`E::new`). -/
def ofLimbs (c0 c1 c2 : K) : E := CompPoly.Extension.Ext.ofVector #v[c0, c1, c2]

/-- Limb `i` of an element, the coefficient of `y^i`. -/
def limb (x : E) (i : Fin 3) : K := CompPoly.Extension.Ext.coeff x i

end Pure

/-! #### The sponge (`verifier/src/transcript.rs:32-95`)

A duplex sponge in overwrite mode over a permutation `P` of `25` lanes. The crate's is
Keccak-f[1600] (`keccak_f`, `verifier/src/hash.rs:50-69`), which `lean_vm` supplies; the
definitions hold for every `P`. A lane is a `u64`, read as the element of `K` with its bits, so
a scalar's limbs are lanes as they are. The rate is lanes `0 … 15`, the capacity lanes
`16 … 24`. -/

/-- The sponge's lanes (`[u64; STATE_LANES]`). -/
abbrev Lanes := Vector K 25

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
  state : Lanes
  /-- The waiting scalars and their tags, in order. -/
  pending : List (E × K)

/-- The rate lanes the waiting scalars fill: scalar `i`'s three limbs and tag in lanes
`4 i … 4 i + 3`. -/
def rateWords (pending : List (E × K)) : List K :=
  pending.flatMap fun x ↦ [limb x.1 0, limb x.1 1, limb x.1 2, x.2]

/-! The sponge, the challenges and the openings' check over a hash `H` and a permutation `P` in
any monad: the games' oracles, or pure functions over `Id`. -/

section Monadic

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (P : Lanes → m Lanes)

/-- The lanes a duplexing permutes: the waiting scalars over the rate, the rest of the rate zero,
the capacity kept. -/
def duplexInput (s : Sponge) : Lanes :=
  Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < rateLanes then (rateWords s.pending).getD i 0 else s.state[i]

/-- The lanes of a fresh sponge: the IV's words in lanes `0 … 3`, the public input's in `4 … 7`. -/
def newInput (iv publicInput : Digest) : Lanes :=
  Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < 4 then word iv i else if (i : ℕ) < 8 then word publicInput (i - 4) else 0

/-- A sponge seeded with one permutation of `newInput` (`Sponge::new`). -/
def Sponge.newM (iv publicInput : Digest) : m Sponge := do
  let state ← P (newInput iv publicInput)
  pure ⟨state, []⟩

/-- A sponge with no public input of its own, seeded from the hash of `label`
(`Sponge::from_label`). -/
def Sponge.fromLabelM (label : List UInt8) : m Sponge := do
  let iv ← H label
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
  pure (ofLimbs s.state[0] s.state[1] s.state[2], s)

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
def membershipChallengesM (root : Digest) : m (List E) := do
  let s ← Sponge.fromLabelM H P label
  let s ← Sponge.observeM P s (ofLimbs (word root 0) (word root 1) 0)
  let s ← Sponge.observeM P s (ofLimbs (word root 2) (word root 3) 0)
  Sponge.samplesM P logK s

/-- Climb from `node` at index `idx` along the siblings `path`. -/
def walkM : ℕ → Digest → List Digest → m Digest
  | _, node, [] => pure node
  | idx, node, s :: rest => do
    let d ← H (if idx % 2 = 0 then pairBytes node s else pairBytes s node)
    walkM (idx / 2) d rest

/-- **Verification of a cell opening**: a path of the column tree's height that climbs from the
cell's digest to a column root, which hashed after the row root gives the commitment. -/
def verifyCellM (r : ℕ) (com : Digest) (p : Fin (r * 128)) (x : Cell) (τ : Opening) : m Bool := do
  let d ← H (cellBytes x)
  let w ← walkM H (colIndex p) d τ.path
  let root ← H (pairBytes τ.rowRoot w)
  pure (decide (τ.path.length = 7 + logPad r) && decide (root = com))

/-- One level up a Merkle tree over an oracle (`up`). -/
def upM (f : ℕ → m Digest) (i : ℕ) : m Digest := do
  let a ← f (2 * i)
  let b ← f (2 * i + 1)
  H (pairBytes a b)

/-- The root of a Merkle tree over an oracle (`merkleRoot`). -/
def merkleRootM : ℕ → (ℕ → m Digest) → m Digest
  | 0, f => f 0
  | d + 1, f => merkleRootM d (upM H f)

/-- The row tree's leaves over an oracle (`rowLeaves`). -/
def rowLeavesM {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) : m Digest := do
  let ds ← (List.range 64).mapM fun j ↦ H (cellBytes (paddedCell c i j))
  H (ds.flatMap Vector.toList)

/-- The column tree's leaves over an oracle (`colLeaves`). -/
def colLeavesM {r : ℕ} (c : Fin (r * 128) → Cell) (l : ℕ) : m Digest :=
  H (cellBytes (paddedCell c (l % nPad r) (l / nPad r)))

/-- The row root over an oracle (`rowRoot`). -/
def rowRootM {r : ℕ} (c : Fin (r * 128) → Cell) : m Digest :=
  merkleRootM H (logPad r) (rowLeavesM H c)

/-- The column root over an oracle (`colRoot`). -/
def colRootM {r : ℕ} (c : Fin (r * 128) → Cell) : m Digest :=
  merkleRootM H (7 + logPad r) (colLeavesM H c)

/-- **The root of a matrix over an oracle** (`commitCells`). -/
def commitCellsM {r : ℕ} (c : Fin (r * 128) → Cell) : m Digest := do
  let a ← rowRootM H c
  let b ← colRootM H c
  H (pairBytes a b)

end Monadic

/-! #### The challenges and the vector -/

variable (H : List UInt8 → Digest) (P : Lanes → Lanes)

/-- The challenges of a root with a pure hash and permutation. -/
def membershipChallenges (root : Digest) : List E :=
  Id.run (membershipChallengesM (fun a ↦ pure (H a)) (fun L ↦ pure (P L)) root)

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
  let top := List.zipWith (fun u v ↦ u + v * CompPoly.Extension.Ext.ofBase twiddle) top bottom
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

/-- The dual codeword, the tensor of the `(1, z_j)` encoded (`dual_codeword`). -/
def dualCodeword (z : List E) : List E :=
  encode (z.foldl (fun t challenge ↦ t ++ t.map (· * challenge)) [1])

/-- **The membership vector of a root** (`membership_vector`). -/
def membershipVector (root : Digest) : List E := dualCodeword (membershipChallenges H P root)

/-- The bytes of entries: three little-endian limbs each. -/
def limbBytes (entries : List E) : List UInt8 :=
  (entries.flatMap fun e ↦ [limb e 0, limb e 1, limb e 2]).flatMap kBytes

/-- The digest of column `j` of a vector, its entries `256 j … 256 j + 255`. -/
def columnDigest (vector : List E) (j : ℕ) : Digest :=
  H (limbBytes ((vector.drop (j * cellSymbols)).take cellSymbols))

/-- **The digest of a vector** (`vector_digest`, `verifier/src/da.rs:87-96`): the hash of its
`128` columns' digests, in order. The crate takes vectors of `2^15` entries and panics on others. -/
def vectorDigest (vector : List E) : Digest :=
  H ((List.range cellsPerRow).flatMap fun j ↦ (columnDigest H vector j).toList)

/-! ## LeanDA's code and the argument's relation -/

/-- **LeanDA's erasure code**: `r` payloads, encoded row by row and cut into cells. -/
noncomputable def code (r : ℕ) : ErasureCode Payload Cell r (r * 128) := ⟨encodeMatrix⟩

/-- The challenges of the membership test. -/
abbrev Challenges := Fin 14 → E

/-- **The relation the argument proves**: the cells commit to the root and pass the membership test
on the challenges. -/
noncomputable def Relation (r : ℕ) (H : List UInt8 → Digest) (stmt : Unit × Digest × Challenges)
    (c : Fin (r * 128) → Cell) : Bool :=
  decide (commitCells H c = stmt.2.1) && membershipCheck stmt.2.2 c

/-- An argument of knowledge for `Relation r H`. -/
abbrev Argument (r : ℕ) (H : List UInt8 → Digest) (Crs Proof : Type) :=
  Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof (Relation r H)

/-! ## LeanDA's verifier over a permutation -/

/-- **A lane's bytes**, little endian. -/
def laneBytes : K ≃ Vector UInt8 8 :=
  BF64.equivFin.trans <| (finCongr (show 2 ^ 64 = 256 ^ 8 by norm_num)).trans <|
    finFunctionFinEquiv.symm.trans <|
      (Equiv.arrowCongr (Equiv.refl _) Common.uInt8EquivFin.symm).trans
        (arrayVectorEquivFin UInt8 8).symm

/-- **The permutation's state of 25 lanes**: lane `i` at bytes `8 i … 8 i + 7`. -/
def lanesToState (L : Lanes) : KState := KState.ofBytes (L.toList.flatMap fun a ↦ (laneBytes a).toList)

/-- **The lanes of a permutation's state.** -/
def stateToLanes (s : KState) : Lanes :=
  Vector.ofFn fun i : Fin 25 ↦ laneBytes.symm (Vector.ofFn fun j : Fin 8 ↦ s.toBytes.getD (8 * i + j) 0)

/-- **The permutation on lanes** from a permutation of the state, in any monad. -/
def lanePerm {m : Type → Type} [Monad m] (π : KState → m KState) (L : Lanes) : m Lanes :=
  stateToLanes <$> π (lanesToState L)

/-- Keccak-256 among the oracles of the random-permutation model. -/
abbrev hK (a : List UInt8) : OracleComp KSpec Digest := liftM (KSpec.query (.inr (.inl a)))

/-- A call `π x` of the permutation among the oracles, on lanes. -/
abbrev pK (L : Lanes) : OracleComp KSpec Lanes :=
  lanePerm (fun x ↦ liftM (KSpec.query (.inr (.inr (.fwd x))))) L

/-- The challenges of the sponge's list. -/
def toChallenges (zs : List E) : Challenges := fun j ↦ zs.getD j 0

/-- **Verification of an opening** (the verification of Wagner's scheme), with a hash `H` and the
sponge's permutation `P` in any monad: the challenges of the commitment's root from the deployed
duplex over `P`, the argument's verification, and the opening's. In the games `H` is Keccak-256
and `P` is `π` (`hK`, `pK`). -/
def verifyRpm {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (P : Lanes → m Lanes)
    (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel) (crs : Crs)
    (com : Digest × Proof) (p : Fin (r * 128)) (x : Cell) (τ : Opening) : m Bool := do
  let zs ← membershipChallengesM H P com.1
  let v ← verifyCellM H r com.1 p x τ
  pure (ps.verify crs ((), com.1, toChallenges zs) com.2 && v)

/-! ## The games in the random-permutation model

Every party queries the same oracles (`KSpec`): the adversary Keccak-256, `π` and `π⁻¹`; the
verifier Keccak-256 and, in the challenges' duplex, `π`. A game is run against the lazily sampled
permutation (`runK`), and its cost counts every party's calls (`permCalls`). -/

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
  (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)

/-- A position-binding adversary: from the commitment key, a commitment, a position, and two cells
with their openings. -/
abbrev PosBindingAdvRpm (Crs Proof : Type) :=
  Unit × Crs → OracleComp KSpec ((Digest × Proof) × Fin (r * 128) × Cell × Opening × Cell × Opening)

/-- **The position-binding game**: the argument's setup, the adversary, then the two
verifications; it wins when both openings verify, at two different cells. -/
def posBindingGame (A : PosBindingAdvRpm r Crs Proof) : OracleComp KSpec Bool := do
  let crs ← liftM ps.setup
  let (com, p, x, τ, x', τ') ← A ((), crs)
  let b ← verifyRpm hK pK r ps crs com p x τ
  let b' ← verifyRpm hK pK r ps crs com p x' τ'
  pure (decide (x ≠ x') && b && b')

/-- A code-binding adversary: from the commitment key, a commitment and a list of opened
positions. -/
abbrev CodeBindingAdvRpm (Crs Proof : Type) :=
  Unit × Crs → OracleComp KSpec ((Digest × Proof) × List (Fin (r * 128) × Cell × Opening))

/-- **The code-binding game**: the argument's setup, the adversary, then the verifications; it wins
when every opening verifies and no codeword agrees with the opened cells. -/
noncomputable def codeBindingGame (A : CodeBindingAdvRpm r Crs Proof) : OracleComp KSpec Bool := do
  let crs ← liftM ps.setup
  let (com, opened) ← A ((), crs)
  let verdicts ← opened.mapM fun o ↦ verifyRpm hK pK r ps crs com o.1 o.2.1 o.2.2
  pure (verdicts.all id && !decide ((code r).Consistent (opened.map fun o ↦ (o.1, o.2.1))))

/-- A knowledge-soundness adversary: from the crs, a statement and a proof. -/
abbrev KsAdvRpm (Crs Proof : Type) := Crs → OracleComp KSpec ((Unit × Digest × Challenges) × Proof)

/-- **The argument's knowledge-soundness game** (Wagner's, Foundations Definition 18, with the hash
over `π`): the argument's setup, the adversary, then the verification and the relation's check; it
wins when the proof verifies and the extracted cells do not satisfy the relation (`Relation`),
their root hashed with Keccak-256. -/
noncomputable def ksGame (B : KsAdvRpm Crs Proof) : OracleComp KSpec Bool := do
  let crs ← liftM ps.setup
  let (stmt, proof) ← B crs
  let root ← commitCellsM hK (ext crs stmt proof)
  pure (ps.verify crs stmt proof &&
    !(decide (root = stmt.2.1) && membershipCheck stmt.2.2 (ext crs stmt proof)))

/-- **Keccak-256 over a permutation `π`**: the sponge over `π` from the zero state with
Keccak-256's padding, the hash `H` of the games when the permutation is `π` (`realImpl`). -/
def keccakWith (π : KState → KState) (a : List UInt8) : Digest :=
  Id.run (spongeWith (m := Id) keccakPadding KState.zero (fun x ↦ pure (π x)) a)

/-- **The completeness experiment for a permutation `π`** (Wagner's, Foundations Definition 8,
with the hash and the challenges over `π`): the argument's setup; the honest commitment to the
message `msg`, the root of its encoding's cells hashed with Keccak-256 over `π` and the argument's
proof for the challenges of the root, drawn by the deployed duplex over `π`
(`membershipChallengesM`); the honest opening of the position `p`; and the binding games'
verification (`verifyRpm`) of the encoding's cell at `p` with that opening, over `π`. -/
noncomputable def completenessExpRpm (π : KState → KState)
    (ps : Argument r (keccakWith π) Crs Proof) (msg : Fin r → Payload) (p : Fin (r * 128)) :
    ProbComp Bool := do
  let crs ← ps.setup
  let H : List UInt8 → Id Digest := fun a ↦ pure (keccakWith π a)
  let P : Lanes → Id Lanes := lanePerm fun x ↦ pure (π x)
  let c := (code r).encode msg
  let root := commitCells (keccakWith π) c
  let proof := ps.prove crs ((), root, toChallenges (Id.run (membershipChallengesM H P root))) c
  pure (Id.run (verifyRpm H P r ps crs (root, proof) p (c p) (openCell (keccakWith π) c p)))

/-! ### The end statements -/

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation.**
For any number `r` of rows, every permutation `π` of the Keccak state (indeed every function), the
hash Keccak-256 over `π` and the membership challenges the deployed duplex over `π`, and every
perfectly complete argument `ps` for the relation with that hash: every position `p` of the
honest commitment to every message `msg` opens and verifies with probability one
(`completenessExpRpm`, over the argument's setup). Holding for each `π`, it holds for every
outcome of the binding statements' uniformly random permutation. The proof is Wagner's
completeness proof, transferred. Proved by `LeanDa.leanDa_perfectlyComplete_rpm`. (Such an argument
does not satisfy `CodeBindingRpm`'s hypothesis: see there.) -/
abbrev PerfectlyCompleteRpm : Prop :=
  ∀ (r : ℕ) (π : KState → KState) {Crs Proof : Type} (ps : Argument r (keccakWith π) Crs Proof),
    ps.PerfectlyComplete →
      ∀ (msg : Fin r → Payload) (p : Fin (r * 128)),
        Pr{let b ← completenessExpRpm r π ps msg p}[b = true] = 1

/-- **LeanDA is position binding in the random-permutation model.** For every argument `ps` (any
verifier, for any relation) and every adversary whose game, verifications included, makes at most
`Q` calls of the permutation on every path (`permCalls`: a hash of `n` bytes costs
`⌊n / 136⌋ + 1`, a call of `π` or `π⁻¹` one, the verifier's sponge's included), the probability
of opening a position to two different cells is at most `(Q + 1)² · 2^-256`, for `Q ≤ 2^128`.
Proved by `LeanDa.leanDa_positionBinding_rpm`. -/
abbrev PositionBindingRpm : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
    (A : PosBindingAdvRpm r Crs Proof) (Q : ℕ),
    IsWeightBound (posBindingGame r ps A) permCalls Q → Q ≤ 2 ^ 128 →
      Pr{let b ← runK (posBindingGame r ps A)}[b = true] ≤
        ((Q : ℝ≥0∞) + 1) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-- **LeanDA is code binding in the random-permutation model, for an argument knowledge sound in
it** (Benedikt Wagner's bound, moved to the random-permutation model). For `1 ≤ r ≤ 1024` rows
(`maxRows`, the crate's bound), every argument `ps` (any verifier, for any relation; an
oracle-free parameter, as in Wagner's model) and extractor `ext`: if every adversary whose
knowledge-soundness game (`ksGame`, the relation's check included) makes at most `q ≤ 2^128`
permutation calls (`permCalls`) wins it with probability at most `(q + c) · 2^-k`, then every
adversary whose code-binding game, verifications included, makes at most `Q ≤ 2^127` calls breaks
code binding with probability at most

`(Q + c + 2^22) · 2^-k + (Q + 2^20) · 2^-93 + (Q + 2^22)² · 2^-158`.

The first term is the argument's knowledge soundness against an adversary that runs the
code-binding adversary and derives the challenges of its root (at most `Q + 2^22` calls with the
relation's commitment). The rest gathers the transfer to the two-oracle model and the duplex
lemma, of the two games, two birthday bounds for collisions of the hash, and the loss of Wagner's
forking lemma, the square root of `(Q + 2) · (N² / 2^256 + 14 / 2^192 + 2^-2688)` for the fork's
`N ≤ 2 Q + 2^21` hash calls, at most `x · 2^-95 + x² · 2^-159 + (Q + 2) · 2^-94` for
`x = Q + 2^20`.

The hypothesis holds only for an argument that stays knowledge sound when the hash is `π`'s:
`ps` proves a relation that hashes with Keccak-256 over `π`, but its prover and verifier do not
call `π`, so an argument that accepts any statement accepts it for every `π`, while the relation
holds for few `π`; an argument without access to `π` (or a simulation of it) satisfies the
hypothesis only if it accepts essentially nothing. An argument complete for every `π`
(`PerfectlyCompleteRpm`) does not, so completeness and code binding are not both meaningful for
one argument, as in Wagner's random-oracle original. Giving the argument oracle access would close
this; it is not done. Proved by `LeanDa.leanDa_codeBinding_rpm_bound`. -/
abbrev CodeBindingRpm : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof) (c k : ℕ),
    (∀ (B : KsAdvRpm Crs Proof) (q : ℕ), IsWeightBound (ksGame r ps ext B) permCalls q →
      q ≤ 2 ^ 128 → Pr{let b ← runK (ksGame r ps ext B)}[b = true] ≤
        ((q : ℝ≥0∞) + c) * (2 : ℝ≥0∞)⁻¹ ^ k) →
    1 ≤ r → r ≤ maxRows →
    ∀ (A : CodeBindingAdvRpm r Crs Proof) (Q : ℕ),
      IsWeightBound (codeBindingGame r ps A) permCalls Q → Q ≤ 2 ^ 127 →
        Pr{let b ← runK (codeBindingGame r ps A)}[b = true] ≤
          ((Q : ℝ≥0∞) + c + 2 ^ 22) * (2 : ℝ≥0∞)⁻¹ ^ k + ((Q : ℝ≥0∞) + 2 ^ 20) * (2 : ℝ≥0∞)⁻¹ ^ 93 +
            ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 158

end LeanDa

end
