module

public import Statement.RandomPermutation
public import CompPoly.Fields.Binary.BF64
public import CompPoly.Fields.Binary.AdditiveNTT.NovelPolynomialBasis
public import VCVio.OracleComp.Constructions.SampleableType
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Lagrange
public import VCVio.CryptoFoundations.CommitmentScheme
public import VCVio.CryptoFoundations.ReplayFork
public import VCVio.OracleComp.Constructions.Fork.Basic
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.HasQuery.Morphism
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.Coercions.Add.Basic
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.EvalDist.Inequalities
public import Mathlib.Data.Set.Finite.List
public import Statement.Fast.FieldWords
public import Statement.Fast.CubicExt
public import Statement.Fast.Keccak

/-!
# LeanDA

LeanDA as `crates/lean_da` computes it, and its security in Benedikt Wagner's framework for erasure
code commitments, moved to the random-permutation model.

**Credit.** The framework (`PqDas`: erasure codes, vector commitments, code checkers, arguments of
knowledge, the relation of the scheme's argument, the code-binding adversary, and the reductions
the code-binding bound names with their simulation of the random oracle) is Benedikt Wagner's
formalization,
https://github.com/b-wagn/fv-pq-da at `4475179c19296acf3469d7d552a3186ad1feda74` (his post:
https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746), ported and modified
to build on VCVio `afa6593f` and Lean v4.34.1, under the Apache License 2.0 (`lean_da/LICENSE`,
`lean_da/NOTICE`); the definitions the end statements need are here, the rest of his framework
(the scheme in the random-oracle model and its games) and his proofs in `lean_da/PqDas/`. The
instantiation with LeanDA (`LeanDa`) follows his framework, and the completeness statement is his
completeness moved to the random-permutation model.

* **The scheme** (`LeanDa`): the fields, the Reed–Solomon encoding of the rows, the Merkle
  commitment of the cells and the membership test.
* **Wagner's framework** (`PqDas`) and **LeanDA in it** (`LeanDa.code`, `merkleVC`, `checker`,
  the relation `Relation` and its arguments `Argument`).
* **The random-permutation model** (`LeanDa.posBindingExpRpm`, `codeBindingExpRpm`,
  `completenessExpRpm`): `H` is Keccak-256 over `π`, the membership challenges the deployed duplex
  over `π` (`membershipChallengesM`), the adversary querying Keccak-256, `π` and `π⁻¹`; the bound's
  terms through Wagner's reductions for a uniformly random table of `H` (`ksExpH`, `wpbCollExpH`,
  `forkCollExpH`); completeness for each permutation `π` (`keccakWith`, `permImpl`).
* **The end statements** (last section): `LeanDa.PerfectlyCompleteRpm`,
  `LeanDa.PositionBindingRpm`, `LeanDa.CodeBindingRpm`. Proved by
  `LeanDa.leanDa_perfectlyComplete_rpm`, `leanDa_positionBinding_rpm` and
  `leanDa_codeBinding_rpm_bound` (`lean_da`).

**What code binding says.** Wagner's framework is kept as it is. `CodeBindingRpm`'s bound keeps
three of his reductions' advantages, which are random-oracle experiments over a uniformly random
table of the hash, not numbers: `ksExpH` (the argument's knowledge-soundness error `ε_ks`),
`wpbCollExpH` and `forkCollExpH`. The argument (`Nark`) proves a relation that involves the hash,
but its prover and verifier do not call the hash; so `ε_ks` is small only for an argument that
stays knowledge sound when the hash is the random oracle, and an oracle-free argument cannot be.
An argument complete for every `π` (as `PerfectlyCompleteRpm` asks) accepts false statements, and
for it `ε_ks ≈ 1`: completeness and code binding cannot both be meaningful for one argument. The
same holds in Wagner's random-oracle original. Giving the argument oracle access would close this;
it is not done.

Not definitions: `daDuplex` is a `Common.Duplex.DuplexSpec`, which carries the duplex's laws, so
the lemmas before it (`daFirst_injective`, `daDec_iff` and what they use) are proved here. The
three `Statement.Fast` imports only make the compiled field arithmetic and Keccak fast (proved
`@[csimp]` lemmas, `Fast/`); they change no definition.
-/

/-! ## LeanDA's fields -/

section

namespace LeanDa

@[expose] public section

/-- `K = GF(2^64)` (`F64`). -/
abbrev K : Type := BF64

/-- `E = K[y]/(y^3 + y + 1)` (`F192`). -/
abbrev E : Type := BF64.Ext3

/-- The element of `K` whose bits are `n`, reduced modulo `2^64`: the wire encoding of a word. -/
def K.ofBits (n : ℕ) : K := BF64.ofBitVec (BitVec.ofNat 64 n)

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

/-- Uniform sampling of `K` through its bits. -/
instance : SampleableType K := SampleableType.ofEquiv BF64.equivFin.symm

/-- Uniform sampling of `E` limb by limb. -/
instance : SampleableType E := SampleableType.ofEquiv (CompPoly.Extension.Ext.equivFn _).symm

end

end LeanDa

end

section

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
  seeded with the label's hash (`membership_challenges`); the end statements draw them by this
  duplex over the permutation (`membershipChallengesM`), and Wagner's games, a step of their
  proofs, model them as one random oracle on the root.
* **The deployed algorithms** (`commit.rs:55-145`, `verifier/src/da.rs:15-96`,
  `verifier/src/transcript.rs:32-95`). The crate's computations, transcribed computably on lists,
  for `lean_vm` to state the aggregation node's DA claim with: `commitCodewords`, the commitment
  level by level, which is `commitCells` of the matrix (`commitCodewords_eq_commitCells`,
  `LeanDa.Commitment`); the challenges' sponge (`Sponge`, `membershipChallenges`); the dual
  codeword by the additive NTT (`membershipVector`), which computes `dual`
  (`membershipVector_eq_dual`, `LeanDa.Dual`); and the vector's digest, the hash of its `128`
  columns' hashes (`vectorDigest`).

The row count `r` is a parameter. The crate takes `1 ≤ r ≤ 1024` (`row_count`, `lib.rs:41-46`);
the statements hold for every `r ≥ 1`. The deployed algorithms take the hash `H` and the sponge's
permutation `P` as parameters: the crate's are Keccak-256 (Ethereum's: rate `136` bytes, padding
`0x01 ‖ 0^* ‖ 0x80`, `verifier/src/hash.rs:79-97`) and the Keccak-f[1600] it is built on, which
`lean_vm` supplies for the aggregation node's DA claim. The end statements are in the
random-permutation model: `H` is Keccak-256 over a permutation `π` and `P` is `π` itself
(`keccakWith`, `permImpl`, the last sections), with `π` uniformly random for the binding
statements and arbitrary for completeness.

Part of `lean_da`, which instantiates Benedikt Wagner's framework for erasure code commitments
(`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

open Polynomial

namespace LeanDa

@[expose] public section

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

/-- Climb from `node` at index `idx` along the siblings `path`. -/
def walk : ℕ → Digest → List Digest → Digest
  | _, node, [] => node
  | idx, node, s :: rest =>
    walk (idx / 2) (if idx % 2 = 0 then H (pairBytes node s) else H (pairBytes s node)) rest

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

/-- **Verification of a cell opening**: a path of the column tree's height that climbs from the
cell's digest to a column root, which hashed after the row root gives the commitment. -/
def verifyCell (r : ℕ) (com : Digest) (p : Fin (r * 128)) (x : Cell) (τ : Opening) : Bool :=
  decide (τ.path.length = 7 + logPad r) &&
    decide (H (pairBytes τ.rowRoot (walk H (colIndex p) (cellDigest H x) τ.path)) = com)

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
statements; Wagner's games, a step of the proofs, model them as one random oracle on the root),
and the dual codeword as the crate computes it, by the additive NTT, which computes `dual`
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

/-! #### The sponge (`verifier/src/transcript.rs:32-95`)

A duplex sponge in overwrite mode over a permutation `P` of `25` lanes. The crate's is
Keccak-f[1600] (`keccak_f`, `verifier/src/hash.rs:50-69`), which `lean_vm` supplies; the
definitions hold for every `P`. A lane is a `u64`, read as the element of `K` with its bits, so
a scalar's limbs are lanes as they are. The rate is lanes `0 … 15`, the capacity lanes
`16 … 24`. -/

/-- The sponge's lanes (`[u64; STATE_LANES]`). -/
abbrev Lanes := Vector K 25

variable (P : Lanes → Lanes)

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

/-- A sponge seeded with one permutation of the zero state with the IV's words in lanes
`0 … 3` and the public input's in lanes `4 … 7` (`Sponge::new`). -/
def Sponge.new (iv publicInput : Digest) : Sponge :=
  ⟨P (Vector.ofFn fun i : Fin 25 ↦
      if (i : ℕ) < 4 then word iv i else if (i : ℕ) < 8 then word publicInput (i - 4) else 0), []⟩

/-- A sponge with no public input of its own, seeded from the hash of `label`
(`Sponge::from_label`). -/
def Sponge.fromLabel (label : List UInt8) : Sponge := Sponge.new P (H label) (Vector.replicate 32 0)

/-- The rate lanes the waiting scalars fill: scalar `i`'s three limbs and tag in lanes
`4 i … 4 i + 3`. -/
def rateWords (pending : List (E × K)) : List K :=
  pending.flatMap fun x ↦ [limb x.1 0, limb x.1 1, limb x.1 2, x.2]

/-- Permute, the waiting scalars written over the rate, the rest of the rate zero and the
capacity kept (`duplex`). -/
def Sponge.duplex (s : Sponge) : Sponge :=
  ⟨P (Vector.ofFn fun i : Fin 25 ↦
      if (i : ℕ) < rateLanes then (rateWords s.pending).getD i 0 else s.state[i]), []⟩

/-- Absorb a scalar with a tag, permuting first when `rateScalars` wait (`absorb`). -/
def Sponge.absorb (s : Sponge) (x : E) (tag : K) : Sponge :=
  let s := if s.pending.length = rateScalars then Sponge.duplex P s else s
  ⟨s.state, s.pending ++ [(x, tag)]⟩

/-- Observe a scalar (`observe`). -/
def Sponge.observe (s : Sponge) (x : E) : Sponge := Sponge.absorb P s x dsObserve

/-- Draw a challenge: a permutation of its own, whose lanes `0 … 2` are its limbs (`sample`). -/
def Sponge.sample (s : Sponge) : E × Sponge :=
  let s := Sponge.duplex P s
  (ofLimbs s.state[0] s.state[1] s.state[2], s)

/-- `n` challenges, in order. -/
def Sponge.samples : ℕ → Sponge → List E
  | 0, _ => []
  | n + 1, s => (Sponge.sample P s).1 :: Sponge.samples n (Sponge.sample P s).2

/-! #### The challenges and the vector -/

/-- **The challenges `z_0 … z_13` of a root** (`membership_challenges`, `verifier/src/da.rs:15-22`):
a sponge from the label, the root's words observed as two scalars `(w_0, w_1, 0)` and
`(w_2, w_3, 0)`, then `14` samples. -/
def membershipChallenges (root : Digest) : List E :=
  let s := Sponge.fromLabel H P label
  let s := Sponge.observe P s (ofLimbs (word root 0) (word root 1) 0)
  let s := Sponge.observe P s (ofLimbs (word root 2) (word root 3) 0)
  Sponge.samples P logK s

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

end

end LeanDa

end

/-! ## Wagner's framework: erasure codes -/

@[expose] public section

namespace PqDas

/-- An erasure code with message alphabet `Γ`, code alphabet `Λ`, message
length `k`, and code length `n`, given by its encoding function. -/
structure ErasureCode (Γ Λ : Type) (k n : ℕ) where
  /-- The encoding function of the code. -/
  encode : (Fin k → Γ) → (Fin n → Λ)

namespace ErasureCode

variable {Γ Λ : Type} {k n : ℕ}

/-- The code itself: the set of codewords, i.e. the image of `encode`. -/
def code (C : ErasureCode Γ Λ k n) : Set (Fin n → Λ) := Set.range C.encode

/-- Codeword membership is decidable for finite alphabets. This is used to
state the winning conditions of security games as `Bool`s. -/
instance decidableMemCode (C : ErasureCode Γ Λ k n) [Fintype Γ] [DecidableEq Λ] :
    DecidablePred (· ∈ C.code) := fun c =>
  decidable_of_iff (∃ m, C.encode m = c) Set.mem_range

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

end

/-! ## Wagner's framework: vector commitments -/

@[expose] public section

open OracleComp ENNReal

namespace PqDas

/-- A vector commitment scheme for vectors in `Fin n → Λ`, with commitment key
type `Ck`, commitment type `Com`, and opening type `Opn` (Foundations
Definition 15, derandomized: `commit` and `openAt` are deterministic, and the
opening state is the committed vector itself, which is WLOG since `commit` is
deterministic). -/
structure VectorCommitment (Λ : Type) (n : ℕ) (Ck Com Opn : Type) where
  /-- Sample a commitment key. -/
  setup : ProbComp Ck
  /-- Commit to a vector (deterministic). -/
  commit : Ck → (Fin n → Λ) → Com
  /-- Open the commitment to position `i` (deterministic; takes the committed
  vector in place of an opening state). -/
  openAt : Ck → (Fin n → Λ) → Fin n → Opn
  /-- Verify an opening `τ` of symbol `x` at position `i` (deterministic). -/
  verify : Ck → Com → Fin n → Λ → Opn → Bool

namespace VectorCommitment

variable {Λ : Type} {n : ℕ} {Ck Com Opn : Type}

/-! #### Position-binding (Foundations Definition 16) -/

/-- A position-binding adversary: outputs a commitment, a position, and two
symbol/opening pairs. -/
def PosBindingAdv (Λ : Type) (n : ℕ) (Ck Com Opn : Type) :=
  Ck → ProbComp (Com × Fin n × Λ × Opn × Λ × Opn)

/-! #### Weak position-binding -/

/-- A weak position-binding adversary: outputs a full vector, a position, and a
symbol/opening pair. -/
def WeakPosBindingAdv (Λ : Type) (n : ℕ) (Ck Opn : Type) :=
  Ck → ProbComp ((Fin n → Λ) × Fin n × Λ × Opn)

/-- Reduction (an explicit PPT algorithm): a weak position-binding adversary
becomes a position-binding adversary by committing to `v` honestly and opening
position `i` honestly as the second symbol/opening pair. -/
def WeakPosBindingAdv.toPosBindingAdv (vc : VectorCommitment Λ n Ck Com Opn)
    (A : WeakPosBindingAdv Λ n Ck Opn) : PosBindingAdv Λ n Ck Com Opn := fun ck => do
  let (v, i, x, τ) ← A ck
  return (vc.commit ck v, i, x, τ, v i, vc.openAt ck v i)

/-! #### Collision resistance of `commit` -/

/-- A collision adversary: outputs two vectors, trying to make them collide
under the (deterministic) `commit`. -/
def CollisionAdv (Λ : Type) (n : ℕ) (Ck : Type) :=
  Ck → ProbComp ((Fin n → Λ) × (Fin n → Λ))

/-- Reduction (an explicit PPT algorithm): a collision adversary becomes a
position-binding adversary by locating a position where the two vectors differ
(`Fin.find`) and opening both honestly at that position. If the vectors do not
differ the adversary has lost anyway and we output a dummy tuple. -/
def CollisionAdv.toPosBindingAdv [NeZero n] [DecidableEq Λ]
    (vc : VectorCommitment Λ n Ck Com Opn) (A : CollisionAdv Λ n Ck) :
    PosBindingAdv Λ n Ck Com Opn := fun ck => do
  let (v, v') ← A ck
  if h : v = v' then
    return (vc.commit ck v, 0, v 0, vc.openAt ck v 0, v 0, vc.openAt ck v 0)
  else
    let i := Fin.find (fun j => v j ≠ v' j) (Function.ne_iff.mp h)
    return (vc.commit ck v, i, v i, vc.openAt ck v i, v' i, vc.openAt ck v' i)

end VectorCommitment

end PqDas

end

/-! ## Wagner's framework: code checkers -/

@[expose] public section

open OracleComp ENNReal

namespace PqDas

/-- A code checker for vectors in `Fin n → Λ` with check-randomness domain `L`:
a deterministic test `check`, intended to accept exactly-the-codewords with
high probability over `L`. -/
structure CodeChecker (Λ : Type) (n : ℕ) (L : Type) where
  /-- The (deterministic) membership check. -/
  check : L → (Fin n → Λ) → Bool

end PqDas

end

/-! ## Wagner's framework: arguments of knowledge -/

@[expose] public section

open OracleComp ENNReal

namespace PqDas

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

/-- A knowledge-soundness adversary: outputs a statement and a proof. -/
def KnowledgeSoundnessAdv (Stmt Crs Proof : Type) := Crs → ProbComp (Stmt × Proof)

/-- Knowledge-soundness experiment (Foundations Definition 18): the adversary
wins if its proof verifies but the extracted witness does not satisfy the
relation. -/
def knowledgeSoundnessExp (ps : Nark Stmt Wit Crs Proof rel)
    (ext : Extractor Stmt Wit Crs Proof)
    (A : KnowledgeSoundnessAdv Stmt Crs Proof) : ProbComp Bool := do
  let crs ← ps.setup
  let (stmt, π) ← A crs
  return (ps.verify crs stmt π && !rel stmt (ext crs stmt π))

end Nark

end PqDas

end

/-! ## Wagner's framework: the code-binding adversary of an erasure code commitment -/

@[expose] public section

open OracleComp ENNReal MeasureTheory

namespace PqDas

namespace ErasureCodeCommitment

/-! #### Code-binding (Foundations Definition 10) -/

/-- A code-binding adversary against an erasure code commitment whose algorithms run in the
monad `m`: outputs a commitment and a list of position/symbol/opening triples. Wagner's
reductions, which the code-binding bound names, take one. -/
def CodeBindingAdv (m : Type → Type) (Λ : Type) (n : ℕ) (Ck Com Opn : Type) :=
  Ck → m (Com × List (Fin n × Λ × Opn))

end ErasureCodeCommitment

end PqDas

end

/-! ## Wagner's framework: the random-oracle simulation of his reductions -/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PqDas

section runtime

variable (ComVC L : Type) [DecidableEq ComVC] [SampleableType L]

/-- The query implementation underlying `simulateRom`: uniform-sampling queries are
forwarded, random-oracle queries are answered by lazy caching. -/
noncomputable def romImpl :
    QueryImpl (unifSpec + (ComVC →ₒ L)) (StateT ((ComVC →ₒ L).QueryCache) ProbComp) :=
  unifFwdImpl (ComVC →ₒ L) + (randomOracle :
    QueryImpl (ComVC →ₒ L) (StateT ((ComVC →ₒ L).QueryCache) ProbComp))

variable {ComVC L}

/-- Run a computation in the random-oracle world as a plain probabilistic
computation, lazily simulating the oracle starting from the given cache.
Reductions use this to simulate the random-oracle world for an adversary. -/
noncomputable def simulateRomWithCache (cache : (ComVC →ₒ L).QueryCache) {α : Type}
    (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) : ProbComp α :=
  (simulateQ (romImpl ComVC L) oa).run' cache

/-- Run a computation in the random-oracle world as a plain probabilistic
computation, with a fresh random oracle. -/
noncomputable def simulateRom {α : Type}
    (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) : ProbComp α :=
  simulateRomWithCache ∅ oa

variable {α β : Type}

end runtime

end PqDas

end

/-! ## Wagner's framework: the relation of the scheme's argument -/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs Proof : Type}

/-- The relation proven by the argument of knowledge. The statement is a
commitment key, a commitment, and check randomness; the witness is an alleged
codeword `c`. The relation holds if `c` commits to the given commitment and
passes the code check. Note that code membership of `c` is *not* part of the
relation; this is the whole point of the construction, and the reason the
code-binding proof is nontrivial. -/
def schemeRel [DecidableEq ComVC] (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) : CkVC × ComVC × L → (Fin n → Λ) → Bool := fun stmt c =>
  decide (vc.commit stmt.1 c = stmt.2.1) && chk.check stmt.2.2 c

end PqDas

end

/-! ## Wagner's reductions: committed soundness -/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

/-- An adversary against the non-interactive committed soundness game: given a
vector-commitment key and access to a random oracle (and uniform sampling), it
outputs a commitment and a vector. -/
def NiCsAdv (Λ : Type) (n : ℕ) (CkVC ComVC L : Type) :=
  CkVC → OracleComp (unifSpec + (ComVC →ₒ L)) (ComVC × (Fin n → Λ))

end PqDas

end

/-! ## Wagner's reductions: the fork -/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PqDas

namespace CommittedSoundness

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

/-- Wrapped oracle spec: uniform sampling plus a single counted challenge
oracle exposing the random-oracle entropy. -/
abbrev wrappedSpec (L : Type) : OracleSpec (ℕ ⊕ Unit) := unifSpec + (Unit →ₒ L)

/-- Internal simulator state: the cached random-oracle answers paired with the
chronological list of cache-miss inputs. -/
abbrev SimState (ComVC L : Type) : Type := (ComVC →ₒ L).QueryCache × List ComVC

/-- Forwards a uniform-spec query to the wrapped spec's `Sum.inl` summand
without touching the simulator state. -/
def unifForward (ComVC L : Type) :
    QueryImpl unifSpec (StateT (SimState ComVC L) (OracleComp (wrappedSpec L))) :=
  fun i => (wrappedSpec L).query (Sum.inl i)

/-- Caching random-oracle implementation: on a cache hit the recorded answer
is returned; on a cache miss a fresh `Sum.inr ()` query is issued, the answer
is cached, and the miss input is appended to the internal log. -/
def roImpl (ComVC L : Type) [DecidableEq ComVC] :
    QueryImpl (ComVC →ₒ L) (StateT (SimState ComVC L) (OracleComp (wrappedSpec L))) :=
  fun com => do
    let (cache, log) ← get
    match cache com with
    | some v => pure v
    | none =>
        let v ← (wrappedSpec L).query (Sum.inr ())
        set (cache.cacheQuery com v, log ++ [com])
        pure v

/-- Trace of one run of the wrapped committed soundness game. -/
structure Trace (Λ : Type) (n : ℕ) (ComVC L : Type) where
  /-- The commitment output by the adversary. -/
  com : ComVC
  /-- The vector output by the adversary. -/
  vec : Fin n → Λ
  /-- The challenge for `com` (always cached, thanks to the wrapped
  computation's final query). -/
  chal : L
  /-- The final random-oracle cache. -/
  roCache : (ComVC →ₒ L).QueryCache
  /-- The chronological list of cache-miss inputs; the forking lemma rewinds
  at a position of this list. -/
  queryLog : List ComVC
  /-- Whether the run wins the committed soundness game. -/
  win : Bool

/-- The wrapped adversary: run the committed soundness adversary, then query
the oracle once more on the commitment it output, so its challenge is always
cached (and, on a miss, logged). -/
def wrappedAdv (A : NiCsAdv Λ n CkVC ComVC L) (ckVC : CkVC) :
    OracleComp (unifSpec + (ComVC →ₒ L)) (ComVC × (Fin n → Λ) × L) := do
  let (com, c) ← A ckVC
  let l ← HasQuery.query (spec := (ComVC →ₒ L)) com
  return (com, c, l)

/-- The winning predicate of the committed soundness game, as a function of
the wrapped adversary's output. -/
def winOn [Fintype Γ] [DecidableEq Λ] [DecidableEq ComVC]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (ckVC : CkVC) (out : ComVC × (Fin n → Λ) × L) : Bool :=
  decide (out.2.1 ∉ C.code) && chk.check out.2.2 out.2.1 &&
    decide (vc.commit ckVC out.2.1 = out.1)

/-- Run the wrapped adversary through the caching simulator against the
counted challenge oracle and record the run. -/
def runTrace [Fintype Γ] [DecidableEq Λ] [DecidableEq ComVC]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (ckVC : CkVC) :
    OracleComp (wrappedSpec L) (Trace Λ n ComVC L) := do
  let (out, st) ← StateT.run
    (simulateQ (unifForward ComVC L + roImpl ComVC L) (wrappedAdv A ckVC)) (∅, [])
  pure { com := out.1, vec := out.2.1, chal := out.2.2, roCache := st.1, queryLog := st.2,
         win := winOn C vc chk ckVC out }

/-- Rewinding point extracted from a trace: the position of the first cache
miss on the output commitment, provided the run wins and the position is
within the query budget. -/
def forkPoint [DecidableEq ComVC] (Q : ℕ) (trace : Trace Λ n ComVC L) :
    Option (Fin (Q + 1)) :=
  if trace.win then
    if trace.com ∈ trace.queryLog then
      let idx := trace.queryLog.findIdx (· == trace.com)
      if hidx : idx < Q + 1 then some ⟨idx, hidx⟩ else none
    else none
  else none

end CommittedSoundness

end PqDas

end

/-! ## Wagner's reductions: the collision from the fork -/

@[expose] public section

open OracleComp OracleSpec ENNReal

open scoped PFunctor

namespace PqDas

namespace CommittedSoundness

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

section forking

variable [DecidableEq ComVC] [SampleableType L] [Fintype L] [Inhabited L]
  [Fintype Γ] [DecidableEq Λ] [DecidableEq L] [Inhabited Λ]

variable (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
  (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (Q : ℕ)

/-- Wrapped-spec fork-and-extract computation: replay-fork the wrapped
committed soundness game at the fork point and output the two recorded
vectors. If the fork fails, output an (equal, hence losing) dummy pair. -/
noncomputable def forkVecPair (ckVC : CkVC) :
    OracleComp (wrappedSpec L) ((Fin n → Λ) × (Fin n → Λ)) :=
  contextFork (runTrace C vc chk A ckVC)
    (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
    (Sum.inr ()) (forkPoint Q) >>= fun
      | some (x₁, x₂) => pure (x₁.vec, x₂.vec)
      | none => pure (fun _ => default, fun _ => default)

/-- The collision reduction (an explicit algorithm): run the wrapped
fork-and-extract computation, interpreting its uniform queries and its counted
challenge oracle by plain uniform sampling. -/
noncomputable def forkCollisionReduction :
    VectorCommitment.CollisionAdv Λ n CkVC := fun ckVC =>
  simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      uniformSampleImpl (spec := ((Unit →ₒ L) : OracleSpec Unit)))
    (forkVecPair C vc chk A Q ckVC)

end forking

end CommittedSoundness

end PqDas

end

/-! ## Wagner's reductions: knowledge soundness and weak position binding -/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs Proof : Type}

/-- The adversary's continuation shared by the reductions below: run the
code-binding adversary, then query the oracle once more on the commitment it
output (a cache hit if the adversary already queried it), obtaining the check
randomness that the scheme's verification would use. -/
def runWithChallenge
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn)
    (ck : CkVC × Crs) :
    OracleComp (unifSpec + (ComVC →ₒ L))
      (((ComVC × Proof) × List (Fin n × Λ × Opn)) × L) := do
  let out ← A ck
  let l ← HasQuery.query (spec := (ComVC →ₒ L)) out.1.1
  return (out, l)

/-- Reduction to knowledge soundness (an explicit PPT algorithm): sample the
vector-commitment key, simulate the random-oracle world for the code-binding
adversary, and output the statement `(ckVC, comVC, l)` together with the
adversary's proof. -/
noncomputable def ksReduction [DecidableEq ComVC] [SampleableType L]
    (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    Nark.KnowledgeSoundnessAdv (CkVC × ComVC × L) Crs Proof := fun crs => do
  let ckVC ← vc.setup
  let ((com, _), l) ← simulateRom (runWithChallenge A (ckVC, crs))
  return ((ckVC, com.1, l), com.2)

/-- Reduction to the non-interactive committed soundness game (an explicit PPT
algorithm): sample the crs, relay the code-binding adversary's oracle access,
and output the vector-commitment part of its commitment together with the
extracted witness. -/
noncomputable def csReduction [DecidableEq ComVC] [SampleableType L]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    NiCsAdv Λ n CkVC ComVC L := fun ckVC => do
  let crs ← liftM ps.setup
  let (com, _) ← A (ckVC, crs)
  let l ← HasQuery.query (spec := (ComVC →ₒ L)) com.1
  return (com.1, ext crs (ckVC, com.1, l) com.2)

/-- Reduction to weak position-binding (an explicit PPT algorithm): sample the
crs, simulate the random-oracle world for the code-binding adversary, extract
the witness `c` from its proof, and search its openings for one whose symbol
disagrees with `c`. If none disagrees the reduction has lost anyway and
outputs a dummy tuple. -/
noncomputable def wpbReduction [NeZero n] [DecidableEq Λ] [DecidableEq ComVC]
    [SampleableType L] [Inhabited Opn]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    VectorCommitment.WeakPosBindingAdv Λ n CkVC Opn := fun ckVC => do
  let crs ← ps.setup
  let ((com, openings), l) ← simulateRom (runWithChallenge A (ckVC, crs))
  let c := ext crs (ckVC, com.1, l) com.2
  match openings.find? (fun p => decide (p.2.1 ≠ c p.1)) with
  | some p => return (c, p.1, p.2.1, p.2.2)
  | none => return (c, 0, c 0, default)

end PqDas

end

/-! ## LeanDA's Merkle collisions -/

@[expose] public section

namespace LeanDa

variable (H : List UInt8 → Digest)

/-- The hash inputs from a cell's bytes `a` at index `idx` up to the root, the last one
`rowRoot ‖ colRoot`. -/
def hashInputs : ℕ → List UInt8 → List Digest → Digest → List (List UInt8)
  | _, a, [], rr => [a, pairBytes rr (H a)]
  | idx, a, s :: rest, rr =>
    a :: hashInputs (idx / 2) (if idx % 2 = 0 then pairBytes (H a) s else pairBytes s (H a)) rest rr

/-- The first pair of inputs, level by level, that differ and hash alike. -/
def findCollision : List (List UInt8) → List (List UInt8) → List UInt8 × List UInt8
  | a :: as, b :: bs => if a ≠ b ∧ H a = H b then (a, b) else findCollision as bs
  | _, _ => ([], [])

/-- The collision two openings of one position give. -/
def openingsCollision (r : ℕ) (p : Fin (r * 128)) (x : Cell) (τ : Opening) (x' : Cell)
    (τ' : Opening) : List UInt8 × List UInt8 :=
  findCollision H (hashInputs H (colIndex p) (cellBytes x) τ.path τ.rowRoot)
    (hashInputs H (colIndex p) (cellBytes x') τ'.path τ'.rowRoot)

end LeanDa

end

/-! ## LeanDA in Wagner's framework -/

@[expose] public section

open PqDas OracleComp OracleSpec ENNReal

namespace LeanDa

/-- **LeanDA's erasure code**: `r` payloads, encoded row by row and cut into cells. -/
noncomputable def code (r : ℕ) : ErasureCode Payload Cell r (r * 128) := ⟨encodeMatrix⟩

/-- The challenges of the membership test. -/
abbrev Challenges := Fin 14 → E

/-- **LeanDA's code checker**: the membership test on challenges `z ∈ E^14`. -/
noncomputable def checker (r : ℕ) : CodeChecker Cell (r * 128) Challenges := ⟨membershipCheck⟩

/-- **LeanDA's vector commitment** with hash `H`: the root of the two Merkle trees, cells opened
by their column-tree paths. It needs no key. -/
def merkleVC (r : ℕ) (H : List UInt8 → Digest) :
    VectorCommitment Cell (r * 128) Unit Digest Opening where
  setup := pure ()
  commit _ c := commitCells H c
  openAt _ c p := openCell H c p
  verify _ com p x τ := verifyCell H r com p x τ

/-- The collision experiment for a hash function: a finder wins if it outputs two different
byte strings with the same hash. -/
def hashCollisionExp (H : List UInt8 → Digest) (B : ProbComp (List UInt8 × List UInt8)) :
    ProbComp Bool := do
  let (a, b) ← B
  return (decide (a ≠ b) && decide (H a = H b))

/-- **The reduction from position binding to a collision**: run the adversary and climb its two
openings (`openingsCollision`). -/
def merkleCollider (r : ℕ) (H : List UInt8 → Digest)
    (A : VectorCommitment.PosBindingAdv Cell (r * 128) Unit Digest Opening) :
    ProbComp (List UInt8 × List UInt8) := do
  let (_, p, x, τ, x', τ') ← A ()
  return openingsCollision H r p x τ x' τ'

/-- The relation the argument proves: the cells commit to the root and pass the membership test
on the challenges. -/
noncomputable abbrev Relation (r : ℕ) (H : List UInt8 → Digest) := schemeRel (merkleVC r H) (checker r)

/-- An argument of knowledge for `Relation r H`. -/
abbrev Argument (r : ℕ) (H : List UInt8 → Digest) (Crs Proof : Type) :=
  Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof (Relation r H)

end LeanDa

end

/-! ## LeanDA's verifier over a permutation -/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common

namespace LeanDa

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

/-- Byte `p` of lanes of eight bytes each is byte `p % 8` of lane `p / 8`. -/
theorem getD_flatMap_laneBytes (l : List K) (p : ℕ) :
    (l.flatMap fun a ↦ (laneBytes a).toList).getD p 0 =
      if h : p / 8 < l.length then (laneBytes l[p / 8])[p % 8] else 0 := by
  induction l generalizing p with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons]
    by_cases hp : p < 8
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hp)]
      have h0 : p / 8 = 0 := by omega
      simp [h0, Nat.mod_eq_of_lt hp, Vector.getElem?_eq_getElem hp]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega), ← List.getD_eq_getElem?_getD]
      simp only [Vector.length_toList]
      rw [ih (p - 8)]
      have h1 : (p - 8) / 8 = p / 8 - 1 := by omega
      have h2 : (p - 8) % 8 = p % 8 := by omega
      simp only [h1, h2, List.length_cons]
      by_cases hl : p / 8 - 1 < l.length
      · have h3 : p / 8 < l.length + 1 := by omega
        simp only [hl, h3, ↓reduceDIte]
        rw [List.getElem_cons (by omega)]
        simp [show p / 8 ≠ 0 by omega]
      · have h3 : ¬ p / 8 < l.length + 1 := by omega
        simp [hl, h3]

section Monadic

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (P : Lanes → m Lanes)

/-- The lanes a duplexing permutes: the waiting scalars over the rate, the rest of the rate zero,
the capacity kept (`Sponge.duplex`). -/
def duplexInput (s : Sponge) : Lanes :=
  Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < rateLanes then (rateWords s.pending).getD i 0 else s.state[i]

/-- The lanes of a fresh sponge (`Sponge.new`). -/
def newInput (iv publicInput : Digest) : Lanes :=
  Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < 4 then word iv i else if (i : ℕ) < 8 then word publicInput (i - 4) else 0

/-- `Sponge.new` over an oracle. -/
def Sponge.newM (iv publicInput : Digest) : m Sponge := do
  let state ← P (newInput iv publicInput)
  pure ⟨state, []⟩

/-- `Sponge.fromLabel` over oracles. -/
def Sponge.fromLabelM (label : List UInt8) : m Sponge := do
  let iv ← H label
  Sponge.newM P iv (Vector.replicate 32 0)

/-- `Sponge.duplex` over an oracle. -/
def Sponge.duplexM (s : Sponge) : m Sponge := do
  let state ← P (duplexInput s)
  pure ⟨state, []⟩

/-- `Sponge.absorb` over an oracle. -/
def Sponge.absorbM (s : Sponge) (x : E) (tag : K) : m Sponge :=
  (if s.pending.length = rateScalars then Sponge.duplexM P s else pure s) >>= fun s ↦
    pure ⟨s.state, s.pending ++ [(x, tag)]⟩

/-- `Sponge.observe` over an oracle. -/
def Sponge.observeM (s : Sponge) (x : E) : m Sponge := Sponge.absorbM P s x dsObserve

/-- `Sponge.sample` over an oracle. -/
def Sponge.sampleM (s : Sponge) : m (E × Sponge) := do
  let s ← Sponge.duplexM P s
  pure (ofLimbs s.state[0] s.state[1] s.state[2], s)

/-- `Sponge.samples` over an oracle. -/
def Sponge.samplesM : ℕ → Sponge → m (List E)
  | 0, _ => pure []
  | n + 1, s => do
    let (z, s) ← Sponge.sampleM P s
    let zs ← Sponge.samplesM n s
    pure (z :: zs)

/-- **The challenges of a root** (`membershipChallenges`) over oracles. -/
def membershipChallengesM (root : Digest) : m (List E) := do
  let s ← Sponge.fromLabelM H P label
  let s ← Sponge.observeM P s (ofLimbs (word root 0) (word root 1) 0)
  let s ← Sponge.observeM P s (ofLimbs (word root 2) (word root 3) 0)
  Sponge.samplesM P logK s

/-- `walk` over an oracle. -/
def walkM : ℕ → Digest → List Digest → m Digest
  | _, node, [] => pure node
  | idx, node, s :: rest => do
    let d ← H (if idx % 2 = 0 then pairBytes node s else pairBytes s node)
    walkM (idx / 2) d rest

/-- **Verification of a cell opening** (`verifyCell`) over an oracle: every hash of the climb is
computed, then the checks. -/
def verifyCellM (r : ℕ) (com : Digest) (p : Fin (r * 128)) (x : Cell) (τ : Opening) : m Bool := do
  let d ← H (cellBytes x)
  let w ← walkM H (colIndex p) d τ.path
  let root ← H (pairBytes τ.rowRoot w)
  pure (decide (τ.path.length = 7 + logPad r) && decide (root = com))

end Monadic

/-- The two-oracle random-oracle model's oracles: coins, `H` and the direct calls `F`. -/
abbrev Rom2 := unifSpec + hfSpec (List UInt8) KDigest KState

/-- The hash `H` in the two-oracle model. -/
abbrev hR (a : List UInt8) : OracleComp Rom2 Digest :=
  hQuery (Msg := List UInt8) (Dg := KDigest) (E := KRest) (C := KCap) a

/-- The direct calls `F`, on lanes. -/
abbrev pR (L : Lanes) : OracleComp Rom2 Lanes :=
  lanePerm (fun x ↦ fQuery (Msg := List UInt8) (Dg := KDigest) x) L

end LeanDa

end

/-! ## LeanDA's challenge duplex -/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.Duplex
open scoped ENNReal

namespace LeanDa

/-- Byte `p` of a state. -/
def byteAt (y : KState) (p : ℕ) : UInt8 := y.toBytes.getD p 0

theorem toBytes_length (y : KState) : y.toBytes.length = 200 := by
  simp only [KState.toBytes, List.length_append, Vector.length_toList]

theorem getD_toBytes_lt32 (y : KState) (p : ℕ) (hp : p < 32) :
    y.toBytes.getD p 0 = y.1.1[p] := by
  rw [List.getD_eq_getElem?_getD, KState.toBytes, List.append_assoc,
    List.getElem?_append_left (by rw [Vector.length_toList]; exact hp),
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hp, Option.getD_some]

theorem getD_toBytes_lt136 (y : KState) (p : ℕ) (hp : 32 ≤ p) (hp' : p < 136) :
    y.toBytes.getD p 0 = y.1.2[p - 32]'(by omega) := by
  rw [List.getD_eq_getElem?_getD, KState.toBytes, List.append_assoc,
    List.getElem?_append_right (by rw [Vector.length_toList]; exact hp), Vector.length_toList,
    List.getElem?_append_left (by rw [Vector.length_toList]; omega),
    Vector.getElem?_toList, Vector.getElem?_eq_getElem (by omega), Option.getD_some]

theorem getD_toBytes_lt200 (y : KState) (p : ℕ) (hp : 136 ≤ p) (hp' : p < 200) :
    y.toBytes.getD p 0 = y.2[p - 136]'(by omega) := by
  have hlen : (y.1.1.toList ++ y.1.2.toList).length = 136 := by
    rw [List.length_append, Vector.length_toList, Vector.length_toList]
  rw [List.getD_eq_getElem?_getD, KState.toBytes, List.getElem?_append_right (by rw [hlen]; exact hp),
    hlen, Vector.getElem?_toList, Vector.getElem?_eq_getElem (by omega), Option.getD_some]

theorem ofBytes_toBytes (y : KState) : KState.ofBytes y.toBytes = y := by
  obtain ⟨⟨a, b⟩, c⟩ := y
  refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> apply Vector.ext <;> intro i hi <;>
    simp only [KState.ofBytes, Vector.getElem_ofFn]
  · exact getD_toBytes_lt32 ((a, b), c) i hi
  · rw [getD_toBytes_lt136 ((a, b), c) (32 + i) (by omega) (by omega)]
    simp only [Nat.add_sub_cancel_left]
  · rw [getD_toBytes_lt200 ((a, b), c) (136 + i) (by omega) (by omega)]
    simp only [Nat.add_sub_cancel_left]

theorem toBytes_ofBytes {l : List UInt8} (hl : l.length = 200) : (KState.ofBytes l).toBytes = l := by
  apply List.ext_getElem (by rw [toBytes_length, hl])
  intro p h1 h2
  rw [toBytes_length] at h1
  rw [← List.getD_eq_getElem _ 0]
  by_cases hp : p < 32
  · rw [getD_toBytes_lt32 _ p hp]
    simp only [KState.ofBytes, Vector.getElem_ofFn]
    rw [List.getD_eq_getElem _ 0 h2]
  · by_cases hp' : p < 136
    · rw [getD_toBytes_lt136 _ p (by omega) hp']
      simp only [KState.ofBytes, Vector.getElem_ofFn]
      rw [show 32 + (p - 32) = p by omega, List.getD_eq_getElem _ 0 h2]
    · rw [getD_toBytes_lt200 _ p (by omega) (by omega)]
      simp only [KState.ofBytes, Vector.getElem_ofFn]
      rw [show 136 + (p - 136) = p by omega, List.getD_eq_getElem _ 0 h2]

/-- **A state is its 200 bytes.** -/
def bytesEquiv : KState ≃ (Fin 200 → UInt8) where
  toFun y i := byteAt y i
  invFun f := KState.ofBytes (List.ofFn f)
  left_inv y := by
    have : List.ofFn (fun i : Fin 200 ↦ byteAt y i) = y.toBytes :=
      List.ext_getElem (by rw [List.length_ofFn, toBytes_length]) fun p h1 h2 ↦ by
        rw [List.getElem_ofFn]; exact List.getD_eq_getElem _ 0 h2
    show KState.ofBytes (List.ofFn _) = y
    rw [this, ofBytes_toBytes]
  right_inv f := by
    funext i
    show byteAt (KState.ofBytes (List.ofFn f)) i = f i
    rw [byteAt, toBytes_ofBytes (List.length_ofFn), List.getD_eq_getElem _ 0
      (by rw [List.length_ofFn]; exact i.2), List.getElem_ofFn]

theorem length_lanesBytes (L : Lanes) :
    (L.toList.flatMap fun a ↦ (laneBytes a).toList).length = 200 := by
  rw [List.length_flatMap]
  simp only [Vector.length_toList]
  rw [List.map_const', List.sum_replicate, Vector.length_toList]
  rfl

theorem byteAt_lanesToState (L : Lanes) (p : ℕ) (hp : p < 200) :
    byteAt (lanesToState L) p = (laneBytes L[p / 8])[p % 8] := by
  rw [byteAt, lanesToState, toBytes_ofBytes (length_lanesBytes L), getD_flatMap_laneBytes]
  simp only [Vector.length_toList, show p / 8 < 25 by omega, ↓reduceDIte, Vector.getElem_toList]

theorem byteAt_stateToLanes (y : KState) (p : ℕ) (hp : p < 200) :
    (laneBytes (stateToLanes y)[p / 8])[p % 8] = byteAt y p := by
  simp only [stateToLanes, Vector.getElem_ofFn, Equiv.apply_symm_apply, byteAt]
  congr 1
  omega

theorem lanesToState_injective : Function.Injective lanesToState := by
  intro L L' h
  apply Vector.ext
  intro i hi
  apply laneBytes.injective
  apply Vector.ext
  intro j hj
  have h1 := byteAt_lanesToState L (8 * i + j) (by omega)
  have h2 := byteAt_lanesToState L' (8 * i + j) (by omega)
  have e1 : (8 * i + j) / 8 = i := by omega
  have e2 : (8 * i + j) % 8 = j := by omega
  rw [h] at h1
  have h3 := h1.symm.trans h2
  have h4 : ∀ (M : Lanes) (a b : ℕ) (ha : a = i) (hb : b = j) (h1 : a < 25) (h2 : b < 8),
      (laneBytes M[a])[b] = (laneBytes M[i])[j] := by
    intro M a b ha hb _ _; subst ha hb; rfl
  rw [h4 L _ _ e1 e2, h4 L' _ _ e1 e2] at h3
  exact h3

/-- Bytes `0 … m-1` and `m … m+k-1`. -/
def splitEquiv (m k : ℕ) : (Fin (m + k) → UInt8) ≃ (Fin m → UInt8) × (Fin k → UInt8) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem splitEquiv_snd {m k : ℕ} (f : Fin (m + k) → UInt8) (j : Fin k) :
    (splitEquiv m k f).2 j = f (Fin.natAdd m j) := by
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

/-- **The challenge of 24 bytes**: three lanes, the limbs of an element of `E`. -/
def limbsEquiv : (Fin 24 → UInt8) ≃ E :=
  (Equiv.arrowCongr (finProdFinEquiv (m := 3) (n := 8)).symm (Equiv.refl UInt8)).trans <|
    (Equiv.curry _ _ _).trans <|
      (Equiv.arrowCongr (Equiv.refl _)
        ((arrayVectorEquivFin UInt8 8).symm.trans laneBytes.symm)).trans
        (CompPoly.Extension.Ext.equivFn BF64.ext3Params).symm

/-- The rest of an answer after its challenge: bytes `24 … 127`, and the capacity, bytes
`128 … 199`. -/
abbrev DaW := (Fin 104 → UInt8) × (Fin 72 → UInt8)

/-- The capacity: bytes `128 … 199`, lanes `16 … 24`. -/
abbrev DaCp := Fin 72 → UInt8

/-- **An answer from its challenge and its rest.** -/
def daBuild : E × DaW ≃ KState :=
  (Equiv.prodCongr limbsEquiv.symm (splitEquiv 104 72).symm).trans
    ((splitEquiv 24 176).symm.trans bytesEquiv.symm)

theorem daBuild_symm_cap (y : KState) (j : Fin 72) :
    (daBuild.symm y).2.2 j = byteAt y (128 + j) := by
  simp only [daBuild, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_snd]
  rw [splitEquiv_snd, splitEquiv_snd]
  show byteAt y (24 + (104 + (j : ℕ))) = _
  congr 1
  omega

/-- The scalars the root's words make (`membership_challenges`). -/
def rootScalars (root : Digest) : List (E × K) :=
  [(ofLimbs (word root 0) (word root 1) 0, dsObserve), (ofLimbs (word root 2) (word root 3) 0, dsObserve)]

/-- The initial state: the label's hash in lanes `0 … 3` (`Sponge.new`). -/
def daInit (iv : Digest) : KState := lanesToState (newInput iv (Vector.replicate 32 0))

/-- The state absorbing the root after the answer `y₀`. -/
def daFirst (root : Digest) (y : KState) : KState :=
  lanesToState (duplexInput ⟨stateToLanes y, rootScalars root⟩)

/-- The state of a sample after the answer `y`. -/
def daNext (y : KState) : KState := lanesToState (duplexInput ⟨stateToLanes y, []⟩)

theorem duplexInput_high (s : Sponge) (i : ℕ) (hi : 16 ≤ i) (hi' : i < 25) :
    (duplexInput s)[i] = s.state[i] := by
  simp only [duplexInput, Vector.getElem_ofFn, rateLanes, show ¬ i < 16 by omega, ↓reduceIte]
  rfl

theorem duplexInput_low (s : Sponge) (i : ℕ) (hi : i < 16) :
    (duplexInput s)[i] = (rateWords s.pending).getD i 0 := by
  simp only [duplexInput, Vector.getElem_ofFn, rateLanes, hi, ↓reduceIte]

/-- A duplexing keeps the capacity bytes. -/
theorem byteAt_duplexInput (y : KState) (pending : List (E × K)) (p : ℕ) (hp : 128 ≤ p)
    (hp' : p < 200) : byteAt (lanesToState (duplexInput ⟨stateToLanes y, pending⟩)) p = byteAt y p := by
  rw [byteAt_lanesToState _ p hp', ← byteAt_stateToLanes y p hp']
  have := duplexInput_high ⟨stateToLanes y, pending⟩ (p / 8) (by omega) (by omega)
  simp only at this
  rw [this]

theorem foldr_bytes_lt (l : List UInt8) : l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, List.length_cons, pow_succ]
    have := b.toNat_lt
    omega

theorem foldr_bytes_digit (l : List UInt8) (t : ℕ) (ht : t < l.length) :
    (l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 / 256 ^ t) % 256 = l[t].toNat := by
  induction l generalizing t with
  | nil => simp at ht
  | cons b l ih =>
    have hb := b.toNat_lt
    simp only [List.foldr_cons]
    rcases t with _ | t
    · simp only [pow_zero, Nat.div_one, List.getElem_cons_zero]
      omega
    · simp only [List.getElem_cons_succ]
      rw [pow_succ', ← Nat.div_div_eq_div_mul,
        show (b.toNat + 256 * l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0) / 256 =
          l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 by omega]
      exact ih t (by simpa using ht)

/-- **Eight bytes read as a word and written back.** -/
theorem kBytes_ofBytes (l : List UInt8) (hl : l.length = 8) : kBytes (ofBytes l) = l := by
  have hN := foldr_bytes_lt l
  rw [hl] at hN
  apply List.ext_getElem (by simp [kBytes, hl])
  intro t h1 h2
  simp only [kBytes, List.getElem_map, List.getElem_range, ofBytes, K.ofBits,
    BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat]
  apply UInt8.toNat_inj.mp
  rw [Nat.mod_eq_of_lt (by simpa using hN), Nat.shiftRight_eq_div_pow, pow_mul]
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
  exact foldr_bytes_digit l t h2

theorem word_bytes (d : Digest) (p : ℕ) (hp : p < 32) :
    d.toList[p]'(by simpa using hp) =
      (kBytes (word d (p / 8)))[p % 8]'(by simp [kBytes]; omega) := by
  have hlen : ((d.toList.drop (8 * (p / 8))).take 8).length = 8 := by
    simp only [List.length_take, List.length_drop, Vector.length_toList]; omega
  simp only [word]
  rw [List.getElem_of_eq (kBytes_ofBytes _ hlen), List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- **A digest is its four words.** -/
theorem eq_of_words {d d' : Digest} (h : ∀ i < 4, word d i = word d' i) : d = d' := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem (by simp)
  intro p h1 h2
  have hp : p < 32 := by simpa using h1
  rw [word_bytes d p hp, word_bytes d' p hp]
  congr 2
  exact h (p / 8) (by omega)

theorem limb_ofLimbs_0 (a b c : K) : limb (ofLimbs a b c) 0 = a := rfl
theorem limb_ofLimbs_1 (a b c : K) : limb (ofLimbs a b c) 1 = b := rfl

theorem rateWords_rootScalars (root : Digest) :
    rateWords (rootScalars root) = [word root 0, word root 1, limb (ofLimbs (word root 0) (word root 1) 0) 2,
      dsObserve, word root 2, word root 3, limb (ofLimbs (word root 2) (word root 3) 0) 2, dsObserve] := by
  simp only [rateWords, rootScalars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    limb_ofLimbs_0, limb_ofLimbs_1, List.cons_append, List.nil_append]

/-- **Absorbing different roots gives different states.** -/
theorem daFirst_injective (y : KState) : Function.Injective fun r ↦ daFirst r y := by
  intro r r' h
  have h' := lanesToState_injective h
  have hl : ∀ i (hi : i < 16), (rateWords (rootScalars r)).getD i 0 =
      (rateWords (rootScalars r')).getD i 0 := fun i hi ↦ by
    have := congrArg (fun L : Lanes ↦ L[i]) h'
    rwa [duplexInput_low _ i hi, duplexInput_low _ i hi] at this
  refine eq_of_words fun i hi ↦ ?_
  have h0 := hl 0 (by omega)
  have h1 := hl 1 (by omega)
  have h4 := hl 4 (by omega)
  have h5 := hl 5 (by omega)
  simp only [rateWords_rootScalars] at h0 h1 h4 h5
  interval_cases i
  · exact h0
  · exact h1
  · exact h4
  · exact h5

/-- The root a state absorbs after `y`, if any. -/
noncomputable def daDec (y x : KState) : Option Digest := by
  classical
  exact if h : ∃ r, daFirst r y = x then some h.choose else none

theorem daDec_iff (y x : KState) (r : Digest) : daDec y x = some r ↔ daFirst r y = x := by
  classical
  unfold daDec
  constructor
  · intro h
    split at h
    · next hx =>
      cases h
      exact hx.choose_spec
    · cases h
  · intro h
    have hx : ∃ r, daFirst r y = x := ⟨r, h⟩
    simp only [hx, ↓reduceDIte]
    congr 1
    exact daFirst_injective y (hx.choose_spec.trans h.symm)

/-- **LeanDA's challenges as a duplex**: `14` challenges of `E` from the label's hash and the
root, the capacity lanes `16 … 24` kept by every duplexing. -/
noncomputable def daDuplex : DuplexSpec (List UInt8) KDigest KState Digest E DaW DaCp 14 where
  label := label
  init := daInit
  first := daFirst
  next := daNext
  build := daBuild
  capW := Prod.snd
  dec := daDec
  dec_iff := daDec_iff
  n_pos := by norm_num
  cap_first r y := by
    funext j
    rw [daBuild_symm_cap, daBuild_symm_cap]
    exact byteAt_duplexInput y _ _ (by omega) (by omega)
  cap_next y := by
    funext j
    rw [daBuild_symm_cap, daBuild_symm_cap]
    exact byteAt_duplexInput y _ _ (by omega) (by omega)

end LeanDa

end

/-! ## The games in the random-permutation model -/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common PqDas MeasureTheory
open scoped ENNReal

namespace LeanDa

/-- The challenges of the sponge's list. -/
def toChallenges (zs : List E) : Challenges := fun j ↦ zs.getD j 0

/-- The adversary's oracles in the random-permutation model: coins, Keccak-256, `π` and `π⁻¹`. -/
abbrev AdvSpec := dSpec (List UInt8) KDigest KState

/-- **Calls of the permutation**: a hash of `n` bytes costs `⌊n / 136⌋ + 1` (one per block of
the padded message), a query of `π` or `π⁻¹` and a direct call one. -/
def permCalls2 : (dSpec2 (List UInt8) KDigest KState).Domain → ℕ
  | .inl _ => 0
  | .inr (.inl m) => m.length / 136 + 1
  | .inr (.inr _) => 1

section Games

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)

/-- **Verification of an opening in the random-permutation model** (the verification of Wagner's
scheme): the challenges of the commitment's root from the deployed duplex over the permutation,
the argument's verification, and the opening's, hashing with Keccak-256. -/
def verifyRpm (crs : Crs) (com : Digest × Proof) (p : Fin (r * 128)) (x : Cell) (τ : Opening) :
    OracleComp Rom2 Bool := do
  let zs ← membershipChallengesM hR pR com.1
  let v ← verifyCellM hR r com.1 p x τ
  pure (ps.verify crs ((), com.1, toChallenges zs) com.2 && v)

/-- A position-binding adversary in the random-permutation model: from the commitment key, a
commitment, a position, and two cells with their openings. -/
abbrev PosBindingAdvRpm (Crs Proof : Type) :=
  Unit × Crs → OracleComp AdvSpec ((Digest × Proof) × Fin (r * 128) × Cell × Opening × Cell × Opening)

/-- The verifier's part of the position-binding game: both openings verify, at two different
cells. -/
def posBindingPost (crs : Crs)
    (out : (Digest × Proof) × Fin (r * 128) × Cell × Opening × Cell × Opening) :
    OracleComp Rom2 Bool := do
  let b ← verifyRpm r ps crs out.1 out.2.1 out.2.2.1 out.2.2.2.1
  let b' ← verifyRpm r ps crs out.1 out.2.1 out.2.2.2.2.1 out.2.2.2.2.2
  pure (decide (out.2.2.1 ≠ out.2.2.2.2.1) && b && b')

/-- **The position-binding game in the random-permutation model**: the argument's setup, the
adversary with Keccak-256, `π` and `π⁻¹`, then the two verifications, whose challenges' sponge
calls the permutation directly. -/
def posBindingGame (A : PosBindingAdvRpm r Crs Proof) :
    OracleComp (dSpec2 (List UInt8) KDigest KState) Bool :=
  rpmGame2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (posBindingPost r ps)

/-- **The position-binding experiment**: the game against the lazily sampled random
permutation, Keccak-256 the sponge over it. -/
noncomputable def posBindingExpRpm (A : PosBindingAdvRpm r Crs Proof) : ProbComp Bool :=
  realGame2 keccakPadding KState.zero (posBindingGame r ps A)

end Games

section CodeBinding

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)

/-- A code-binding adversary in the random-permutation model: from the commitment key, a
commitment and a list of opened positions. -/
abbrev CodeBindingAdvRpm (Crs Proof : Type) :=
  Unit × Crs → OracleComp AdvSpec ((Digest × Proof) × List (Fin (r * 128) × Cell × Opening))

/-- The verifier's part of the code-binding game: every opening verifies, and no codeword agrees
with the opened cells. -/
noncomputable def codeBindingPost (crs : Crs)
    (out : (Digest × Proof) × List (Fin (r * 128) × Cell × Opening)) : OracleComp Rom2 Bool := do
  let verdicts ← out.2.mapM fun o ↦ verifyRpm r ps crs out.1 o.1 o.2.1 o.2.2
  pure (verdicts.all id && !decide ((code r).Consistent (out.2.map fun o ↦ (o.1, o.2.1))))

/-- **The code-binding game in the random-permutation model**: the argument's setup, the adversary
with Keccak-256, `π` and `π⁻¹`, then the verifications, whose challenges' sponge calls the
permutation directly. -/
noncomputable def codeBindingGame (A : CodeBindingAdvRpm r Crs Proof) :
    OracleComp (dSpec2 (List UInt8) KDigest KState) Bool :=
  rpmGame2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (codeBindingPost r ps)

/-- **The code-binding experiment**: the game against the lazily sampled random permutation. -/
noncomputable def codeBindingExpRpm (A : CodeBindingAdvRpm r Crs Proof) : ProbComp Bool :=
  realGame2 keccakPadding KState.zero (codeBindingGame r ps A)

end CodeBinding

section Completeness

/-- **Keccak-256 over a permutation `π`**: the sponge over `π` from the zero state with
Keccak-256's padding, the hash `H` of the games when the permutation is `π` (`realImpl`). -/
def keccakWith (π : KState → KState) (a : List UInt8) : Digest :=
  Id.run (spongeWith (m := Id) keccakPadding KState.zero (fun x ↦ pure (π x)) a)

/-- **The verifier's oracles for a permutation `π`**: coins forwarded, `H` Keccak-256 over `π`
(`keccakWith`), the direct calls `π` itself, as the games answer them (`realGame2`) when the
permutation is `π`. -/
def permImpl (π : KState → KState) : QueryImpl Rom2 ProbComp
  | .inl n => (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.inl a) => pure (keccakWith π a)
  | .inr (.inr x) => pure (π x)

variable (r : ℕ) {Crs Proof : Type}

/-- **The completeness experiment for a permutation `π`** (Wagner's, Foundations Definition 8,
with the hash and the challenges over `π`): the argument's setup; the honest commitment to the
message `msg`, the root of its encoding's cells hashed with Keccak-256 over `π` and the argument's
proof for the challenges of the root, drawn by the deployed duplex over `π`
(`membershipChallengesM`); the honest opening of the position `p`; and the binding games'
verification (`verifyRpm`) of the encoding's cell at `p` with that opening. -/
noncomputable def completenessExpRpm (π : KState → KState)
    (ps : Argument r (keccakWith π) Crs Proof) (msg : Fin r → Payload) (p : Fin (r * 128)) :
    ProbComp Bool := do
  let crs ← ps.setup
  let c := (code r).encode msg
  let root := commitCells (keccakWith π) c
  simulateQ (permImpl π) do
    let zs ← membershipChallengesM hR pR root
    let proof := ps.prove crs ((), root, toChallenges zs) c
    verifyRpm r ps crs (root, proof) p (c p) (openCell (keccakWith π) c p)

end Completeness

end LeanDa

end

/-! ## Wagner's terms, for a uniformly random table of the hash -/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.Duplex PqDas
open scoped ENNReal

namespace LeanDa

/-- Wagner's oracles: coins and the challenges `G`, a random oracle of the roots. -/
abbrev WSpec := unifSpec + (Digest →ₒ Challenges)

/-- The challenges and `H`. -/
abbrev TSpec := (Digest →ₒ Challenges) + roSpec (List UInt8) KDigest

/-- A cache of `H`. -/
abbrev HCache := (roSpec (List UInt8) KDigest).QueryCache

/-- A short string: at most `2048` bytes, a cell's. -/
def shortP (a : List UInt8) : Prop := a.length ≤ 2048

instance : DecidablePred shortP := fun a ↦ inferInstanceAs (Decidable (a.length ≤ 2048))

noncomputable instance : Fintype {a : List UInt8 // shortP a} :=
  (List.finite_length_le (α := UInt8) 2048).fintype

/-- A table of `H` on the short strings. -/
abbrev HTab := {a : List UInt8 // shortP a} → KDigest

/-- **The hash of a table**: the table's answer on a short string, `default` on a long one. -/
def Hh (h : HTab) (a : List UInt8) : Digest := if ha : shortP a then h ⟨a, ha⟩ else default

/-- **`H` from a table, in Wagner's world**: the table on short strings, lazily sampled on long
ones (the state), the challenges forwarded to Wagner's random oracle. -/
noncomputable def tImpl (h : HTab) : QueryImpl (unifSpec + TSpec) (StateT HCache (OracleComp WSpec))
  | .inl k => StateT.mk fun c ↦ (·, c) <$> liftM (WSpec.query (.inl k))
  | .inr (.inl d) => StateT.mk fun c ↦ (·, c) <$> liftM (WSpec.query (.inr d))
  | .inr (.inr a) =>
      if ha : shortP a then StateT.mk fun c ↦ pure (h ⟨a, ha⟩, c)
      else StateT.mk fun c ↦ liftM (((roSpec (List UInt8) KDigest).randomOracle a).run c)

/-- The simulated world's oracles from a table `h` of `H`. -/
noncomputable def phiG (h : HTab) :
    QueryImpl (unifSpec + GSpec (List UInt8) KDigest Digest E 14) (StateT HCache (OracleComp WSpec)) :=
  tImpl h ∘ₛ (swapImpl ∘ₛ toV)

section Adversary

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)

/-- The crs the adversary runs with: the given one when the setup can output it, else one it
can (the bound on the adversary's queries holds for these). -/
noncomputable def fixCrs (crs : Crs) : Crs := by
  classical
  exact if crs ∈ support ps.setup then crs else (support_nonempty ps.setup).some

/-- The adversary in the simulated world: `H` queried at the label, then the RPM adversary with
its permutation queries simulated from `H` and `F`, `F` answered by the duplex lemma's simulator. -/
noncomputable def advSim (A : CodeBindingAdvRpm r Crs Proof) (crs : Crs) :
    OracleComp (unifSpec + GSpec (List UInt8) KDigest Digest E 14)
      ((Digest × Proof) × List (Fin (r * 128) × Cell × Opening)) :=
  (simulateQ (simImpl daDuplex hP gaP) (hQ (St := KState) daDuplex.label >>= fun _ ↦
    advS2 keccakPadding KState.zero (A ((), crs)))).run' SimSt.init

/-- **Wagner's adversary for the table `h` of `H`**: the simulated adversary, with `H` answered
from `h` on short strings and lazily on long ones, and the challenges `G` from Wagner's random
oracle. -/
noncomputable def advH (A : CodeBindingAdvRpm r Crs Proof) (h : HTab) :
    ErasureCodeCommitment.CodeBindingAdv (OracleComp WSpec) Cell (r * 128) (Unit × Crs)
      (Digest × Proof) Opening :=
  fun ck ↦ (simulateQ (phiG h) (advSim r A (fixCrs r ps ck.2))).run' ∅

end Adversary

section Verify

variable (r : ℕ) {Crs Proof : Type}

/-- The argument for the relation of a hash `H`, from an argument for any relation. -/
def argH {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
    (H : List UInt8 → Digest) : Argument r H Crs Proof :=
  ⟨ps.setup, ps.prove, ps.verify⟩

end Verify

section Final

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)

/-- Wagner's knowledge-soundness experiment for the table `h`: his reduction `ksReduction` from
`advH h`, against the argument `ps` for the relation with the hash `Hh h`. -/
noncomputable def ksExpH
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : CodeBindingAdvRpm r Crs Proof) (h : HTab) : ProbComp Bool :=
  (argH r ps (Hh h)).knowledgeSoundnessExp ext (ksReduction (merkleVC r (Hh h)) (advH r ps A h))

/-- The collision experiment of `Hh h` against Wagner's weak-position-binding reduction from
`advH h`, through `merkleCollider`. -/
noncomputable def wpbCollExpH [NeZero r]
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : CodeBindingAdvRpm r Crs Proof) (h : HTab) : ProbComp Bool :=
  hashCollisionExp (Hh h) (merkleCollider r (Hh h)
    ((wpbReduction (argH r ps (Hh h)) ext (advH r ps A h)).toPosBindingAdv (merkleVC r (Hh h))))

/-- The collision experiment of `Hh h` against Wagner's forking reduction from `advH h` (at most
`Q + 1` queries of the challenges), through `merkleCollider`. -/
noncomputable def forkCollExpH [NeZero r]
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : CodeBindingAdvRpm r Crs Proof) (Q : ℕ) (h : HTab) : ProbComp Bool :=
  hashCollisionExp (Hh h) (merkleCollider r (Hh h)
    ((CommittedSoundness.forkCollisionReduction (code r) (merkleVC r (Hh h)) (checker r)
      (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) (Q + 1)).toPosBindingAdv
        (merkleVC r (Hh h))))

end Final

end LeanDa

end

@[expose] public section

/-! ### The end statements -/

namespace LeanDa

open PqDas PqDas.CommittedSoundness OracleComp OracleSpec ENNReal Common

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation.**
For any number `r` of rows, every permutation `π` of the Keccak state (indeed every function), the
hash Keccak-256 over `π` and the membership challenges the deployed duplex over `π`, and every
perfectly complete argument `ps` for the relation with that hash: every position `p` of the
honest commitment to every message `msg` opens and verifies with probability one
(`completenessExpRpm`, over the argument's setup). Holding for each `π`, it holds for every
outcome of the binding statements' uniformly random permutation. The proof is Wagner's
completeness proof, transferred. Proved by
`LeanDa.leanDa_perfectlyComplete_rpm`. An argument complete for every `π` makes `CodeBindingRpm`'s
knowledge-soundness term `ε_ks` close to `1`, so this and code binding are not both meaningful for
one argument (the file's header, "What code binding says"). -/
abbrev PerfectlyCompleteRpm : Prop :=
  ∀ (r : ℕ) (π : KState → KState) {Crs Proof : Type} (ps : Argument r (keccakWith π) Crs Proof),
    ps.PerfectlyComplete →
      ∀ (msg : Fin r → Payload) (p : Fin (r * 128)),
        Pr{let b ← completenessExpRpm r π ps msg p}[b = true] = 1

/-- **LeanDA is position binding in the random-permutation model.** For every argument `ps` (any
verifier, for any relation) and every adversary whose game, verifications included, makes at most
`Q` calls of the permutation on every path (`permCalls2`: a hash of `n` bytes costs
`⌊n / 136⌋ + 1`, a query of `π` or `π⁻¹` and a sponge call one), the probability of opening a
position to two different cells is at most `Q² / 2^256 + Q² / 2^508`. Proved by
`LeanDa.leanDa_positionBinding_rpm`. -/
abbrev PositionBindingRpm : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
    (A : PosBindingAdvRpm r Crs Proof) (Q : ℕ),
    IsWeightBound (posBindingGame r ps A) permCalls2 Q →
      Pr{let b ← posBindingExpRpm r ps A}[b = true] ≤
        (Q ^ 2 : ℝ≥0∞) / 2 ^ 256 + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508

/-- **LeanDA is code binding in the random-permutation model** (Benedikt Wagner's bound, moved to
the random-permutation model). For every argument `ps` (any verifier, for any relation; an
oracle-free parameter, as in Wagner's model), every extractor `ext`, and every adversary whose
game, verifications included, makes at most `Q` permutation calls (`permCalls2`),

`(Pr[code-bind] − (Q²/2^508 + 2(Q+15)²/2^576 + ε_ks + ε₁))² ≤ (Q + 2)(ε₂ + 14/2^192 + 2^-2688)`,

where, for a uniformly random table `h` of `H` on the strings of at most `2048` bytes (`Hh h`
its hash) and Wagner's adversary `advH h` built from the RPM adversary, `ε_ks` is the success of
Wagner's reduction against the knowledge soundness of `ps` for the relation with the hash `Hh h`
(`ksExpH`), and `ε₁`, `ε₂` those of his two reductions finding a collision of `Hh h`
(`wpbCollExpH`, `forkCollExpH`). Proved by `LeanDa.leanDa_codeBinding_rpm_bound`.

The bound keeps these three random-oracle experiments over the table `h`; they are not numbers.
`ps` proves a relation involving the hash, but its prover and verifier do not call the hash, so
`ε_ks` is small only for an argument that stays knowledge sound when the hash is the random oracle,
which an oracle-free argument cannot. For an argument complete for every `π`
(`PerfectlyCompleteRpm`), which accepts false statements, `ε_ks ≈ 1`: completeness and code
binding are not both meaningful for one argument, as in Wagner's random-oracle original. Giving
the argument oracle access would close this; it is not done. -/
abbrev CodeBindingRpm : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel) [NeZero r]
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : CodeBindingAdvRpm r Crs Proof) (Q : ℕ),
    IsWeightBound (codeBindingGame r ps A) permCalls2 Q →
    (Pr{let b ← codeBindingExpRpm r ps A}[b = true] -
        ((Q ^ 2 : ℝ≥0∞) / 2 ^ 508 + 2 * ((Q + 15 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576 +
          (Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= ksExpH r ps ext A}[b = true] +
            Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= wpbCollExpH r ps ext A}[b = true]))) ^ 2 ≤
      ((Q : ℝ≥0∞) + 2) *
        (Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= forkCollExpH r ps ext A Q}[b = true] +
          14 / 2 ^ 192 + (2 ^ 2688)⁻¹)

end LeanDa

end
