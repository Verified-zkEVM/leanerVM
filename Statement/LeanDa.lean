module

public import Statement.Field
public import Statement.RandomPermutation
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
open LeanVM.Parameters (K.toBytes E.toBytes)
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol (Digest)
open LeanVM.Protocol.KeccakHash (keccak256With digestHalves littleEndianLane)
open LeanVM.Protocol.Compile (Sponge absorb squeeze seedInput dsObserve)

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
  `H(rowRoot ‖ columnRoot)`. A tree hashes neighbours in pairs, level by level (`tree_from_leaves`).
  The padding digests of `padding_digests` are the digests of zero cells and rows, so the root is
  the commitment to the padded matrix.
* **Openings.** A cell is opened by its authentication path in the column tree and the row root.
  The crate keeps the column tree for this (`DaWitness::column_tree`, `commit.rs:23-45`), whose
  level `⌈log₂ r⌉` holds the column roots (`column_roots`), but verifies no sample:
  `verifyCellWith` is the check this path determines.
* **Membership** (`membership.rs:33-83`, `verifier/src/da.rs:15-85`). Challenges `z ∈ E^14` give
  the dual codeword `L`, the tensor `⊗_j (1, z_j)` read as novel-basis coefficients and encoded,
  that is `L(x) = ∏_j (1 + z_j Ŵ_j(x))` on the domain (Annex D, eq. dual-product), with
  `Ŵ_j` the normalized subspace polynomial of the span of `e_0 … e_(j-1)`. A matrix passes when
  every row is orthogonal to `L` (`check_membership`, `membership.rs:94-103`; the guest program's
  `da_verify`). The challenges are drawn from the root by a duplex sponge over Keccak-f[1600]
  seeded with the label's hash (`membership_challenges`), the Fiat-Shamir sponge of leanVM's
  verifier (`verifier/src/transcript.rs`, `Field.lean`'s `Sponge`); the end statements draw them
  by this duplex over the permutation (`membershipChallengesWith`).

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
def rowCell (row : Row) (j : Fin 128) : Cell := fun s ↦ row ⟨256 * j + s, by omega⟩

/-- The position of cell `j` of row `i`. -/
def cellPosition {r : ℕ} (i : Fin r) (j : Fin 128) : Fin (r * 128) := ⟨128 * i + j, by omega⟩

/-- The row of a position. -/
def positionRow {r : ℕ} (p : Fin (r * 128)) : Fin r := ⟨p / 128, by omega⟩

/-- The cell of a position within its row. -/
def positionCell {r : ℕ} (p : Fin (r * 128)) : Fin 128 := ⟨p % 128, by omega⟩

/-- The cells of a matrix of encoded payloads. -/
noncomputable def encodeMatrix {r : ℕ} (message : Fin r → Payload) : Fin (r * 128) → Cell :=
  fun p ↦ rowCell (encodeRow (message (positionRow p))) (positionCell p)

/-- Row `i` of a matrix given by its cells. -/
def matrixRow {r : ℕ} (cells : Fin (r * 128) → Cell) (i : Fin r) : Row :=
  fun b ↦ cells (cellPosition i ⟨b / 256, by omega⟩) ⟨b % 256, by omega⟩

/-- The cells of the matrix whose rows are `rows`, codewords as lists of symbols: cell `j` of row
`i` at position `128 i + j`. -/
def cellsOfRows (rows : List (List K)) : Fin (rows.length * 128) → Cell :=
  fun p s ↦ (rows.getD (p / 128) []).getD (256 * (p % 128) + s) 0

/-- **LeanDA's hash** over a permutation `π` of the Keccak state in any monad: Keccak-256 over `π`
(`keccak256With`), its digest's 32 bytes (`Digest.toBytes`). The crate's is Keccak-256 over
Keccak-f[1600] (`verifier/src/hash.rs`); the end statements' is over the random permutation. -/
def keccakDigestBytes {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (bytes : List UInt8) : m DigestBytes :=
  LeanVM.Protocol.Digest.toBytes <$> keccak256With π bytes

/-! ### The commitment (`commit.rs`)

The commitment, the openings and their check, and the membership challenges over a permutation `π`
in any monad, the hash Keccak-256 over `π`: the games' oracles, or over `Id` the deployed
algorithms (`commitCells`, `openCell`). -/

/-- A cell's bytes: its symbols' eight little-endian bytes in order (`as_bytes`). -/
def cellBytes (cell : Cell) : List UInt8 := (List.ofFn cell).flatMap K.toBytes

/-- The 64 bytes of a pair of digests (`hash_pair`, `tree_from_leaves`). -/
def pairBytes (a b : DigestBytes) : List UInt8 := a.toList ++ b.toList

/-- `⌈log₂ r⌉`: the padded row count `2^⌈log₂ r⌉` is `r.next_power_of_two()`. -/
def logPaddedRowCount (r : ℕ) : ℕ := Nat.clog 2 r

/-- The padded row count. -/
def paddedRowCount (r : ℕ) : ℕ := 2 ^ logPaddedRowCount r

/-- Cell `j` of row `i` of the padded matrix: zero below the `r` rows. -/
def paddedCell {r : ℕ} (cells : Fin (r * 128) → Cell) (i j : ℕ) : Cell :=
  if h : i < r ∧ j < 128 then cells (cellPosition ⟨i, h.1⟩ ⟨j, h.2⟩) else 0

/-- The other node of the pair of node `index`. -/
def sibling (index : ℕ) : ℕ := if index % 2 = 0 then index + 1 else index - 1

/-- The opening of a cell: the row root and the cell's path in the column tree. -/
structure CellOpening where
  /-- The row root. -/
  rowRoot : DigestBytes
  /-- The siblings from the cell's leaf up to the column root. -/
  path : List DigestBytes
deriving Inhabited

/-- The column tree index of a position: cell `j` of row `i` is leaf `j · 2^⌈log₂ r⌉ + i`. -/
def columnTreeIndex {r : ℕ} (p : Fin (r * 128)) : ℕ :=
  (positionCell p : ℕ) * paddedRowCount r + positionRow p

/-- `leanDA/rs-membership/v1`, the label of the challenges' transcript (`LABEL`). -/
def membershipLabel : List UInt8 := "leanDA/rs-membership/v1".toUTF8.toList

/-- The digest of 32 bytes: its four little-endian words (`Digest::words`). -/
def digestOfBytes (bytes : DigestBytes) : Digest :=
  Vector.ofFn fun i : Fin 4 ↦ littleEndianLane bytes.toList i

section Monadic

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- One level up a Merkle tree: node `i` hashes nodes `2i` and `2i + 1`. -/
def merkleLevelUpWith (nodeAt : ℕ → m DigestBytes) (i : ℕ) : m DigestBytes := do
  let a ← nodeAt (2 * i)
  let b ← nodeAt (2 * i + 1)
  keccakDigestBytes π (pairBytes a b)

/-- The root of the Merkle tree over the leaves `nodeAt 0 … nodeAt (2^d - 1)`
(`tree_from_leaves`). -/
def merkleRootWith : ℕ → (ℕ → m DigestBytes) → m DigestBytes
  | 0, nodeAt => nodeAt 0
  | d + 1, nodeAt => merkleRootWith d (merkleLevelUpWith π nodeAt)

/-- The authentication path of leaf `index`, siblings from the bottom. -/
def merklePathWith : ℕ → (ℕ → m DigestBytes) → ℕ → m (List DigestBytes)
  | 0, _, _ => pure []
  | d + 1, nodeAt, index => do
    let s ← nodeAt (sibling index)
    let rest ← merklePathWith d (merkleLevelUpWith π nodeAt) (index / 2)
    pure (s :: rest)

/-- The row tree's leaves: each padded row's digest of its first `64` cell digests. -/
def rowLeavesWith {r : ℕ} (cells : Fin (r * 128) → Cell) (i : ℕ) : m DigestBytes := do
  let ds ← (List.range 64).mapM fun j ↦ keccakDigestBytes π (cellBytes (paddedCell cells i j))
  keccakDigestBytes π (ds.flatMap Vector.toList)

/-- The column tree's leaves: leaf `j · 2^⌈log₂ r⌉ + i` is the digest of cell `j` of padded row
`i` (`hash_cells`). -/
def columnLeavesWith {r : ℕ} (cells : Fin (r * 128) → Cell) (l : ℕ) : m DigestBytes :=
  keccakDigestBytes π (cellBytes (paddedCell cells (l % paddedRowCount r) (l / paddedRowCount r)))

/-- The row root (`root_row`). -/
def rowRootWith {r : ℕ} (cells : Fin (r * 128) → Cell) : m DigestBytes :=
  merkleRootWith π (logPaddedRowCount r) (rowLeavesWith π cells)

/-- The column root (`root_col`). -/
def columnRootWith {r : ℕ} (cells : Fin (r * 128) → Cell) : m DigestBytes :=
  merkleRootWith π (7 + logPaddedRowCount r) (columnLeavesWith π cells)

/-- **The root of a matrix** (`commit_codewords`): `H(rowRoot ‖ columnRoot)`. -/
def commitCellsWith {r : ℕ} (cells : Fin (r * 128) → Cell) : m DigestBytes := do
  let a ← rowRootWith π cells
  let b ← columnRootWith π cells
  keccakDigestBytes π (pairBytes a b)

/-- The honest opening of a position: the row root and the cell's path in the column tree. -/
def openCellWith {r : ℕ} (cells : Fin (r * 128) → Cell) (p : Fin (r * 128)) : m CellOpening := do
  let rowRoot ← rowRootWith π cells
  let path ← merklePathWith π (7 + logPaddedRowCount r) (columnLeavesWith π cells)
    (columnTreeIndex p)
  pure ⟨rowRoot, path⟩

/-- Climb from `node` at index `index` along the siblings `path`. -/
def climbWith : ℕ → DigestBytes → List DigestBytes → m DigestBytes
  | _, node, [] => pure node
  | index, node, s :: rest => do
    let d ← keccakDigestBytes π (if index % 2 = 0 then pairBytes node s else pairBytes s node)
    climbWith (index / 2) d rest

/-- **Verification of a cell opening**: a path of the column tree's height that climbs from the
cell's digest to a column root, which hashed after the row root gives the commitment. -/
def verifyCellWith (r : ℕ) (commitment : DigestBytes) (position : Fin (r * 128)) (cell : Cell)
    (opening : CellOpening) : m Bool := do
  let d ← keccakDigestBytes π (cellBytes cell)
  let w ← climbWith π (columnTreeIndex position) d opening.path
  let root ← keccakDigestBytes π (pairBytes opening.rowRoot w)
  pure (decide (opening.path.length = 7 + logPaddedRowCount r) && decide (root = commitment))

/-! ### The membership challenges (`verifier/src/da.rs:15-22`)

Drawn from the root by the duplex sponge of the leanVM verifier (`Field.lean`: `Sponge`, `absorb`,
`squeeze`), over the permutation `π` (`verifier/src/transcript.rs:32-95`). The crate's membership
vector, their dual codeword by the additive NTT, is `lean_da`'s (`membershipVector`, which computes
`dualCodewordAt`: `membershipVector_eq_dual`). -/

/-- `n` challenges squeezed in order (`sample`). -/
def squeezeChallenges : ℕ → Sponge → m (List E)
  | 0, _ => pure []
  | n + 1, sponge => do
    let (z, sponge) ← squeeze π sponge
    let zs ← squeezeChallenges n sponge
    pure (z :: zs)

/-- **The challenges `z_0 … z_13` of a root** (`membership_challenges`, `verifier/src/da.rs:15-22`):
a sponge seeded with the label's hash and a zero public input (`Sponge::from_label`), the root
observed as its two halves `(w_0, w_1, 0)` and `(w_2, w_3, 0)`, then `14` samples. -/
def membershipChallengesWith (root : DigestBytes) : m (List E) := do
  let iv ← keccak256With π membershipLabel
  let state ← π (seedInput iv (Vector.replicate 4 0))
  let (low, high) := digestHalves (digestOfBytes root)
  let sponge ← absorb π ⟨state, []⟩ low dsObserve
  let sponge ← absorb π sponge high dsObserve
  squeezeChallenges π logK sponge

end Monadic

/-- **The root of a matrix** over a permutation `π` (`commitCellsWith` over `Id`). -/
def commitCells (π : KeccakState → KeccakState) {r : ℕ} (cells : Fin (r * 128) → Cell) :
    DigestBytes :=
  Id.run (commitCellsWith (fun x ↦ pure (π x)) cells)

/-- The honest opening of a position over a permutation `π` (`openCellWith` over `Id`). -/
def openCell (π : KeccakState → KeccakState) {r : ℕ} (cells : Fin (r * 128) → Cell)
    (p : Fin (r * 128)) : CellOpening :=
  Id.run (openCellWith (fun x ↦ pure (π x)) cells p)

/-! ### Membership (`membership.rs`, `verifier/src/da.rs`) -/

/-- The normalized subspace polynomial `Ŵ_j`, vanishing on the span of `e_0 … e_(j-1)` and one
at `e_j` (CompPoly's `normalizedW`; `subspace_evaluations` tabulates it on the basis). -/
noncomputable def normalizedSubspacePolynomial (j : Fin 14) : K[X] :=
  AdditiveNTT.normalizedW (ZMod 2) basis (Fin.castLE (by omega) j)

/-- **The dual codeword of challenges `z`** (`dual_codeword`): `L(x) = ∏_j (1 + z_j Ŵ_j(x))` on
the domain, the encoding of `tensor z` (`lean_da`'s `dual_eq_sum`). -/
noncomputable def dualCodewordAt (z : Fin 14 → E) (b : Fin (2 ^ 15)) : E :=
  ∏ j : Fin 14, (1 + z j * ι ((normalizedSubspacePolynomial j).eval (point b)))

/-- The inner product of the dual codeword with a row: `Σ_x L(x) row(x)` (`check_membership`). -/
noncomputable def innerProduct (L : Fin (2 ^ 15) → E) (row : Row) : E := ∑ b, L b * ι (row b)

/-- **The membership check**: every row is orthogonal to the dual codeword. -/
noncomputable def membershipCheck {r : ℕ} (z : Fin 14 → E) (cells : Fin (r * 128) → Cell) : Bool :=
  decide (∀ i : Fin r, innerProduct (dualCodewordAt z) (matrixRow cells i) = 0)

/-! ### The vector's digest -/

variable (π : KeccakState → KeccakState)

/-- The digest of column `j` of a vector, its entries `256 j … 256 j + 255`, each its three limbs'
little-endian bytes (`E.toBytes`). -/
def columnDigest (vector : List E) (j : ℕ) : DigestBytes :=
  Id.run (keccakDigestBytes π (((vector.drop (j * cellSymbols)).take cellSymbols).flatMap
    E.toBytes))

/-- **The digest of a vector** (`vector_digest`, `verifier/src/da.rs:87-96`): the hash of its
`128` columns' digests, in order. The crate takes vectors of `2^15` entries and panics on others. -/
def vectorDigest (vector : List E) : DigestBytes :=
  Id.run (keccakDigestBytes π
    ((List.range cellsPerRow).flatMap fun j ↦ (columnDigest π vector j).toList))

/-! ## LeanDA's code and the argument's relation -/

/-- **LeanDA's erasure code**: `r` payloads, encoded row by row and cut into cells. -/
noncomputable def leanDaErasureCode (r : ℕ) : ErasureCode Payload Cell r (r * 128) := ⟨encodeMatrix⟩

/-- The challenges of the membership test. -/
abbrev MembershipChallenges := Fin 14 → E

/-- The challenges of the sponge's list. -/
def toChallenges (challenges : List E) : MembershipChallenges := fun j ↦ challenges.getD j 0

/-- **The relation the argument proves**, over a permutation `π` in any monad: the cells commit to
the root and pass the membership test on the root's challenges, drawn by the deployed duplex
(`membershipChallengesWith`), the hash Keccak-256 over `π`. In the games `π` is `π`
(`queryPermutation`). -/
noncomputable def relationWith {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState) {r : ℕ}
    (root : DigestBytes) (cells : Fin (r * 128) → Cell) : m Bool := do
  let zs ← membershipChallengesWith π root
  let d ← commitCellsWith π cells
  pure (decide (d = root) && membershipCheck (toChallenges zs) cells)

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
`π`, an honest proof of a statement the relation `relation π` holds for verifies with probability
one. -/
def OracleArgument.PerfectlyComplete {Stmt Wit Crs Proof : Type}
    (argument : OracleArgument Stmt Wit Crs Proof)
    (relation : Equiv.Perm KeccakState → Stmt → Wit → Bool) : Prop :=
  ∀ (π : Equiv.Perm KeccakState), ∀ crs ∈ support argument.setup, ∀ stmt wit,
    relation π stmt wit = true →
    Pr{let b ← simulateQ (oraclesFromPermutation π)
         (argument.prove crs stmt wit >>= argument.verify crs stmt)}[b = true] = 1

/-- **LeanDA's relation for a permutation `π`**: `relationWith` over `π`. -/
noncomputable def relationForPermutation (r : ℕ) (π : Equiv.Perm KeccakState) (root : DigestBytes)
    (cells : Fin (r * 128) → Cell) : Bool :=
  Id.run (relationWith (fun x ↦ pure (π x)) root cells)

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

variable (r : ℕ) {Crs Proof : Type} (argument : LeanDaArgument r Crs Proof)
  (extractor : StraightLineExtractor DigestBytes (Fin (r * 128) → Cell) Crs Proof)

/-- A position-binding adversary: from the commitment key, a commitment, a position, and two cells
with their openings. -/
abbrev PositionBindingAdversary (Crs Proof : Type) :=
  Unit × Crs →
    OracleComp RandomPermutationOracles
      ((DigestBytes × Proof) × Fin (r * 128) × Cell × CellOpening × Cell × CellOpening)

/-- **The position-binding game**: the argument's setup, the adversary, then the verifications:
the argument's of the root's proof and the two openings'; it wins when all verify, at two
different cells. -/
def positionBindingGame (adversary : PositionBindingAdversary r Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM argument.setup
  let (commitment, position, cell, opening, cell', opening') ← adversary ((), crs)
  let ok ← argument.verify crs commitment.1 commitment.2
  let b ← verifyCellWith queryPermutation r commitment.1 position cell opening
  let b' ← verifyCellWith queryPermutation r commitment.1 position cell' opening'
  pure (decide (cell ≠ cell') && ok && b && b')

/-- A code-binding adversary: from the commitment key, a commitment and a list of opened
positions. -/
abbrev CodeBindingAdversary (Crs Proof : Type) :=
  Unit × Crs →
    OracleComp RandomPermutationOracles
      ((DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening))

/-- **The code-binding game**: the argument's setup, the adversary, then the verifications; it wins
when the root's proof and every opening verify and no codeword agrees with the opened cells. -/
noncomputable def codeBindingGame (adversary : CodeBindingAdversary r Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM argument.setup
  let (commitment, opened) ← adversary ((), crs)
  let ok ← argument.verify crs commitment.1 commitment.2
  let verdicts ← opened.mapM fun entry ↦
    verifyCellWith queryPermutation r commitment.1 entry.1 entry.2.1 entry.2.2
  pure (ok && verdicts.all id &&
    !decide ((leanDaErasureCode r).Consistent (opened.map fun entry ↦ (entry.1, entry.2.1))))

/-- A knowledge-soundness adversary: from the crs, a root and a proof. -/
abbrev KnowledgeSoundnessAdversary (Crs Proof : Type) :=
  Crs → OracleComp RandomPermutationOracles (DigestBytes × Proof)

/-- **The argument's knowledge-soundness game** (Wagner's, Foundations Definition 18, in the
random-permutation model with a straight-line extractor): the argument's setup, the adversary with
its queries logged, the argument's verification, then the relation's check on the cells the
extractor reads off the proof and the adversary's transcript; it wins when the proof verifies and
the extracted cells do not satisfy the relation (`relationWith` over `π`). -/
noncomputable def knowledgeSoundnessGame (adversary : KnowledgeSoundnessAdversary Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM argument.setup
  let ((root, proof), log) ← (simulateQ loggedOracles (adversary crs)).run []
  let v ← argument.verify crs root proof
  let ok ← relationWith queryPermutation root (extractor crs root proof log)
  pure (v && !ok)

/-- **The completeness experiment for a permutation `π`** (Wagner's, Foundations Definition 8,
with the hash and the oracles answered by `π`): the argument's setup; the honest commitment to the
message `message`, the root of its encoding's cells hashed with Keccak-256 over `π`; the argument's
honest proof for the root and its verification, both with the oracles answered by `π`; and the
verification of the encoding's cell at `position` with its honest opening. -/
noncomputable def completenessExperiment (π : Equiv.Perm KeccakState)
    (argument : LeanDaArgument r Crs Proof) (message : Fin r → Payload) (position : Fin (r * 128)) :
    ProbComp Bool := do
  let crs ← argument.setup
  let cells := (leanDaErasureCode r).encode message
  let root := commitCells π cells
  let ok ← simulateQ (oraclesFromPermutation π)
    (argument.prove crs root cells >>= argument.verify crs root)
  pure (ok && Id.run (verifyCellWith (fun x ↦ pure (π x)) r root position (cells position)
    (openCell π cells position)))

/-! ### The end statements -/

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation.**
For any number `r` of rows, every permutation `π` of the Keccak state, and every argument `argument`
perfectly complete for LeanDA's relation for every permutation (`relationForPermutation`, the hash
Keccak-256 over `π` and the challenges the deployed duplex over `π`; the argument's prover and
verifier answered by `π`): every position `position` of the honest commitment to every message
`message` opens and verifies with probability one (`completenessExperiment`). Holding for each `π`,
it holds for every outcome of the binding statements' uniformly random permutation. The proof is
Wagner's completeness proof, transferred. Proved by `LeanDa.leanDa_perfectlyComplete_rpm`. -/
abbrev LeanDaPerfectlyComplete : Prop :=
  ∀ (r : ℕ) (π : Equiv.Perm KeccakState) {Crs Proof : Type} (argument : LeanDaArgument r Crs Proof),
    argument.PerfectlyComplete (relationForPermutation r) →
      ∀ (message : Fin r → Payload) (position : Fin (r * 128)),
        Pr{let b ← completenessExperiment r π argument message position}[b = true] = 1

/-- **LeanDA is position binding in the random-permutation model.** For every argument `argument`
(any prover and verifier) and every adversary whose game, verifications included, makes at most `Q`
calls of `π` and `π⁻¹` on every path (`permutationCallCost`; a hash of `n` bytes, Keccak-256 over
`π`, makes `⌊n / 136⌋ + 1`; the argument's verifier's included), the probability of opening a
position to two different cells is at most `(Q + 1)² · 2^-256`, for every `Q` (past `2^128` the
bound exceeds one). Proved by `LeanDa.leanDa_positionBinding_rpm`. -/
abbrev LeanDaPositionBinding : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} (argument : LeanDaArgument r Crs Proof)
    (adversary : PositionBindingAdversary r Crs Proof)
    (Q : ℕ), QueryCostAtMost (positionBindingGame r argument adversary) permutationCallCost Q →
      Pr{let b ← runWithRandomPermutation (positionBindingGame r argument adversary)}[b = true] ≤
        ((Q : ℝ≥0∞) + 1) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-- **LeanDA is code binding in the random-permutation model, for an argument knowledge sound in
it** (Benedikt Wagner's framework and games, moved to the random-permutation model, with a
straight-line argument in place of his forking lemma). For `1 ≤ r ≤ 1024` rows (`maxRows`, the
crate's bound), every argument `argument` (its prover and verifier querying the model's oracles) and
straight-line extractor `extractor` (reading the adversary's transcript): if every adversary whose
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
be perfectly complete for every permutation (`LeanDaPerfectlyComplete`). An argument whose relation
uses the deployed Keccak-f[1600] instead of `π`, such as leanVM proving the guest program's DA
check, cannot meet the hypothesis in this model: an adversary computes such a root with no query
to `π` and proves its opening honestly, and no straight-line extractor finds a `π`-preimage of it.
The theorem covers arguments whose relation is evaluated over `π`. Proved by
`LeanDa.leanDa_codeBinding_rpm_bound`. -/
abbrev LeanDaCodeBinding : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} (argument : LeanDaArgument r Crs Proof)
    (extractor : StraightLineExtractor DigestBytes (Fin (r * 128) → Cell) Crs Proof) (c k : ℕ),
    (∀ (adversary : KnowledgeSoundnessAdversary Crs Proof) (q : ℕ),
      QueryCostAtMost (knowledgeSoundnessGame r argument extractor adversary) permutationCallCost
        q →
      q ≤ 2 ^ 128 →
        Pr{let b ← runWithRandomPermutation
            (knowledgeSoundnessGame r argument extractor adversary)}[b = true] ≤
        ((q : ℝ≥0∞) + c) * (2 : ℝ≥0∞)⁻¹ ^ k) →
    1 ≤ r → r ≤ maxRows →
    ∀ (adversary : CodeBindingAdversary r Crs Proof) (Q : ℕ),
      QueryCostAtMost (codeBindingGame r argument adversary) permutationCallCost Q →
        Pr{let b ← runWithRandomPermutation (codeBindingGame r argument adversary)}[b = true] ≤
          ((Q : ℝ≥0∞) + c + 2 ^ 22) * (2 : ℝ≥0∞)⁻¹ ^ k +
            ((Q : ℝ≥0∞) + 2 ^ 22) * (2 : ℝ≥0∞)⁻¹ ^ 188 +
            ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247

end LeanDa

end
