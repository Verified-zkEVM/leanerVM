/-
  LeanVM.Protocol.LeanIsa

  The leanISA instance of the M3 model, and the two maps of the adaptor: the committed stack of
  a constraint-system witness, and the witness read back off any stack.
-/

module

public import LeanVM.Protocol.ToClean.ComponentPolynomial
public import LeanVM.Arithmetization.Statement
public import LeanVM.Protocol.Bus
public import LeanVM.Protocol.FixedColumns
public import LeanVM.Protocol.Stack

/-!
# The leanISA instance

The proof system is stated over an abstract `M3Instance`; this module builds the one leanVM
proves, from leanISA's constraint system (`leanIsaEnsemble prog`, Clean), the public program
`prog` and the announced sizes `s`. It is the only place where the proof system meets leanISA,
and it is data: what the adaptor's theorems say of it is in `LeanIsa/Sound.lean` and
`LeanIsa/Complete.lean`.

**Sizes.** `Sizes` is what the prover announces: the memory log-size and the six opcode tables'
row counts (`crates/verifier/src/lib.rs`); the bytecode's log-size is the program's. A table's
log-height is `max(log2_ceil(rows), floor)`, the floor `0` but for `KECCAK`'s `9`
(`TABLE_LOG_FLOORS`, `python-verifier/verifier.py:970`; `KECCAK_MIN_STEPS_LOG`).
`Sizes.Admissible prog s` is the part of the verifier's checks on sizes (`build_layout`,
`verifier.py:973-1013`): the memory window `[16, 32]`, the row cap `2^32`, and the stacked size
`leanIsaμ prog s ≤ 28` (`crates/leanvm_core/src/pcs.rs:49-51`; its floor `15` holds by
construction). `validRate` is the WHIR rate check, read off the same announcement and used by
the commitment, not by the instance.

**The tables.** Nine, in the order of the Rust's global columns
(`crates/leanvm_core/src/cpu/layout.rs:13-27`): the memory columns `MEM_LO, MEM_HI, MEM_TOP,
MFCNT` at height `2^logMem`; the bytecode finalize count `BFCNT` at `2^prog.logSize`; the Keccak
reduction's column `QKECCAK` at `2^(τ_KECCAK + 6)` (`layout.rs:222`, `SLOT_LOG = 6`); then the six
opcode tables at their log-heights, each `Component.toM3` of its Clean component with leanISA's
separators, directions and counted channels (`channelSep`, `channelDir`, the memory and bytecode
pulls). The first three are column groups: no constraint, flush or count, so the table sumcheck
never visits them.

**The bus.** The opcode tables' flushes, and six boundary blocks equal to the interactions of
leanISA's three remaining components: the verifier's state push `(1, 1)` and pull
`(g^(N - 1), 1)` (`leanIsaVerifier`), the memory block's seed push `(g^i, 1, m_i)` and finalize
pull `(g^i, MFCNT_i, m_i)` (`memTable`), and the bytecode block's seed push and finalize pull of
the program's entries (`bytecodeTable`, with the program's eleven entry columns known to both
parties, `Coord.known`; `bytecode_columns`, `layout.rs:291`). The index column is the verifier's
(`idxColumn`), as the Rust's `Coord::Index` is.

**The stack** (`crates/leanvm_core/src/witness.rs:57-96`). Every committed column has a
log-size, its table's; the fifty `KECCAK` value lanes have none (`Placement::VIRTUAL`,
`witness.rs:20`; `layout.rs:227-239`). The committed columns, in global order, are sorted by
log-size, largest first, ties in global order (`stack_offsets`), and laid end to end at aligned
offsets (`Blocks.layout`); the stack has `μ = max(⌈log₂ total⌉, 15)` variables
(`placements_of`). Input lane `l` of the `KECCAK` table is read at slot `l` of `QKECCAK`
(`Blocks.sliceLayout`; `verifier.py:1009`): cell `x` of the lane is cell `x + l · 2^τ_KECCAK` of
the region. The output lanes are *derived* (`derived`): lane `l` at row `x` is lane `l` of the
last twelve rounds of Keccak-f[1600] (`keccakSegment 1`) of the state after twelve rounds that
`QKECCAK` commits for step `x` (slots `25 … 49`, `midState`), so a stack carries no output lane, as
the Rust commits none. This is what the Keccak reduction proves of the claims on them: its first
claim checks the output against the second segment of the committed middle state and the middle
state against the first segment of the input, at the point the table sumcheck drew. With the
Keccak predicate of `M3Holds` (every step's middle state is the first segment of its input), an
output lane is the lane of Keccak-f[1600] of the row's input lanes (`keccakF_eq_segments`). The layout is `Layout.piecewise` of the blocks and the
slices, renamed to the instance's columns; an output lane is routed to its input lane's slice,
a reading no one makes, since the instance reads a derived column through `derived`.

**The public lines** (§8.2). Three: cells `0, 1` of `MEM_LO` are `input₀, input₂`, of `MEM_HI`
are `input₁, input₃`, and of `MEM_TOP` are `0, 0`. None is sent: the verifier computes every
limb's value on its line itself. The third line pins the top limbs, which the statement's words
have zero by type.

**The Keccak region** is `QKECCAK`, with `2^τ_KECCAK` steps: `M3Holds` asks of it that every
step's slots `25 … 49` hold the first twelve rounds of its slots `0 … 24`.

**The maps.** `stackOf s w` stacks the columns a witness `w` carries: the memory and bytecode
blocks' committed cells, the opcode tables' rows, and, as `QKECCAK`, the `KECCAK` rows' input
lanes and their states after twelve rounds (padding steps: the zero state). `witnessOf prog s q`
reads a witness off any stack `q`: the six opcode tables from their rows, the memory block from
the memory columns and the index `g^i`, the bytecode block from the program and `BFCNT`, the
prover data's image from the memory columns, the public input from cells `0, 1` of `MEM_LO,
MEM_HI`. Both are total and computable.

**The bus phase's conditions.** `leanIsa_conditions`: at every size the instance meets
`Bus.Conditions`, so leanVM's master theorems apply to it: the pull side has as many leaves as the
push side (each table pulls as often as it pushes, and the boundary blocks pair up), the count
side has no more (each count is a pull's), and `JUMP`, the one table with constraints, pushes.
With `d = 2` it meets the table sumcheck's degree bound by definition.

The layout, the boundary blocks and the sizes are transcribed from `crates/leanvm_core/src` and
`python-verifier/verifier.py` at leanVM `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`; the instance's
polynomials are Clean's, through `Component.toM3`.

## Wrong readings excluded

* The `KECCAK` value lanes are not committed columns: a stack carrying the input lanes twice
  would let a prover commit lanes different from `QKECCAK`'s, and nothing would tie the bus to
  the permutation (the region is the sole copy, `layout.rs:18-25`).
* The output lanes are not free: an instance reading them off the stack would let a prover flush
  any output, since the Keccak reduction proves the permutation of the inputs, not a committed
  column.
* The output lanes are not Keccak-f[1600] of the input lanes: the reduction's claims are checked
  against the committed middle state at one point, which, without the Keccak predicate on the whole
  region, says nothing of the permutation of the inputs; the predicate is the relation's own clause,
  which the table sumcheck carries to that point (`Spine/KeccakZero.lean`).
* Ties in the stacking order are broken by global index, the shared columns first; a
  tables-first order places a table whose height equals `2^logMem` before the memory columns.
* The memory index column is the verifier's, never a committed column.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization CompPoly CPoly
open CMlPolynomialEval
open Air.Flat (Component EnsembleWitness)

@[expose] public section

namespace LeanIsa

/-! ## The components -/

/-- The six opcode tables, in the ensemble's order. -/
def opcodeComponent : Fin 6 → Component K
  | 0 => ⟨xorTable⟩
  | 1 => ⟨mulTable⟩
  | 2 => ⟨setTable⟩
  | 3 => ⟨derefTable⟩
  | 4 => ⟨jumpTable⟩
  | 5 => ⟨keccakTable⟩

/-- The channels whose coordinate `1` is a read count: the memory and bytecode pulls (§6.2). -/
def counted (c : RawChannel K) : Bool := c.name = MemPull.name || c.name = BytecodePull.name

/-- Opcode table `j` as an M3 table. -/
def opcodeTable (j : Fin 6) : M3Table K Arithmetization.Direction :=
  (opcodeComponent j).toM3 channelSep channelDir counted

/-- The side of the bus a direction flushes on. -/
def sideOf : Arithmetization.Direction → Side
  | .push => .push
  | .pull => .pull

/-! ## Sizes -/

/-- The announced sizes: the memory log-size, positive, and the six opcode tables'
log-heights. -/
structure Sizes where
  /-- The memory log-size `log_mem`. -/
  logMem : ℕ
  /-- The memory has at least two cells. -/
  logMem_pos : 0 < logMem
  /-- The opcode tables' row counts, in the ensemble's order. -/
  rows : Fin 6 → ℕ

/-- An opcode table's log-height: the least `τ` with `rows ≤ 2^τ` (`log2_ceil`), at least the
table's floor (`TABLE_LOG_FLOORS`, `python-verifier/verifier.py:970`): `9` for `KECCAK`, `0`
otherwise. -/
def Sizes.τ (s : Sizes) (j : Fin 6) : ℕ :=
  max (Nat.clog 2 (s.rows j)) (Verifier.tableLogFloors.getD j 0)

/-- An opcode table's rows fit in its height. -/
theorem Sizes.rows_le (s : Sizes) (j : Fin 6) : s.rows j ≤ 2 ^ s.τ j :=
  (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

/-- The `KECCAK` table has at least `2^9` rows (`KECCAK_MIN_STEPS_LOG`). -/
theorem Sizes.minSteps_le (s : Sizes) : Verifier.keccakMinStepsLog ≤ s.τ 5 :=
  le_max_right _ _

/-! ## The tables -/

/-- The index of opcode table `j` among the instance's tables. -/
def opIdx (j : Fin 6) : Fin 9 := ⟨j + 3, by omega⟩

/-- The widths: the four memory columns, `BFCNT`, `QKECCAK`, then the opcode tables'. -/
def width : Fin 9 → ℕ
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨j + 3, h⟩ => (opcodeComponent ⟨j, by omega⟩).width

/-- The log-heights: the memory's, the program's, `QKECCAK`'s `τ_KECCAK + 6`, then the opcode
tables'. -/
def height (prog : Program) (s : Sizes) : Fin 9 → ℕ
  | ⟨0, _⟩ => s.logMem
  | ⟨1, _⟩ => prog.logSize
  | ⟨2, _⟩ => s.τ 5 + 6
  | ⟨j + 3, h⟩ => s.τ ⟨j, by omega⟩

/-- The tables of the instance. -/
def shape (prog : Program) (s : Sizes) : Shape := ⟨9, height prog s, width⟩

/-- The row counts: every row of the memory, bytecode and `QKECCAK` column groups, then the
announced ones. -/
def rows (prog : Program) (s : Sizes) : Fin 9 → ℕ
  | ⟨0, _⟩ => 2 ^ s.logMem
  | ⟨1, _⟩ => 2 ^ prog.logSize
  | ⟨2, _⟩ => 2 ^ (s.τ 5 + 6)
  | ⟨j + 3, h⟩ => s.rows ⟨j, by omega⟩

/-- Every table's rows fit in its height. -/
theorem rows_le (prog : Program) (s : Sizes) : ∀ j, rows prog s j ≤ 2 ^ height prog s j
  | ⟨0, _⟩ => le_rfl
  | ⟨1, _⟩ => le_rfl
  | ⟨2, _⟩ => le_rfl
  | ⟨j + 3, h⟩ => s.rows_le ⟨j, by omega⟩

/-- The constraint polynomials: the opcode tables' only. -/
def constraints : (j : Fin 9) → List (CMvPolynomial (width j) K)
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => []
  | ⟨2, _⟩ => []
  | ⟨j + 3, h⟩ => (opcodeTable ⟨j, by omega⟩).constraints

/-- The flushes: the opcode tables' only, each on its channel's side. -/
def flushes : (j : Fin 9) → List (Side × Vector (CMvPolynomial (width j) K) 16)
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => []
  | ⟨2, _⟩ => []
  | ⟨j + 3, h⟩ => (opcodeTable ⟨j, by omega⟩).flushes.map fun f ↦ (sideOf f.1, f.2)

/-- The count columns: the opcode tables' only. -/
def counts : (j : Fin 9) → List (Fin (width j))
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => []
  | ⟨2, _⟩ => []
  | ⟨j + 3, h⟩ => (opcodeTable ⟨j, by omega⟩).count

/-- Every assert expression of an opcode table has syntactic degree at most two. -/
theorem opcode_constraints_degreeBound :
    ∀ j : Fin 6, ∀ e ∈ (opcodeComponent j).rowOperations.constraints, e.degreeBound ≤ 2 := by
  decide +kernel

/-- Every message coordinate of an opcode table has syntactic degree at most two. -/
theorem opcode_flushes_degreeBound :
    ∀ j : Fin 6, ∀ i ∈ (opcodeComponent j).rowOperations.interactions,
      ∀ e ∈ i.msg.toList, e.degreeBound ≤ 2 := by
  decide +kernel

/-- Every constraint has total degree at most two. -/
theorem constraints_degree : ∀ j, ∀ C ∈ constraints j, C.totalDegree ≤ 2
  | ⟨0, _⟩ => by simp [constraints]
  | ⟨1, _⟩ => by simp [constraints]
  | ⟨2, _⟩ => by simp [constraints]
  | ⟨j + 3, h⟩ => toM3_constraints_degree _ _ _ _ (opcode_constraints_degreeBound ⟨j, by omega⟩)

/-- Every flush coordinate has total degree at most two. -/
theorem flushes_degree : ∀ j, ∀ f ∈ flushes j, ∀ k, (f.2.get k).totalDegree ≤ 2
  | ⟨0, _⟩ => by simp [flushes]
  | ⟨1, _⟩ => by simp [flushes]
  | ⟨2, _⟩ => by simp [flushes]
  | ⟨j + 3, h⟩ => by
    intro f hf k
    obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
    exact toM3_flushes_degree _ _ _ _ (opcode_flushes_degreeBound ⟨j, by omega⟩) f' hf' k

/-! ## The columns -/

/-- A column of the instance: table `j`, column `i`. -/
abbrev Col : Type := Σ j : Fin 9, Fin (width j)

/-- Memory column `i`: `MEM_LO, MEM_HI, MEM_TOP, MFCNT`. -/
def memCol (i : Fin 4) : Col := ⟨⟨0, by decide⟩, i⟩

/-- The bytecode finalize count `BFCNT`. -/
def bfcntCol : Col := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩

/-- The Keccak reduction's column `QKECCAK`. -/
def keccakCol : Col := ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩

/-- The `KECCAK` table has ninety columns. -/
theorem width_keccak : width (opIdx 5) = 90 := by decide +kernel

/-- Input lane `l` of the `KECCAK` table: its column `13 + l`. -/
def inCol (l : Fin 25) : Col := ⟨opIdx 5, ⟨13 + l, by rw [width_keccak]; omega⟩⟩

/-- Output lane `l` of the `KECCAK` table: its column `38 + l`. -/
def outCol (l : Fin 25) : Col := ⟨opIdx 5, ⟨38 + l, by rw [width_keccak]; omega⟩⟩

/-- The column is a `KECCAK` value lane, input or output: not committed (`KECCAK_VALUE_COLS`,
`crates/leanvm_core/src/tables.rs:428-440`). -/
def IsLane (c : Col) : Prop := c.1 = opIdx 5 ∧ 13 ≤ c.2.val ∧ c.2.val < 63

instance (c : Col) : Decidable (IsLane c) := inferInstanceAs (Decidable (_ ∧ _))

/-- The column is a `KECCAK` output lane: derived from the input lanes. -/
def IsOut (c : Col) : Prop := c.1 = opIdx 5 ∧ 38 ≤ c.2.val ∧ c.2.val < 63

instance (c : Col) : Decidable (IsOut c) := inferInstanceAs (Decidable (_ ∧ _))

/-- Every column, in global order: table by table, column by column. -/
def columns : List Col := (List.finRange 9).flatMap fun j ↦ (List.finRange (width j)).map (⟨j, ·⟩)

/-- The committed columns, in global order: every column but the `KECCAK` value lanes. -/
def committedColumns : List Col := columns.filter fun c ↦ !decide (IsLane c)

/-- A column that is not a lane is committed. -/
theorem mem_committedColumns {c : Col} (h : ¬ IsLane c) : c ∈ committedColumns := by
  simp only [committedColumns, columns, List.mem_filter, List.mem_flatMap, List.mem_finRange,
    List.mem_map, true_and, h, decide_false, Bool.not_false, and_true]
  exact ⟨c.1, c.2, rfl⟩

/-! ## The stack -/

variable (prog : Program) (s : Sizes)

/-- The log-height of a column: its table's. -/
abbrev kappa (c : Col) : ℕ := height prog s c.1

/-- The committed columns in stacking order: largest first, ties in global order
(`witness.rs:57-76`; `List.mergeSort` is stable). -/
def stackOrder : List Col :=
  committedColumns.mergeSort fun a b ↦ decide (kappa prog s b ≤ kappa prog s a)

/-- Largest first. -/
theorem stackOrder_pairwise :
    (stackOrder prog s).Pairwise fun a b ↦ decide (kappa prog s b ≤ kappa prog s a) :=
  List.pairwise_mergeSort (fun _ _ _ h₁ h₂ ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _

/-- The committed columns as aligned blocks, in stacking order. -/
def blocks : Blocks where
  n := (stackOrder prog s).length
  size b := kappa prog s (stackOrder prog s)[b]
  descending a b hab := by
    rcases (Fin.le_iff_val_le_val.mp hab).eq_or_lt with h | h
    · rw [Fin.ext h]
    · have := List.pairwise_iff_getElem.mp (stackOrder_pairwise prog s) a b a.isLt b.isLt h
      simp only [decide_eq_true_eq] at this
      exact this

/-- The minimum stacked size, `MIN_MU` (`pcs.rs:49`). -/
def minMu : ℕ := 15

/-- The maximum stacked size, `MAX_MU` (`pcs.rs:51`). -/
def maxMu : ℕ := 28

/-- The stack's number of variables: the blocks' total, rounded up to a power of two, at least
`2 ^ MIN_MU` (`placements_of`, `witness.rs:92`). -/
def leanIsaμ : ℕ := max (Nat.clog 2 (blocks prog s).total) minMu

/-- The blocks fit on the stack. -/
theorem blocks_fits : (blocks prog s).total ≤ 2 ^ leanIsaμ prog s :=
  (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

variable {prog s} in
/-- The block of a committed column. -/
def blockOf (c : Col) (h : ¬ IsLane c) : Fin (blocks prog s).n :=
  ⟨(stackOrder prog s).idxOf c,
    List.idxOf_lt_length_of_mem (List.mem_mergeSort.mpr (mem_committedColumns h))⟩

/-- The block of a committed column holds that column. -/
theorem stackOrder_blockOf (c : Col) (h : ¬ IsLane c) :
    (stackOrder prog s)[(blockOf (prog := prog) (s := s) c h : ℕ)] = c :=
  List.getElem_idxOf _

/-- A committed column's block has the column's log-height. -/
theorem size_blockOf (c : Col) (h : ¬ IsLane c) :
    (blocks prog s).size (blockOf c h) = kappa prog s c := by
  show kappa prog s (stackOrder prog s)[(blockOf (prog := prog) (s := s) c h : ℕ)] = _
  rw [stackOrder_blockOf]

/-- `QKECCAK` is committed. -/
theorem not_isLane_keccakCol : ¬ IsLane keccakCol := by decide

/-- The block of `QKECCAK`. -/
def keccakBlock : Fin (blocks prog s).n := blockOf keccakCol not_isLane_keccakCol

/-- The block of `QKECCAK` has `τ_KECCAK + 6` variables. -/
theorem size_keccakBlock : (blocks prog s).size (keccakBlock prog s) = s.τ 5 + 6 :=
  size_blockOf prog s _ _

/-- The slot of a lane: lane `l`'s, input or output. -/
def laneSlot (c : Col) : Fin 25 := ⟨(c.2.val - 13) % 25, Nat.mod_lt _ (by omega)⟩

/-- Where a column is read: a committed column at its block, a lane at its slot of `QKECCAK`. -/
def route (c : Col) : Fin (blocks prog s).n ⊕ Fin 25 :=
  if h : IsLane c then .inr (laneSlot c) else .inl (blockOf c h)

/-- A route keeps the column's log-height. -/
theorem route_kappa (c : Col) :
    Sum.elim (blocks prog s).size (fun _ ↦ s.τ 5) (route prog s c) = kappa prog s c := by
  unfold route
  split_ifs with h
  · simp only [Sum.elim_inr, kappa, h.1]
    rfl
  · simp only [Sum.elim_inl, size_blockOf]

/-- The layout of the stack: the committed columns at their aligned blocks, lane `l` of the
`KECCAK` table at slot `l` of `QKECCAK`. -/
def layout : Layout (leanIsaμ prog s) Col (kappa prog s) :=
  (((blocks prog s).layout (blocks_fits prog s)).piecewise
    ((blocks prog s).sliceLayout (blocks_fits prog s) (keccakBlock prog s) 6
      (fun l : Fin 25 ↦ (⟨l, by omega⟩ : Fin (2 ^ 6)))
      (κ := fun _ ↦ s.τ 5) fun _ ↦ size_keccakBlock prog s)).comap (route prog s)
    (route_kappa prog s)

/-- A lane has `KECCAK`'s log-height. -/
theorem kappa_of_isLane {c : Col} (h : IsLane c) : kappa prog s c = s.τ 5 := by
  simp only [kappa, h.1]
  rfl

/-- The Keccak region: `QKECCAK`, `2 ^ τ_KECCAK` steps. -/
def keccakRegion : KeccakRegion (shape prog s) := ⟨keccakCol, s.τ 5, rfl⟩

/-- The state after twelve rounds the stack commits at step `x`: slots `25 … 49` of `QKECCAK`. -/
def midState (q : Column (leanIsaμ prog s)) (x : Fin (2 ^ s.τ 5)) : KState :=
  (keccakRegion prog s).state ((layout prog s).read q keccakCol) 25 x

/-- The output column `c`: at row `x`, its lane of the last twelve rounds of Keccak-f[1600] of
the state after twelve rounds committed at step `x` (`midState`). With the Keccak predicate (the
committed state is the first twelve rounds of the row's input lanes), this is the lane of
Keccak-f[1600] of the input lanes (`keccakF_eq_segments`). -/
def outColumn (q : Column (leanIsaμ prog s)) (c : Col) (h : IsOut c) : Column (kappa prog s c) :=
  ⟨Vector.ofFn fun x ↦
    stateLanes (keccakSegment 1 (midState prog s q
      (Fin.cast (congrArg (2 ^ ·) (kappa_of_isLane prog s ⟨h.1, by have := h.2.1; omega, h.2.2⟩))
        x))) ⟨c.2.val - 38, by have := h.2.2; omega⟩⟩

/-- The derived columns: the `KECCAK` output lanes. -/
def derived (c : Col) : Option (Column (leanIsaμ prog s) → Column (kappa prog s c)) :=
  if h : IsOut c then some fun q ↦ outColumn prog s q c h else none

/-! ## The bus -/

/-- Sixteen coordinates: the given ones, then constant zeros. -/
def coords {S : Shape} {κ : ℕ} (cs : List (Coord S κ)) : Vector (Coord S κ) 16 :=
  Vector.ofFn fun k ↦ cs.getD k (.const 0)

/-- Column `k` of the program's entries, `bytecode_columns` (`layout.rs:291`): the entry's
coordinate `k` at every slot, coordinate `3 + k` of the bytecode tuple. -/
def entryColumn (k : Fin 11) : Column prog.logSize :=
  ⟨Vector.ofFn fun i ↦ (entry (prog.code i))[k]⟩

/-- The six boundary blocks (`layout.rs:415-461`): the state boundary, the memory seed and
finalize, the bytecode seed and finalize. -/
def boundary : List (BoundaryBlock (shape prog s)) :=
  let entries : List (Coord (shape prog s) prog.logSize) :=
    (List.finRange 11).map fun k ↦ .known (entryColumn prog k)
  [⟨0, .push, coords [.const (channelSep StatePush.toRaw), .const 1, .const 1]⟩,
    ⟨s.logMem, .push, coords [.const (channelSep MemPush.toRaw), .known (idxColumn s.logMem),
      .const 1, .committed (memCol 0) rfl, .committed (memCol 1) rfl, .committed (memCol 2) rfl]⟩,
    ⟨prog.logSize, .push, coords ([.const (channelSep BytecodePush.toRaw),
      .known (idxColumn prog.logSize), .const 1] ++ entries)⟩,
    ⟨0, .pull, coords [.const (channelSep StatePull.toRaw), .const prog.finalPc, .const 1]⟩,
    ⟨s.logMem, .pull, coords [.const (channelSep MemPull.toRaw), .known (idxColumn s.logMem),
      .committed (memCol 3) rfl, .committed (memCol 0) rfl, .committed (memCol 1) rfl,
      .committed (memCol 2) rfl]⟩,
    ⟨prog.logSize, .pull, coords ([.const (channelSep BytecodePull.toRaw),
      .known (idxColumn prog.logSize), .committed bfcntCol rfl] ++ entries)⟩]

/-- The three public lines (§8.2): `MEM_LO` holds `input₀, input₂` at cells `0, 1`, `MEM_HI`
holds `input₁, input₃`, `MEM_TOP` holds `0, 0`; none is sent. -/
def publicLines (input : PublicInput) : Vector (PublicLine (shape prog s)) 3 :=
  #v[⟨memCol 0, input.lanes 0, input.lanes 2, false, s.logMem_pos⟩,
    ⟨memCol 1, input.lanes 1, input.lanes 3, false, s.logMem_pos⟩,
    ⟨memCol 2, 0, 0, false, s.logMem_pos⟩]

/-- The verifier's padding row of a table, in `K` (`Table.padding`,
`python-verifier/verifier.py:797-803`): zero, but for the `KECCAK` output lanes, which hold
Keccak-f[1600] of the zero state. -/
def padRowK (t : Verifier.Table) : List K :=
  if t.opcode = Verifier.opKeccak then
    t.columns.map fun name ↦
      if name ∈ Verifier.keccakOutputs then
        K.ofBits (Keccak.lane (keccakF (Vector.replicate 25 0))
          (Verifier.keccakOutputs.idxOf name)).toNat
      else 0
  else t.columns.map fun _ ↦ 0

/-- The verifier's padding row is `padRowK`, lifted to `E`. -/
theorem padding_eq_map_ofK (t : Verifier.Table) : t.padding = (padRowK t).map ofK := by
  simp only [Verifier.Table.padding, padRowK]
  split_ifs
  · simp only [List.map_map]
    refine List.map_congr_left fun name _ ↦ ?_
    simp only [Function.comp_apply]
    split_ifs <;> first | rfl | exact (map_zero (algebraMap K E)).symm
  · simp only [List.map_map]
    exact List.map_congr_left fun _ _ ↦ (map_zero (algebraMap K E)).symm

/-! ### The `KECCAK` padding row, by column -/

/-- The output lanes' names are distinct. -/
theorem keccakOutputs_nodup : Verifier.keccakOutputs.Nodup := by decide +kernel

/-- The `KECCAK` table has ninety column names. -/
theorem keccakColumns_length : Verifier.keccakColumns.length = 90 := by decide +kernel

/-- There are twenty-five output lanes. -/
theorem keccakOutputs_length : Verifier.keccakOutputs.length = 25 := by decide +kernel

/-- The `KECCAK` table's column `38 + l` is `KECCAK_OUTPUTS[l]`, and no other column is an output
lane: checked in the kernel. -/
theorem keccakColumns_outputs : ∀ i : Fin 90,
    (Verifier.keccakColumns.getD i "" ∈ Verifier.keccakOutputs ↔ 38 ≤ i.val ∧ i.val < 63) ∧
      (38 ≤ i.val → i.val < 63 →
        Verifier.keccakColumns.getD i "" = Verifier.keccakOutputs.getD (i.val - 38) "") := by
  decide +kernel

/-- Column `38 + l` of the `KECCAK` table is `out_l`, `KECCAK_OUTPUTS[l]`. -/
theorem keccakColumns_out (l : ℕ) (hl : l < 25) :
    Verifier.keccakColumns[38 + l]'(by rw [keccakColumns_length]; omega) =
      Verifier.keccakOutputs[l]'(by rw [keccakOutputs_length]; omega) := by
  have h := (keccakColumns_outputs ⟨38 + l, by omega⟩).2 (by simp) (by simp; omega)
  simp only [Nat.add_sub_cancel_left] at h
  rw [List.getD_eq_getElem _ _ (by rw [keccakColumns_length]; omega),
    List.getD_eq_getElem _ _ (by rw [keccakOutputs_length]; omega)] at h
  exact h

/-- No column of the `KECCAK` table outside `38 … 62` is an output lane. -/
theorem keccakColumns_not_out (i : ℕ) (hi : i < 90) (h : i < 38 ∨ 63 ≤ i) :
    Verifier.keccakColumns[i]'(by rw [keccakColumns_length]; exact hi) ∉
      Verifier.keccakOutputs := by
  have h' := (keccakColumns_outputs ⟨i, hi⟩).1
  rw [List.getD_eq_getElem _ _ (by rw [keccakColumns_length]; exact hi)] at h'
  rw [h']
  show ¬ (38 ≤ i ∧ i < 63)
  omega

/-- The zero state's lanes. -/
theorem laneState_zero : laneState (fun _ ↦ 0) = Vector.replicate 25 0 := by
  apply Vector.ext
  intro i hi
  simp only [laneState, Vector.getElem_ofFn, Vector.getElem_replicate]
  rfl

/-- The `KECCAK` padding row, column by column: the output lanes hold Keccak-f[1600] of the zero
state, every other column zero. -/
theorem padRowK_keccak_getD (i : ℕ) (hi : i < 90) :
    (padRowK (Verifier.tables.getD 5 default)).getD i 0 =
      if h : 38 ≤ i ∧ i < 63 then
        stateLanes (keccakF (laneState fun _ ↦ 0)) ⟨i - 38, by omega⟩
      else 0 := by
  have ht : padRowK (Verifier.tables.getD 5 default) = Verifier.keccakColumns.map fun name ↦
      if name ∈ Verifier.keccakOutputs then
        K.ofBits (Keccak.lane (keccakF (Vector.replicate 25 0))
          (Verifier.keccakOutputs.idxOf name)).toNat
      else 0 := rfl
  have hlt : i < Verifier.keccakColumns.length := by rw [keccakColumns_length]; exact hi
  rw [ht, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
    Option.map_some, Option.getD_some]
  by_cases h : 38 ≤ i ∧ i < 63
  · obtain ⟨l, rfl⟩ : ∃ l, i = 38 + l := ⟨i - 38, by omega⟩
    have hl : l < 25 := by omega
    have hout := keccakColumns_out l hl
    have hmem : Verifier.keccakColumns[38 + l] ∈ Verifier.keccakOutputs :=
      hout ▸ List.getElem_mem _
    rw [ite_eq_left hmem, dite_eq_left h, hout,
      List.Nodup.idxOf_getElem (xs := Verifier.keccakOutputs) keccakOutputs_nodup l,
      laneState_zero]
    simp only [stateLanes, K.ofLane, K.ofBits, Nat.add_sub_cancel_left]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp
  · rw [ite_eq_right (keccakColumns_not_out i hi (by omega)), dite_eq_right h]

/-- The public row a padding row holds: the verifier's (`padRowK`) for an opcode table, zero for
the column groups, which have no padding row. -/
def padRow (j : Fin 9) (i : Fin (width j)) : K :=
  if 3 ≤ j.val then (padRowK (Verifier.tables.getD (j.val - 3) default)).getD i 0 else 0

/-- Off the `KECCAK` table, the padding row is zero. -/
theorem padRow_of_ne_keccak :
    ∀ j : Fin 6, j ≠ 5 → ∀ i : Fin (width (opIdx j)), padRow (opIdx j) i = 0 := by
  decide +kernel

/-- The `KECCAK` padding row: Keccak-f[1600] of the zero state at the output lanes, zero
elsewhere. -/
theorem padRow_keccak (i : Fin (width (opIdx 5))) :
    padRow (opIdx 5) i = if h : 38 ≤ i.val ∧ i.val < 63 then
      stateLanes (keccakF (laneState fun _ ↦ 0)) ⟨i.val - 38, by omega⟩ else 0 :=
  padRowK_keccak_getD i.val (width_keccak ▸ i.isLt)

end LeanIsa

open LeanIsa

/-- The leanISA instance of the public program `prog` at the announced sizes `s`. -/
abbrev leanIsaInstance (prog : Program) (s : Sizes) : M3Instance where
  toShape := shape prog s
  Stmt := PublicInput
  constraints := constraints
  flushes := flushes
  d := 2
  constraints_degree := constraints_degree
  flushes_degree := flushes_degree
  counts := counts
  rows := rows prog s
  rows_le := rows_le prog s
  padRow := padRow
  boundary := boundary prog s
  μ := leanIsaμ prog s
  layout := layout prog s
  derived := derived prog s
  nLines := 3
  publicLines := publicLines prog s
  keccak := some (keccakRegion prog s)

namespace LeanIsa

/-! ## Admissible sizes -/

/-- The checks the verifier makes of the announced sizes (`build_layout`,
`python-verifier/verifier.py:891`, and `:1392`): the memory window, the row cap, and the stacked
size's cap. The bytecode cap is `Program`'s by type, and the stacked size's floor holds by construction
(`leanIsaμ`). -/
def Sizes.Admissible (prog : Program) (s : Sizes) : Prop :=
  minLogMem ≤ s.logMem ∧ s.logMem ≤ maxLogMem ∧ (∀ j, s.rows j ≤ 2 ^ maxLogRows) ∧
    leanIsaμ prog s ≤ maxMu

instance (prog : Program) (s : Sizes) : Decidable (s.Admissible prog) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The WHIR rate check (`pcs/src/whir_config.rs:43-55`): the inverse rate's logarithm is in
`[1, 4]`. A parameter of the commitment, read off the same announcement. -/
def validRate (ρ : ℕ) : Prop := 1 ≤ ρ ∧ ρ ≤ 4

instance (ρ : ℕ) : Decidable (validRate ρ) := inferInstanceAs (Decidable (_ ∧ _))

/-- The sizes a witness carries: the memory log-size of its image and the row counts of its six
opcode tables; none when the image has a single word. -/
def Sizes.ofWitness {prog : Program} (w : EnsembleWitness (leanIsaEnsemble prog)) :
    Option Sizes :=
  if h : 0 < (imageOf w.data).1 then
    some ⟨_, h, fun j ↦ (tableAt w ⟨j, by omega⟩).table.length⟩
  else none

/-! ## The witness read off a stack -/

section WitnessOf

variable (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- Cell `x` of column `c`, read off the stack. -/
abbrev cell (c : Col) (x : Fin (2 ^ kappa prog s c)) : K :=
  ((leanIsaInstance prog s).column q c).values.get x

/-- The executed rows of opcode table `j`, read off the stack: its padding rows are not the
witness's. -/
def opcodeRows (j : Fin 6) : List (Array K) :=
  List.ofFn fun x : Fin (s.rows j) ↦
    Array.ofFn ((leanIsaInstance prog s).row q (opIdx j) (Fin.castLE (s.rows_le j) x))

/-- The memory block's rows: the index `g^x`, the finalize count `MFCNT`, the three limbs. -/
def memBlockRowsOf : List (Array K) :=
  List.ofFn fun x : Fin (2 ^ s.logMem) ↦ (toElements (⟨gpow x, cell prog s q (memCol 3) x,
    #v[cell prog s q (memCol 0) x, cell prog s q (memCol 1) x,
      cell prog s q (memCol 2) x]⟩ : MemRow K)).toArray

/-- The bytecode block's rows: the program's, with the finalize counts `BFCNT`. -/
def bytecodeBlockRowsOf : List (Array K) :=
  List.ofFn fun i : Fin (2 ^ prog.logSize) ↦
    (toElements (bytecodeRowOf prog i (cell prog s q bfcntCol i))).toArray

/-- The memory image: the three limb columns, word by word. -/
def imageRows : Array (Vector K 3) :=
  Array.ofFn fun x : Fin (2 ^ s.logMem) ↦
    #v[cell prog s q (memCol 0) x, cell prog s q (memCol 1) x, cell prog s q (memCol 2) x]

/-- Prover data whose one table is the memory image, `"mem"`. -/
def dataOf (mem : Array (Vector K 3)) : ProverData K := fun name n ↦
  if h : name = memDataName ∧ n = 3 then h.2 ▸ mem else #[]

/-- Cell `0` of a memory column. -/
def cell0 (i : Fin 4) : K := cell prog s q (memCol i) ⟨0, Nat.two_pow_pos _⟩

/-- Cell `1` of a memory column. -/
def cell1 (i : Fin 4) : K := cell prog s q (memCol i) ⟨1, Nat.one_lt_two_pow s.logMem_pos.ne'⟩

/-- The public input: cells `0` and `1` of `MEM_LO` and `MEM_HI`. -/
def publicInputOf : PublicIO K :=
  ⟨#v[cell0 prog s q 0, cell0 prog s q 1, cell1 prog s q 0, cell1 prog s q 1]⟩

/-- The memory block has five columns. -/
theorem width_memTable : (⟨memTable⟩ : Component K).width = 5 := by decide +kernel

/-- The bytecode block has thirteen columns. -/
theorem width_bytecodeTable : (⟨bytecodeTable⟩ : Component K).width = 13 := by decide +kernel

/-- A table of the witness: a component, its rows of its width, the data. -/
def tableOf (c : Component K) (rows : List (Array K)) (data : ProverData K)
    (h : ∀ r ∈ rows, r.size = c.width) : Air.Flat.Table K :=
  ⟨c, c.width, rows, data, h⟩

/-- The witness a stack carries: the six opcode tables from their rows, the memory and
bytecode blocks from the memory columns, the program and `BFCNT`, the image from the memory
columns, the public input from the first two cells of `MEM_LO` and `MEM_HI`. -/
def witnessOf : EnsembleWitness (leanIsaEnsemble prog) :=
  let data := dataOf (imageRows prog s q)
  let op (j : Fin 6) : Air.Flat.Table K :=
    tableOf (opcodeComponent j) (opcodeRows prog s q j) data (by
      simp only [opcodeRows, List.mem_ofFn, forall_exists_index]
      rintro _ x rfl
      exact Array.size_ofFn)
  { tables := [op 0, op 1, op 2, op 3, op 4, op 5,
      tableOf ⟨memTable⟩ (memBlockRowsOf prog s q) data (by
        simp only [memBlockRowsOf, List.mem_ofFn, forall_exists_index]
        rintro _ x rfl
        rw [Vector.size_toArray, width_memTable]
        rfl),
      tableOf ⟨bytecodeTable⟩ (bytecodeBlockRowsOf prog s q) data (by
        simp only [bytecodeBlockRowsOf, List.mem_ofFn, forall_exists_index]
        rintro _ x rfl
        rw [Vector.size_toArray, width_bytecodeTable]
        rfl)]
    data := data
    publicInput := publicInputOf prog s q
    same_length := rfl
    same_circuits := fun i hi ↦ by
      change i < 8 at hi
      interval_cases i <;> rfl
    same_data := by simp [tableOf, op] }

end WitnessOf

/-! ## The stack of a witness -/

section StackOf

variable (prog : Program) (s : Sizes)

/-- Cell `i` of row `x` of a table, `0` when missing. -/
def cellOf (t : Air.Flat.Table K) (x i : ℕ) : K := ((t.table[x]?).bind (·[i]?)).getD 0

/-- The memory block's cell of memory column `i`: the limbs at `2, 3, 4`, `MFCNT` at `1`. -/
def memRowCell : Fin 4 → ℕ := ![2, 3, 4, 1]

/-- Input lane `l` of row `x` of the `KECCAK` table; a padding row's is zero (`padRow`). -/
def inLaneOf (w : EnsembleWitness (leanIsaEnsemble prog)) (x : ℕ) (l : Fin 25) : K :=
  if x < s.rows 5 then cellOf (tableAt w 5) x (13 + l) else 0

/-- `QKECCAK` of a witness (`crates/leanvm_core/src/keccak.rs`): slot `l < 25` of step `x` is
input lane `l` of row `x`, slot `25 + l` lane `l` of its state after twelve rounds, the other
slots zero. -/
def keccakWitness (w : EnsembleWitness (leanIsaEnsemble prog)) : Vector K (2 ^ (s.τ 5 + 6)) :=
  Vector.ofFn fun i ↦
    if h : i.val / 2 ^ s.τ 5 < 25 then inLaneOf prog s w (i.val % 2 ^ s.τ 5) ⟨_, h⟩
    else if h' : i.val / 2 ^ s.τ 5 < 50 then
      stateLanes (keccakSegment 0 (laneState (inLaneOf prog s w (i.val % 2 ^ s.τ 5))))
        ⟨i.val / 2 ^ s.τ 5 - 25, by omega⟩
    else 0

/-- The column `c` a witness carries: the memory and bytecode blocks' committed cells,
`QKECCAK` of the `KECCAK` rows, the opcode tables' cells. -/
def witnessColumn (w : EnsembleWitness (leanIsaEnsemble prog)) :
    (c : Col) → Vector K (2 ^ kappa prog s c)
  | ⟨⟨0, _⟩, i⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w 6) x (memRowCell i)
  | ⟨⟨1, _⟩, _⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w 7) x 1
  | ⟨⟨2, _⟩, _⟩ => keccakWitness prog s w
  | ⟨⟨j + 3, h⟩, i⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w ⟨j, by omega⟩) x i

/-- The stack of a witness at the sizes `s`: its committed columns at their blocks, zero past
the last. -/
def stackOf (w : EnsembleWitness (leanIsaEnsemble prog)) : Column (leanIsaμ prog s) :=
  (blocks prog s).stackColumn (fun b ↦ witnessColumn prog s w (stackOrder prog s)[b])
    (leanIsaμ prog s)

end StackOf

end LeanIsa

/-! ## The bus phase's conditions -/

namespace LeanIsa

/-- Summing over a list with repetitions. -/
private theorem sum_flatMap_replicate {α : Type} (l : List α) (a : α → ℕ) (f : α → ℕ)
    (g : ℕ → ℕ) :
    ((l.flatMap fun x ↦ List.replicate (a x) (f x)).map g).sum =
      (l.map fun x ↦ a x * g (f x)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_replicate,
      List.sum_replicate, smul_eq_mul, List.map_cons, List.sum_cons]

/-- Every table has at most as many count columns as push flushes. -/
theorem counts_le_pushes : ∀ j : Fin 9,
    (counts j).length ≤ ((flushes j).filter fun f ↦ decide (f.1 = Side.push)).length := by
  decide +kernel

/-- A table with a constraint has a push flush. -/
theorem constrained_pushes : ∀ j : Fin 9, 0 < (LeanIsa.constraints j).length →
    0 < ((LeanIsa.flushes j).filter fun f ↦ decide (f.1 = Side.push)).length := by
  decide +kernel

variable (prog : Program) (s : Sizes)

/-- A side's leaf count, from its blocks' log-heights. -/
private theorem leafCount_eq (I : M3Instance) (k : Fin 3) :
    Bus.leafCount I k = (((Bus.sources I k).map Bus.Source.κ).map (2 ^ ·)).sum := by
  rw [Bus.leafCount, List.map_map]
  rfl

/-- The leaves of the push side, by table. -/
private theorem leafCount_push :
    Bus.leafCount (leanIsaInstance prog s) 0 =
      (((boundary prog s).filter fun b ↦ decide (b.side = .push)).map fun b ↦ 2 ^ b.κ).sum +
      ((List.finRange 9).map fun j ↦
        ((LeanIsa.flushes j).filter fun f ↦ decide (f.1 = Side.push)).length *
          2 ^ height prog s j).sum := by
  rw [leafCount_eq]
  change ((((Bus.sideSources _ .push).map Bus.Source.κ).map (2 ^ ·))).sum = _
  rw [Bus.sideSources_map_κ, List.map_append, List.sum_append, sum_flatMap_replicate,
    List.map_map]
  rfl

/-- The pull side has as many leaves as the push side: a table pulls as often as it pushes, and the
boundary blocks pair up. -/
private theorem leafCount_pull :
    Bus.leafCount (leanIsaInstance prog s) 1 = Bus.leafCount (leanIsaInstance prog s) 0 := by
  rw [leafCount_push, leafCount_eq]
  change ((((Bus.sideSources _ .pull).map Bus.Source.κ).map (2 ^ ·))).sum = _
  rw [Bus.sideSources_map_κ, List.map_append, List.sum_append, sum_flatMap_replicate,
    List.map_map]
  congr 1

/-- The count side has at most as many leaves as the push side. -/
private theorem leafCount_count_le :
    Bus.leafCount (leanIsaInstance prog s) 2 ≤ Bus.leafCount (leanIsaInstance prog s) 0 := by
  rw [leafCount_push, leafCount_eq]
  change ((((Bus.countSources _).map Bus.Source.κ).map (2 ^ ·))).sum ≤ _
  rw [Bus.countSources_map_κ, sum_flatMap_replicate]
  refine le_add_left (List.sum_le_sum fun j _ ↦ ?_)
  exact Nat.mul_le_mul_right _ (counts_le_pushes j)

/-- Every flush's first coordinate is its channel's separator, a constant. -/
theorem flushes_separator : ∀ j : Fin 9, ∀ g ∈ LeanIsa.flushes j, ∀ r r' : Fin (width j) → K,
    (g.2[0]).eval r = (g.2[0]).eval r'
  | ⟨0, _⟩ => by simp [LeanIsa.flushes]
  | ⟨1, _⟩ => by simp [LeanIsa.flushes]
  | ⟨2, _⟩ => by simp [LeanIsa.flushes]
  | ⟨j + 3, h⟩ => by
    intro g hg r r'
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact toM3_separator _ _ _ _ hg' r r'

/-- The leanISA instance meets the bus phase's side conditions, at every size. -/
theorem leanIsa_conditions : Bus.Conditions (leanIsaInstance prog s) where
  one_le_d := by norm_num
  constrained j hj := by
    have hfit : Bus.leafCount (leanIsaInstance prog s) 0 ≤ 2 ^ (leanIsaInstance prog s).μBus :=
      (Bus.blocks_total _ 0).symm.trans_le (Bus.push_fits _)
    have hpos := constrained_pushes j (List.length_pos_iff.mpr hj)
    refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (le_trans ?_ hfit)
    rw [leafCount_push]
    refine le_add_left ((Nat.le_mul_of_pos_left _ hpos).trans ?_)
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  pull_fits := by
    rw [leafCount_pull, ← Bus.blocks_total]
    exact Bus.push_fits _
  count_fits := (leafCount_count_le prog s).trans
    ((Bus.blocks_total _ 0).symm.trans_le (Bus.push_fits _))
  separator j f r r' := flushes_separator j _ (List.getElem_mem f.isLt) r r'

end LeanIsa

end
end LeanVM.Protocol
