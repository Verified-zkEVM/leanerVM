/-
  LeanerVM.Protocol.LeanIsa

  The leanISA instance of the M3 model, and the two maps of the adaptor: the committed stack of
  a constraint-system witness, and the witness read back off any stack.
-/

module

public import LeanerVM.Protocol.ToClean.ComponentPolynomial
public import LeanerVM.Arithmetization.Statement
public import LeanerVM.Protocol.FixedColumns
public import LeanerVM.Protocol.FlockSpec
public import LeanerVM.Protocol.Stack

/-!
# The leanISA instance

The proof system is stated over an abstract `M3Instance`; this module builds the one leanVM
proves, from leanISA's constraint system (`leanIsaEnsemble prog κ`, Clean), the public program
`prog`, the announced sizes `s` and a Flock specification `F`. It is the only place where the
proof system meets leanISA, and it is data: what the adaptor's theorems say of it is in
`LeanIsa/Sound.lean` and `LeanIsa/Complete.lean`.

**Sizes.** `Sizes` is what the prover announces: the memory log-size and the six opcode tables'
log-heights (`cpu/mod.rs:144-149`, `read_public`); the bytecode's log-size is the program's.
`Sizes.Admissible prog s` is the part of `read_public`'s checks on sizes (`:157-176`): the
memory window `[16, 32]`, the height cap `32`, the `BLAKE2S` floor `3`, and the stacked size
`leanIsaμ prog s ≤ 28` (`pcs.rs:49-51`; its floor `15` holds by construction). `validRate` is the
WHIR rate check (`pcs/src/whir_config.rs:43-55`), read off the same announcement and used by
the commitment, not by the instance.

**The tables.** Nine, in the order of the Rust's global columns (`cpu/layout.rs:13-49`): the
memory columns `MEM_LO, MEM_HI, MEM_TOP, MFCNT` at height `2^logMem`; the bytecode finalize
count `BFCNT` at `2^prog.logSize`; the Flock region `QFLOCK` at `2^(8 + τ_BLAKE2S)`
(`layout.rs:151-157`, `qflock_kappa`); then the six opcode tables at their announced heights,
each `Component.toM3` of its Clean component with leanISA's separators and counted interactions
(`channelSep`; the memory and bytecode pulls), each flush on the side of its interaction's
direction. The first three are column
groups: no constraint, flush or count, so the table sumcheck never visits them.

**The bus.** The opcode tables' flushes, and six boundary blocks written from the Rust's
(`layout.rs:349-395`) and equal to the interactions of leanISA's three remaining components:
the verifier's state push `(1, 1)` and pull `(g^(N - 1), 1)` (`leanIsaVerifier`), the memory
block's seed push `(g^i, 1, m_i)` and finalize pull `(g^i, MFCNT_i, m_i)` (`memTable`), and the
bytecode block's seed push and finalize pull of the program's entries (`bytecodeTable`, with the
program's eight entry columns known to both parties, `Coord.known`). The index column is the
verifier's (`idxColumn`), as the Rust's `Coord::Index` is.

**The stack** (`witness.rs:67-101`). Every committed column has a log-size, its table's; the
eighteen `BLAKE2S` limb columns have none (`Placement::VIRTUAL`, `witness.rs:21-29`;
`layout.rs:160-168`). The committed columns, in global order, are sorted by log-size, largest first,
ties in global order (`stack_offsets`), and laid end to end at aligned offsets (`Blocks.layout`);
the stack has `μ = max(⌈log₂ total⌉, 15)` variables (`placements_of`). Limb `k` of the `BLAKE2S`
table is read at the strided slot `F.slot k` of the Flock region (`Blocks.stridedLayout`;
`hash_flock.rs:79-115`): row `t`'s limb is cell `F.slot k` of block `t`. The layout is
`Layout.piecewise` of the two, renamed to the instance's columns; no two columns share a cell except
the limbs and the region they are read from, as the Rust routes them.

**The public lines** (§8.2). Three: cells `0, 1` of `MEM_LO` are `input₀, input₂` and of
`MEM_HI` are `input₁, input₃`, both sent; cells `0, 1` of `MEM_TOP` are `0, 0`, not sent. The
third line pins the top limbs, which the statement's words have zero by type.

**The Flock region** is `QFLOCK`, with `kBatch = τ_BLAKE2S` and `F`'s R1CS.

**The maps.** `stackOf F s w` stacks the columns a witness `w` carries: the memory and bytecode
blocks' committed cells, the opcode tables' rows, and `F.gen` of the `BLAKE2S` rows' limbs as the
Flock region. `witnessOf F prog s q`, a witness of `leanIsaEnsemble prog s.logMem`, reads one off
any stack `q`: the six opcode tables from their rows, the memory block from the memory columns
and its fixed index `g^i`, the bytecode block from its fixed program columns and `BFCNT`, the
public input from cells `0, 1` of `MEM_LO, MEM_HI`; the prover data, and so the image, is
derived from the memory block (`witnessOfTables`). A table holds at most `2^64` rows (Clean's
row indices), so a table taller than that is read as empty; within the caps none is. Both maps
are total and computable.

**The bus phase's conditions** are `LeanIsa/Conditions.lean`'s `leanIsa_conditions`. With
`d = 2` the instance meets the table sumcheck's degree bound by definition.

Category B for the layout, the boundary blocks and the sizes, transcribed from
`crates/lean_vm/src` at `a386121f84292f6fa663aaa3e570c15bc0240ea2`; the instance's
polynomials are Clean's, through `Component.toM3`.

## Wrong readings excluded

* The `BLAKE2S` limbs are not committed columns: a stack carrying them twice would let a
  prover commit limbs different from the Flock region's, and nothing would tie the bus to the
  compression (the region is the sole copy, `layout.rs:20-26`).
* Ties in the stacking order are broken by global index, the shared columns first; a
  tables-first order places a table whose height equals `2^logMem` before the memory columns.
* The memory index column is the verifier's, never a committed column.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization CompPoly CPoly
open CMlPolynomialEval
open Air.Flat (Component EnsembleWitness)

@[expose] public section

namespace LeanIsa

/-! ## The components -/

/-- The six opcode tables, in the ensemble's order. -/
def opcodeComponent : Fin 6 → Component K :=
  ![xorComponent, mulComponent, setComponent, derefComponent, jumpComponent, blake2sComponent]

/-- The interactions whose coordinate `1` is a read count: the memory and bytecode pulls
(§6.2). -/
def counted (i : AbstractInteraction K) : Bool :=
  (i.channel.name = MemChannel.name || i.channel.name = BytecodeChannel.name) &&
    i.direction == .pull

/-- Opcode table `j` as an M3 table, each flush with its interaction's direction. -/
def opcodeTable (j : Fin 6) : M3Table K BusDir :=
  (opcodeComponent j).toM3 channelSep (·.direction) counted

/-- The side of the bus a direction flushes on. -/
def sideOf : BusDir → Side
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
  /-- The opcode tables' log-heights, in the ensemble's order. -/
  τ : Fin 6 → ℕ

/-! ## The tables -/

/-- The index of opcode table `j` among the instance's tables. -/
def opIdx (j : Fin 6) : Fin 9 := ⟨j + 3, by omega⟩

/-- The widths: the four memory columns, `BFCNT`, `QFLOCK`, then the opcode tables'. -/
def width : Fin 9 → ℕ
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨j + 3, h⟩ => (opcodeComponent ⟨j, by omega⟩).width

/-- The log-heights: the memory's, the program's, the Flock region's `8 + τ_BLAKE2S`, then the
announced ones. -/
def height (prog : Program) (s : Sizes) : Fin 9 → ℕ
  | ⟨0, _⟩ => s.logMem
  | ⟨1, _⟩ => prog.logSize
  | ⟨2, _⟩ => 8 + s.τ 5
  | ⟨j + 3, h⟩ => s.τ ⟨j, by omega⟩

/-- The tables of the instance. -/
def shape (prog : Program) (s : Sizes) : Shape := ⟨9, height prog s, width⟩

/-- The constraint polynomials: the opcode tables' only. -/
def constraints : (j : Fin 9) → List (CMvPolynomial (width j) K)
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => []
  | ⟨j + 3, h⟩ => (opcodeTable ⟨j, by omega⟩).constraints

/-- The flushes: the opcode tables' only, each on its channel's side. -/
def flushes : (j : Fin 9) → List (Side × Vector (CMvPolynomial (width j) K) 16)
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => []
  | ⟨j + 3, h⟩ => (opcodeTable ⟨j, by omega⟩).flushes.map fun f ↦ (sideOf f.1, f.2)

/-- The count columns: the opcode tables' only. -/
def counts : (j : Fin 9) → List (Fin (width j))
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => []
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
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => by simp [constraints]
  | ⟨j + 3, h⟩ => toM3_constraints_degree _ _ _ _ (opcode_constraints_degreeBound ⟨j, by omega⟩)

/-- Every flush coordinate has total degree at most two. -/
theorem flushes_degree : ∀ j, ∀ f ∈ flushes j, ∀ k, (f.2.get k).totalDegree ≤ 2
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => by simp [flushes]
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

/-- The Flock region `QFLOCK`. -/
def flockCol : Col := ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩

/-- The `BLAKE2S` table has thirty-seven columns. -/
theorem width_blake2s : width (opIdx 5) = 37 := by decide +kernel

/-- Limb `k` of the `BLAKE2S` table: its column `9 + k`, in the order `m0, m1, m2, m3, out0,
out1, cv0, cv1, md`, low limb first. -/
def limbCol (k : Fin 18) : Col := ⟨opIdx 5, ⟨9 + k, by rw [width_blake2s]; omega⟩⟩

/-- The column is a `BLAKE2S` limb: not committed, read off the Flock region. -/
def IsLimb (c : Col) : Prop := c.1 = opIdx 5 ∧ 9 ≤ c.2.val ∧ c.2.val < 27

instance (c : Col) : Decidable (IsLimb c) := inferInstanceAs (Decidable (_ ∧ _))

/-- Every column, in global order: table by table, column by column. -/
def columns : List Col := (List.finRange 9).flatMap fun j ↦ (List.finRange (width j)).map (⟨j, ·⟩)

/-- The committed columns, in global order: every column but the limbs. -/
def committedColumns : List Col := columns.filter fun c ↦ !decide (IsLimb c)

/-- A column that is not a limb is committed. -/
theorem mem_committedColumns {c : Col} (h : ¬ IsLimb c) : c ∈ committedColumns := by
  simp only [committedColumns, columns, List.mem_filter, List.mem_flatMap, List.mem_finRange,
    List.mem_map, true_and, h, decide_false, Bool.not_false, and_true]
  exact ⟨c.1, c.2, rfl⟩

/-! ## The stack -/

variable (prog : Program) (s : Sizes)

/-- The log-height of a column: its table's. -/
abbrev kappa (c : Col) : ℕ := height prog s c.1

/-- The committed columns in stacking order: largest first, ties in global order
(`witness.rs:67-81`; `List.mergeSort` is stable). -/
def stackOrder : List Col :=
  committedColumns.mergeSort fun a b ↦ decide (kappa prog s b ≤ kappa prog s a)

/-- Largest first. -/
theorem stackOrder_pairwise :
    (stackOrder prog s).Pairwise fun a b ↦ decide (kappa prog s b ≤ kappa prog s a) :=
  List.pairwise_mergeSort (fun _ _ _ h₁ h₂ ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _

/-- The log-heights along the stacking order are antitone. -/
theorem stackOrder_antitone :
    Antitone fun b : Fin (stackOrder prog s).length ↦ kappa prog s (stackOrder prog s)[b] := by
  intro a b hab
  rcases (Fin.le_iff_val_le_val.mp hab).eq_or_lt with h | h
  · rw [Fin.ext h]
  · have := List.pairwise_iff_getElem.mp (stackOrder_pairwise prog s) a b a.isLt b.isLt h
    simp only [decide_eq_true_eq] at this
    exact this

/-- The committed columns as aligned blocks, in stacking order. -/
def blocks : Blocks where
  n := (stackOrder prog s).length
  size b := kappa prog s (stackOrder prog s)[b]
  descending := stackOrder_antitone prog s

/-- The minimum stacked size, `MIN_MU` (`pcs.rs:49`). -/
def minMu : ℕ := 15

/-- The maximum stacked size, `MAX_MU` (`pcs.rs:51`). -/
def maxMu : ℕ := 28

/-- The stack's number of variables: the blocks' total, rounded up to a power of two, at least
`2 ^ MIN_MU` (`placements_of`, `witness.rs:97`). -/
def leanIsaμ : ℕ := max (Nat.clog 2 (blocks prog s).total) minMu

/-- The blocks fit on the stack. -/
theorem blocks_fits : (blocks prog s).total ≤ 2 ^ leanIsaμ prog s :=
  (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

variable {prog s} in
/-- The block of a committed column. -/
def blockOf (c : Col) (h : ¬ IsLimb c) : Fin (blocks prog s).n :=
  ⟨(stackOrder prog s).idxOf c,
    List.idxOf_lt_length_of_mem (List.mem_mergeSort.mpr (mem_committedColumns h))⟩

/-- The block of a committed column holds that column. -/
theorem stackOrder_blockOf (c : Col) (h : ¬ IsLimb c) :
    (stackOrder prog s)[(blockOf (prog := prog) (s := s) c h : ℕ)] = c :=
  List.getElem_idxOf _

/-- A committed column's block has the column's log-height. -/
theorem size_blockOf (c : Col) (h : ¬ IsLimb c) :
    (blocks prog s).size (blockOf c h) = kappa prog s c := by
  show kappa prog s (stackOrder prog s)[(blockOf (prog := prog) (s := s) c h : ℕ)] = _
  rw [stackOrder_blockOf]

/-- The Flock region is committed. -/
theorem not_isLimb_flockCol : ¬ IsLimb flockCol := by decide

/-- The block of the Flock region. -/
def flockBlock : Fin (blocks prog s).n := blockOf flockCol not_isLimb_flockCol

/-- The Flock region's block has `8 + τ_BLAKE2S` variables. -/
theorem size_flockBlock : (blocks prog s).size (flockBlock prog s) = 8 + s.τ 5 :=
  size_blockOf prog s _ _

/-- Where a column is read: a committed column at its block, a limb at its slot. -/
def route (c : Col) : Fin (blocks prog s).n ⊕ Fin 18 :=
  if h : IsLimb c then .inr ⟨c.2.val - 9, by have := h.2.2; omega⟩ else .inl (blockOf c h)

/-- A route keeps the column's log-height. -/
theorem route_kappa (c : Col) :
    Sum.elim (blocks prog s).size (fun _ ↦ s.τ 5) (route prog s c) = kappa prog s c := by
  unfold route
  split_ifs with h
  · simp only [Sum.elim_inr, kappa, h.1]
    rfl
  · simp only [Sum.elim_inl, size_blockOf]

/-- The layout of the stack: the committed columns at their aligned blocks, limb `k` of the
`BLAKE2S` table at the strided slot `slot k` of the Flock region. -/
def layout (slot : Fin 18 → Fin 256) : Layout (leanIsaμ prog s) Col (kappa prog s) :=
  (((blocks prog s).layout (blocks_fits prog s)).piecewise
    ((blocks prog s).stridedLayout (blocks_fits prog s) (flockBlock prog s) 8 slot
      (κ := fun _ ↦ s.τ 5) fun _ ↦ size_flockBlock prog s)).comap (route prog s)
    (route_kappa prog s)

/-! ## The bus -/

/-- Sixteen coordinates: the given ones, then constant zeros. -/
def coords {S : Shape} {κ : ℕ} (cs : List (Coord S κ)) : Vector (Coord S κ) 16 :=
  Vector.ofFn fun k ↦ cs.getD k (.const 0)

/-- Column `k` of the program's entries, `bytecode_columns` (`layout.rs:229-290`): the entry's
coordinate `k + 1` of the bytecode tuple at every slot. -/
def entryColumn (k : Fin 8) : Column prog.logSize :=
  ⟨Vector.ofFn fun i ↦ (entry (prog.code i))[k]⟩

/-- The six boundary blocks (`layout.rs:349-395`): the state boundary, the memory seed and
finalize, the bytecode seed and finalize. -/
def boundary : List (BoundaryBlock (shape prog s)) :=
  let entries : List (Coord (shape prog s) prog.logSize) :=
    (List.finRange 8).map fun k ↦ .known (entryColumn prog k)
  [⟨0, .push, coords [.const (channelSep StateChannel.toRaw), .const 1, .const 1]⟩,
    ⟨s.logMem, .push, coords [.const (channelSep MemChannel.toRaw), .known (idxColumn s.logMem),
      .const 1, .committed (memCol 0) rfl, .committed (memCol 1) rfl, .committed (memCol 2) rfl]⟩,
    ⟨prog.logSize, .push, coords ([.const (channelSep BytecodeChannel.toRaw),
      .known (idxColumn prog.logSize), .const 1] ++ entries)⟩,
    ⟨0, .pull, coords [.const (channelSep StateChannel.toRaw), .const prog.finalPc, .const 1]⟩,
    ⟨s.logMem, .pull, coords [.const (channelSep MemChannel.toRaw), .known (idxColumn s.logMem),
      .committed (memCol 3) rfl, .committed (memCol 0) rfl, .committed (memCol 1) rfl,
      .committed (memCol 2) rfl]⟩,
    ⟨prog.logSize, .pull, coords ([.const (channelSep BytecodeChannel.toRaw),
      .known (idxColumn prog.logSize), .committed bfcntCol rfl] ++ entries)⟩]

/-- The three public lines (§8.2): `MEM_LO` holds `input₀, input₂` at cells `0, 1`, `MEM_HI`
holds `input₁, input₃`, both sent; `MEM_TOP` holds `0, 0`, not sent. -/
def publicLines (input : PublicInput) : Vector (PublicLine (shape prog s)) 3 :=
  #v[⟨memCol 0, input.lanes 0, input.lanes 2, true, s.logMem_pos⟩,
    ⟨memCol 1, input.lanes 1, input.lanes 3, true, s.logMem_pos⟩,
    ⟨memCol 2, 0, 0, false, s.logMem_pos⟩]

/-- The Flock region: `QFLOCK`, `2 ^ τ_BLAKE2S` blocks, with the specification's R1CS. -/
def flockRegion (F : FlockSpec) : FlockRegion (shape prog s) := ⟨flockCol, s.τ 5, rfl, F.r1cs⟩

end LeanIsa

open LeanIsa

/-- The leanISA instance of the public program `prog` at the announced sizes `s`, with the
Flock specification `F`. -/
abbrev leanIsaInstance (F : FlockSpec) (prog : Program) (s : Sizes) : M3Instance where
  toShape := shape prog s
  Stmt := PublicInput
  constraints := constraints
  flushes := flushes
  d := 2
  constraints_degree := constraints_degree
  flushes_degree := flushes_degree
  counts := counts
  boundary := boundary prog s
  μ := leanIsaμ prog s
  layout := layout prog s F.slot
  nLines := 3
  publicLines := publicLines prog s
  flock := some (flockRegion prog s F)

namespace LeanIsa

/-! ## Admissible sizes -/

/-- The checks `read_public` makes of the announced sizes (`cpu/mod.rs:157-176`): the memory
window, the height cap, the `BLAKE2S` floor, and the stacked size's cap. The bytecode cap is
`Program`'s by type, and the stacked size's floor holds by construction (`leanIsaμ`). -/
def Sizes.Admissible (prog : Program) (s : Sizes) : Prop :=
  minLogMem ≤ s.logMem ∧ s.logMem ≤ maxLogMem ∧ (∀ j, s.τ j ≤ maxLogRows) ∧
    minLogRowsBlake2s ≤ s.τ 5 ∧ leanIsaμ prog s ≤ maxMu

instance (prog : Program) (s : Sizes) : Decidable (s.Admissible prog) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The WHIR rate check (`pcs/src/whir_config.rs:43-55`): the inverse rate's logarithm is in
`[1, 4]`. A parameter of the commitment, read off the same announcement. -/
def validRate (ρ : ℕ) : Prop := 1 ≤ ρ ∧ ρ ≤ 4

instance (ρ : ℕ) : Decidable (validRate ρ) := inferInstanceAs (Decidable (_ ∧ _))

/-- The announced sizes fit Clean's tables, whose row indices are 64-bit: the memory block below
`2^64` rows, the opcode tables at most `2^64`. Admissible sizes fit (`Sizes.Admissible.fits`). -/
def Sizes.Fits (s : Sizes) : Prop := s.logMem < 64 ∧ ∀ j, s.τ j ≤ 64

/-- Admissible sizes fit Clean's tables. -/
theorem Sizes.Admissible.fits {prog : Program} {s : Sizes} (h : s.Admissible prog) : s.Fits :=
  ⟨lt_of_le_of_lt h.2.1 (by decide), fun j ↦ (h.2.2.1 j).trans (by decide)⟩

/-- The sizes a witness carries: the memory log-size `κ` of its ensemble and the log-heights of
its six opcode tables; none when `κ = 0`. -/
def Sizes.ofWitness {prog : Program} {κ : ℕ} (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    Option Sizes :=
  if h : 0 < κ then
    some ⟨κ, h, fun j ↦ Nat.log 2 (tableAt w ⟨j, by omega⟩).table.length⟩
  else none

/-! ## The witness read off a stack -/

section WitnessOf

variable (F : FlockSpec) (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- Cell `x` of column `c`, read off the stack. -/
abbrev cell (c : Col) (x : Fin (2 ^ kappa prog s c)) : K :=
  ((leanIsaInstance F prog s).column q c).values.get x

/-- The rows of opcode table `j`, read off the stack. -/
def opcodeRows (j : Fin 6) : List (Array K) :=
  List.ofFn fun x : Fin (2 ^ s.τ j) ↦ Array.ofFn ((leanIsaInstance F prog s).row q (opIdx j) x)

/-- The memory block's rows: the index `g^x`, the finalize count `MFCNT`, the three limbs. -/
def memBlockRowsOf : List (Array K) :=
  List.ofFn fun x : Fin (2 ^ s.logMem) ↦ (toElements (⟨gpow x, cell F prog s q (memCol 3) x,
    #v[cell F prog s q (memCol 0) x, cell F prog s q (memCol 1) x,
      cell F prog s q (memCol 2) x]⟩ : MemRow K)).toArray

/-- The bytecode block's rows: the program's, with the finalize counts `BFCNT`. -/
def bytecodeBlockRowsOf : List (Array K) :=
  List.ofFn fun i : Fin (2 ^ prog.logSize) ↦
    (toElements (bytecodeRowOf prog i (cell F prog s q bfcntCol i))).toArray

/-- Cell `0` of a memory column. -/
def cell0 (i : Fin 4) : K := cell F prog s q (memCol i) ⟨0, Nat.two_pow_pos _⟩

/-- Cell `1` of a memory column. -/
def cell1 (i : Fin 4) : K := cell F prog s q (memCol i) ⟨1, Nat.one_lt_two_pow s.logMem_pos.ne'⟩

/-- The public input: cells `0` and `1` of `MEM_LO` and `MEM_HI`. -/
def publicInputOf : PublicIO K :=
  ⟨#v[cell0 F prog s q 0, cell0 F prog s q 1, cell1 F prog s q 0, cell1 F prog s q 1]⟩

/-- The memory block has five columns. -/
theorem width_memComponent (κ : ℕ) : (memComponent κ).width = 5 := by
  change (memComponent 0).width = 5
  decide +kernel

/-- The bytecode block has ten columns. -/
theorem width_bytecodeComponent : (bytecodeComponent prog).width = 10 := by
  change (bytecodeComponent ⟨0, Nat.zero_le _, fun _ ↦ .jump 0 0 0⟩).width = 10
  decide +kernel

/-- The rows of opcode table `j` have its width. -/
private theorem size_of_mem_opcodeRows (j : Fin 6) :
    ∀ r ∈ opcodeRows F prog s q j, r.size = (opcodeComponent j).width := by
  simp only [opcodeRows, List.mem_ofFn, forall_exists_index]
  rintro _ x rfl
  exact Array.size_ofFn

/-- The memory block's rows have its width. -/
private theorem size_of_mem_memBlockRowsOf :
    ∀ r ∈ memBlockRowsOf F prog s q, r.size = (memComponent s.logMem).width := by
  simp only [memBlockRowsOf, List.mem_ofFn, forall_exists_index]
  rintro _ x rfl
  rw [Vector.size_toArray, width_memComponent]
  rfl

/-- The bytecode block's rows have its width. -/
private theorem size_of_mem_bytecodeBlockRowsOf :
    ∀ r ∈ bytecodeBlockRowsOf F prog s q, r.size = (bytecodeComponent prog).width := by
  simp only [bytecodeBlockRowsOf, List.mem_ofFn, forall_exists_index]
  rintro _ x rfl
  rw [Vector.size_toArray, width_bytecodeComponent]
  rfl

/-- An opcode table has no fixed cells. -/
private theorem opcode_fixedRowsMatch (j : Fin 6) (rows : List (Array K)) :
    (opcodeComponent j).FixedRowsMatch rows := by
  fin_cases j <;> exact trivial

/-- A typed row written as a raw row is read back by the fixed-cell check. -/
private theorem fromElements_rowPrefix {Row : TypeMap} [ProvableType Row] (r : Row K) :
    fromElements (Air.Flat.rowPrefix (size Row) (toElements r).toArray) = r :=
  (Air.Flat.valueFromOffset_fromArray (Input := Row) _ fun _ _ ↦ #[]).symm.trans
    (rowAt_toElements _ r)

/-- A table of at most `2^64` rows. -/
private theorem pow_le_uint64Size {τ : ℕ} (h : τ ≤ 64) : 2 ^ τ ≤ UInt64.size :=
  Nat.pow_le_pow_right (by norm_num) h

/-- The memory block's rows agree with its fixed index column. -/
private theorem memBlockRowsOf_fixed (h : s.logMem < 64) :
    (memComponent s.logMem).FixedRowsMatch (memBlockRowsOf F prog s q) := by
  have h64 : 2 ^ s.logMem < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) h
  show _ ∧ ∀ i (hi : i < _), (memMode s.logMem).FixedAt (UInt64.ofNat i)
    (fromElements (Air.Flat.rowPrefix (size MemRow) (memBlockRowsOf F prog s q)[i]))
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [memBlockRowsOf, List.length_ofFn]
    exact (UInt64.toNat_ofNat_of_lt' h64).symm
  · have hi' : i < 2 ^ s.logMem := by simpa only [memBlockRowsOf, List.length_ofFn] using hi
    refine (memMode_fixedAt_iff hi' h _).mpr ?_
    simp only [memBlockRowsOf, List.getElem_ofFn, fromElements_rowPrefix]

/-- A memory block of `2^64` rows or more has no row index of Clean's: its rows are none. -/
private theorem memBlock_fixed_nil (h : ¬ s.logMem < 64) :
    (memComponent s.logMem).FixedRowsMatch [] := by
  show _ ∧ _
  refine ⟨?_, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  show 0 = (UInt64.ofNat (2 ^ s.logMem)).toNat
  rw [UInt64.toNat_ofNat', Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))]

/-- The bytecode block's rows agree with its fixed index and program columns. -/
private theorem bytecodeBlockRowsOf_fixed :
    (bytecodeComponent prog).FixedRowsMatch (bytecodeBlockRowsOf F prog s q) := by
  have h64 : 2 ^ prog.logSize < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by norm_num) (lt_of_le_of_lt prog.logSize_le (by decide))
  show _ ∧ ∀ i (hi : i < _), (bytecodeMode prog).FixedAt (UInt64.ofNat i)
    (fromElements (Air.Flat.rowPrefix (size BytecodeRow) (bytecodeBlockRowsOf F prog s q)[i]))
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [bytecodeBlockRowsOf, List.length_ofFn]
    exact (UInt64.toNat_ofNat_of_lt' h64).symm
  · have hi' : i < 2 ^ prog.logSize := by
      simpa only [bytecodeBlockRowsOf, List.length_ofFn] using hi
    refine (bytecodeMode_fixedAt_iff prog hi' _).mpr ?_
    simp only [bytecodeBlockRowsOf, List.getElem_ofFn, fromElements_rowPrefix]
    exact ⟨rfl, by ext k hk; interval_cases k <;> rfl⟩

/-- Opcode table `j` read off the stack: its rows, or none past `2^64` rows. -/
def opTableOf (j : Fin 6) : Air.Flat.Table K :=
  if h : s.τ j ≤ 64 then
    tableOf (opcodeComponent j) (opcodeRows F prog s q j)
      (by exact size_of_mem_opcodeRows F prog s q j)
      (by rw [opcodeRows, List.length_ofFn]; exact pow_le_uint64Size h)
      (by exact opcode_fixedRowsMatch j _)
  else tableOf (opcodeComponent j) [] (by simp) (by simp) (by exact opcode_fixedRowsMatch j _)

/-- The memory block read off the stack: its rows, or none past `2^64` rows. -/
def memTableOf : Air.Flat.Table K :=
  if h : s.logMem < 64 then
    tableOf (memComponent s.logMem) (memBlockRowsOf F prog s q)
      (by exact size_of_mem_memBlockRowsOf F prog s q)
      (by rw [memBlockRowsOf, List.length_ofFn]; exact pow_le_uint64Size h.le)
      (by exact memBlockRowsOf_fixed F prog s q h)
  else tableOf (memComponent s.logMem) [] (by simp) (by simp) (by exact memBlock_fixed_nil s h)

/-- The bytecode block read off the stack. -/
def bytecodeTableOf : Air.Flat.Table K :=
  tableOf (bytecodeComponent prog) (bytecodeBlockRowsOf F prog s q)
    (by exact size_of_mem_bytecodeBlockRowsOf F prog s q)
    (by
      rw [bytecodeBlockRowsOf, List.length_ofFn]
      exact pow_le_uint64Size (prog.logSize_le.trans (by decide)))
    (by exact bytecodeBlockRowsOf_fixed F prog s q)

/-- The tables read off the stack, in the ensemble's order. -/
def tablesOf : List (Air.Flat.Table K) :=
  [opTableOf F prog s q 0, opTableOf F prog s q 1, opTableOf F prog s q 2, opTableOf F prog s q 3,
    opTableOf F prog s q 4, opTableOf F prog s q 5, memTableOf F prog s q,
    bytecodeTableOf F prog s q]

/-- The tables read off the stack run the ensemble's components. -/
theorem tablesOf_components :
    (tablesOf F prog s q).map (·.component) = (leanIsaEnsemble prog s.logMem).tables := by
  have ho : ∀ j, (opTableOf F prog s q j).component = opcodeComponent j := fun j ↦ by
    unfold opTableOf
    split <;> rfl
  have hm : (memTableOf F prog s q).component = memComponent s.logMem := by
    unfold memTableOf
    split <;> rfl
  simp only [tablesOf, List.map_cons, List.map_nil, ho, hm]
  rfl

/-- The witness a stack carries: the six opcode tables from their rows, the memory and bytecode
blocks from the memory columns, the program and `BFCNT`, the public input from the first two
cells of `MEM_LO` and `MEM_HI`; its prover data is derived from the tables. -/
def witnessOf : EnsembleWitness (leanIsaEnsemble prog s.logMem) :=
  witnessOfTables prog s.logMem (publicInputOf F prog s q) (tablesOf F prog s q)
    (tablesOf_components F prog s q)

end WitnessOf

/-! ## The stack of a witness -/

section StackOf

variable (F : FlockSpec) (prog : Program) (s : Sizes)

/-- Cell `i` of row `x` of a table, `0` when missing. -/
def cellOf (t : Air.Flat.Table K) (x i : ℕ) : K := ((t.table[x]?).bind (·[i]?)).getD 0

/-- The memory block's cell of memory column `i`: the limbs at `2, 3, 4`, `MFCNT` at `1`. -/
def memRowCell : Fin 4 → ℕ := ![2, 3, 4, 1]

/-- The `BLAKE2S` rows' eighteen limbs, columns `9 … 26`. -/
def blake2sLimbs {κ : ℕ} (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    Vector (Fin 18 → K) (2 ^ s.τ 5) :=
  Vector.ofFn fun x ↦ fun k ↦ cellOf (tableAt w 5) x (9 + k)

/-- The column `c` a witness carries: the memory and bytecode blocks' committed cells, `F.gen` of
the `BLAKE2S` limbs as the Flock region, the opcode tables' cells. -/
def witnessColumn {κ : ℕ} (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (c : Col) → Vector K (2 ^ kappa prog s c)
  | ⟨⟨0, _⟩, i⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w 6) x (memRowCell i)
  | ⟨⟨1, _⟩, _⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w 7) x 1
  | ⟨⟨2, _⟩, _⟩ => (F.gen (blake2sLimbs prog s w)).values
  | ⟨⟨j + 3, h⟩, i⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w ⟨j, by omega⟩) x i

/-- The stack of a witness at the sizes `s`: its committed columns at their blocks, zero past
the last. -/
def stackOf {κ : ℕ} (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Column (leanIsaμ prog s) :=
  (blocks prog s).stackColumn (fun b ↦ witnessColumn F prog s w (stackOrder prog s)[b])
    (leanIsaμ prog s)

end StackOf

end LeanIsa

end
end LeanerVM.Protocol
