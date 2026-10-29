module

public import Statement.Prover.Witness

/-!
# The columns, the sizes and the stack of an execution, executable

From the rows of a run (`rowsOf`, `Witness.lean`):

* the announced sizes: the memory log-size and the six tables' row counts, the tables'
  log-heights as `build_layout` computes them (`tableLogsOf`, `verifier.py:974-1014`), the
  columns' log-sizes (`columnKappas`) and the stack's log-size (`placementsOf`);
* every column of the instance as an array, indexed by the verifier's global column number
  (`colsOf`): the memory's three limbs and finalize counts, the bytecode's finalize counts,
  `QKECCAK` (each `KECCAK` row's input lanes, its state after twelve rounds, its cells of the
  spare columns), the opcode tables' columns at their heights (a padding row zero), and the
  `KECCAK` output lanes derived from the twelve-round states (the last twelve rounds, padding
  rows those of the zero state). The `KECCAK` states are computed once per row (`midStates`,
  `outStates`);
* the stack (`stackArray`): the committed columns end to end in the stacking order
  (`stackOrderOf`: largest first, ties in global order, as `stack_offsets` sorts them), then
  zeros up to `2^μ`.

`witness?` puts them together; `none` exactly when `checkTrace` is `false`.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol.Verifier

/-! ## Sizes -/

/-- The tables' log-heights from their row counts: the least `h` with `rows ≤ 2^h`, at least the
table's floor (`build_layout`, `verifier.py:977-979`). -/
def tableLogsOf (rows : List ℕ) : List ℕ :=
  List.zipWith (fun r floor ↦ max (log2Ceil r) floor) rows tableLogFloors

/-! ## Columns -/

/-- Cell `i` of row `x` of a table, `0` when missing. -/
def cellAt (R : Array (Array K)) (x i : ℕ) : K := ((R[x]?).bind (·[i]?)).getD 0

/-- Column `i` of a table at the height `2^h`: its rows' cells, zero past them. -/
def tableColumn (R : Array (Array K)) (h i : ℕ) : Array K :=
  Array.ofFn (n := 2 ^ h) fun x ↦ cellAt R x.val i

/-- Rounds `12m` to `12m + 11` of Keccak-f[1600]. -/
def segment (m : ℕ) (a : KState) : KState :=
  ((keccakRC.drop (12 * m)).take 12).foldl Keccak.round a

/-- The zero state. -/
def zeroState : KState := Vector.replicate 25 0

/-- The input state of row `x` of the `KECCAK` table: its cells `13 … 37`. -/
def inState (R : Array (Array K)) (x : ℕ) : KState :=
  Vector.ofFn fun l : Fin 25 ↦ (cellAt R x (13 + l.val)).lane

/-- The state after twelve rounds of every step of the `KECCAK` table at the height `2^h`, once
per row; a padding row's is that of the zero state, computed once. -/
def midStates (R : Array (Array K)) (h : ℕ) : Array KState :=
  let zMid := segment 0 zeroState
  Array.ofFn (n := 2 ^ h) fun x ↦ if x.val < R.size then segment 0 (inState R x.val) else zMid

/-- The state after twenty-four rounds of every step, from its state after twelve. -/
def outStates (R : Array (Array K)) (mids : Array KState) : Array KState :=
  let zOut := segment 1 (segment 0 zeroState)
  Array.ofFn (n := mids.size) fun x ↦ if x.val < R.size then segment 1 mids[x] else zOut

/-- The `KECCAK` column spare slot `50 + k` of `QKECCAK` carries: column `k` for `k < 13`, then
column `63` (`_KECCAK_COMMITTED[:QKECCAK_SPARE]`, `verifier.py:948-954`). -/
def spareCol (k : ℕ) : ℕ := if k < 13 then k else 63

/-- `QKECCAK` of the `KECCAK` table at the height `2^h`: slot `l < 25` of step `x` is input lane
`l` of row `x`, slot `25 + l` lane `l` of its state after twelve rounds, slot `50 + k` its cell of
the column `spareCol k`. -/
def qkeccakColumn (R : Array (Array K)) (h : ℕ) (mids : Array KState) : Array K :=
  let p := 2 ^ h
  Array.ofFn (n := 2 ^ (h + 6)) fun i ↦
    let x := i.val % p
    let k := i.val / p
    if k < 25 then cellAt R x (13 + k)
    else if k < 50 then laneK (mids.getD x zeroState) (k - 25)
    else cellAt R x (spareCol (k - 50))

/-- The first global column of each opcode table (`GLOBAL_COLUMN_BASES`). -/
def tableBase : ℕ → ℕ
  | 0 => 6
  | 1 => 21
  | 2 => 36
  | 3 => 44
  | 4 => 59
  | 5 => 73
  | _ => 73

/-- The opcode table of a global column from `6` on. -/
def tableIndexOf (c : ℕ) : ℕ :=
  if c < 21 then 0 else if c < 36 then 1 else if c < 44 then 2 else if c < 59 then 3
  else if c < 73 then 4 else 5

/-- The column of global number `c`: the memory's limbs and finalize counts `0 … 3`, `BFCNT` `4`,
`QKECCAK` `5`, then column `c - base` of the opcode table `c` falls in, the `KECCAK` output lanes
(its columns `38 … 62`) derived from the twelve-round states `mids`, through the twenty-four-round
states `outs`. -/
def columnAt {κ : ℕ} (img : MemImage κ) (acc : Rows) (logs : List ℕ) (mids outs : Array KState)
    (c : ℕ) : Array K :=
  if c = 0 then Array.ofFn (n := 2 ^ κ) fun x ↦ (img x).limb 0
  else if c = 1 then Array.ofFn (n := 2 ^ κ) fun x ↦ (img x).limb 1
  else if c = 2 then Array.ofFn (n := 2 ^ κ) fun x ↦ (img x).limb 2
  else if c = 3 then acc.mem
  else if c = 4 then acc.bc
  else if c = 5 then qkeccakColumn (acc.tabs.getD 5 #[]) (logs.getD 5 0) mids
  else
    let j := tableIndexOf c
    let i := c - tableBase j
    if j = 5 ∧ 38 ≤ i ∧ i < 63 then
      Array.ofFn (n := 2 ^ logs.getD 5 0) fun x ↦ laneK (outs.getD x.val zeroState) (i - 38)
    else tableColumn (acc.tabs.getD j #[]) (logs.getD j 0) i

/-- **Every column of the instance**, by its global column number (`163` of them); the
`KECCAK` states computed once per row, for `QKECCAK` and the output lanes. -/
def colsOf {κ : ℕ} (img : MemImage κ) (acc : Rows) (logs : List ℕ) : Array (Array K) :=
  let mids := midStates (acc.tabs.getD 5 #[]) (logs.getD 5 0)
  let outs := outStates (acc.tabs.getD 5 #[]) mids
  Array.ofFn (n := 163) fun c ↦ columnAt img acc logs mids outs c.val

/-! ## The stack -/

/-- The committed columns' global numbers, in global order (`block_cols`, `verifier.py:998`). -/
def blockColumns : List ℕ :=
  (List.range 163).filter fun c ↦ (keccakSlot c).isNone ∧ c ∉ keccakOutputColumns

/-- The committed columns' global numbers in stacking order, from every column's log-size:
largest first, ties in global order (`stack_offsets`, `verifier.py:320-326`). -/
def stackOrderOf (kappas : List ℕ) : List ℕ :=
  let sizes := blockColumns.map (kappas.getD · 0)
  ((List.range blockColumns.length).mergeSort fun i j ↦
    decide (sizes.getD j 0 ≤ sizes.getD i 0)).map (blockColumns.getD · 0)

/-- **The stack**: the columns `order` end to end, then zeros up to `2^μ`. -/
def stackArray (μ : ℕ) (cols : Array (Array K)) (order : List ℕ) : Array K :=
  let a := order.foldl (fun acc c ↦ acc ++ cols.getD c #[]) (Array.emptyWithCapacity (2 ^ μ))
  a ++ Array.replicate (2 ^ μ - a.size) 0

/-! ## The witness -/

/-- The prover's data of an execution: the announced memory log-size and row counts, the
stack's log-size, every column by global number, and the stack. -/
structure Witness where
  /-- The memory log-size. -/
  logMem : ℕ
  /-- The six opcode tables' row counts, in the ensemble's order. -/
  rows : List ℕ
  /-- The stack's log-size. -/
  μ : ℕ
  /-- Every column, by global column number. -/
  cols : Array (Array K)
  /-- The stack, `2^μ` cells. -/
  stack : Array K

/-- The prover's data of the run `steps` of `t`. -/
def buildWitness (prog : Program) (t : Trace prog) (memIdx : Std.HashMap UInt64 ℕ)
    (steps : Array Step) : Witness :=
  let acc := rowsOf memIdx t.image prog.logSize steps
  let rows := acc.tabs.toList.map (·.size)
  let logs := tableLogsOf rows
  let kappas := columnKappas t.κ prog.logSize logs
  let μ := (placementsOf kappas).2
  let cols := colsOf t.image acc logs
  ⟨t.κ, rows, μ, cols, stackArray μ cols (stackOrderOf kappas)⟩

/-- **The prover's data of an execution**, after the check of `checkTrace`, from the same run:
`none` when the trace is no valid execution of `prog` on `input` within `2^28` committed
cells. -/
def witness? (prog : Program) (input : PublicInput) (t : Trace prog) : Option Witness :=
  if boundaryOK input t then
    let memIdx := powIndex t.κ
    match runSteps memIdx (powIndex prog.logSize) prog t with
    | some steps =>
      if committedSizeOf prog.logSize t.κ (opCount steps) ≤ maxCommitted then
        some (buildWitness prog t memIdx steps)
      else none
    | none => none
  else none

/-- The eight scalars announcing the sizes and the rate `ρ` (`announce`): the memory log-size,
the six row counts, the rate, each the Python's `E(n)`. -/
def Witness.announce (W : Witness) (ρ : ℕ) : List E := (W.logMem :: W.rows ++ [ρ]).map eOfNat

end LeanVM.Prover

end
