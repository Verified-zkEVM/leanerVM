import LeanVM.Arithmetization.Completeness.Basics
import LeanVM.Arithmetization.Completeness.Satisfied

/-!
# Tests: the constraint statement

A classic test for kernel evaluation: the fixture decides `K` and `E` arithmetic, one
Keccak-f[1600] permutation, and the bus permutations in the kernel.

**The fixture** is one hand-built witness of `SatisfiedBy` for the program of the execution
tests, the executor's `mul_192bit_word` (`crates/leanvm_core/src/cpu/mod.rs:888-903` at leanVM
`4af2cddd`, `tests/LeanVMTests/Semantics/Execution.lean`), extended with closed walks: a `JUMP` to
the sentinel after the three instructions, and three blocks run in frames disjoint from the
program's own, each a loop ending in a `JUMP` back to its first instruction: one `XOR`, one
`DEREF`, one `KECCAK`. The `KECCAK` row is the first permutation of the executor test
`keccak_permutes_in_both_layouts` (`cpu/mod.rs:842-875` at leanVM `4af2cddd`): the input cells
`a, b, a, b` (the two `m` pairs aliasing one another), the padding's first byte `0x01` in the
tail's first cell, `b8 = (0x8000000000000000, 0x5555, 0)` whose high limb holds no lane in the
even layout (the row's free limb), a zero capacity, and the thirteen output cells in the odd
layout, the output lanes the pinned Python verifier's `keccak_f` computes (computed outside Lean,
as in the table and execution tests). The statement accepts rows that are not steps of the run as
long as the state pair balances (Prop. 6.1: one walk from the initial to the final registers, and
closed walks), and the fixture exercises that. The thirty-two-slot program `walkProg` runs four
steps from `(1, 1)` to `(g^31, 1)` (`walk_run`, a `ValidExecution`), and its honest witness
`walkW kLout 1 g memCnt` at the minimum memory size `2^16` satisfies every conjunct of
`SatisfiedBy` (`walk_satisfiedBy`) and represents the trace (`walk_represents`): the completeness
instance for this program, by hand (`walk_t1_instance`). The witness is parametric in the
`KECCAK` row's output lanes (written consistently in the row and in the image), the first
`SET_CONSTANT` row's read count, the product row's read count of `x`, and the memory block's
finalize counts, so that the rejections below are the honest witness with one thing changed.

**What the proofs exercise.** The eight tables are the witness's `tables` in the ensemble's
order, the memory block's `2^16` rows built by `List.ofFn` and never enumerated: its constraints
hold row-generically (the block has none), its interactions on a foreign channel are `[]` by a
lemma (`memT_filter`), and its share of the memory pair is split (`List.ofFn_add`) into the
forty-four cells the run touches, decided in the kernel with the tables' reads, and the
untouched suffix, whose seed and finalize messages coincide because its finalize counts are `1`
(`memCnt_of_ge`). The kernel evaluates a table's interactions through Clean's
`Component.rowOperations` (`table_interactions_eq`), since `Component.operations` reaches them
through `instantiate` and `toSubcircuit`, which the kernel does not unfold. `KeccakRowsValid`
is one kernel evaluation of Keccak-f[1600] (`keccak_lanes`).

**Rejections**, each the honest witness with one thing changed, and each failing exactly the
conjunct named. A wrong finalize count unbalances the memory pair (§6.2 "Nothing checks the
finalize counts"): cell `4`'s finalize count `1` instead of `g`. A read count of `0` that
*balances* fails `CountsNonzero` alone (§6.2 "The count product"): the first `SET_CONSTANT`
row reads `x` with count `0`, a pull and a push of one tuple, the product row then reads `x`
first, and every other conjunct still holds (`zero_count_witness`). A wrong output lane, written
consistently in the `KECCAK` row and in the image, fails `KeccakRowsValid` alone
(`wrong_lane_witness`): the bus binds the lanes to the cells, not the permutation, and the table
has no constraint; the permutation is the Keccak reduction's. A memory block whose index column
is shifted fails `IndexColumnsAreRowIndices` (§6.5). A wrong public word fails `word0_eq`
(§8.2). A three-row table and a four-row `KECCAK` table are within `Caps`: a table's row count
need not be a power of two, and there is no `KECCAK` floor (`Caps` bounds the memory log-size and
each table's rows by `2^MAX_LOG_ROWS` only; the protocol pads every table with public padding
rows, `doc/leanvm` §`sec:e2e-pad`).
-/

-- The kernel decisions one at a time: elaborated in parallel, the fixture's bus permutations and
-- its Keccak-f[1600] evaluation reserve more than a 40 GB address-space cap (about 41 GB, against
-- about 20 GB in sequence, at the same wall time).
set_option Elab.async false

namespace LeanVMTests.Arithmetization.Statement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open Air.Flat (Component EnsembleWitness)

/-! ## The fixture: `mul_192bit_word` with closed walks -/

-- The operands and product of the executor test `mul_192bit_word` at leanVM a386121f.
def mulX : E :=
  E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfeedfacedeadbeef) (K.ofBits 0x1111222233334444)
def mulY : E :=
  E.ofLimbs (K.ofBits 0x9999aaaabbbbcccc) (K.ofBits 0x13579bdf2468ace0) (K.ofBits 0x5555666677778888)
def mulXY : E :=
  E.ofLimbs (K.ofBits 0xf4bccd9a2e8e525b) (K.ofBits 0xf85ebb9433986f2f) (K.ofBits 0x918137982bf175ac)

-- The executor test `keccak_permutes_in_both_layouts` at leanVM 4af2cddd, its first permutation
-- (as in `tests/LeanVMTests/Arithmetization/Tables.lean` and `Semantics/Execution.lean`): the
-- input cells, the words `a, b` (each read twice through the aliased `m` pairs), the padding's
-- first byte in the tail, its last bit in `b8` (whose free high limb `0x5555` holds no lane), and
-- a zero capacity; the input lanes they hold in the even layout, and their image under `keccak_f`
-- (`verifier.py`, computed outside Lean).
def kA : E := E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfedcba9876543210) 0
def kB : E := E.ofLimbs (K.ofBits 0xdeadbeefcafebabe) (K.ofBits 0x0badf00d0badf00d) 0
def kPad : E := E.ofLimbs (K.ofBits 0x01) 0 0
def kEnd : E := E.ofLimbs (K.ofBits 0x8000000000000000) (K.ofBits 0x5555) 0

def kLin : Vector K 25 :=
  #v[K.ofBits 0x123456789abcdef, K.ofBits 0xfedcba9876543210, K.ofBits 0xdeadbeefcafebabe,
    K.ofBits 0xbadf00d0badf00d, K.ofBits 0x123456789abcdef, K.ofBits 0xfedcba9876543210,
    K.ofBits 0xdeadbeefcafebabe, K.ofBits 0xbadf00d0badf00d, K.ofBits 0x1, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0,
    K.ofBits 0x8000000000000000, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0]

def kLout : Vector K 25 :=
  #v[K.ofBits 0x8dbfafed17b66d45, K.ofBits 0x30fd63be3bf8b935, K.ofBits 0x77167d7a851a2a5a,
    K.ofBits 0xd9174937e0d9005e, K.ofBits 0xa6a08643e0752e62, K.ofBits 0x96fa9d5eb49e3867,
    K.ofBits 0xd3075d1a22781d5, K.ofBits 0x81ae728bf7328686, K.ofBits 0xf51da81b6f1b6499,
    K.ofBits 0xdaf2a8af5b43dbf9, K.ofBits 0xdbf85b3cc1312641, K.ofBits 0x993d35c56291827e,
    K.ofBits 0x47fd59ac60e225e2, K.ofBits 0x36607d1d9e6abed, K.ofBits 0x6cee5561314ca0f3,
    K.ofBits 0x3e20ee955c09012e, K.ofBits 0x8a928dc9e22c3dcf, K.ofBits 0x7f24a1dac6837929,
    K.ofBits 0xd22b33eacce5fcd2, K.ofBits 0x2b1e71fdcd52b881, K.ofBits 0x427618061608ac91,
    K.ofBits 0x44c480aa40bfdbf9, K.ofBits 0x7a29ee993739ddb0, K.ofBits 0xf7f9aa87f90247d1,
    K.ofBits 0xe5177d767bf6bd92]

/-- The thirteen output cells of the lanes `L` in the odd layout: lane `0` alone in the high limb
of cell `0`, then the lane pairs `(2c - 1, 2c)`. At `kLout` they are the executor's (`kOut` of
the execution tests). -/
def outCells (L : Vector K 25) : List E :=
  [E.ofLimbs 0 L[0] 0, E.ofLimbs L[1] L[2] 0, E.ofLimbs L[3] L[4] 0, E.ofLimbs L[5] L[6] 0,
    E.ofLimbs L[7] L[8] 0, E.ofLimbs L[9] L[10] 0, E.ofLimbs L[11] L[12] 0,
    E.ofLimbs L[13] L[14] 0, E.ofLimbs L[15] L[16] 0, E.ofLimbs L[17] L[18] 0,
    E.ofLimbs L[19] L[20] 0, E.ofLimbs L[21] L[22] 0, E.ofLimbs L[23] L[24] 0]

/-- The public input `[w(1), w(2)]`. -/
def mulInput : PublicInput := ⟨![1, 0, K.ofBits 2, 0]⟩

/-- A word of `K` as a cell. -/
def cellK (a : K) : E := E.ofLimbs a 0 0

/-- The program: the executor's three instructions in frame `1` (slots `0..2`), a `JUMP` to the
sentinel (`3`), an `XOR` loop in frame `g^5` (`4`, `5`), a `DEREF` loop in the same frame
(`6`, `7`), a `KECCAK` loop of one row in frame `g^14` (`8`, `9`), never-executed slots
(`10..30`) and the sentinel (`31`, not a `JUMP`). Each block's `JUMP` reads `c = 1`, its
block's first counter `d`, and its own frame `f`. The `KECCAK` operands are the executor
test's layout moved into the frame: `m = [0, 1, 0, 1]`, `tail = 2`, `b8 = 6`, `cap = 7`,
`out = 11`, even layout in, odd layout out. -/
def walkProg : Program :=
  ⟨5, by decide, fun i ↦
    match (i : ℕ) with
    | 0 => .setConstant (gpow 2) mulX
    | 1 => .setConstant (gpow 3) mulY
    | 2 => .mulNative (gpow 2) (gpow 3) (gpow 4)
    | 3 => .jump (gpow 41) (gpow 42) (gpow 43)
    | 4 => .xor 1 1 1
    | 5 => .jump g (gpow 2) (gpow 6)
    | 6 => .deref (gpow 6) 1 1 .cell
    | 7 => .jump g (gpow 3) (gpow 6)
    | 8 => .keccak ![1, g, 1, g] (gpow 2) (gpow 6) (gpow 7) (gpow 11) false true
    | 9 => .jump (gpow 24) (gpow 25) (gpow 26)
    | _ => .xor 1 1 1⟩

/-- The forty-four cells the run and the loops touch, by index, the `KECCAK` output cells holding
the lanes `L`; every other cell of the image is `0`. Frame `1`: the public words (`0`, `1`), the
operands and the product (`2..4`), the sentinel `JUMP`'s `c, d, f` (`41..43`). Frame `g^5`: the
`XOR` and `DEREF` cell (`5`), `c` (`6`), the two blocks' `d` (`7`, `8`), the pointer and `f`
(`11`). Frame `g^14`: the `KECCAK` cells in the executor's layout, `a, b` (`14`, `15`), the tail
(`16..19`), `b8` (`20`), the capacity (`21..24`), the output (`25..37`), and the block's
`c, d, f` (`38..40`). -/
def walkCells (L : Vector K 25) : Array E :=
  ([cellK 1, cellK (K.ofBits 2), mulX, mulY, mulXY,
    0, cellK 1, cellK (gpow 4), cellK (gpow 6), 0, 0, cellK (gpow 5), 0, 0,
    kA, kB, kPad, 0, 0, 0, kEnd, 0, 0, 0, 0] ++ outCells L ++
    [cellK 1, cellK (gpow 8), cellK (gpow 14), cellK 1, cellK (gpow 31), cellK 1]).toArray

/-- The image, at the minimum size `2^16`. -/
def walkImage (L : Vector K 25) : MemImage minLogMem := fun i ↦ ((walkCells L)[(i : ℕ)]?).getD 0

/-- The trace: four steps, over the honest image. -/
def walkTrace : Trace walkProg := ⟨minLogMem, walkImage kLout, 4⟩

/-- The `"mem"` table of the prover data: the image, one row of limbs per word. -/
def walkRows (L : Vector K 25) : Array (Vector K 3) :=
  Array.ofFn fun i : Fin (2 ^ minLogMem) ↦
    #v[(walkImage L i).limb 0, (walkImage L i).limb 1, (walkImage L i).limb 2]

/-- The prover data: the image as its `"mem"` table, matched on arity (as in the channel, table
and boundary tests). -/
def walkData (L : Vector K 25) : ProverData K := fun _ n ↦
  match n with
  | 3 => walkRows L
  | _ => #[]

/-- The table, read back. By `unfold` and not by `rfl`: the match on the arity `3` is stuck for
definitional unfolding, which then unrolls `Array.ofFn` over the `2^16` rows. -/
theorem memRows_walk (L : Vector K 25) : memRows (walkData L) = walkRows L := by
  unfold memRows walkData
  rfl

/-- The honest finalize counts `g^A[i]` of the touched cells; `1` elsewhere (`memCnt`). The
`KECCAK` row reads `a` and `b` twice, every other cell of its frame once. -/
def walkCounts : Array K :=
  #[1, 1, g ^ 2, g ^ 2, g, g ^ 5, g ^ 2, g, g, 1, 1, g ^ 3, 1, 1,
    g ^ 2, g ^ 2, g, g, g, g, g, g, g, g, g,
    g, g, g, g, g, g, g, g, g, g, g, g, g,
    g, g, g, g, g, g]

/-- The finalize count of cell `i`. -/
def memCnt (i : ℕ) : K := (walkCounts[i]?).getD 1

/-- Past the touched cells every finalize count is `1`: the cell was never read. -/
theorem memCnt_of_ge {i : ℕ} (h : 44 ≤ i) : memCnt i = 1 := by
  have hs : walkCounts.size = 44 := rfl
  unfold memCnt
  rw [Array.getElem?_eq_none (hs ▸ h)]
  rfl

/-- The finalize count of slot `i`: every slot up to `9` executes once. -/
def bcCnt (i : ℕ) : K := if i ≤ 9 then g else 1

/-- The same, as the bytecode block's finalize-count column. -/
def bcCntFin (i : Fin (2 ^ walkProg.logSize)) : K := bcCnt i

/-! ## The rows -/

-- Frame `1`: the run.
/-- Slot `0`, `SET_CONSTANT g^2 ← x`, with read count `c` (`1` for the honest prover). -/
def setRow0 (c : K) : SetRow K :=
  ⟨gpow 0, 1, gpow 2, #v[mulX.limb 0, mulX.limb 1, mulX.limb 2], c, 1⟩
/-- Slot `1`, `SET_CONSTANT g^3 ← y`. -/
def setRow1 : SetRow K := ⟨gpow 1, 1, gpow 3, #v[mulY.limb 0, mulY.limb 1, mulY.limb 2], 1, 1⟩
/-- Slot `2`, `MUL_NATIVE`: the read of `x` with count `rA` (`g` for the honest prover, the
second read), the second read of `y`, the first of the product. -/
def mulRow (rA : K) : MulRow K :=
  ⟨gpow 2, 1, gpow 2, gpow 3, gpow 4, #v[mulX.limb 0, mulX.limb 1, mulX.limb 2],
    #v[mulY.limb 0, mulY.limb 1, mulY.limb 2], rA, g, 1, 1⟩
/-- Slot `3`, the `JUMP` to the sentinel: `(g^3, 1) → (g^31, 1)`. -/
def jumpRow3 : JumpRow K := ⟨gpow 3, 1, gpow 41, gpow 42, gpow 43, 1, gpow 31, 1, 1, 1, 1, 1⟩

-- Frame `g^5`: the `XOR` and `DEREF` blocks.
/-- Slot `4`, `XOR 1 1 1` on the zero cell `g^5`: three reads. -/
def xorRow : XorRow K := ⟨gpow 4, gpow 5, 1, 1, 1, #v[0, 0, 0], #v[0, 0, 0], 1, g, g ^ 2, 1⟩
/-- Slot `5`, the `JUMP` back to slot `4`. -/
def jumpRow5 : JumpRow K := ⟨gpow 5, gpow 5, g, gpow 2, gpow 6, 1, gpow 4, gpow 5, 1, 1, 1, 1⟩
/-- Slot `6`, `DEREF` in `cell` mode: the pointer `g^5` at `g^11`, the local and target cell
both `g^5` (its fourth and fifth reads). -/
def derefRow : DerefRow K :=
  ⟨gpow 6, gpow 5, gpow 6, 1, 1, 0, 0, gpow 5, #v[0, 0, 0], g, g ^ 4, g ^ 3, 1⟩
/-- Slot `7`, the `JUMP` back to slot `6`. -/
def jumpRow7 : JumpRow K := ⟨gpow 7, gpow 5, g, gpow 3, gpow 6, 1, gpow 6, gpow 5, g, 1, g ^ 2, 1⟩

-- Frame `g^14`: the `KECCAK` block.
/-- The `KECCAK` row's read counts: the first reads of `a, b`, their second reads (the aliased
`m` pairs), then the first read of every other cell. -/
def kCnt : Vector K 26 :=
  #v[1, 1, g, g, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
/-- Slot `8`, the executor's `KECCAK` row in frame `g^14`, with output lanes `L` (`kLout` for the
honest prover): even layout in (flag `0`), odd layout out (flag `1`), the free limb `0x5555`. -/
def kRow (L : Vector K 25) : KeccakRow K :=
  ⟨gpow 8, gpow 14, #v[1, g, 1, g], gpow 2, gpow 6, gpow 7, gpow 11, 0, 1, K.ofBits 0x5555, kLin,
    L, kCnt, 1⟩
/-- Slot `9`, the `JUMP` back to slot `8`. -/
def jumpRow9 : JumpRow K :=
  ⟨gpow 9, gpow 14, gpow 24, gpow 25, gpow 26, 1, gpow 8, gpow 14, 1, 1, 1, 1⟩

/-- The `JUMP` rows as raw rows `jumpRaw r 1 1`, their two local witnesses `w = 1`, `b = 1`
(every condition is `1`), have the table's width. -/
theorem jumpRaws_size (rs : List (JumpRow K)) :
    ∀ r ∈ rs.map (jumpRaw · 1 1), r.size = size JumpRow + 2 := by
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨_, -, rfl⟩ := hr
  rw [jumpRaw, Array.size_append, rawRow_size]
  rfl

/-- Row `i` of the memory block: `(g^i, cnt i, mem[i])`, the raw form of the typed row. -/
def memRowArr (L : Vector K 25) (cnt : ℕ → K) (i : Fin (2 ^ minLogMem)) : Array K :=
  (toElements (⟨gpow i, cnt i,
    #v[(walkImage L i).limb 0, (walkImage L i).limb 1, (walkImage L i).limb 2]⟩ : MemRow K)).toArray

/-- The memory row's five coordinates, without evaluating the block's row list. -/
theorem memRowArr_eq (L : Vector K 25) (cnt : ℕ → K) (i : Fin (2 ^ minLogMem)) :
    memRowArr L cnt i =
      #[gpow i, cnt i, (walkImage L i).limb 0, (walkImage L i).limb 1, (walkImage L i).limb 2] := by
  with_unfolding_all rfl

/-! ## The tables and the witness -/

/-- A table of the witness: a component and its rows, over the data of the lanes `L`. -/
def mkT {Input Output : TypeMap} [ProvableType Input] [ProvableType Output] (L : Vector K 25)
    (c : GeneralFormalCircuit K Input Output) (width : ℕ) (rows : List (Array K))
    (h : ∀ r ∈ rows, r.size = width) : Air.Flat.Table K :=
  ⟨⟨c⟩, width, rows, walkData L, h⟩

def xorT (L : Vector K 25) : Air.Flat.Table K :=
  mkT L xorTable (size XorRow) ([xorRow].map rawRow) (rawRows_size [xorRow])
/-- The `MUL_NATIVE` table, its row's read count of `x` `rA`. -/
def mulT (L : Vector K 25) (rA : K) : Air.Flat.Table K :=
  mkT L mulTable (size MulRow) ([mulRow rA].map rawRow) (rawRows_size [mulRow rA])
/-- The `SET_CONSTANT` table, its first row's read count `c`. -/
def setT (L : Vector K 25) (c : K) : Air.Flat.Table K :=
  mkT L setTable (size SetRow) ([setRow0 c, setRow1].map rawRow)
    (rawRows_size [setRow0 c, setRow1])
def derefT (L : Vector K 25) : Air.Flat.Table K :=
  mkT L derefTable (size DerefRow) ([derefRow].map rawRow) (rawRows_size [derefRow])
def jumpT (L : Vector K 25) : Air.Flat.Table K :=
  mkT L jumpTable (size JumpRow + 2) ([jumpRow3, jumpRow5, jumpRow7, jumpRow9].map (jumpRaw · 1 1))
    (jumpRaws_size [jumpRow3, jumpRow5, jumpRow7, jumpRow9])
/-- The `KECCAK` table: the one row, its output lanes `L`. -/
def kT (L : Vector K 25) : Air.Flat.Table K :=
  mkT L keccakTable (size KeccakRow) ([kRow L].map rawRow) (rawRows_size [kRow L])
/-- The memory block, with finalize counts `cnt`. -/
def memT (L : Vector K 25) (cnt : ℕ → K) : Air.Flat.Table K :=
  mkT L memTable (size MemRow) (List.ofFn (memRowArr L cnt)) (by
    intro r hr
    rw [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    exact Vector.size_toArray _)
/-- The bytecode block: the program's rows (`bytecodeRowOf`). -/
def bcT (L : Vector K 25) : Air.Flat.Table K :=
  mkT L bytecodeTable (size BytecodeRow)
    (List.ofFn fun i ↦ (toElements (bytecodeRowOf walkProg i (bcCntFin i))).toArray) (by
      intro r hr
      rw [List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact rawRow_size _)

/-- A witness over the data and input of the lanes `L` with the tables `ts`, eight tables of the
ensemble's components in order: the proofs are by cases on the list, so `ts` is a literal. -/
def mkW (L : Vector K 25) (ts : List (Air.Flat.Table K))
    (hlen : (leanIsaEnsemble walkProg).tables.length = ts.length := by rfl)
    (hc : ∀ i (hi : i < (leanIsaEnsemble walkProg).tables.length),
      (leanIsaEnsemble walkProg).tables[i] = (ts[i]'(hlen ▸ hi)).component := by
        intro i hi
        have hi' : i < 8 := hi
        interval_cases i <;> rfl)
    (hd : ∀ t ∈ ts, t.data = walkData L := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) :
    EnsembleWitness (leanIsaEnsemble walkProg) :=
  ⟨ts, walkData L, PublicIO.ofInput mulInput, hlen, hc, hd⟩

/-- The witness, with the `KECCAK` row's output lanes `L` (in the row and in the image), the
first `SET_CONSTANT` row's read count `c`, the product row's read count of `x` `rA`, and the
memory block's finalize counts `cnt`; the honest one is `walkW kLout 1 g memCnt`. -/
def walkW (L : Vector K 25) (c rA : K) (cnt : ℕ → K) : EnsembleWitness (leanIsaEnsemble walkProg) :=
  mkW L [xorT L, mulT L rA, setT L c, derefT L, jumpT L, kT L, memT L cnt, bcT L]

/-! ## The tables of the witness, read back -/

/-- The three blocks the statement names, read off the witness. -/
theorem tableAt_five (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    tableAt (walkW L c rA cnt) 5 = kT L := rfl
theorem tableAt_six (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    tableAt (walkW L c rA cnt) 6 = memT L cnt := rfl
theorem tableAt_seven (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    tableAt (walkW L c rA cnt) 7 = bcT L := rfl

/-- Their rows. By `dsimp`, never by `rfl`: a definitional comparison of a stuck projection
against a `List.ofFn` unrolls the `2^16` rows. -/
theorem kT_table (L : Vector K 25) : (kT L).table = [kRow L].map rawRow := by
  dsimp only [kT, mkT]
theorem memT_table (L : Vector K 25) (cnt : ℕ → K) :
    (memT L cnt).table = List.ofFn (memRowArr L cnt) := by
  dsimp only [memT, mkT]
theorem bcT_table (L : Vector K 25) :
    (bcT L).table =
      List.ofFn fun i ↦ (toElements (bytecodeRowOf walkProg i (bcCntFin i))).toArray := by
  dsimp only [bcT, mkT]
theorem memBlockRows_eq (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    memBlockRows (walkW L c rA cnt) = List.ofFn (memRowArr L cnt) := by
  rw [memBlockRows, tableAt_six, memT_table]

/-! ## The image the data names -/

theorem walk_logSize (L : Vector K 25) : (imageOf (walkData L)).1 = minLogMem := by
  show min (Nat.log 2 (memRows (walkData L)).size) maxLogMem = minLogMem
  rw [memRows_walk, walkRows, Array.size_ofFn, Nat.log_pow (by norm_num)]
  rfl

theorem walk_wellShaped (L : Vector K 25) : WellShapedData (walkData L) :=
  ⟨by rw [walk_logSize, memRows_walk, walkRows, Array.size_ofFn]⟩

theorem walk_pow_eq (L : Vector K 25) : 2 ^ (imageOf (walkData L)).1 = 2 ^ minLogMem := by
  rw [walk_logSize]

/-- Row `k` of the table, through `getElem?`: a `getElem` with a bound on the `2^16`-row table
makes both the elaborator and the kernel unroll it. -/
theorem walkRows_get? (L : Vector K 25) (k : ℕ) (hk : k < 2 ^ minLogMem) :
    (walkRows L)[k]? = some #v[(walkImage L ⟨k, hk⟩).limb 0, (walkImage L ⟨k, hk⟩).limb 1,
      (walkImage L ⟨k, hk⟩).limb 2] := by
  rw [walkRows, Array.getElem?_ofFn, dite_eq_left hk]

theorem walk_image_apply' (L : Vector K 25) (k : ℕ) (hk : k < 2 ^ (imageOf (walkData L)).1) :
    (imageOf (walkData L)).2 ⟨k, hk⟩ = walkImage L ⟨k, by rw [← walk_pow_eq L]; exact hk⟩ := by
  conv_rhs => rw [← ofLimbs_limb (walkImage L ⟨k, _⟩)]
  refine imageOf_apply (walk_wellShaped L) ⟨k, hk⟩ (v := #v[(walkImage L ⟨k, _⟩).limb 0,
    (walkImage L ⟨k, _⟩).limb 1, (walkImage L ⟨k, _⟩).limb 2]) ?_
  rw [Array.getElem_eq_iff, memRows_walk]
  exact walkRows_get? L k _

/-- Every word the data names is the fixture's image. -/
theorem walk_image_apply (L : Vector K 25) (i : Fin (2 ^ (imageOf (walkData L)).1)) :
    (imageOf (walkData L)).2 i = walkImage L (Fin.cast (walk_pow_eq L) i) :=
  walk_image_apply' L i i.isLt

/-- The image the data names, as one equality of dependent pairs: what every conjunct over
`imageOf w.data` is rewritten with, so that nothing compares the data's log-size against
`minLogMem` definitionally. -/
theorem walk_imageOf (L : Vector K 25) : imageOf (walkData L) = ⟨minLogMem, walkImage L⟩ := by
  have hκ : (imageOf (walkData L)).1 = minLogMem := walk_logSize L
  have hpow : 2 ^ (imageOf (walkData L)).1 = 2 ^ minLogMem := walk_pow_eq L
  have hf : ∀ i, (imageOf (walkData L)).2 i = walkImage L (Fin.cast hpow i) := walk_image_apply L
  revert hκ hpow hf
  generalize imageOf (walkData L) = s
  obtain ⟨κ, img⟩ := s
  intro hκ hpow hf
  dsimp only at hκ hpow hf
  subst hκ
  exact congrArg _ (funext fun i ↦ (hf i).trans (congrArg (walkImage L) (Fin.ext rfl)))

theorem data_eq (L : Vector K 25) (c rA : K) (cnt : ℕ → K) : (walkW L c rA cnt).data = walkData L :=
  rfl

/-! ## The run -/

/-- The instruction at `g^i`. -/
theorem fetch_at (i : ℕ) (ins : Instr) (hi : i < 2 ^ walkProg.logSize := by decide)
    (hd : walkProg.code ⟨i, hi⟩ = ins := by rfl) : walkProg.fetch (gpow i) = some ins := by
  rw [show gpow i = gpow ((⟨i, hi⟩ : Fin (2 ^ walkProg.logSize)) : ℕ) from rfl,
    Program.fetch_gpow, hd]

/-- The instruction at the counter `1 = g^0`. -/
theorem fetch_one : walkProg.fetch 1 = some (.setConstant (gpow 2) mulX) := by
  simpa using fetch_at 0 (.setConstant (gpow 2) mulX)

/-- The word at `g^k`. -/
theorem read_at (L : Vector K 25) (k : ℕ) (v : E) (hk : k < 2 ^ minLogMem := by decide)
    (hv : walkImage L ⟨k, hk⟩ = v := by rfl) : (walkImage L).read (gpow k) = some v := by
  rw [show gpow k = gpow ((⟨k, hk⟩ : Fin (2 ^ minLogMem)) : ℕ) from rfl,
    MemImage.read_gpow (by decide), hv]

theorem walk_step0 : step walkProg (walkImage kLout) ⟨1, 1⟩ = some ⟨gpow 1, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) fetch_one]
  show execute (walkImage kLout) ⟨1, 1⟩ (.setConstant (gpow 2) mulX) = _
  simp only [execute, executeWith, one_mul, read_at kLout 2 mulX]
  decide +kernel

theorem walk_step1 : step walkProg (walkImage kLout) ⟨gpow 1, 1⟩ = some ⟨gpow 2, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 1, 1⟩) (fetch_at 1 (.setConstant (gpow 3) mulY))]
  show execute (walkImage kLout) ⟨gpow 1, 1⟩ (.setConstant (gpow 3) mulY) = _
  simp only [execute, executeWith, one_mul, read_at kLout 3 mulY]
  decide +kernel

theorem walk_step2 : step walkProg (walkImage kLout) ⟨gpow 2, 1⟩ = some ⟨gpow 3, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 2, 1⟩) (fetch_at 2 (.mulNative (gpow 2) (gpow 3) (gpow 4)))]
  show execute (walkImage kLout) ⟨gpow 2, 1⟩ (.mulNative (gpow 2) (gpow 3) (gpow 4)) = _
  simp only [execute, executeWith, one_mul, read_at kLout 2 mulX, read_at kLout 3 mulY,
    read_at kLout 4 mulXY]
  decide +kernel

theorem walk_step3 : step walkProg (walkImage kLout) ⟨gpow 3, 1⟩ = some ⟨gpow 31, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 3, 1⟩) (fetch_at 3 (.jump (gpow 41) (gpow 42) (gpow 43)))]
  show execute (walkImage kLout) ⟨gpow 3, 1⟩ (.jump (gpow 41) (gpow 42) (gpow 43)) = _
  simp only [execute, executeWith, one_mul, read_at kLout 41 (cellK 1),
    read_at kLout 42 (cellK (gpow 31)), read_at kLout 43 (cellK 1)]
  decide +kernel

theorem walk_run1 : run walkProg (walkImage kLout) 1 ⟨1, 1⟩ = some ⟨gpow 1, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, Option.bind_eq_bind,
    Option.bind_some, run_zero]

theorem walk_run2 : run walkProg (walkImage kLout) 2 ⟨1, 1⟩ = some ⟨gpow 2, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, walk_step1,
    Option.bind_eq_bind, Option.bind_some, run_zero]

theorem walk_run3 : run walkProg (walkImage kLout) 3 ⟨1, 1⟩ = some ⟨gpow 3, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, walk_step1, walk_step2,
    Option.bind_eq_bind, Option.bind_some, run_zero]

theorem walk_run4 : run walkProg (walkImage kLout) 4 ⟨1, 1⟩ = some ⟨gpow 31, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, walk_step1, walk_step2,
    walk_step3, Option.bind_eq_bind, Option.bind_some, run_zero]

/-- The run: four steps from `(1, 1)` to the final registers `(g^31, 1)`. -/
theorem walk_run : run walkProg (walkImage kLout) 4 Regs.initial = some (Regs.final walkProg) :=
  walk_run4

/-- The public words are in place. -/
theorem walk_boundary : HasPublicBoundary mulInput walkTrace :=
  ⟨le_rfl, by decide, read_at kLout 0 (cellK 1), read_at kLout 1 (cellK (K.ofBits 2))⟩

/-- The extended program is a valid execution of the executor's on the same input. -/
example : ValidExecution walkProg mulInput walkTrace := ⟨walk_boundary, walk_run⟩

/-- Its register sequence. -/
theorem walk_regs :
    walkTrace.regs = [⟨1, 1⟩, ⟨gpow 1, 1⟩, ⟨gpow 2, 1⟩, ⟨gpow 3, 1⟩, ⟨gpow 31, 1⟩] := by
  show (List.range 5).filterMap (fun n ↦ run walkProg (walkImage kLout) n ⟨1, 1⟩) = _
  simp only [List.range_succ, List.range_zero, List.nil_append, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil, run_zero, walk_run1, walk_run2, walk_run3, walk_run4,
    List.singleton_append]
  rfl

/-! ## Proof helpers: the interactions the kernel evaluates -/

/-- The memory block sends nothing on a channel that is not its pair. -/
theorem memT_filter (L : Vector K 25) (cnt : ℕ → K) (c : RawChannel K) (hc : c.name ≠ MemPush.name)
    (hc' : c.name ≠ MemPull.name) :
    (memT L cnt).interactions.filter (·.channel.name = c.name) = [] :=
  filter_eq_nil_of_rowOps _ c (by
    rw [show (memT L cnt).component = ⟨memTable⟩ from rfl, memTable_rowOps]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl)
    · exact fun h ↦ hc (h.symm.trans rfl)
    · exact fun h ↦ hc' (h.symm.trans rfl))

/-- The bytecode block sends nothing on a channel that is not its pair. -/
theorem bcT_filter (L : Vector K 25) (c : RawChannel K) (hc : c.name ≠ BytecodePush.name)
    (hc' : c.name ≠ BytecodePull.name) :
    (bcT L).interactions.filter (·.channel.name = c.name) = [] :=
  filter_eq_nil_of_rowOps _ c (by
    rw [show (bcT L).component = ⟨bytecodeTable⟩ from rfl, bytecodeTable_rowOps]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl)
    · exact fun h ↦ hc (h.symm.trans rfl)
    · exact fun h ↦ hc' (h.symm.trans rfl))

/-- The cells the run and the loops touch are the first `touched`; the `untouched` rest
of the `2^16` are seeded and finalized with count `1` and cancel. -/
abbrev touched : ℕ := 44
abbrev untouched : ℕ := 65492
theorem touched_add_untouched : touched + untouched = 2 ^ minLogMem := by decide

/-- The seed message of cell `i`: `(g^i, 1, mem[i])`. -/
def seedMsg (L : Vector K 25) (i : Fin (2 ^ minLogMem)) : Array K :=
  #[gpow i, 1, (walkImage L i).limb 0, (walkImage L i).limb 1, (walkImage L i).limb 2]

/-- The finalize message of cell `i`: `(g^i, cnt i, mem[i])`. -/
def finMsg (L : Vector K 25) (cnt : ℕ → K) (i : Fin (2 ^ minLogMem)) : Array K :=
  #[gpow i, cnt i, (walkImage L i).limb 0, (walkImage L i).limb 1, (walkImage L i).limb 2]

/-- A row of the memory block pushes its seed message … -/
theorem memRow_push (d : ProverData K) (a : Array K) :
    (((⟨memTable⟩ : Component K).rowOperations.interactions.map
      (·.eval (Environment.fromArray a d))).filter
        (·.channel.name = MemPush.toRaw.name)).map (·.msg) =
      [#[a[0]?.getD 0, 1, a[2]?.getD 0, a[3]?.getD 0, a[4]?.getD 0]] := by
  rw [memTable_rowOps]
  -- The filter decides the two names by evaluation; the message is the row's variables
  -- evaluated (`Vector.map` is defined by well-founded recursion, so it is rewritten, not
  -- unfolded).
  show [((toElements (⟨var ⟨0⟩, 1, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ : MemMsg (Expression K))).map
    (Expression.eval (Environment.fromArray a d))).toArray] = _
  rw [show toElements (⟨var ⟨0⟩, 1, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ : MemMsg (Expression K)) =
    #v[var ⟨0⟩, 1, var ⟨2⟩, var ⟨3⟩, var ⟨4⟩] from by with_unfolding_all rfl]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.toArray_mk]
  rfl

/-- … and pulls its finalize message. -/
theorem memRow_pull (d : ProverData K) (a : Array K) :
    (((⟨memTable⟩ : Component K).rowOperations.interactions.map
      (·.eval (Environment.fromArray a d))).filter
        (·.channel.name = MemPull.toRaw.name)).map (·.msg) =
      [#[a[0]?.getD 0, a[1]?.getD 0, a[2]?.getD 0, a[3]?.getD 0, a[4]?.getD 0]] := by
  rw [memTable_rowOps]
  show [((toElements (⟨var ⟨0⟩, var ⟨1⟩, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ :
    MemMsg (Expression K))).map (Expression.eval (Environment.fromArray a d))).toArray] = _
  rw [show toElements (⟨var ⟨0⟩, var ⟨1⟩, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ :
    MemMsg (Expression K)) = #v[var ⟨0⟩, var ⟨1⟩, var ⟨2⟩, var ⟨3⟩, var ⟨4⟩] from by with_unfolding_all rfl]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.toArray_mk]
  rfl

/-- The memory block's pushes are the seeds of every cell, in order. -/
theorem memT_pushes (L : Vector K 25) (cnt : ℕ → K) :
    ((memT L cnt).interactions.filter (·.channel.name = MemPush.toRaw.name)).map (·.msg) =
      List.ofFn (seedMsg L) := by
  rw [table_interactions_eq, List.filter_flatMap, List.map_flatMap]
  simp only [memT, mkT, Air.Flat.Table.environment, memRow_push, ← List.map_eq_flatMap,
    List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [memRowArr_eq]
  rfl

/-- The memory block's pulls are the finalizes of every cell, in order. -/
theorem memT_pulls (L : Vector K 25) (cnt : ℕ → K) :
    ((memT L cnt).interactions.filter (·.channel.name = MemPull.toRaw.name)).map (·.msg) =
      List.ofFn (finMsg L cnt) := by
  rw [table_interactions_eq, List.filter_flatMap, List.map_flatMap]
  simp only [memT, mkT, Air.Flat.Table.environment, memRow_pull, ← List.map_eq_flatMap,
    List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [memRowArr_eq]
  rfl

/-- The seeds, split at the touched cells. -/
theorem seeds_split (L : Vector K 25) : List.ofFn (seedMsg L) =
    (List.ofFn fun i : Fin touched ↦ seedMsg L (Fin.castAdd untouched i)) ++
      List.ofFn fun j : Fin untouched ↦ seedMsg L (Fin.natAdd touched j) := by
  rw [show List.ofFn (seedMsg L) = List.ofFn fun i : Fin (touched + untouched) ↦ seedMsg L i
    from rfl, List.ofFn_add]
  rfl

/-- The finalizes, split the same way: past the touched cells, with counts `1`, they are the
seeds. -/
theorem fins_split (L : Vector K 25) (cnt : ℕ → K) (h : ∀ i, touched ≤ i → cnt i = 1) :
    List.ofFn (finMsg L cnt) =
      (List.ofFn fun i : Fin touched ↦ finMsg L cnt (Fin.castAdd untouched i)) ++
        List.ofFn fun j : Fin untouched ↦ seedMsg L (Fin.natAdd touched j) := by
  rw [show List.ofFn (finMsg L cnt) = List.ofFn fun i : Fin (touched + untouched) ↦ finMsg L cnt i
    from rfl, List.ofFn_add]
  refine congrArg₂ _ rfl (congrArg _ (funext fun j ↦ ?_))
  show #[gpow (touched + j), cnt (touched + j), (walkImage L (Fin.natAdd touched j)).limb 0,
    (walkImage L (Fin.natAdd touched j)).limb 1, (walkImage L (Fin.natAdd touched j)).limb 2] = _
  rw [h _ (Nat.le_add_right touched j)]
  rfl

/-! ## The witness satisfies the statement -/

/-- Every component's constraints hold, for every count and every output lane: the counts are
never constrained, only balanced (§6.2), and the `KECCAK` table has no constraint, so the
rejections below fail on their conjunct alone. The `JUMP` residuals hold with `w = b = 1`. -/
theorem walk_constraints (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    (walkW L c rA cnt).Constraints := by
  intro t ht
  simp only [EnsembleWitness.allTables, walkW, mkW, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ ↦ verifier_constraints _ _
  · exact fun _ _ ↦ xor_constraints _
  · exact fun _ _ ↦ mul_constraints _
  · exact fun _ _ ↦ set_constraints _
  · exact fun _ _ ↦ deref_constraints _
  · intro r hr
    simp only [jumpT, mkT, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact jumpRaw_constraints _ 1 1 (by decide +kernel) (by decide +kernel) _
  · exact fun _ _ ↦ keccak_constraints _
  · exact fun _ _ ↦ mem_constraints _
  · exact fun _ _ ↦ bytecode_constraints _

/-- The state pair balances: the run's four steps against the boundary, and the three closed
walks of the loops. -/
theorem walk_state_balanced :
    BalancedPair (walkW kLout 1 g memCnt) StatePull.toRaw StatePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, walkW, mkW, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter kLout memCnt StatePush.toRaw (by decide) (by decide),
    memT_filter kLout memCnt StatePull.toRaw (by decide) (by decide),
    bcT_filter kLout StatePush.toRaw (by decide) (by decide),
    bcT_filter kLout StatePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

/-- The bytecode pair balances: every executed slot read once, the seeds and finalizes of all
thirty-two. -/
theorem walk_bytecode_balanced :
    BalancedPair (walkW kLout 1 g memCnt) BytecodePull.toRaw BytecodePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, walkW, mkW, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter kLout memCnt BytecodePush.toRaw (by decide) (by decide),
    memT_filter kLout memCnt BytecodePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

/-- The memory pair, reduced to the touched cells: with the block's seeds and finalizes split
at cell `touched` and the untouched suffix cancelled, balance is a permutation the kernel
decides. -/
theorem mem_balanced_iff (L : Vector K 25) (c rA : K) (cnt : ℕ → K)
    (h : ∀ i, touched ≤ i → cnt i = 1) :
    BalancedPair (walkW L c rA cnt) MemPull.toRaw MemPush.toRaw ↔
      (List.map (·.msg) (List.filter (·.channel.name = MemPush.toRaw.name)
        ((walkW L c rA cnt).verifierTable.interactions ++ (xorT L).interactions ++
          (mulT L rA).interactions ++ (setT L c).interactions ++ (derefT L).interactions ++
          (jumpT L).interactions ++ (kT L).interactions)) ++
        List.ofFn fun i : Fin touched ↦ seedMsg L (Fin.castAdd untouched i)).Perm
      (List.map (·.msg) (List.filter (·.channel.name = MemPull.toRaw.name)
        ((walkW L c rA cnt).verifierTable.interactions ++ (xorT L).interactions ++
          (mulT L rA).interactions ++ (setT L c).interactions ++ (derefT L).interactions ++
          (jumpT L).interactions ++ (kT L).interactions)) ++
        List.ofFn fun i : Fin touched ↦ finMsg L cnt (Fin.castAdd untouched i)) := by
  unfold BalancedPair messagesOn
  rw [EnsembleWitness.interactions]
  simp only [EnsembleWitness.allTables, walkW, mkW, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.filter_append, List.map_append,
    bcT_filter L MemPush.toRaw (by decide) (by decide),
    bcT_filter L MemPull.toRaw (by decide) (by decide), memT_pushes, memT_pulls,
    seeds_split, fins_split L cnt h, ← List.append_assoc]
  exact List.perm_append_right_iff _

/-- The memory pair balances. -/
theorem walk_mem_balanced : BalancedPair (walkW kLout 1 g memCnt) MemPull.toRaw MemPush.toRaw := by
  rw [mem_balanced_iff kLout 1 g memCnt fun _ ↦ memCnt_of_ge]
  simp only [table_interactions_eq]
  decide +kernel

/-- Every read count is nonzero. -/
theorem walk_countsNonzero : CountsNonzero (walkW kLout 1 g memCnt) := by
  unfold CountsNonzero
  simp only [walkW, mkW, table_interactions_eq]
  decide +kernel

/-- A witness over the data of the lanes `L` whose tables are within the row cap is within the
caps: the memory log-size is `16`. -/
theorem caps_of {w : EnsembleWitness (leanIsaEnsemble walkProg)} (L : Vector K 25)
    (hd : w.data = walkData L) (h : ∀ t ∈ w.tables, t.table.length ≤ 2 ^ maxLogRows) : Caps w where
  minLogMem_le := by rw [hd, walk_logSize]
  le_maxLogMem := by rw [hd, walk_logSize]; decide
  heights := h
  well_shaped := hd ▸ walk_wellShaped L

/-- The caps: `κ = 16`, heights `1, 1, 2, 1, 4, 1, 2^16, 2^5`; for every count and lane. -/
theorem walk_caps (L : Vector K 25) (c rA : K) (cnt : ℕ → K) : Caps (walkW L c rA cnt) := by
  refine caps_of L rfl ?_
  intro t ht
  simp only [walkW, mkW, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show (xorT L).table.length = 1 from rfl).trans_le (by decide)
  · exact (show (mulT L rA).table.length = 1 from rfl).trans_le (by decide)
  · exact (show (setT L c).table.length = 2 from rfl).trans_le (by decide)
  · exact (show (derefT L).table.length = 1 from rfl).trans_le (by decide)
  · exact (show (jumpT L).table.length = 4 from rfl).trans_le (by decide)
  · rw [kT_table, List.length_map, List.length_singleton]; decide
  · rw [memT_table, List.length_ofFn]; decide
  · rw [bcT_table, List.length_ofFn]; decide

/-- The index column is the row index, for every count and lane. -/
theorem walk_indexColumns (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    IndexColumnsAreRowIndices (walkW L c rA cnt) := by
  intro i hi
  simp only [memBlockRows_eq]
  rw [List.getElem_ofFn, memRowArr, memRowAt_toElements]

/-- The seed-rows conjunct over any image `s` equal to the fixture's: substituting the image
before anything is compared, since a rewrite under the conjunct's dependent binders unrolls
the data. -/
theorem seedRows_gen (L : Vector K 25) {tables : List (Air.Flat.Table K)} {pi : PublicIO K}
    {h1 h2 h3} (cnt : ℕ → K) (hrows : memBlockRows (⟨tables, walkData L, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble walkProg)) = List.ofFn (memRowArr L cnt))
    (s : (κ : ℕ) × MemImage κ) (hs : s = ⟨minLogMem, walkImage L⟩) :
    ∃ idx cntFin : Fin (2 ^ s.1) → K,
      memBlockRows (⟨tables, walkData L, pi, h1, h2, h3⟩ :
        EnsembleWitness (leanIsaEnsemble walkProg)) = List.ofFn fun i ↦
          (toElements (⟨idx i, cntFin i, #v[(s.2 i).limb 0, (s.2 i).limb 1, (s.2 i).limb 2]⟩ :
            MemRow K)).toArray := by
  subst hs
  exact ⟨fun i ↦ gpow i, fun i ↦ cnt i, hrows⟩

/-- A witness over the fixture's data whose memory block is the honest one, with any finalize
counts, has the image as its seed rows. Stated over a destructured witness, so that its
`data` is the constant `walkData L`. -/
theorem seedRows_of (L : Vector K 25) {tables : List (Air.Flat.Table K)} {pi : PublicIO K}
    {h1 h2 h3} (cnt : ℕ → K) (hrows : memBlockRows (⟨tables, walkData L, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble walkProg)) = List.ofFn (memRowArr L cnt)) :
    SeedRowsAreTheImage (⟨tables, walkData L, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble walkProg)) := by
  unfold SeedRowsAreTheImage
  dsimp only
  exact seedRows_gen L cnt hrows (imageOf (walkData L)) (walk_imageOf L)

/-- The memory block's rows are the image, for every count and lane. -/
theorem walk_seedRows (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    SeedRowsAreTheImage (walkW L c rA cnt) :=
  seedRows_of L cnt (memBlockRows_eq L c rA cnt)

/-- The bytecode block's rows are the program's, with the honest counts. -/
theorem walk_bytecodeRows (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    BytecodeRowsAreTheProgram walkProg (walkW L c rA cnt) :=
  ⟨bcCntFin, by rw [bytecodeBlockRows, tableAt_seven, bcT_table]⟩

/-- The executor's input lanes permute to its output lanes (the table tests' `keccak_lanes`):
one kernel evaluation of Keccak-f[1600]. -/
theorem keccak_lanes :
    ∀ l : Fin 25, stateLanes (keccakF (laneState fun l ↦ kLin[l])) l = kLout[l] := by
  decide +kernel

/-- The honest `KECCAK` row satisfies the relation. -/
theorem kRow_relation : KeccakRelation (kRow kLout) := by
  funext l
  exact (keccak_lanes l).symm

/-- The `KECCAK` table is valid, for every count. -/
theorem walk_keccakValid (c rA : K) (cnt : ℕ → K) : KeccakRowsValid (walkW kLout c rA cnt) := by
  intro r hr
  rw [keccakRows, tableAt_five, kT_table, List.map_singleton, List.mem_singleton] at hr
  subst hr
  rw [rawRow, keccakRowAt_toElements]
  exact kRow_relation

/-- The two public words sit at `g^0` and `g^1` of the image the data names, whatever the output
lanes. -/
theorem walk_word0 (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    (imageOf (walkW L c rA cnt).data).2.read (gpow 0) = some mulInput.word0 := by
  rw [data_eq, walk_imageOf]
  exact read_at L 0 mulInput.word0

theorem walk_word1 (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    (imageOf (walkW L c rA cnt).data).2.read (gpow 1) = some mulInput.word1 := by
  rw [data_eq, walk_imageOf]
  exact read_at L 1 mulInput.word1

/-- The honest witness satisfies the constraint statement. -/
theorem walk_satisfiedBy : SatisfiedBy walkProg mulInput (walkW kLout 1 g memCnt) where
  public_input_eq := rfl
  constraints := walk_constraints kLout 1 g memCnt
  state_balanced := walk_state_balanced
  mem_balanced := walk_mem_balanced
  bytecode_balanced := walk_bytecode_balanced
  counts_nonzero := walk_countsNonzero
  caps := walk_caps kLout 1 g memCnt
  index_columns := walk_indexColumns kLout 1 g memCnt
  seed_rows := walk_seedRows kLout 1 g memCnt
  bytecode_rows := walk_bytecodeRows kLout 1 g memCnt
  keccak_valid := walk_keccakValid 1 g memCnt
  word0_eq := walk_word0 kLout 1 g memCnt
  word1_eq := walk_word1 kLout 1 g memCnt

/-! ## The witness represents the trace -/

/-- Each of the run's four steps is one row's state pull and push. -/
theorem walk_regs_embed :
    ∀ k (hk : k + 1 < walkTrace.regs.length),
      RowSteps (walkW kLout 1 g memCnt) walkTrace.regs[k] walkTrace.regs[k + 1] := by
  intro k hk
  have hk' : k < 4 := by rw [walk_regs] at hk; exact Nat.lt_of_succ_lt_succ hk
  simp only [walk_regs]
  interval_cases k
  · show RowSteps (walkW kLout 1 g memCnt) ⟨1, 1⟩ ⟨gpow 1, 1⟩
    exact ⟨setT kLout 1, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      rawRow (setRow0 1), List.mem_cons_self,
      by rw [rowMessagesOn_eq]; decide +kernel, by rw [rowMessagesOn_eq]; decide +kernel⟩
  · show RowSteps (walkW kLout 1 g memCnt) ⟨gpow 1, 1⟩ ⟨gpow 2, 1⟩
    exact ⟨setT kLout 1, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      rawRow setRow1, List.mem_cons_of_mem _ List.mem_cons_self,
      by rw [rowMessagesOn_eq]; decide +kernel, by rw [rowMessagesOn_eq]; decide +kernel⟩
  · show RowSteps (walkW kLout 1 g memCnt) ⟨gpow 2, 1⟩ ⟨gpow 3, 1⟩
    exact ⟨mulT kLout g, List.mem_cons_of_mem _ List.mem_cons_self, rawRow (mulRow g),
      List.mem_cons_self,
      by rw [rowMessagesOn_eq]; decide +kernel, by rw [rowMessagesOn_eq]; decide +kernel⟩
  · show RowSteps (walkW kLout 1 g memCnt) ⟨gpow 3, 1⟩ ⟨gpow 31, 1⟩
    exact ⟨jumpT kLout, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))), jumpRaw jumpRow3 1 1, List.mem_cons_self,
      by rw [rowMessagesOn_eq]; decide +kernel, by rw [rowMessagesOn_eq]; decide +kernel⟩

/-- A witness over the fixture's data whose rows step the trace represents it. Stated over a
destructured witness, so that its `data` is the constant `walkData kLout` and no field is
compared against a projection of the witness. -/
theorem represents_of {tables : List (Air.Flat.Table K)} {pi : PublicIO K} {h1 h2 h3}
    (hregs : ∀ k (hk : k + 1 < walkTrace.regs.length),
      RowSteps (⟨tables, walkData kLout, pi, h1, h2, h3⟩ :
        EnsembleWitness (leanIsaEnsemble walkProg)) walkTrace.regs[k] walkTrace.regs[k + 1]) :
    AssignmentRepresents (⟨tables, walkData kLout, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble walkProg)) walkTrace where
  κ_eq := walk_logSize kLout
  image_eq := fun i hi ↦ walk_image_apply' kLout i (by rw [walk_logSize]; exact hi)
  regs_embed := hregs

/-- The honest witness represents the trace: the completeness instance for this program,
by hand. -/
theorem walk_represents : AssignmentRepresents (walkW kLout 1 g memCnt) walkTrace :=
  represents_of walk_regs_embed

/-- The completeness instance for this program: the trace is a valid execution, the
witness satisfies the statement and represents the trace. -/
theorem walk_t1_instance : ValidExecution walkProg mulInput walkTrace ∧
    SatisfiedBy walkProg mulInput (walkW kLout 1 g memCnt) ∧
      AssignmentRepresents (walkW kLout 1 g memCnt) walkTrace :=
  ⟨⟨walk_boundary, walk_run⟩, walk_satisfiedBy, walk_represents⟩

/-- The image the witness names is the trace's, as one equality. -/
example : imageOf (walkW kLout 1 g memCnt).data = ⟨minLogMem, walkImage kLout⟩ :=
  assignmentRepresents_image walk_represents

/-! ## Rejections -/

/-- A wrong finalize count: cell `4` is read once, its finalize count `1` instead of `g`. -/
def wrongCnt (i : ℕ) : K := if i = 4 then 1 else memCnt i

theorem wrongCnt_of_ge {i : ℕ} (h : 44 ≤ i) : wrongCnt i = 1 := by
  unfold wrongCnt
  rw [ite_eq_right (by omega), memCnt_of_ge h]

/-- Nothing checks the finalize counts (§6.2): the block accepts the row, and the bus does not
balance. -/
example : ¬ BalancedPair (walkW kLout 1 g wrongCnt) MemPull.toRaw MemPush.toRaw := by
  rw [mem_balanced_iff kLout 1 g wrongCnt fun _ ↦ wrongCnt_of_ge]
  simp only [table_interactions_eq]
  decide +kernel

/-- The finalize counts of a read count `0` at cell `2`: the first `SET_CONSTANT` row's read
pulls and pushes `(g^2, 0, x)`, the product row's read is then the first, and the cell is
finalized at `g`. -/
def zeroCnt (i : ℕ) : K := if i = 2 then g else memCnt i

theorem zeroCnt_of_ge {i : ℕ} (h : 44 ≤ i) : zeroCnt i = 1 := by
  unfold zeroCnt
  rw [ite_eq_right (by omega), memCnt_of_ge h]

/-- The zero-count witness balances the memory pair: a pull and a push of one tuple cancel,
which is what the count product exists to reject (§6.2 "The count product", Theorem 6.4). -/
theorem zero_mem_balanced :
    BalancedPair (walkW kLout 0 1 zeroCnt) MemPull.toRaw MemPush.toRaw := by
  rw [mem_balanced_iff kLout 0 1 zeroCnt fun _ ↦ zeroCnt_of_ge]
  simp only [table_interactions_eq]
  decide +kernel

theorem zero_state_balanced :
    BalancedPair (walkW kLout 0 1 zeroCnt) StatePull.toRaw StatePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, walkW, mkW,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter kLout zeroCnt StatePush.toRaw (by decide) (by decide),
    memT_filter kLout zeroCnt StatePull.toRaw (by decide) (by decide),
    bcT_filter kLout StatePush.toRaw (by decide) (by decide),
    bcT_filter kLout StatePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

theorem zero_bytecode_balanced :
    BalancedPair (walkW kLout 0 1 zeroCnt) BytecodePull.toRaw BytecodePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, walkW, mkW,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter kLout zeroCnt BytecodePush.toRaw (by decide) (by decide),
    memT_filter kLout zeroCnt BytecodePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

/-- The count product is load-bearing: the zero-count witness satisfies every other conjunct
of `SatisfiedBy` and fails `CountsNonzero` (§6.2 "The count product"). -/
theorem zero_count_witness :
    (walkW kLout 0 1 zeroCnt).publicInput = PublicIO.ofInput mulInput ∧
    (walkW kLout 0 1 zeroCnt).Constraints ∧
    BalancedPair (walkW kLout 0 1 zeroCnt) StatePull.toRaw StatePush.toRaw ∧
    BalancedPair (walkW kLout 0 1 zeroCnt) MemPull.toRaw MemPush.toRaw ∧
    BalancedPair (walkW kLout 0 1 zeroCnt) BytecodePull.toRaw BytecodePush.toRaw ∧
    Caps (walkW kLout 0 1 zeroCnt) ∧ IndexColumnsAreRowIndices (walkW kLout 0 1 zeroCnt) ∧
    SeedRowsAreTheImage (walkW kLout 0 1 zeroCnt) ∧
    BytecodeRowsAreTheProgram walkProg (walkW kLout 0 1 zeroCnt) ∧
    KeccakRowsValid (walkW kLout 0 1 zeroCnt) ∧
    (imageOf (walkW kLout 0 1 zeroCnt).data).2.read (gpow 0) = some mulInput.word0 ∧
    (imageOf (walkW kLout 0 1 zeroCnt).data).2.read (gpow 1) = some mulInput.word1 ∧
    ¬ CountsNonzero (walkW kLout 0 1 zeroCnt) :=
  ⟨rfl, walk_constraints kLout 0 1 zeroCnt, zero_state_balanced, zero_mem_balanced,
    zero_bytecode_balanced, walk_caps kLout 0 1 zeroCnt, walk_indexColumns kLout 0 1 zeroCnt,
    walk_seedRows kLout 0 1 zeroCnt, walk_bytecodeRows kLout 0 1 zeroCnt,
    walk_keccakValid 0 1 zeroCnt, walk_word0 kLout 0 1 zeroCnt, walk_word1 kLout 0 1 zeroCnt, by
      unfold CountsNonzero
      simp only [walkW, mkW, table_interactions_eq]
      decide +kernel⟩

/-- A wrong output lane: lane `0` plus one, a canonical word, written consistently in the
`KECCAK` row and in its output cell `0` of the image (cell `25`). -/
def wrongLout : Vector K 25 := kLout.set 0 (kLout[0] + 1)

/-- The wrong row fails the relation: its lane `0` is not Keccak-f[1600]'s. -/
theorem kRow_wrong_no_relation : ¬ KeccakRelation (kRow wrongLout) := by
  intro h
  exact absurd ((congrFun h 0).trans (keccak_lanes 0)) (by decide +kernel)

/-- The permutation is checked (§8.5): the wrong output lane fails `KeccakRowsValid`. -/
theorem wrong_lane_not_valid : ¬ KeccakRowsValid (walkW wrongLout 1 g memCnt) := fun h ↦
  kRow_wrong_no_relation (by
    have hrel := h (rawRow (kRow wrongLout)) (by
      rw [keccakRows, tableAt_five, kT_table]
      exact List.mem_cons_self)
    rwa [rawRow, keccakRowAt_toElements] at hrel)

theorem wrong_mem_balanced :
    BalancedPair (walkW wrongLout 1 g memCnt) MemPull.toRaw MemPush.toRaw := by
  rw [mem_balanced_iff wrongLout 1 g memCnt fun _ ↦ memCnt_of_ge]
  simp only [table_interactions_eq]
  decide +kernel

theorem wrong_state_balanced :
    BalancedPair (walkW wrongLout 1 g memCnt) StatePull.toRaw StatePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, walkW, mkW,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter wrongLout memCnt StatePush.toRaw (by decide) (by decide),
    memT_filter wrongLout memCnt StatePull.toRaw (by decide) (by decide),
    bcT_filter wrongLout StatePush.toRaw (by decide) (by decide),
    bcT_filter wrongLout StatePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

theorem wrong_bytecode_balanced :
    BalancedPair (walkW wrongLout 1 g memCnt) BytecodePull.toRaw BytecodePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, walkW, mkW,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter wrongLout memCnt BytecodePush.toRaw (by decide) (by decide),
    memT_filter wrongLout memCnt BytecodePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

/-- The permutation is the Keccak reduction's alone (§8.5): the witness with the wrong output
lane, consistent in the row and in the image, satisfies every other conjunct of `SatisfiedBy`
and fails `KeccakRowsValid`. It fails no constraint: the table has none (`keccak_constraints`),
and the bus binds the lanes to the cells, which hold the wrong lane too. -/
theorem wrong_lane_witness :
    (walkW wrongLout 1 g memCnt).publicInput = PublicIO.ofInput mulInput ∧
    (walkW wrongLout 1 g memCnt).Constraints ∧
    BalancedPair (walkW wrongLout 1 g memCnt) StatePull.toRaw StatePush.toRaw ∧
    BalancedPair (walkW wrongLout 1 g memCnt) MemPull.toRaw MemPush.toRaw ∧
    BalancedPair (walkW wrongLout 1 g memCnt) BytecodePull.toRaw BytecodePush.toRaw ∧
    CountsNonzero (walkW wrongLout 1 g memCnt) ∧
    Caps (walkW wrongLout 1 g memCnt) ∧ IndexColumnsAreRowIndices (walkW wrongLout 1 g memCnt) ∧
    SeedRowsAreTheImage (walkW wrongLout 1 g memCnt) ∧
    BytecodeRowsAreTheProgram walkProg (walkW wrongLout 1 g memCnt) ∧
    (imageOf (walkW wrongLout 1 g memCnt).data).2.read (gpow 0) = some mulInput.word0 ∧
    (imageOf (walkW wrongLout 1 g memCnt).data).2.read (gpow 1) = some mulInput.word1 ∧
    ¬ KeccakRowsValid (walkW wrongLout 1 g memCnt) :=
  ⟨rfl, walk_constraints wrongLout 1 g memCnt, wrong_state_balanced, wrong_mem_balanced,
    wrong_bytecode_balanced, by
      unfold CountsNonzero
      simp only [walkW, mkW, table_interactions_eq]
      decide +kernel,
    walk_caps wrongLout 1 g memCnt, walk_indexColumns wrongLout 1 g memCnt,
    walk_seedRows wrongLout 1 g memCnt, walk_bytecodeRows wrongLout 1 g memCnt,
    walk_word0 wrongLout 1 g memCnt, walk_word1 wrongLout 1 g memCnt, wrong_lane_not_valid⟩

/-- The memory block with its index column shifted by one row. -/
def memRowArrShift (i : Fin (2 ^ minLogMem)) : Array K :=
  (toElements (⟨gpow (i + 1), memCnt i,
    #v[(walkImage kLout i).limb 0, (walkImage kLout i).limb 1, (walkImage kLout i).limb 2]⟩ :
      MemRow K)).toArray

def memTShift : Air.Flat.Table K :=
  mkT kLout memTable (size MemRow) (List.ofFn memRowArrShift) (by
    intro r hr
    rw [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    exact Vector.size_toArray _)

def idxW : EnsembleWitness (leanIsaEnsemble walkProg) :=
  mkW kLout [xorT kLout, mulT kLout g, setT kLout 1, derefT kLout, jumpT kLout, kT kLout,
    memTShift, bcT kLout]

theorem idxW_memBlockRows : memBlockRows idxW = List.ofFn memRowArrShift := by
  rw [memBlockRows, show tableAt idxW 6 = memTShift from rfl]
  dsimp only [memTShift, mkT]

/-- The index column is checked (§6.5): row `0` carrying `g^1` fails
`IndexColumnsAreRowIndices`. -/
example : ¬ IndexColumnsAreRowIndices idxW := fun h ↦ by
  have h0 := h 0 (by rw [idxW_memBlockRows, List.length_ofFn]; decide)
  simp only [idxW_memBlockRows, List.getElem_ofFn, memRowArrShift, memRowAt_toElements] at h0
  revert h0
  decide +kernel

/-- The public words are checked (§8.2): `input₀ = 3` in place of `1` fails `word0_eq`. -/
example : ¬ SatisfiedBy walkProg ⟨![K.ofBits 3, 0, K.ofBits 2, 0]⟩ (walkW kLout 1 g memCnt) :=
  fun h ↦ by
    have h0 := h.word0_eq
    rw [walk_word0] at h0
    have h1 := congrArg (fun o : Option E ↦ (o.getD 0).limb 0) h0
    revert h1
    decide +kernel

/-- A three-row `SET_CONSTANT` table, not a power of two. -/
def setT3 : Air.Flat.Table K :=
  mkT kLout setTable (size SetRow) ([setRow0 1, setRow1, setRow1].map rawRow)
    (rawRows_size [setRow0 1, setRow1, setRow1])

def heightW : EnsembleWitness (leanIsaEnsemble walkProg) :=
  mkW kLout [xorT kLout, mulT kLout g, setT3, derefT kLout, jumpT kLout, kT kLout,
    memT kLout memCnt, bcT kLout]

/-- A row count that is not a power of two is within the caps (`crates/verifier/src/layout.rs`,
`build_layout`, at `3a37fb6e1`: a table's height is the least power of two holding its rows):
`Caps` bounds each table's rows by `2^MAX_LOG_ROWS` and nothing else. -/
example : Caps heightW := by
  refine caps_of kLout rfl ?_
  intro t ht
  simp only [heightW, mkW, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [kT_table, List.length_map, List.length_singleton]; decide
  · rw [memT_table, List.length_ofFn]; decide
  · rw [bcT_table, List.length_ofFn]; decide

/-- Four `KECCAK` rows, the honest row repeated. -/
def kT4 : Air.Flat.Table K :=
  mkT kLout keccakTable (size KeccakRow) ((List.replicate 4 (kRow kLout)).map rawRow)
    (rawRows_size (List.replicate 4 (kRow kLout)))

theorem kT4_table : kT4.table = (List.replicate 4 (kRow kLout)).map rawRow := by
  dsimp only [kT4, mkT]

def floorW : EnsembleWitness (leanIsaEnsemble walkProg) :=
  mkW kLout [xorT kLout, mulT kLout g, setT kLout 1, derefT kLout, jumpT kLout, kT4,
    memT kLout memCnt, bcT kLout]

/-- There is no `KECCAK` floor: four rows are within the caps. -/
example : Caps floorW := by
  refine caps_of kLout rfl ?_
  intro t ht
  simp only [floorW, mkW, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [kT4_table, List.length_map, List.length_replicate]; decide
  · rw [memT_table, List.length_ofFn]; decide
  · rw [bcT_table, List.length_ofFn]; decide

end LeanVMTests.Arithmetization.Statement
