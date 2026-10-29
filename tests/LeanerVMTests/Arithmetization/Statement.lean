import LeanerVM.Arithmetization.Completeness.Basics

/-!
# Layer 8 tests: the constraint statement

A classic test for kernel evaluation: the fixture decides `K` and `E` arithmetic and the
bus permutations in the kernel.

**The fixture** is one hand-built witness of `SatisfiedBy` for the Layer 3 program, the
executor's `mul_192bit_word` (`crates/lean_vm/src/cpu/mod.rs:982-999`, `tests/LeanerVMTests/
Semantics/Execution.lean`), extended in the shape of the compiler's fill blocks, simplified: a
`JUMP` to the sentinel after the three instructions, and the fill blocks every table needs to
reach a power-of-two height (§8.3; `crates/lean_vm/src/cpu/filler.rs:36-87`, emitted by
`crates/lean_compiler/src/filler.rs`; roadmap acceptance test 15): one `XOR`, one `DEREF`,
eight `BLAKE2S` rows (the verifier's floor, `cpu/mod.rs:166`), each block a closed walk ending
in a `JUMP` back to its first instruction, run in a frame disjoint from the program's own (the
compiler's closing `JUMP` reuses one frame cell as condition and destination and its dummy
`JUMP` falls through; the fixture's use distinct cells). The thirty-two-slot program
`fillProg` runs four steps from `(1, 1)` to `(g^31, 1)` (`fill_run`, a `ValidExecution`), and
its honest witness `fillW 1 g memCnt` at the minimum memory size `2^16` satisfies every
conjunct of `SatisfiedBy` (`fill_satisfiedBy`) and represents the trace (`fill_represents`):
the completeness instance of T1 for this program, by hand (`fill_t1_instance`). The witness
is parametric in the first `SET_CONSTANT` row's read count, the product row's read count of
`x`, and the memory block's finalize counts, so that the rejections below are the honest
witness with one thing changed.

**What the proofs exercise.** The eight tables are built with `tableOf` and the witness with
`witnessOfTables`, so its prover data is derived from the tables: the image the data names is
read off the memory block's rows (`fill_memRows_get?`, `fill_imageOf`), never stated. The two
blocks' rows agree with their fixed columns (`memRows_fixed`, `bcRows_fixed`). The memory
block's `2^16` rows are built by `List.ofFn` and never enumerated: its constraints hold
row-generically (the block has none), its interactions on a foreign channel are `[]` by a lemma
(`memT_filter`), and its share of the memory channel is split (`List.ofFn_add`) into the
twenty-nine cells the run touches, decided in the kernel with the tables' reads, and the
untouched suffix, whose seed and finalize messages coincide because its finalize counts are `1`
(`memCnt_of_ge`). The kernel evaluates a table's interactions through Clean's
`Component.rowOperations` (`intsOver`, `table_interactions_eq`), since `Component.operations`
reaches them through `instantiate` and `toSubcircuit`, which the kernel does not unfold (status
finding E8), and the active messages of a direction in their multiplicity-`1` form
(`activeMessages_of_mults`), since Clean decides `mult ≠ 0` by the field's generic equality,
which the kernel does not reduce. Balance is Clean's multiset check on the three channels
(`balanced_of`): every multiplicity `1`, fewer than `2^64` interactions, and each channel's
pushes a permutation of its pulls.

**Rejections**, each the honest witness with one thing changed, and each failing exactly the
conjunct named. A wrong finalize count unbalances the memory channel (§6.2 "Nothing checks the
finalize counts"): cell `4`'s finalize count `1` instead of `g`. A read count of `0` that
*balances* fails `CountsNonzero` alone (§6.2 "The count product"): the first `SET_CONSTANT`
row reads `x` with count `0`, a pull and a push of one tuple, the product row then reads `x`
first, and every other conjunct still holds (`zero_count_witness`). A wrong digest fails
`Blake2sRowsValid` (§8.5). A memory block whose index column is shifted is no table of the
block: it disagrees with the fixed address column (§6.5), so no witness has it. A wrong public
word fails `word0_eq` (§8.2). A three-row table and a four-row `BLAKE2S` table fail `Caps`
(`read_public`).
-/

namespace LeanerVMTests.Arithmetization.Statement

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open Air.Flat (Component EnsembleWitness)

/-! ## The fixture: `mul_192bit_word` with fill blocks -/

-- scripts/dump-mul-rust.sh at leanVM a386121f
def mulX : E :=
  E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfeedfacedeadbeef) (K.ofBits 0x1111222233334444)
def mulY : E :=
  E.ofLimbs (K.ofBits 0x9999aaaabbbbcccc) (K.ofBits 0x13579bdf2468ace0) (K.ofBits 0x5555666677778888)
def mulXY : E :=
  E.ofLimbs (K.ofBits 0xf4bccd9a2e8e525b) (K.ofBits 0xf85ebb9433986f2f) (K.ofBits 0x918137982bf175ac)

-- scripts/dump-blake2s-rust.sh at leanVM a386121f: the nine cells of the executor's row.
def rustM0 : E := E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfedcba9876543210) 0
def rustM1 : E := E.ofLimbs (K.ofBits 0x1111222233334444) (K.ofBits 0x5555666677778888) 0
def rustM2 : E := E.ofLimbs (K.ofBits 0xdeadbeefcafebabe) (K.ofBits 0x0badf00d0badf00d) 0
def rustM3 : E := E.ofLimbs (K.ofBits 0x9999aaaabbbbcccc) (K.ofBits 0xddddeeeeffff0000) 0
def rustCv0 : E := E.ofLimbs (K.ofBits 0x0000000000000007) 0 0
def rustCv1 : E := E.ofLimbs (K.ofBits 0x000000000000000b) 0 0
def rustMd : E := E.ofLimbs (K.ofBits 0x0000000000000040) (K.ofBits 0x00000000ffffffff) 0
def rustOut0 : E := E.ofLimbs (K.ofBits 0x583fffe1350e2137) (K.ofBits 0x0de9e32629a5c508) 0
def rustOut1 : E := E.ofLimbs (K.ofBits 0xf1b0679a15df60bb) (K.ofBits 0x0228c8d4ed9b3a24) 0

/-- The public input `[w(1), w(2)]`. -/
def mulInput : PublicInput := ⟨![1, 0, K.ofBits 2, 0]⟩

/-- A word of `K` as a cell. -/
def cellK (a : K) : E := E.ofLimbs a 0 0

/-- The program: the executor's three instructions in frame `1` (slots `0..2`), a `JUMP` to the
sentinel (`3`), an `XOR` fill block in frame `g^5` (`4`, `5`), a `DEREF` fill block in the same
frame (`6`, `7`), a `BLAKE2S` fill block of eight rows in frame `g^14` (`8..16`), never-executed
filler (`17..30`) and the sentinel (`31`, not a `JUMP`). Each block's `JUMP` reads `c = 1`, its
block's first counter `d`, and its own frame `f`. -/
def fillProg : Program :=
  ⟨5, by decide, fun i ↦
    match (i : ℕ) with
    | 0 => .setConstant (gpow 2) mulX
    | 1 => .setConstant (gpow 3) mulY
    | 2 => .mulNative (gpow 2) (gpow 3) (gpow 4)
    | 3 => .jump (gpow 26) (gpow 27) (gpow 28)
    | 4 => .xor 1 1 1
    | 5 => .jump g (gpow 2) (gpow 6)
    | 6 => .deref (gpow 6) 1 1 .cell
    | 7 => .jump g (gpow 3) (gpow 6)
    | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
      .blake2s ![gpow 2, gpow 3, gpow 4, gpow 5] 1 (gpow 6) (gpow 8)
    | 16 => .jump (gpow 9) (gpow 10) (gpow 11)
    | _ => .xor 1 1 1⟩

/-- The twenty-nine cells the run and the fill blocks touch, by index; every other cell of the
image is `0`. Frame `1`: the public words (`0`, `1`), the operands and the product (`2..4`),
the sentinel `JUMP`'s `c, d, f` (`26..28`). Frame `g^5`: the `XOR` and `DEREF` cell (`5`),
`c` (`6`), the two blocks' `d` (`7`, `8`), the pointer and `f` (`11`). Frame `g^14`: the
`BLAKE2S` cells in the executor's layout (`14..22`) and the block's `c, d, f` (`23..25`). -/
def fillCells : Array E :=
  #[cellK 1, cellK (K.ofBits 2), mulX, mulY, mulXY,
    0, cellK 1, cellK (gpow 4), cellK (gpow 6), 0, 0, cellK (gpow 5), 0, 0,
    rustCv0, rustCv1, rustM0, rustM1, rustM2, rustM3, rustOut0, rustOut1, rustMd,
    cellK 1, cellK (gpow 8), cellK (gpow 14),
    cellK 1, cellK (gpow 31), cellK 1]

/-- The image, at the minimum size `2^16`. -/
def fillImage : MemImage minLogMem := fun i ↦ (fillCells[(i : ℕ)]?).getD 0

/-- The trace: four steps. -/
def fillTrace : Trace fillProg := ⟨minLogMem, fillImage, 4⟩

/-- The honest finalize counts `g^A[i]` of the touched cells; `1` elsewhere (`memCnt`). -/
def fillCounts : Array K :=
  #[1, 1, g ^ 2, g ^ 2, g, g ^ 5, g ^ 2, g, g, 1, 1, g ^ 3, 1, 1,
    g ^ 8, g ^ 8, g ^ 8, g ^ 8, g ^ 8, g ^ 8, g ^ 8, g ^ 8, g ^ 8, g, g, g, g, g, g]

/-- The finalize count of cell `i`. -/
def memCnt (i : ℕ) : K := (fillCounts[i]?).getD 1

/-- Past the touched cells every finalize count is `1`: the cell was never read. -/
theorem memCnt_of_ge {i : ℕ} (h : 29 ≤ i) : memCnt i = 1 := by
  have hs : fillCounts.size = 29 := rfl
  unfold memCnt
  rw [Array.getElem?_eq_none (hs ▸ h)]
  rfl

/-- The finalize count of slot `i`: every slot up to `16` executes once. -/
def bcCnt (i : ℕ) : K := if i ≤ 16 then g else 1

/-- The same, as the bytecode block's finalize-count column. -/
def bcCntFin (i : Fin (2 ^ fillProg.logSize)) : K := bcCnt i

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
def jumpRow3 : JumpRow K := ⟨gpow 3, 1, gpow 26, gpow 27, gpow 28, 1, gpow 31, 1, 1, 1, 1, 1⟩

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

-- Frame `g^14`: the `BLAKE2S` block.
/-- The two limbs of a canonical cell. -/
def cell (v : E) : Vector K 2 := #v[v.limb 0, v.limb 1]
/-- Slot `8 + j`, the executor's `BLAKE2S` row in frame `g^14`: the `j`-th read of each of its
nine cells. -/
def blakeRow (j : Fin 8) : Blake2sRow K :=
  ⟨gpow (8 + j), gpow 14, gpow 2, gpow 3, gpow 4, gpow 5, 1, gpow 6, gpow 8,
    cell rustM0, cell rustM1, cell rustM2, cell rustM3, cell rustOut0, cell rustOut1,
    cell rustCv0, cell rustCv1, cell rustMd,
    gpow j, gpow j, gpow j, gpow j, gpow j, gpow j, gpow j, gpow j, gpow j, 1⟩
/-- Slot `16`, the `JUMP` back to slot `8`. -/
def jumpRow16 : JumpRow K :=
  ⟨gpow 16, gpow 14, gpow 9, gpow 10, gpow 11, 1, gpow 8, gpow 14, 1, 1, 1, 1⟩

/-- A `JUMP` row with its two local witnesses `w = 1`, `b = 1` (every condition is `1`). -/
def jumpRaw (r : JumpRow K) : Array K := rawRow r ++ #[1, 1]

theorem jumpRaw_size (rs : List (JumpRow K)) :
    ∀ r ∈ rs.map jumpRaw, r.size = jumpComponent.width := by
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨_, -, rfl⟩ := hr
  rw [jumpRaw, Array.size_append, rawRow_size]
  rfl

/-- Row `i` of the memory block: `(g^i, cnt i, mem[i])`, the raw form of the typed row. -/
def memRowArr (cnt : ℕ → K) (i : Fin (2 ^ minLogMem)) : Array K :=
  (toElements (⟨gpow i, cnt i,
    #v[(fillImage i).limb 0, (fillImage i).limb 1, (fillImage i).limb 2]⟩ : MemRow K)).toArray

/-- The memory row's five coordinates, without evaluating the block's row list. -/
theorem memRowArr_eq (cnt : ℕ → K) (i : Fin (2 ^ minLogMem)) :
    memRowArr cnt i =
      #[gpow i, cnt i, (fillImage i).limb 0, (fillImage i).limb 1, (fillImage i).limb 2] := by
  with_unfolding_all rfl


/-! ## The tables and the witness -/

/-- A typed row read back from its raw row. -/
theorem fromElements_rawRow {Row : TypeMap} [ProvableType Row] (r : Row K) :
    (fromElements (Air.Flat.rowPrefix (size Row) (rawRow r)) : Row K) = r :=
  (Air.Flat.valueFromOffset_fromArray (rawRow r) fun _ _ ↦ #[]).symm.trans (rowAt_toElements _ r)

/-- An eight-coordinate entry is its opcode followed by its seven operand slots. -/
theorem cons_append_ops (e : Vector K 8) :
    #v[e[0]] ++ #v[e[1], e[2], e[3], e[4], e[5], e[6], e[7]] = e := by
  ext j hj
  interval_cases j <;> rfl

/-- A table of the witness: a component and its rows. A demand component has no fixed column. -/
def mkT (c : Component K) (rows : List (Array K)) (hw : ∀ r ∈ rows, r.size = c.width)
    (hl : rows.length ≤ UInt64.size := by
      simp only [List.length_map, List.length_cons, List.length_nil, List.length_ofFn]; decide)
    (hf : c.FixedRowsMatch rows := by exact trivial) :
    Air.Flat.Table K :=
  tableOf c rows hw hl hf

def xorT : Air.Flat.Table K := mkT xorComponent ([xorRow].map rawRow) (rawRows_size [xorRow])
/-- The `MUL_NATIVE` table, its row's read count of `x` `rA`. -/
def mulT (rA : K) : Air.Flat.Table K :=
  mkT mulComponent ([mulRow rA].map rawRow) (rawRows_size [mulRow rA])
/-- The `SET_CONSTANT` table, its first row's read count `c`. -/
def setT (c : K) : Air.Flat.Table K :=
  mkT setComponent ([setRow0 c, setRow1].map rawRow) (rawRows_size [setRow0 c, setRow1])
def derefT : Air.Flat.Table K :=
  mkT derefComponent ([derefRow].map rawRow) (rawRows_size [derefRow])
def jumpT : Air.Flat.Table K :=
  mkT jumpComponent ([jumpRow3, jumpRow5, jumpRow7, jumpRow16].map jumpRaw)
    (jumpRaw_size [jumpRow3, jumpRow5, jumpRow7, jumpRow16])
def blakeT : Air.Flat.Table K :=
  mkT blake2sComponent ((List.ofFn blakeRow).map rawRow) (rawRows_size (List.ofFn blakeRow))

/-- The memory block's rows agree with its fixed address column: row `i` at `g^i`. -/
theorem memRows_fixed (cnt : ℕ → K) :
    (memComponent minLogMem).FixedRowsMatch (List.ofFn (memRowArr cnt)) := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [List.length_ofFn]
    exact (UInt64.toNat_ofNat_of_lt' (by decide)).symm
  · have hi' : i < 2 ^ minLogMem := by rwa [List.length_ofFn] at hi
    refine (memMode_fixedAt_iff hi' (by decide) _).mpr ?_
    rw [List.getElem_ofFn]
    exact congrArg MemRow.idx (fromElements_rawRow (⟨gpow i, cnt i, #v[(fillImage ⟨i, hi'⟩).limb 0,
      (fillImage ⟨i, hi'⟩).limb 1, (fillImage ⟨i, hi'⟩).limb 2]⟩ : MemRow K))

/-- The memory block, with finalize counts `cnt`. -/
def memT (cnt : ℕ → K) : Air.Flat.Table K :=
  mkT (memComponent minLogMem) (List.ofFn (memRowArr cnt)) (by
    intro r hr
    rw [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    exact Vector.size_toArray _) (by rw [List.length_ofFn]; decide) (memRows_fixed cnt)

/-- The bytecode block's rows: the program's (Layer 7's `bytecodeRowOf`). -/
def bcRows : List (Array K) :=
  List.ofFn fun i ↦ rawRow (bytecodeRowOf fillProg i (bcCntFin i))

/-- They agree with the block's fixed columns: row `i` at `g^i`, holding the program's entry. -/
theorem bcRows_fixed : (bytecodeComponent fillProg).FixedRowsMatch bcRows := by
  unfold bcRows
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [List.length_ofFn]
    exact (UInt64.toNat_ofNat_of_lt' (by decide)).symm
  · have hi' : i < 2 ^ fillProg.logSize := by rwa [List.length_ofFn] at hi
    rw [List.getElem_ofFn]
    show (bytecodeMode fillProg).FixedAt (UInt64.ofNat i) (fromElements (Air.Flat.rowPrefix
      (size BytecodeRow) (rawRow (bytecodeRowOf fillProg ⟨i, hi'⟩ (bcCntFin ⟨i, hi'⟩)))))
    rw [fromElements_rawRow, bytecodeMode_fixedAt_iff fillProg hi']
    exact ⟨rfl, cons_append_ops _⟩

/-- The bytecode block. -/
def bcT : Air.Flat.Table K :=
  mkT (bytecodeComponent fillProg) bcRows (by
      intro r hr
      rw [bcRows, List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact rawRow_size _) (by rw [bcRows, List.length_ofFn]; decide) bcRows_fixed

/-- A witness at the minimum memory size with the fixture's input and the tables `ts`, eight
tables of the ensemble's components in order; its prover data is derived from `ts`. -/
def mkW (ts : List (Air.Flat.Table K))
    (hc : ts.map (·.component) = (leanIsaEnsemble fillProg minLogMem).tables := by rfl) :
    EnsembleWitness (leanIsaEnsemble fillProg minLogMem) :=
  witnessOfTables fillProg minLogMem (PublicIO.ofInput mulInput) ts hc

/-- The witness, with the first `SET_CONSTANT` row's read count `c`, the product row's read
count of `x` `rA`, and the memory block's finalize counts `cnt`; the honest one is
`fillW 1 g memCnt`. -/
def fillW (c rA : K) (cnt : ℕ → K) : EnsembleWitness (leanIsaEnsemble fillProg minLogMem) :=
  mkW [xorT, mulT rA, setT c, derefT, jumpT, blakeT, memT cnt, bcT]

/-! ## The tables of the witness, read back -/

/-- Their rows. By `dsimp`, never by `rfl`: a definitional comparison of a stuck projection
against a `List.ofFn` unrolls the `2^16` rows (finding E8). -/
theorem blakeT_table : blakeT.table = (List.ofFn blakeRow).map rawRow := by
  dsimp only [blakeT, mkT, tableOf]
theorem memT_table (cnt : ℕ → K) : (memT cnt).table = List.ofFn (memRowArr cnt) := by
  dsimp only [memT, mkT, tableOf]
theorem bcT_table : bcT.table = bcRows := by
  dsimp only [bcT, mkT, tableOf]

/-- The three blocks the statement names, read off the witness. -/
theorem tableAt_five (c rA : K) (cnt : ℕ → K) :
    (tableAt (fillW c rA cnt) 5).table = blakeT.table := by
  simp only [tableAt, fillW, mkW, witnessOfTables, Air.Flat.withDerivedData, List.getElem_map,
    List.getElem_attach]
  rfl
theorem tableAt_six (c rA : K) (cnt : ℕ → K) :
    (tableAt (fillW c rA cnt) 6).table = (memT cnt).table := by
  simp only [tableAt, fillW, mkW, witnessOfTables, Air.Flat.withDerivedData, List.getElem_map,
    List.getElem_attach]
  rfl
theorem tableAt_seven (c rA : K) (cnt : ℕ → K) :
    (tableAt (fillW c rA cnt) 7).table = bcT.table := by
  simp only [tableAt, fillW, mkW, witnessOfTables, Air.Flat.withDerivedData, List.getElem_map,
    List.getElem_attach]
  rfl

/-- The witness's data is derived from its tables. -/
theorem fillW_data (c rA : K) (cnt : ℕ → K) : (fillW c rA cnt).data =
    Air.Flat.deriveProverData [xorT, mulT rA, setT c, derefT, jumpT, blakeT, memT cnt, bcT] :=
  witnessOfTables_data (hc := rfl)

/-- A table of a built witness has the component and rows of one of the tables it was built
from. -/
theorem mem_mkW {ts : List (Air.Flat.Table K)} {hc} {t : Air.Flat.Table K}
    (ht : t ∈ (mkW ts hc).tables) : ∃ t₀ ∈ ts, t.component = t₀.component ∧ t.table = t₀.table := by
  have h : (t.component, t.table) ∈ ts.map fun t ↦ (t.component, t.table) :=
    witnessOfTables_map ▸ List.mem_map_of_mem ht
  obtain ⟨t₀, h₀, he⟩ := List.mem_map.mp h
  exact ⟨t₀, h₀, (Prod.mk.inj he).1.symm, (Prod.mk.inj he).2.symm⟩

/-! ## The image the data names -/

/-- Row `k` of the data's `"mem"` table, through `getElem?`: the block's row `k`, derived. A
`getElem` with a bound on the `2^16`-row table makes both the elaborator and the kernel unroll
it (finding E8). -/
theorem fill_memRows_get? (c rA : K) (cnt : ℕ → K) (k : ℕ) (hk : k < 2 ^ minLogMem) :
    (memRows (fillW c rA cnt).data)[k]? = some #v[(fillImage ⟨k, hk⟩).limb 0,
      (fillImage ⟨k, hk⟩).limb 1, (fillImage ⟨k, hk⟩).limb 2] := by
  have hmem : memT cnt ∈ [xorT, mulT rA, setT c, derefT, jumpT, blakeT, memT cnt, bcT] := by
    simp only [List.mem_cons, true_or, or_true]
  rw [memRows, ProverData.getRows, fillW_data,
    show memDataName = (memT cnt).component.circuit.name from rfl,
    Air.Flat.deriveProverData_eq_of_mem _ (names_nodup rfl) hmem, Air.Flat.Table.rowPrefixes,
    memT_table, Array.getElem?_map, Array.getElem?_map, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_ofFn, dite_eq_left hk, Option.map_some, Option.map_some]
  exact congrArg (fun r : MemRow K ↦ some r.m) (fromElements_rawRow _)

/-- The image's log-size is the minimum. -/
theorem fill_logSize (c rA : K) (cnt : ℕ → K) : (imageOf (fillW c rA cnt).data).1 = minLogMem :=
  imageOf_data_fst (by decide)

theorem fill_pow_eq (c rA : K) (cnt : ℕ → K) :
    2 ^ (imageOf (fillW c rA cnt).data).1 = 2 ^ minLogMem := by rw [fill_logSize]

theorem fill_image_apply' (c rA : K) (cnt : ℕ → K) (k : ℕ)
    (hk : k < 2 ^ (imageOf (fillW c rA cnt).data).1) :
    (imageOf (fillW c rA cnt).data).2 ⟨k, hk⟩ =
      fillImage ⟨k, by rw [← fill_pow_eq c rA cnt]; exact hk⟩ := by
  conv_rhs => rw [← ofLimbs_limb (fillImage ⟨k, _⟩)]
  exact imageOf_apply ⟨k, hk⟩ (v := #v[(fillImage ⟨k, _⟩).limb 0, (fillImage ⟨k, _⟩).limb 1,
    (fillImage ⟨k, _⟩).limb 2]) (fill_memRows_get? c rA cnt k _)

/-- The image the data names, as one equality of dependent pairs: what every conjunct over
`imageOf w.data` is rewritten with, so that nothing compares the data's log-size against
`minLogMem` definitionally (finding E8). -/
theorem fill_imageOf (c rA : K) (cnt : ℕ → K) :
    imageOf (fillW c rA cnt).data = ⟨minLogMem, fillImage⟩ := by
  have hκ : (imageOf (fillW c rA cnt).data).1 = minLogMem := fill_logSize c rA cnt
  have hpow : 2 ^ (imageOf (fillW c rA cnt).data).1 = 2 ^ minLogMem := fill_pow_eq c rA cnt
  have hf : ∀ i, (imageOf (fillW c rA cnt).data).2 i = fillImage (Fin.cast hpow i) :=
    fun i ↦ fill_image_apply' c rA cnt i i.isLt
  revert hκ hpow hf
  generalize imageOf (fillW c rA cnt).data = s
  obtain ⟨κ, img⟩ := s
  intro hκ hpow hf
  dsimp only at hκ hpow hf
  subst hκ
  exact congrArg _ (funext fun i ↦ (hf i).trans (congrArg fillImage (Fin.ext rfl)))
/-! ## The run (Layer 3) -/

/-- The instruction at `g^i`. -/
theorem fetch_at (i : ℕ) (ins : Instr) (hi : i < 2 ^ fillProg.logSize := by decide)
    (hd : fillProg.code ⟨i, hi⟩ = ins := by rfl) : fillProg.fetch (gpow i) = some ins := by
  rw [show gpow i = gpow ((⟨i, hi⟩ : Fin (2 ^ fillProg.logSize)) : ℕ) from rfl,
    Program.fetch_gpow, hd]

/-- The instruction at the counter `1 = g^0`. -/
theorem fetch_one : fillProg.fetch 1 = some (.setConstant (gpow 2) mulX) := by
  simpa using fetch_at 0 (.setConstant (gpow 2) mulX)

/-- The word at `g^k`. -/
theorem read_at (k : ℕ) (v : E) (hk : k < 2 ^ minLogMem := by decide)
    (hv : fillImage ⟨k, hk⟩ = v := by rfl) : fillImage.read (gpow k) = some v := by
  rw [show gpow k = gpow ((⟨k, hk⟩ : Fin (2 ^ minLogMem)) : ℕ) from rfl,
    MemImage.read_gpow (by decide), hv]

theorem fill_step0 : step fillProg fillImage ⟨1, 1⟩ = some ⟨gpow 1, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) fetch_one]
  show execute fillImage ⟨1, 1⟩ (.setConstant (gpow 2) mulX) = _
  simp only [execute, executeWith, one_mul, read_at 2 mulX]
  decide +kernel

theorem fill_step1 : step fillProg fillImage ⟨gpow 1, 1⟩ = some ⟨gpow 2, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 1, 1⟩) (fetch_at 1 (.setConstant (gpow 3) mulY))]
  show execute fillImage ⟨gpow 1, 1⟩ (.setConstant (gpow 3) mulY) = _
  simp only [execute, executeWith, one_mul, read_at 3 mulY]
  decide +kernel

theorem fill_step2 : step fillProg fillImage ⟨gpow 2, 1⟩ = some ⟨gpow 3, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 2, 1⟩) (fetch_at 2 (.mulNative (gpow 2) (gpow 3) (gpow 4)))]
  show execute fillImage ⟨gpow 2, 1⟩ (.mulNative (gpow 2) (gpow 3) (gpow 4)) = _
  simp only [execute, executeWith, one_mul, read_at 2 mulX, read_at 3 mulY, read_at 4 mulXY]
  decide +kernel

theorem fill_step3 : step fillProg fillImage ⟨gpow 3, 1⟩ = some ⟨gpow 31, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 3, 1⟩) (fetch_at 3 (.jump (gpow 26) (gpow 27) (gpow 28)))]
  show execute fillImage ⟨gpow 3, 1⟩ (.jump (gpow 26) (gpow 27) (gpow 28)) = _
  simp only [execute, executeWith, one_mul, read_at 26 (cellK 1), read_at 27 (cellK (gpow 31)),
    read_at 28 (cellK 1)]
  decide +kernel

theorem fill_run1 : run fillProg fillImage 1 ⟨1, 1⟩ = some ⟨gpow 1, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, fill_step0, Option.bind_eq_bind,
    Option.bind_some, run_zero]

theorem fill_run2 : run fillProg fillImage 2 ⟨1, 1⟩ = some ⟨gpow 2, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, fill_step0, fill_step1,
    Option.bind_eq_bind, Option.bind_some, run_zero]

theorem fill_run3 : run fillProg fillImage 3 ⟨1, 1⟩ = some ⟨gpow 3, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, fill_step0, fill_step1, fill_step2,
    Option.bind_eq_bind, Option.bind_some, run_zero]

theorem fill_run4 : run fillProg fillImage 4 ⟨1, 1⟩ = some ⟨gpow 31, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, fill_step0, fill_step1, fill_step2,
    fill_step3, Option.bind_eq_bind, Option.bind_some, run_zero]

/-- The run: four steps from `(1, 1)` to the final registers `(g^31, 1)`. -/
theorem fill_run : run fillProg fillImage 4 Regs.initial = some (Regs.final fillProg) :=
  fill_run4

/-- The public words are in place. -/
theorem fill_boundary : HasPublicBoundary mulInput fillTrace :=
  ⟨le_rfl, by decide, read_at 0 (cellK 1), read_at 1 (cellK (K.ofBits 2))⟩

/-- The extended program is a valid execution of the executor's on the same input. -/
example : ValidExecution fillProg mulInput fillTrace := ⟨fill_boundary, fill_run⟩

/-- Its register sequence. -/
theorem fill_regs :
    fillTrace.regs = [⟨1, 1⟩, ⟨gpow 1, 1⟩, ⟨gpow 2, 1⟩, ⟨gpow 3, 1⟩, ⟨gpow 31, 1⟩] := by
  show (List.range 5).filterMap (fun n ↦ run fillProg fillImage n ⟨1, 1⟩) = _
  simp only [List.range_succ, List.range_zero, List.nil_append, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil, run_zero, fill_run1, fill_run2, fill_run3, fill_run4,
    List.singleton_append]
  rfl


/-! ## Proof helpers: the interactions the kernel evaluates -/

/-- A table's interactions over the data `D`, through its row circuit (`table_interactions_eq`):
the form the kernel evaluates. -/
def intsOver (D : ProverData K) (t : Air.Flat.Table K) : List (Interaction K) :=
  t.table.flatMap fun row ↦
    t.component.rowOperations.interactions.map (·.eval (Environment.fromArray row D))

theorem mkW_data (ts : List (Air.Flat.Table K)) (hc) :
    (mkW ts hc).data = Air.Flat.deriveProverData ts :=
  witnessOfTables_data

/-- A built witness's interactions: the verifier's, then each table's over the derived data. -/
theorem mkW_interactions (ts : List (Air.Flat.Table K)) (hc) :
    (mkW ts hc).interactions =
      (leanIsaEnsemble fillProg minLogMem).verifierOperations.interactionValues
          (.fromInput (PublicIO.ofInput mulInput) (mkW ts hc).data) ++
        ts.flatMap (intsOver (mkW ts hc).data) := by
  rw [EnsembleWitness.interactions]
  congr 1
  show (List.map _ ts.attach).flatMap _ = _
  rw [List.flatMap_map, List.flatMap_subtype (g := intsOver _) (fun t _ ↦ ?_),
    List.unattach_attach]
  rw [table_interactions_eq, mkW_data]
  rfl

/-- A table's interactions over `D` have its rows' count times its row circuit's. -/
theorem intsOver_length (D : ProverData K) (t : Air.Flat.Table K) :
    (intsOver D t).length = t.table.length * t.component.rowOperations.interactions.length := by
  rw [intsOver, List.length_flatMap]
  simp only [List.length_map, List.map_const', List.sum_replicate, smul_eq_mul]

theorem activeMessages_append (l l' : List (Interaction K)) (d : BusDir) :
    activeMessages (l ++ l') d = activeMessages l d ++ activeMessages l' d := by
  simp only [activeMessages, List.filter_append, List.map_append]

theorem activeMessages_flatMap {α : Type} (l : List α) (f : α → List (Interaction K))
    (d : BusDir) : activeMessages (l.flatMap f) d = l.flatMap fun x ↦ activeMessages (f x) d := by
  simp only [activeMessages, List.filter_flatMap, List.map_flatMap]

theorem one_ne_zero_K : (1 : K) ≠ 0 := by decide +kernel

/-- On interactions of multiplicity `1`, the active messages in a direction are the messages of
the interactions in it. The kernel evaluates this form: Clean's `activeMessages` decides `mult ≠
0` by the field's generic equality, which it does not reduce. -/
theorem activeMessages_of_mults {l : List (Interaction K)} (h : ∀ i ∈ l, i.mult = 1)
    (d : BusDir) : activeMessages l d = (l.filter (·.direction = d)).map (·.msg) := by
  unfold activeMessages
  congr 1
  refine List.filter_congr fun i hi ↦ ?_
  rw [decide_eq_decide]
  exact ⟨And.left, fun h' ↦ ⟨h', by rw [h i hi]; exact one_ne_zero_K⟩⟩

/-- The messages of a witness whose interactions all have multiplicity `1`, in the form the
kernel evaluates. -/
theorem messagesOn_of_mults {w : EnsembleWitness (leanIsaEnsemble fillProg minLogMem)}
    (hm : ∀ i ∈ w.interactions, i.mult = 1) (c : RawChannel K) (d : BusDir) :
    messagesOn w c d =
      ((w.interactions.filter (·.channel.name = c.name)).filter (·.direction = d)).map (·.msg) :=
  activeMessages_of_mults (fun i hi ↦ hm i (List.mem_of_mem_filter hi)) d

/-- A table whose row circuit interacts on no channel named `c` sends nothing on `c`. -/
theorem intsOver_filter_nil (D : ProverData K) (t : Air.Flat.Table K) (c : RawChannel K)
    (h : ∀ i ∈ t.component.rowOperations.interactions, i.channel.name ≠ c.name) :
    (intsOver D t).filter (·.channel.name = c.name) = [] := by
  rw [List.filter_eq_nil_iff]
  intro i hi
  rw [intsOver, List.mem_flatMap] at hi
  obtain ⟨r, -, hi⟩ := hi
  rw [List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact fun h' ↦ h j hj (of_decide_eq_true h')

/-- The memory block sends nothing on another channel. -/
theorem memT_filter (cnt : ℕ → K) (c : RawChannel K) (hc : c.name ≠ MemChannel.name)
    (D : ProverData K) : (intsOver D (memT cnt)).filter (·.channel.name = c.name) = [] :=
  intsOver_filter_nil D _ c (by
    rw [show (memT cnt).component = memComponent minLogMem from rfl, memComponent_rowOps]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl) <;> exact fun h ↦ hc (h.symm.trans rfl))

/-- The bytecode block sends nothing on another channel. -/
theorem bcT_filter (c : RawChannel K) (hc : c.name ≠ BytecodeChannel.name) (D : ProverData K) :
    (intsOver D bcT).filter (·.channel.name = c.name) = [] :=
  intsOver_filter_nil D _ c (by
    rw [show bcT.component = bytecodeComponent fillProg from rfl, bytecodeComponent_rowOps]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl) <;> exact fun h ↦ hc (h.symm.trans rfl))

/-- Every interaction of the memory block has multiplicity `1`. -/
theorem memT_mults (cnt : ℕ → K) (D : ProverData K) : ∀ i ∈ intsOver D (memT cnt), i.mult = 1 := by
  intro i hi
  rw [intsOver, List.mem_flatMap] at hi
  obtain ⟨r, -, hi⟩ := hi
  rw [show (memT cnt).component = memComponent minLogMem from rfl, memComponent_rowOps,
    List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> rfl

/-- The cells the run and the fill blocks touch are the first `touched`; the `untouched` rest
of the `2^16` are seeded and finalized with count `1` and cancel. -/
abbrev touched : ℕ := 29
abbrev untouched : ℕ := 65507
theorem touched_add_untouched : touched + untouched = 2 ^ minLogMem := by decide

/-- The seed message of cell `i`: `(g^i, 1, mem[i])`. -/
def seedMsg (i : Fin (2 ^ minLogMem)) : Array K :=
  #[gpow i, 1, (fillImage i).limb 0, (fillImage i).limb 1, (fillImage i).limb 2]

/-- The finalize message of cell `i`: `(g^i, cnt i, mem[i])`. -/
def finMsg (cnt : ℕ → K) (i : Fin (2 ^ minLogMem)) : Array K :=
  #[gpow i, cnt i, (fillImage i).limb 0, (fillImage i).limb 1, (fillImage i).limb 2]

/-- The memory block's row interactions have multiplicity `1`. -/
theorem memRow_mults (D : ProverData K) (a : Array K) :
    ∀ i ∈ (memComponent minLogMem).rowOperations.interactions.map
      (·.eval (Environment.fromArray a D)), i.mult = 1 := by
  rw [memComponent_rowOps]
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  rintro i (rfl | rfl) <;> rfl

/-- A row of the memory block pushes its seed message … -/
theorem memRow_push (D : ProverData K) (a : Array K) :
    activeMessages (((memComponent minLogMem).rowOperations.interactions.map
      (·.eval (Environment.fromArray a D))).filter
        (·.channel.name = MemChannel.toRaw.name)) .push =
      [#[a[0]?.getD 0, 1, a[2]?.getD 0, a[3]?.getD 0, a[4]?.getD 0]] := by
  -- The filters decide the names and directions by evaluation; the message is the row's
  -- variables evaluated (`Vector.map` is defined by well-founded recursion, so it is rewritten,
  -- not unfolded).
  rw [activeMessages_of_mults fun i hi ↦ memRow_mults D a i (List.mem_of_mem_filter hi),
    memComponent_rowOps, List.map_cons, List.map_cons, List.map_nil,
    List.filter_cons_of_pos (by rfl), List.filter_cons_of_pos (by rfl),
    List.filter_cons_of_pos (by rfl), List.filter_nil,
    List.filter_cons_of_neg ?hn, List.filter_nil, List.map_cons, List.map_nil]
  case hn => exact fun h ↦ nomatch of_decide_eq_true h
  show [((toElements (⟨var ⟨0⟩, 1, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ : MemMsg (Expression K))).map
    (Expression.eval (Environment.fromArray a D))).toArray] = _
  rw [show toElements (⟨var ⟨0⟩, 1, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ : MemMsg (Expression K)) =
    #v[var ⟨0⟩, 1, var ⟨2⟩, var ⟨3⟩, var ⟨4⟩] from by with_unfolding_all rfl]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.toArray_mk]
  rfl

/-- … and pulls its finalize message. -/
theorem memRow_pull (D : ProverData K) (a : Array K) :
    activeMessages (((memComponent minLogMem).rowOperations.interactions.map
      (·.eval (Environment.fromArray a D))).filter
        (·.channel.name = MemChannel.toRaw.name)) .pull =
      [#[a[0]?.getD 0, a[1]?.getD 0, a[2]?.getD 0, a[3]?.getD 0, a[4]?.getD 0]] := by
  rw [activeMessages_of_mults fun i hi ↦ memRow_mults D a i (List.mem_of_mem_filter hi),
    memComponent_rowOps, List.map_cons, List.map_cons, List.map_nil,
    List.filter_cons_of_pos (by rfl), List.filter_cons_of_neg ?hn,
    List.filter_cons_of_pos (by rfl), List.filter_nil, List.filter_cons_of_pos (by rfl),
    List.filter_nil, List.map_cons, List.map_nil]
  case hn => exact fun h ↦ nomatch of_decide_eq_true h
  show [((toElements (⟨var ⟨0⟩, var ⟨1⟩, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ :
    MemMsg (Expression K))).map (Expression.eval (Environment.fromArray a D))).toArray] = _
  rw [show toElements (⟨var ⟨0⟩, var ⟨1⟩, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ :
    MemMsg (Expression K)) = #v[var ⟨0⟩, var ⟨1⟩, var ⟨2⟩, var ⟨3⟩, var ⟨4⟩] from by
      with_unfolding_all rfl]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.toArray_mk]
  rfl

/-- The memory block's pushes are the seeds of every cell, in order. -/
theorem memT_pushes (cnt : ℕ → K) (D : ProverData K) :
    activeMessages ((intsOver D (memT cnt)).filter (·.channel.name = MemChannel.toRaw.name)) .push =
      List.ofFn seedMsg := by
  rw [intsOver, List.filter_flatMap, activeMessages_flatMap,
    show (memT cnt).component = memComponent minLogMem from rfl, memT_table]
  simp only [memRow_push, ← List.map_eq_flatMap, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [memRowArr_eq]
  rfl

/-- The memory block's pulls are the finalizes of every cell, in order. -/
theorem memT_pulls (cnt : ℕ → K) (D : ProverData K) :
    activeMessages ((intsOver D (memT cnt)).filter (·.channel.name = MemChannel.toRaw.name)) .pull =
      List.ofFn (finMsg cnt) := by
  rw [intsOver, List.filter_flatMap, activeMessages_flatMap,
    show (memT cnt).component = memComponent minLogMem from rfl, memT_table]
  simp only [memRow_pull, ← List.map_eq_flatMap, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [memRowArr_eq]
  rfl

/-- The seeds, split at the touched cells. -/
theorem seeds_split : List.ofFn seedMsg =
    (List.ofFn fun i : Fin touched ↦ seedMsg (Fin.castAdd untouched i)) ++
      List.ofFn fun j : Fin untouched ↦ seedMsg (Fin.natAdd touched j) := by
  rw [show List.ofFn seedMsg = List.ofFn fun i : Fin (touched + untouched) ↦ seedMsg i from rfl,
    List.ofFn_add]
  rfl

/-- The finalizes, split the same way: past the touched cells, with counts `1`, they are the
seeds. -/
theorem fins_split (cnt : ℕ → K) (h : ∀ i, touched ≤ i → cnt i = 1) :
    List.ofFn (finMsg cnt) =
      (List.ofFn fun i : Fin touched ↦ finMsg cnt (Fin.castAdd untouched i)) ++
        List.ofFn fun j : Fin untouched ↦ seedMsg (Fin.natAdd touched j) := by
  rw [show List.ofFn (finMsg cnt) = List.ofFn fun i : Fin (touched + untouched) ↦ finMsg cnt i
    from rfl, List.ofFn_add]
  refine congrArg₂ _ rfl (congrArg _ (funext fun j ↦ ?_))
  show #[gpow (touched + j), cnt (touched + j), (fillImage (Fin.natAdd touched j)).limb 0,
    (fillImage (Fin.natAdd touched j)).limb 1, (fillImage (Fin.natAdd touched j)).limb 2] = _
  rw [h _ (Nat.le_add_right touched j)]
  rfl

/-! ## Proof helpers: balance -/

/-- The witness's interactions: the verifier's, then the eight tables' over its data. -/
theorem fillW_interactions (c rA : K) (cnt : ℕ → K) :
    (fillW c rA cnt).interactions =
      (leanIsaEnsemble fillProg minLogMem).verifierOperations.interactionValues
          (.fromInput (PublicIO.ofInput mulInput) (fillW c rA cnt).data) ++
        [xorT, mulT rA, setT c, derefT, jumpT, blakeT, memT cnt, bcT].flatMap
          (intsOver (fillW c rA cnt).data) :=
  mkW_interactions _ _

/-- Fewer interactions than `2^64`, for every count. -/
theorem fill_length (c rA : K) (cnt : ℕ → K) :
    (fillW c rA cnt).interactions.length < FiniteField.size K := by
  rw [fillW_interactions]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    intsOver_length, Operations.interactionValues, List.length_map,
    show (mulT rA).table.length = 1 from rfl, show (setT c).table.length = 2 from rfl,
    show (mulT rA).component = mulComponent from rfl,
    show (setT c).component = setComponent from rfl,
    show (memT cnt).component = memComponent minLogMem from rfl, memT_table, List.length_ofFn]
  decide +kernel

/-- The multiset check on each channel, from its permutation, the multiplicities and the
length. -/
theorem balanced_of {w : EnsembleWitness (leanIsaEnsemble fillProg minLogMem)}
    (hm : ∀ i ∈ w.interactions, i.mult = 1) (hl : w.interactions.length < FiniteField.size K)
    (hs : (messagesOn w StateChannel.toRaw .push).Perm (messagesOn w StateChannel.toRaw .pull))
    (hmem : (messagesOn w MemChannel.toRaw .push).Perm (messagesOn w MemChannel.toRaw .pull))
    (hb : (messagesOn w BytecodeChannel.toRaw .push).Perm
      (messagesOn w BytecodeChannel.toRaw .pull)) : w.Balanced .multiset := by
  intro c hc
  rw [EnsembleWitness.interactionsWith_eq_filter_name hc]
  refine ⟨lt_of_le_of_lt (List.length_filter_le _ _) hl,
    fun i hi ↦ Or.inr (hm i (List.mem_of_mem_filter hi)), ?_⟩
  have hp : (messagesOn w c .push).Perm (messagesOn w c .pull) := by
    simp only [leanIsaEnsemble, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hs
    · exact hmem
    · exact hb
  unfold messagesOn at hp
  convert hp using 3

/-- Balance read back on one channel. -/
theorem perm_of_balanced {w : EnsembleWitness (leanIsaEnsemble fillProg minLogMem)}
    (h : w.Balanced .multiset) {c : RawChannel K}
    (hc : c ∈ (leanIsaEnsemble fillProg minLogMem).channels) :
    (messagesOn w c .push).Perm (messagesOn w c .pull) := by
  have hb := (h c hc).2.2
  rw [EnsembleWitness.interactionsWith_eq_filter_name hc] at hb
  unfold messagesOn
  convert hb using 3

/-- The memory messages of the verifier and the six opcode tables. -/
def memSmall (c rA : K) (cnt : ℕ → K) : List (Interaction K) :=
  ((leanIsaEnsemble fillProg minLogMem).verifierOperations.interactionValues
      (.fromInput (PublicIO.ofInput mulInput) (fillW c rA cnt).data) ++
    [xorT, mulT rA, setT c, derefT, jumpT, blakeT].flatMap (intsOver (fillW c rA cnt).data)).filter
      (·.channel.name = MemChannel.toRaw.name)

/-- The memory channel, reduced to the touched cells: with the block's seeds and finalizes split
at cell `touched` and the untouched suffix cancelled, balance is a permutation the kernel
decides. -/
theorem mem_perm_iff (c rA : K) (cnt : ℕ → K) (h : ∀ i, touched ≤ i → cnt i = 1) :
    (messagesOn (fillW c rA cnt) MemChannel.toRaw .push).Perm
        (messagesOn (fillW c rA cnt) MemChannel.toRaw .pull) ↔
      (activeMessages (memSmall c rA cnt) .push ++
        List.ofFn fun i : Fin touched ↦ seedMsg (Fin.castAdd untouched i)).Perm
      (activeMessages (memSmall c rA cnt) .pull ++
        List.ofFn fun i : Fin touched ↦ finMsg cnt (Fin.castAdd untouched i)) := by
  unfold messagesOn
  rw [fillW_interactions,
    show [xorT, mulT rA, setT c, derefT, jumpT, blakeT, memT cnt, bcT].flatMap
        (intsOver (fillW c rA cnt).data) =
      [xorT, mulT rA, setT c, derefT, jumpT, blakeT].flatMap (intsOver (fillW c rA cnt).data) ++
        (intsOver (fillW c rA cnt).data (memT cnt) ++ intsOver (fillW c rA cnt).data bcT) by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc],
    ← List.append_assoc, ← List.append_assoc, List.filter_append, List.filter_append,
    bcT_filter MemChannel.toRaw (by decide), List.append_nil, activeMessages_append,
    activeMessages_append, memT_pushes, memT_pulls, seeds_split, fins_split cnt h,
    ← List.append_assoc, ← List.append_assoc]
  exact List.perm_append_right_iff _

/-! ## Proof helpers: constraints -/

/-- An expression reads the row only, not the data. -/
theorem eval_fromArray (row : Array K) (D D' : ProverData K) (e : Expression K) :
    Expression.eval (Environment.fromArray row D) e =
      Expression.eval (Environment.fromArray row D') e := by
  induction e with
  | var _ => rfl
  | const _ => rfl
  | add _ _ hx hy => simp only [Expression.eval, hx, hy]
  | mul _ _ hx hy => simp only [Expression.eval, hx, hy]

/-- The `JUMP` table's two residuals hold on its four rows, with the witnesses `w = b = 1`, over
any data. -/
theorem jumpT_constraints (D : ProverData K) :
    ∀ row ∈ jumpT.table,
      jumpComponent.operations.ConstraintsHold (Environment.fromArray row D) := by
  intro r hr
  simp only [jumpT, mkT, tableOf, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
  · rw [Component.constraintsHold_iff]
    simp only [circuit_norm, jumpComponent, jumpTable, instructionStep, memRead, bytecodeRead,
      -BitVec.reduceNeg]
    rintro e (rfl | rfl) <;> rw [eval_fromArray _ D fun _ _ ↦ #[]] <;> decide +kernel

/-- A table of a built witness: its rows' constraints are those of the table it was built from,
over the witness's data. -/
theorem mkW_constraints {ts : List (Air.Flat.Table K)} {hc}
    (h : ∀ t ∈ ts, ∀ row ∈ t.table,
      t.component.operations.ConstraintsHold (Environment.fromArray row (mkW ts hc).data)) :
    (mkW ts hc).Constraints := by
  intro t ht row hrow
  have hd : t.data = (mkW ts hc).data := (mkW ts hc).same_data t ht
  obtain ⟨t₀, h₀, hcomp, hr⟩ := mem_mkW ht
  rw [Air.Flat.Table.environment, hd, hcomp]
  exact h t₀ h₀ row (hr ▸ hrow)

/-! ## The witness satisfies the statement -/

/-- Every component's constraints hold, for every count: the counts are never constrained,
only balanced (§6.2), so the rejections below fail on their conjunct alone. -/
theorem fill_constraints (c rA : K) (cnt : ℕ → K) : (fillW c rA cnt).Constraints := by
  refine mkW_constraints fun t ht ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ ↦ xor_constraints _
  · exact fun _ _ ↦ mul_constraints _
  · exact fun _ _ ↦ set_constraints _
  · exact fun _ _ ↦ deref_constraints _
  · exact jumpT_constraints _
  · exact fun _ _ ↦ blake2s_constraints _
  · exact fun _ _ ↦ mem_constraints _ _
  · exact fun _ _ ↦ bytecode_constraints _ _

/-- Every interaction has multiplicity `1`. -/
theorem fill_mults : ∀ i ∈ (fillW 1 g memCnt).interactions, i.mult = 1 := by
  rw [fillW_interactions]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall_mem_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, memT_mults _ _, ?_⟩ <;> decide +kernel

/-- The state channel balances: the run's four steps against the boundary, and the three closed
walks of the fill blocks. -/
theorem fill_state_perm : (messagesOn (fillW 1 g memCnt) StateChannel.toRaw .push).Perm
    (messagesOn (fillW 1 g memCnt) StateChannel.toRaw .pull) := by
  rw [messagesOn_of_mults fill_mults, messagesOn_of_mults fill_mults, fillW_interactions]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append,
    memT_filter memCnt StateChannel.toRaw (by decide), bcT_filter StateChannel.toRaw (by decide)]
  decide +kernel

/-- The bytecode channel balances: every executed slot read once, the seeds and finalizes of all
thirty-two. -/
theorem fill_bytecode_perm : (messagesOn (fillW 1 g memCnt) BytecodeChannel.toRaw .push).Perm
    (messagesOn (fillW 1 g memCnt) BytecodeChannel.toRaw .pull) := by
  rw [messagesOn_of_mults fill_mults, messagesOn_of_mults fill_mults, fillW_interactions]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append,
    memT_filter memCnt BytecodeChannel.toRaw (by decide)]
  decide +kernel

/-- The memory channel balances. -/
theorem fill_mem_perm : (messagesOn (fillW 1 g memCnt) MemChannel.toRaw .push).Perm
    (messagesOn (fillW 1 g memCnt) MemChannel.toRaw .pull) := by
  rw [mem_perm_iff 1 g memCnt fun _ ↦ memCnt_of_ge,
    activeMessages_of_mults (l := memSmall 1 g memCnt) (by decide +kernel),
    activeMessages_of_mults (l := memSmall 1 g memCnt) (by decide +kernel)]
  decide +kernel

/-- The three channels balance as multisets. -/
theorem fill_balanced : (fillW 1 g memCnt).Balanced .multiset :=
  balanced_of fill_mults (fill_length 1 g memCnt) fill_state_perm fill_mem_perm fill_bytecode_perm

/-- Every read count is nonzero. -/
theorem fill_countsNonzero : CountsNonzero (fillW 1 g memCnt) := by
  unfold CountsNonzero
  simp only [table_interactions_eq]
  decide +kernel

/-- The caps: `κ = 16`, heights `1, 1, 2, 1, 4, 8, 2^16, 2^5`, eight `BLAKE2S` rows; for
every count. -/
theorem fill_caps (c rA : K) (cnt : ℕ → K) : Caps (fillW c rA cnt) where
  minLogMem_le := le_rfl
  le_maxLogMem := by decide
  heights := by
    intro t ht
    obtain ⟨t₀, h₀, -, hr⟩ := mem_mkW ht
    rw [hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h₀
    rcases h₀ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨3, by decide, by rw [blakeT_table, List.length_map, List.length_ofFn]; rfl⟩
    · exact ⟨minLogMem, by decide, by rw [memT_table, List.length_ofFn]⟩
    · exact ⟨5, by decide, by rw [bcT_table, bcRows, List.length_ofFn]; rfl⟩
  blake2s_height := by
    rw [blake2sRows, tableAt_five, blakeT_table, List.length_map, List.length_ofFn]
    decide

/-- The executor's nine cells compress, as the row carries them (Layer 6's `blake2s_relation`
on the same cells): one kernel compression. -/
theorem blake_cells_compress :
    CompressCells ![E.ofCell (cell rustM0), E.ofCell (cell rustM1), E.ofCell (cell rustM2),
      E.ofCell (cell rustM3)] (E.ofCell (cell rustCv0)) (E.ofCell (cell rustCv1))
      (E.ofCell (cell rustOut0)) (E.ofCell (cell rustOut1)) (E.ofCell (cell rustMd)) := by
  decide +kernel

/-- Every `BLAKE2S` row of the fixture satisfies the relation: the eight rows share the cells
and differ in their read counts. -/
theorem blakeRow_relation (j : Fin 8) : Blake2sRelation (blakeRow j) := blake_cells_compress

/-- The `BLAKE2S` table is valid, for every count. -/
theorem fill_blake2sValid (c rA : K) (cnt : ℕ → K) : Blake2sRowsValid (fillW c rA cnt) := by
  intro r hr
  rw [blake2sRows, tableAt_five, blakeT_table, List.mem_map] at hr
  obtain ⟨rj, hrj, rfl⟩ := hr
  rw [List.mem_ofFn] at hrj
  obtain ⟨j, rfl⟩ := hrj
  rw [rawRow, blake2sRowAt_toElements]
  exact blakeRow_relation j

/-- The two public words sit at `g^0` and `g^1` of the image the data names. -/
theorem fill_word0 (c rA : K) (cnt : ℕ → K) :
    (imageOf (fillW c rA cnt).data).2.read (gpow 0) = some mulInput.word0 := by
  rw [fill_imageOf]
  exact read_at 0 mulInput.word0

theorem fill_word1 (c rA : K) (cnt : ℕ → K) :
    (imageOf (fillW c rA cnt).data).2.read (gpow 1) = some mulInput.word1 := by
  rw [fill_imageOf]
  exact read_at 1 mulInput.word1

/-- The honest witness satisfies the constraint statement. -/
theorem fill_satisfiedBy : SatisfiedBy fillProg mulInput (fillW 1 g memCnt) where
  public_input_eq := rfl
  constraints := fill_constraints 1 g memCnt
  balanced := fill_balanced
  counts_nonzero := fill_countsNonzero
  caps := fill_caps 1 g memCnt
  blake2s_valid := fill_blake2sValid 1 g memCnt
  word0_eq := fill_word0 1 g memCnt
  word1_eq := fill_word1 1 g memCnt

/-! ## The witness represents the trace -/

/-- Each of the run's four steps is one row's state pull and push. -/
theorem fill_regs_embed :
    ∀ k (hk : k + 1 < fillTrace.regs.length),
      RowSteps (fillW 1 g memCnt) fillTrace.regs[k] fillTrace.regs[k + 1] := by
  intro k hk
  have hk' : k < 4 := by rw [fill_regs] at hk; exact Nat.lt_of_succ_lt_succ hk
  simp only [fill_regs]
  interval_cases k
  · show RowSteps (fillW 1 g memCnt) ⟨1, 1⟩ ⟨gpow 1, 1⟩
    exact ⟨tableAt (fillW 1 g memCnt) 2, List.getElem_mem _, rawRow (setRow0 1), List.mem_cons_self,
      by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel,
      by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel⟩
  · show RowSteps (fillW 1 g memCnt) ⟨gpow 1, 1⟩ ⟨gpow 2, 1⟩
    exact ⟨tableAt (fillW 1 g memCnt) 2, List.getElem_mem _, rawRow setRow1,
      List.mem_cons_of_mem _ List.mem_cons_self,
      by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel,
      by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel⟩
  · show RowSteps (fillW 1 g memCnt) ⟨gpow 2, 1⟩ ⟨gpow 3, 1⟩
    exact ⟨tableAt (fillW 1 g memCnt) 1, List.getElem_mem _, rawRow (mulRow g), List.mem_cons_self,
      by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel,
      by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel⟩
  · show RowSteps (fillW 1 g memCnt) ⟨gpow 3, 1⟩ ⟨gpow 31, 1⟩
    exact ⟨tableAt (fillW 1 g memCnt) 4, List.getElem_mem _, jumpRaw jumpRow3, List.mem_cons_self,
      by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel,
      by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel⟩

/-- The honest witness represents the trace. -/
theorem fill_represents : AssignmentRepresents (fillW 1 g memCnt) fillTrace where
  κ_eq := fill_logSize 1 g memCnt
  image_eq := fun i _ ↦ fill_image_apply' 1 g memCnt i _
  regs_embed := fill_regs_embed

/-- The completeness instance of T1 for this program: the trace is a valid execution, the
witness satisfies the statement and represents the trace. -/
theorem fill_t1_instance : ValidExecution fillProg mulInput fillTrace ∧
    SatisfiedBy fillProg mulInput (fillW 1 g memCnt) ∧
      AssignmentRepresents (fillW 1 g memCnt) fillTrace :=
  ⟨⟨fill_boundary, fill_run⟩, fill_satisfiedBy, fill_represents⟩

/-- The image the witness names is the trace's, as one equality. -/
example : imageOf (fillW 1 g memCnt).data = ⟨minLogMem, fillImage⟩ :=
  assignmentRepresents_image fill_represents

/-! ## Rejections -/

/-- The memory channel is in the ensemble. -/
theorem mem_channel_mem : MemChannel.toRaw ∈ (leanIsaEnsemble fillProg minLogMem).channels :=
  List.mem_cons_of_mem _ List.mem_cons_self

/-- A wrong finalize count: cell `4` is read once, its finalize count `1` instead of `g`. -/
def wrongCnt (i : ℕ) : K := if i = 4 then 1 else memCnt i

theorem wrongCnt_of_ge {i : ℕ} (h : 29 ≤ i) : wrongCnt i = 1 := by
  unfold wrongCnt
  rw [ite_eq_right (by omega), memCnt_of_ge h]

/-- Nothing checks the finalize counts (§6.2): the block accepts the row, and the bus does not
balance. -/
example : ¬ (fillW 1 g wrongCnt).Balanced .multiset := fun h ↦ by
  have hp := perm_of_balanced h mem_channel_mem
  rw [mem_perm_iff 1 g wrongCnt fun _ ↦ wrongCnt_of_ge,
    activeMessages_of_mults (l := memSmall 1 g wrongCnt) (by decide +kernel),
    activeMessages_of_mults (l := memSmall 1 g wrongCnt) (by decide +kernel)] at hp
  revert hp
  decide +kernel

/-- The finalize counts of a read count `0` at cell `2`: the first `SET_CONSTANT` row's read
pulls and pushes `(g^2, 0, x)`, the product row's read is then the first, and the cell is
finalized at `g`. -/
def zeroCnt (i : ℕ) : K := if i = 2 then g else memCnt i

theorem zeroCnt_of_ge {i : ℕ} (h : 29 ≤ i) : zeroCnt i = 1 := by
  unfold zeroCnt
  rw [ite_eq_right (by omega), memCnt_of_ge h]

theorem zero_mults : ∀ i ∈ (fillW 0 1 zeroCnt).interactions, i.mult = 1 := by
  rw [fillW_interactions]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall_mem_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, memT_mults _ _, ?_⟩ <;> decide +kernel

theorem zero_state_perm : (messagesOn (fillW 0 1 zeroCnt) StateChannel.toRaw .push).Perm
    (messagesOn (fillW 0 1 zeroCnt) StateChannel.toRaw .pull) := by
  rw [messagesOn_of_mults zero_mults, messagesOn_of_mults zero_mults, fillW_interactions]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append,
    memT_filter zeroCnt StateChannel.toRaw (by decide), bcT_filter StateChannel.toRaw (by decide)]
  decide +kernel

theorem zero_bytecode_perm : (messagesOn (fillW 0 1 zeroCnt) BytecodeChannel.toRaw .push).Perm
    (messagesOn (fillW 0 1 zeroCnt) BytecodeChannel.toRaw .pull) := by
  rw [messagesOn_of_mults zero_mults, messagesOn_of_mults zero_mults, fillW_interactions]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append,
    memT_filter zeroCnt BytecodeChannel.toRaw (by decide)]
  decide +kernel

/-- The zero-count witness balances the memory channel: a pull and a push of one tuple cancel,
which is what the count product exists to reject (§6.2 "The count product", Theorem 6.4). -/
theorem zero_mem_perm : (messagesOn (fillW 0 1 zeroCnt) MemChannel.toRaw .push).Perm
    (messagesOn (fillW 0 1 zeroCnt) MemChannel.toRaw .pull) := by
  rw [mem_perm_iff 0 1 zeroCnt fun _ ↦ zeroCnt_of_ge,
    activeMessages_of_mults (l := memSmall 0 1 zeroCnt) (by decide +kernel),
    activeMessages_of_mults (l := memSmall 0 1 zeroCnt) (by decide +kernel)]
  decide +kernel

/-- The count product is load-bearing: the zero-count witness satisfies every other conjunct
of `SatisfiedBy` and fails `CountsNonzero` (§6.2 "The count product"). -/
theorem zero_count_witness :
    (fillW 0 1 zeroCnt).publicInput = PublicIO.ofInput mulInput ∧
    (fillW 0 1 zeroCnt).Constraints ∧ (fillW 0 1 zeroCnt).Balanced .multiset ∧
    Caps (fillW 0 1 zeroCnt) ∧ Blake2sRowsValid (fillW 0 1 zeroCnt) ∧
    (imageOf (fillW 0 1 zeroCnt).data).2.read (gpow 0) = some mulInput.word0 ∧
    (imageOf (fillW 0 1 zeroCnt).data).2.read (gpow 1) = some mulInput.word1 ∧
    ¬ CountsNonzero (fillW 0 1 zeroCnt) :=
  ⟨rfl, fill_constraints 0 1 zeroCnt,
    balanced_of zero_mults (fill_length 0 1 zeroCnt) zero_state_perm zero_mem_perm
      zero_bytecode_perm,
    fill_caps 0 1 zeroCnt, fill_blake2sValid 0 1 zeroCnt, fill_word0 0 1 zeroCnt,
    fill_word1 0 1 zeroCnt, by
      unfold CountsNonzero
      simp only [table_interactions_eq]
      decide +kernel⟩

/-- A wrong digest: the executor's row with the low bit of `out1` flipped. -/
def wrongOut1 : E := E.ofLimbs (K.ofBits 0xf1b0679a15df60ba) (K.ofBits 0x0228c8d4ed9b3a24) 0
def blakeRow' : Blake2sRow K := { blakeRow 0 with out1 := cell wrongOut1 }

theorem blakeRow'_no_relation : ¬ Blake2sRelation blakeRow' := by
  show ¬ CompressCells _ _ _ _ _ _
  decide +kernel

def blakeT' : Air.Flat.Table K :=
  mkT blake2sComponent ([blakeRow'].map rawRow) (rawRows_size [blakeRow'])

/-- The witness with the wrong digest in its `BLAKE2S` table (one row; the caps are not the
point). -/
def digestW : EnsembleWitness (leanIsaEnsemble fillProg minLogMem) :=
  mkW [xorT, mulT g, setT 1, derefT, jumpT, blakeT', memT memCnt, bcT]

/-- The compression is checked (§8.5): the wrong digest fails `Blake2sRowsValid`. It fails no
constraint: the table has none (`blake2s_constraints`). -/
example : ¬ Blake2sRowsValid digestW := fun h ↦
  blakeRow'_no_relation (by
    have hrel := h (rawRow blakeRow') (by
      show rawRow blakeRow' ∈ (tableAt digestW 5).table
      exact List.mem_cons_self)
    rwa [rawRow, blake2sRowAt_toElements] at hrel)

/-- The memory block with its index column shifted by one row. -/
def memRowArrShift (i : Fin (2 ^ minLogMem)) : Array K :=
  (toElements (⟨gpow (i + 1), memCnt i,
    #v[(fillImage i).limb 0, (fillImage i).limb 1, (fillImage i).limb 2]⟩ : MemRow K)).toArray

/-- The index column is fixed (§6.5): the shifted rows disagree with the memory block's fixed
address column at row `0`, so no table of the block has them … -/
example : ¬ (memComponent minLogMem).FixedRowsMatch (List.ofFn memRowArrShift) := fun h ↦ by
  obtain ⟨-, h⟩ := h
  have h0 := h 0 (by rw [List.length_ofFn]; decide)
  rw [List.getElem_ofFn] at h0
  have h0' := (memMode_fixedAt_iff (κ := minLogMem) (i := 0) (by decide) (by decide) _).mp h0
  revert h0'
  show (fromElements (Air.Flat.rowPrefix (size MemRow) (rawRow (⟨gpow (0 + 1), memCnt 0,
    #v[(fillImage ⟨0, by decide⟩).limb 0, (fillImage ⟨0, by decide⟩).limb 1,
      (fillImage ⟨0, by decide⟩).limb 2]⟩ : MemRow K))) : MemRow K).idx = gpow 0 → False
  rw [fromElements_rawRow]
  decide +kernel

/-- … and no witness has them as its memory block. -/
example (w : EnsembleWitness (leanIsaEnsemble fillProg minLogMem)) :
    memBlockRows w ≠ List.ofFn memRowArrShift := fun h ↦ by
  have h0 := ((memBlock_rows w (by decide)).2 0 (by rw [h, List.length_ofFn]; decide)).1
  simp only [h, List.getElem_ofFn, memRowArrShift, memRowAt_toElements] at h0
  revert h0
  decide +kernel

/-- The public words are checked (§8.2): `input₀ = 3` in place of `1` fails `word0_eq`. -/
example : ¬ SatisfiedBy fillProg ⟨![K.ofBits 3, 0, K.ofBits 2, 0]⟩ (fillW 1 g memCnt) := fun h ↦ by
  have h0 := h.word0_eq
  rw [fill_word0] at h0
  have h1 := congrArg (fun o : Option E ↦ (o.getD 0).limb 0) h0
  revert h1
  decide +kernel

/-- A three-row `SET_CONSTANT` table, not a power of two. -/
def setT3 : Air.Flat.Table K :=
  mkT setComponent ([setRow0 1, setRow1, setRow1].map rawRow)
    (rawRows_size [setRow0 1, setRow1, setRow1])

def heightW : EnsembleWitness (leanIsaEnsemble fillProg minLogMem) :=
  mkW [xorT, mulT g, setT3, derefT, jumpT, blakeT, memT memCnt, bcT]

theorem three_ne_two_pow (τ : ℕ) : (3 : ℕ) ≠ 2 ^ τ := by
  intro h
  rcases τ with _ | _ | τ
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rw [Nat.pow_succ, Nat.pow_succ] at h
    have := Nat.one_le_two_pow (n := τ)
    omega

/-- The heights are checked (`read_public`, `:114-117`, `:161`): a height that is not a power
of two fails `Caps`. -/
example : ¬ Caps heightW := fun h ↦ by
  obtain ⟨τ, -, hτ⟩ := h.heights (tableAt heightW 2) (List.getElem_mem _)
  rw [show (tableAt heightW 2).table.length = 3 from rfl] at hτ
  exact three_ne_two_pow τ hτ

/-- Four `BLAKE2S` rows, below the floor `2^3`. -/
def blakeT4 : Air.Flat.Table K :=
  mkT blake2sComponent ((List.ofFn fun j : Fin 4 ↦ blakeRow (j.castAdd 4)).map rawRow)
    (rawRows_size (List.ofFn fun j : Fin 4 ↦ blakeRow (j.castAdd 4)))

def floorW : EnsembleWitness (leanIsaEnsemble fillProg minLogMem) :=
  mkW [xorT, mulT g, setT 1, derefT, jumpT, blakeT4, memT memCnt, bcT]

/-- The `BLAKE2S` floor is checked (`:166`): four rows fail `Caps`. -/
example : ¬ Caps floorW := fun h ↦ by
  have h8 := h.blake2s_height
  rw [blake2sRows, show (tableAt floorW 5).table.length = 4 from rfl] at h8
  exact absurd h8 (by decide)

end LeanerVMTests.Arithmetization.Statement
