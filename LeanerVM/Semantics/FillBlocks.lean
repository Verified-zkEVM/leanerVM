/-
  LeanerVM.Semantics.FillBlocks

  The fill blocks the compiler emits past `main`'s halt, and the program-shape condition that
  they are present.
-/

module

public import LeanerVM.Semantics.Execution

/-!
# Fill blocks

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category B, transcribed from
`crates/lean_compiler/src/lower.rs:462-533` (`lower_filler_blocks`) and
`crates/lean_vm/src/cpu/filler.rs:36-87` (the sizes and the frame offsets), which are identical
at leanVM `48a904208d682848dac0e18ef8b01ebfc40df9ad`. Artifact: a shape of the public program.
Direction: none, a definition. Contribution: the program-shape hypothesis of T1-C
(`WellFormedBytecode`, roadmap acceptance test 15).

**The ladder.** A table is proven over a power-of-two number of rows, so a run whose counts are
not powers of two makes up the difference by executing more instructions. The compiler appends,
for each of the six tables and each size in `fillSizes`, a *block*: `size` dummy instructions of
the table's opcode, then a `JUMP` back to the block's own first instruction. A block is a cycle
and no program code jumps into it; the interpreter enters it itself once the program has halted.
A traversal of the size-`s` block costs exactly `s + 1` rows: `s` of its table and one `JUMP`.
For the `JUMP` table the dummies are themselves `JUMP`s that fall through, so a traversal gives
that table `s + 1` rows, not `s`.

**The frame.** A block runs in a twelve-cell frame the interpreter carves out
(`cpu/filler.rs:73-87`): the closing jump reads its destination `g^{pc}` and its frame `g^{fp}`
from cells the interpreter writes (`DEST` and `NEXT_FP`), so they are cells of the image, not of
the program, and `HasFillBlocks` says nothing about them. Every dummy names one scratch cell as
each of its operands, which is why a block costs one cell whatever its size.

**What is defined.** `fillDummy t` is the dummy of table `t`, `fillClose` the closing jump,
`IsFillBlock prog t s p` says the block of size `s` for `t` starts at slot `p`, and
`HasFillBlocks prog` says every table has a block of every size. `WellFormedBytecode` is the
roadmap's pair of program-shape conditions, the sentinel slot is not a `JUMP`
(Layer 3's `SentinelSafe`, not restated) and the fill blocks are present; both T1 theorems take
it, and a further condition the Clean proofs need is one more field here, never a new hypothesis
on a theorem.

## Wrong readings excluded

* The closing jump is not the sentinel: `IsFillBlock.below` places the block, closing jump
  included, strictly below the last slot, since a row at the sentinel counter is the
  roadmap's acceptance test 20.
* Blocks are found by `Program.fetch`, the lookup `step` uses, so a block is present exactly
  when the machine would fetch its instructions; there is no second reading of the code.
* No disjointness of blocks is required: the fill blocks of one table may share slots (a size-`s`
  block can be the tail of a larger one), since every cycle has a frame of its own.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## The ladder -/

/-- The block sizes, largest first (`cpu/filler.rs:38`, `SIZES`): a fill of `f` rows takes `f / 128`
traversals of the largest block and then one per set bit of the remainder. -/
def fillSizes : List ℕ := [128, 64, 32, 16, 8, 4, 2, 1]

/-- The six tables in the order of their bus codes (Layer 2's `Opcode`, `tables.rs:95-100`). -/
def fillTables : List Opcode := [.xor, .mulNative, .setConstant, .deref, .jump, .blake2s]

/-! ## The frame

The cells of a fill block's twelve-cell frame, as exponents of `g` from the frame pointer
(`cpu/filler.rs:73-87`). -/

namespace FillFrame

/-- Where the closing jump goes: `g^{pc}` of the block's first instruction, a nonzero word. -/
abbrev dest : ℕ := 0

/-- The frame the closing jump goes to: this frame's own pointer. -/
abbrev nextFp : ℕ := 1

/-- The pointer a `DEREF` dummy follows: `g^0`, memory cell `0`. -/
abbrev ptr : ℕ := 2

/-- A cell nothing ever writes, so it reads as zero. -/
abbrev zero : ℕ := 3

/-- The scratch cell every dummy but `JUMP` names as each operand. -/
abbrev scratch : ℕ := 4

/-- The `BLAKE2S` dummy's output pair; the four message cells follow at `digest + 2 ..`. -/
abbrev digest : ℕ := 6

/-- The cells a block's frame occupies. -/
abbrev cells : ℕ := 12

end FillFrame

/-! ## The blocks -/

/-- The dummy instruction of a table (`lower.rs:482-519`): the cheapest instruction of that opcode
that can be executed any number of times in one frame. `XOR`, `MUL_NATIVE` and `SET_CONSTANT` name
the scratch cell as every operand, `DEREF` reads memory cell `0` through the frame's pointer,
`JUMP` reads a cell nothing writes (a zero condition falls through) and `BLAKE2S` compresses
cells nothing writes. -/
def fillDummy : Opcode → Instr
  | .xor => .xor (gpow FillFrame.scratch) (gpow FillFrame.scratch) (gpow FillFrame.scratch)
  | .mulNative =>
    .mulNative (gpow FillFrame.scratch) (gpow FillFrame.scratch) (gpow FillFrame.scratch)
  | .setConstant => .setConstant (gpow FillFrame.scratch) 0
  | .deref => .deref (gpow FillFrame.ptr) (gpow 0) (gpow FillFrame.scratch) .cell
  | .jump => .jump (gpow FillFrame.zero) (gpow FillFrame.zero) (gpow FillFrame.zero)
  | .blake2s =>
    .blake2s ![gpow (FillFrame.digest + 2), gpow (FillFrame.digest + 3),
      gpow (FillFrame.digest + 4), gpow (FillFrame.digest + 5)]
      (gpow FillFrame.scratch) (gpow FillFrame.digest) (gpow FillFrame.zero)

/-- The jump that closes a block (`lower.rs:525-529`): condition and destination are the cell
`DEST`, the new frame the cell `NEXT_FP`. -/
def fillClose : Instr :=
  .jump (gpow FillFrame.dest) (gpow FillFrame.dest) (gpow FillFrame.nextFp)

/-- A block of size `s` for table `t` starts at slot `p`: `s` dummies, then the closing jump, all
below the sentinel slot. -/
structure IsFillBlock (prog : Program) (t : Opcode) (s p : ℕ) : Prop where
  /-- The closing jump, the block's last slot, is below the sentinel slot `2^logSize - 1`. -/
  below : p + s + 1 < 2 ^ prog.logSize
  /-- Slots `p .. p + s - 1` fetch the table's dummy. -/
  dummies : ∀ i, i < s → prog.fetch (gpow (p + i)) = some (fillDummy t)
  /-- Slot `p + s` fetches the closing jump. -/
  close : prog.fetch (gpow (p + s)) = some fillClose

/-- The program has a block of every size for every table (`lower.rs:473-531`): the fill blocks
the prover pads the tables with. -/
def HasFillBlocks (prog : Program) : Prop :=
  ∀ t : Opcode, ∀ s ∈ fillSizes, ∃ p, IsFillBlock prog t s p

/-- The program-shape conditions the two T1 theorems need (roadmap Layer 10). A further condition
the Clean proofs require is one more field here, never a new hypothesis on a theorem. -/
structure WellFormedBytecode (prog : Program) : Prop where
  /-- The sentinel slot is not a `JUMP`: a row there pushes a counter outside the bytecode
  (acceptance test 20). Layer 3's `SentinelSafe`, not restated here. -/
  sentinelSafe : SentinelSafe prog
  /-- The fill blocks are present (acceptance test 15). -/
  hasFillBlocks : HasFillBlocks prog

/-! ## Load-bearing lemmas -/

/-- A dummy has the opcode of its table. -/
theorem fillDummy_opcode (t : Opcode) : (fillDummy t).opcode = t := by
  cases t <;> rfl

/-- The closing jump is a `JUMP`. -/
theorem fillClose_opcode : fillClose.opcode = .jump := rfl

/-- Every table has a block ladder. -/
theorem mem_fillTables (t : Opcode) : t ∈ fillTables := by
  cases t <;> simp [fillTables]

/-- The sizes of the ladder are positive. -/
theorem fillSizes_pos : ∀ s ∈ fillSizes, 0 < s := by
  simp [fillSizes]

end
end LeanerVM.Semantics
