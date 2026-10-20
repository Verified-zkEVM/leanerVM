/-
  LeanerVM.Arithmetization.Padding.FillBlocks

  The fill blocks the compiler emits past `main`'s halt, and the program-shape condition that
  they are present.
-/

module

public import LeanerVM.Semantics.Lemmas

/-!
# Fill blocks

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`. Category B, transcribed from
`crates/lean_compiler/src/lower.rs:435-506` (`lower_filler_blocks`) and
`crates/leanvm_core/src/cpu/filler.rs:36-87` (the sizes and the frame offsets), which are identical
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

**What is defined.** The blocks themselves (`fillDummy`, `fillClose`, `IsFillBlock`,
`HasFillBlocks`) are defined in `LeanerVM.Spec.Isa`, since completeness assumes them. Here:
`WellFormedBytecode`, the roadmap's pair of program-shape conditions, the sentinel slot is not a
`JUMP` (Layer 3's `SentinelSafe`, not restated) and the fill blocks are present; both T1 theorems
take it, and a further condition the Clean proofs need is one more field here, never a new
hypothesis on a theorem.

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

end
end LeanerVM.Semantics
