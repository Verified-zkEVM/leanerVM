import LeanerVM.Semantics.FillBlocks

/-!
# Layer 10 tests: the fill block shape

The ladder is `crates/lean_compiler/src/lower.rs:462-533` and `crates/lean_vm/src/cpu/filler.rs`
at leanVM `a386121f`: each dummy is checked operand by operand against the compiler. Two
rejections: a program with no block has no `HasFillBlocks`, and a block whose closing jump is the
sentinel slot fails `IsFillBlock.below` alone (its dummies and its closing jump are fetched).
-/

namespace LeanerVMTests.Semantics.FillBlocks

open LeanerVM.Parameters LeanerVM.Semantics

/-! ## The ladder -/

example : fillSizes = [128, 64, 32, 16, 8, 4, 2, 1] := rfl

/-- A fill of `f` rows is delivered exactly by the ladder: the sizes add to `255`, one less than
the next power of two above the largest block. -/
example : fillSizes.sum = 255 := by decide

example : fillTables.length = 6 := rfl

example : fillTables.Nodup := by decide

example (t : Opcode) : t ∈ fillTables := mem_fillTables t

/-! ## The dummies, as the compiler emits them -/

example : fillDummy .xor = .xor (gpow 4) (gpow 4) (gpow 4) := rfl

example : fillDummy .mulNative = .mulNative (gpow 4) (gpow 4) (gpow 4) := rfl

example : fillDummy .setConstant = .setConstant (gpow 4) 0 := rfl

example : fillDummy .deref = .deref (gpow 2) (gpow 0) (gpow 4) .cell := rfl

example : fillDummy .jump = .jump (gpow 3) (gpow 3) (gpow 3) := rfl

example : fillDummy .blake2s =
    .blake2s ![gpow 8, gpow 9, gpow 10, gpow 11] (gpow 4) (gpow 6) (gpow 3) := rfl

example : fillClose = .jump (gpow 0) (gpow 0) (gpow 1) := rfl

example (t : Opcode) : (fillDummy t).opcode = t := fillDummy_opcode t

/-! ## A program with no block -/

/-- Two slots, every one a `SET_CONSTANT`. -/
def blankProg : Program := ⟨1, by decide, fun _ ↦ .setConstant (gpow 0) 0⟩

/-- No block is present: the first dummy of any block would have to be fetched. -/
theorem blank_has_no_blocks : ¬ HasFillBlocks blankProg := by
  intro h
  obtain ⟨p, hp⟩ := h .xor 128 (by simp [fillSizes])
  obtain ⟨i, -, hi⟩ := (blankProg.fetch_eq_some_iff).mp (hp.dummies 0 (by norm_num))
  exact absurd hi (by simp [blankProg, fillDummy])

/-! ## The block must lie below the sentinel -/

/-- A size-one `XOR` block in a two-slot program: the dummy at slot `0`, the closing jump at slot
`1`, which is the sentinel slot. -/
def tinyProg : Program := ⟨1, by decide, ![fillDummy .xor, fillClose]⟩

/-- The dummy is fetched. -/
theorem tiny_dummies : ∀ i, i < 1 → tinyProg.fetch (gpow (0 + i)) = some (fillDummy .xor) := by
  intro i hi
  obtain rfl : i = 0 := by omega
  exact tinyProg.fetch_gpow ⟨0, by decide⟩

/-- The closing jump is fetched. -/
theorem tiny_close : tinyProg.fetch (gpow (0 + 1)) = some fillClose := by
  simpa [tinyProg] using tinyProg.fetch_gpow ⟨1, by decide⟩

/-- Both fetch conditions hold, and the block is rejected on `below` alone: the closing jump
would sit in the sentinel slot, where a row is acceptance test 20. -/
theorem tiny_block_not_below : ¬ IsFillBlock tinyProg .xor 1 0 := fun h ↦ by
  have := h.below
  revert this
  decide

end LeanerVMTests.Semantics.FillBlocks
