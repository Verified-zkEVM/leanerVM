import LeanerVM.Semantics.FillCycle
import LeanerVMTests.Semantics.FillSteps

/-!
# Layer 10 tests: the fill-block lemma

The ladder program over the executor's image, padded with the fill frames. Every one of the
forty-eight cycles closes: any number of traversals return to the cycle's start state, whatever the
table and the size (the `JUMP` table's own blocks included). Two rejections: without its closing
jump a block does not return, and the same closing slot run in another cycle's frame goes where
that frame says, not to its own block.
-/

namespace LeanerVMTests.Semantics.FillCycle

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Execution LeanerVMTests.Semantics.FillBlocks
open LeanerVMTests.Semantics.FillSteps

/-- The table of a table's index is the table. -/
theorem tableOf_tableIdx (t : Opcode) : tableOf (tableIdx t) = t := by
  cases t <;> rfl

/-- Every block of the ladder is a block at the starting slot the plan uses. -/
theorem ladder_isFillBlock (t : Opcode) {k : ℕ} (hk : k < 8) :
    IsFillBlock ladderProg t (sizeAt k) (pcsLadder t (sizeAt k)) := by
  have h := ladder_block t (tableIdx t) (tableIdx_lt t) (tableOf_tableIdx t)
  interval_cases k
  · exact h 128 0 (by norm_num) (by decide) (by decide)
  · exact h 64 129 (by norm_num) (by decide) (by decide)
  · exact h 32 194 (by norm_num) (by decide) (by decide)
  · exact h 16 227 (by norm_num) (by decide) (by decide)
  · exact h 8 244 (by norm_num) (by decide) (by decide)
  · exact h 4 253 (by norm_num) (by decide) (by decide)
  · exact h 2 258 (by norm_num) (by decide) (by decide)
  · exact h 1 261 (by norm_num) (by decide) (by decide)

/-! ## Every cycle closes -/

/-- Any number of traversals of any block return to the start. -/
theorem ladder_cycle_closed (t : Opcode) {k : ℕ} (hk : k < 8) (n : ℕ) :
    run ladderProg (padImage mulImage pcsLadder) (n * (sizeAt k + 1))
        (cycleStart minLogMem pcsLadder t k) = some (cycleStart minLogMem pcsLadder t k) :=
  fill_cycle_run (by decide) (by decide) mulImage pcsLadder t hk (ladder_isFillBlock t hk) n

/-- The largest `XOR` block, three traversals: `387` steps. -/
example : run ladderProg (padImage mulImage pcsLadder) (3 * 129)
    (cycleStart minLogMem pcsLadder .xor 0) = some (cycleStart minLogMem pcsLadder .xor 0) :=
  ladder_cycle_closed .xor (by norm_num) 3

/-- The `JUMP` table's own size-one block: the dummy jump falls through and the closing jump
returns, two rows a traversal. -/
example : run ladderProg (padImage mulImage pcsLadder) (5 * 2)
    (cycleStart minLogMem pcsLadder .jump 7) = some (cycleStart minLogMem pcsLadder .jump 7) :=
  ladder_cycle_closed .jump (by norm_num) 5

/-- The `BLAKE2S` size-eight block, a traversal: nine steps. -/
example : run ladderProg (padImage mulImage pcsLadder) 9
    (cycleStart minLogMem pcsLadder .blake2s 4) = some (cycleStart minLogMem pcsLadder .blake2s 4) :=
  ladder_cycle_closed .blake2s (by norm_num) 1

/-! ## A block is a cycle only with its jump -/

/-- After the dummies and before the closing jump the state is the closing slot, not the start. -/
theorem ladder_dummies_do_not_close (t : Opcode) {k : ℕ} (hk : k < 8) (hs : 0 < sizeAt k) :
    run ladderProg (padImage mulImage pcsLadder) (sizeAt k)
        (cycleStart minLogMem pcsLadder t k) ≠ some (cycleStart minLogMem pcsLadder t k) := by
  have hb := ladder_isFillBlock t hk
  rw [fill_dummies_run (by decide) (by decide) mulImage pcsLadder t hk hb (sizeAt k) le_rfl]
  intro h
  have hpc := congrArg Regs.pc (Option.some.inj h)
  have hc : (2 : ℕ) ^ 64 - 1 = 18446744073709551615 := by norm_num
  have hbelow : pcsLadder t (sizeAt k) + sizeAt k + 1 < 2 ^ 11 := hb.below
  have h1 : pcsLadder t (sizeAt k) + sizeAt k ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio, hc]; omega
  have h2 : pcsLadder t (sizeAt k) ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio, hc]; omega
  have := gpow_injOn h1 h2 hpc
  omega

/-! ## The destination is read from the frame -/

/-- The closing slot of the size-one `XOR` block goes to the cycle of the frame it runs in: in the
`XOR` frame to the `XOR` block, in the `MUL_NATIVE` frame to the `MUL_NATIVE` block. The two starts
differ, so a jump is not tied to its own block but to its frame. -/
theorem close_goes_where_the_frame_says :
    ∃ pc : K, ladderProg.fetch pc = some fillClose ∧
      step ladderProg (padImage mulImage pcsLadder)
        ⟨pc, gpow (frameBase minLogMem (8 * tableIdx .xor + 7))⟩ =
          some (cycleStart minLogMem pcsLadder .xor 7) ∧
      step ladderProg (padImage mulImage pcsLadder)
        ⟨pc, gpow (frameBase minLogMem (8 * tableIdx .mulNative + 7))⟩ =
          some (cycleStart minLogMem pcsLadder .mulNative 7) ∧
      cycleStart minLogMem pcsLadder .xor 7 ≠ cycleStart minLogMem pcsLadder .mulNative 7 := by
  obtain ⟨pc, hf⟩ : ∃ pc : K, ladderProg.fetch pc = some fillClose :=
    ⟨_, (ladder_isFillBlock .xor (k := 7) (by norm_num)).close⟩
  refine ⟨pc, hf, fill_close_step (by decide) (by decide) mulImage pcsLadder .xor (by norm_num) hf,
    fill_close_step (by decide) (by decide) mulImage pcsLadder .mulNative (by norm_num) hf, ?_⟩
  intro h
  have hfp := congrArg Regs.fp h
  have hc : (2 : ℕ) ^ 64 - 1 = 18446744073709551615 := by norm_num
  have h1 : frameBase minLogMem (8 * tableIdx .xor + 7) ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio, hc]; decide
  have h2 : frameBase minLogMem (8 * tableIdx .mulNative + 7) ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio, hc]; decide
  have := gpow_injOn h1 h2 hfp
  revert this
  decide

end LeanerVMTests.Semantics.FillCycle
