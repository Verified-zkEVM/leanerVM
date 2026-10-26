import LeanerVM.Semantics.FillRows
import LeanerVMTests.Semantics.FillCycle

/-!
# Layer 10 tests: the rows of a fill

The ladder program over the executor's image, padded with the fill frames. The skeletons of any
fill, whatever the traversal counts, are valid fillers in the repository's own sense. Two
rejections: the dummies of a block without its closing jump are not valid fillers (the multiset of
starts is not the multiset of successors), and a skeleton at the sentinel is not.
-/

namespace LeanerVMTests.Semantics.FillRows

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Execution LeanerVMTests.Semantics.FillBlocks
open LeanerVMTests.Semantics.FillSteps LeanerVMTests.Semantics.FillCycle

/-! ## Every fill is valid -/

/-- The ladder program has a block of every size at the slots the tests use. -/
theorem ladder_hasStarts : ∀ t, ∀ k < 8,
    IsFillBlock ladderProg t (sizeAt k) (pcsLadder t (sizeAt k)) :=
  fun t _ hk ↦ ladder_isFillBlock t hk

/-- The skeletons of any fill of the ladder program are valid fillers over its padded image. -/
theorem ladder_fill_valid (count : Opcode → ℕ → ℕ) :
    SkelsValid ladderProg (padImage mulImage pcsLadder) (padSkels minLogMem pcsLadder count) :=
  padSkels_valid (by decide) (by decide) mulImage pcsLadder ladder_hasStarts count

/-- A fill that traverses every block three times. -/
example : SkelsValid ladderProg (padImage mulImage pcsLadder)
    (padSkels minLogMem pcsLadder fun _ _ ↦ 3) :=
  ladder_fill_valid _

/-- A single traversal of the largest `XOR` block. -/
example : SkelsValid ladderProg (padImage mulImage pcsLadder)
    (cycleSkels minLogMem pcsLadder .xor 0) :=
  cycleSkels_valid (by decide) (by decide) mulImage pcsLadder .xor (by norm_num)
    (ladder_isFillBlock .xor (by norm_num))

/-- Well formed bytecode has the starting slots: the ladder's. -/
example : ∃ pcs : Opcode → ℕ → ℕ, ∀ t, ∀ k < 8,
    IsFillBlock ladderProg t (sizeAt k) (pcs t (sizeAt k)) :=
  ladder_hasFillBlocks.exists_starts

/-! ## A block is a filler only with its jump -/

/-- The dummies of a traversal, without its closing jump. -/
def dummiesOnly (t : Opcode) (k : ℕ) : List Skel :=
  (List.range (sizeAt k)).map fun i ↦
    ⟨gpow (pcsLadder t (sizeAt k) + i), gpow (frameBase minLogMem (8 * tableIdx t + k)),
      fillDummy t⟩

/-- The dummies of a block without its closing jump are not valid fillers: the first state is
nobody's successor, so the multiset of starts is not the multiset of successors. -/
theorem dummiesOnly_invalid (t : Opcode) {k : ℕ} (hk : k < 8) (hs : 0 < sizeAt k) :
    ¬ SkelsValid ladderProg (padImage mulImage pcsLadder) (dummiesOnly t k) := by
  intro h
  have hb := ladder_isFillBlock t hk
  have hstarts : (dummiesOnly t k).map Skel.regs =
      (List.range (sizeAt k)).map (cycleState minLogMem pcsLadder t k) := by
    simp only [dummiesOnly, List.map_map]
    rfl
  have hmem : some (cycleState minLogMem pcsLadder t k 0) ∈
      ((dummiesOnly t k).map Skel.regs).map some := by
    rw [hstarts]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨0, List.mem_range.mpr hs, rfl⟩, rfl⟩
  have hmem' := h.2.mem_iff.mp hmem
  obtain ⟨r, hr, hre⟩ := List.mem_map.mp hmem'
  rw [hstarts] at hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  have hi' := List.mem_range.mp hi
  have hst := cycleSkels_step (by decide : 10 ≤ minLogMem) (by decide : minLogMem < 63) mulImage
    pcsLadder t hk hb hi'.le
  simp only [hi', ↓reduceIte] at hst
  rw [hst] at hre
  have hpc : gpow (pcsLadder t (sizeAt k) + (i + 1)) = gpow (pcsLadder t (sizeAt k) + 0) :=
    congrArg Regs.pc (Option.some.inj hre)
  have hbelow : pcsLadder t (sizeAt k) + sizeAt k + 1 < 2 ^ 11 := hb.below
  have hc : (2 : ℕ) ^ 64 - 1 = 18446744073709551615 := by norm_num
  have h1 : pcsLadder t (sizeAt k) + (i + 1) ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio, hc]; omega
  have h2 : pcsLadder t (sizeAt k) + 0 ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio, hc]; omega
  have := gpow_injOn h1 h2 hpc
  omega

/-! ## The sentinel is not a filler -/

/-- A skeleton at the sentinel is not a valid filler, whatever it fetches. -/
theorem sentinel_skel_invalid (prog : Program) {κ : ℕ} (image : MemImage κ) (fp : K)
    (ins : Instr) : ¬ SkelsValid prog image [⟨prog.finalPc, fp, ins⟩] := fun h ↦
  h.1 ⟨prog.finalPc, fp⟩ (by simp [Skel.regs]) rfl

end LeanerVMTests.Semantics.FillRows
