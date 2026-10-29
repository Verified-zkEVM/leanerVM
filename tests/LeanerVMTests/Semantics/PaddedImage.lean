import LeanerVM.Semantics.PaddedImage
import LeanerVMTests.Semantics.PaddedRun

/-!
# Layer 10 tests: the padded image

The executor's `mul_192bit_word` padded with the fill frames. Its padded trace is a valid execution
with the same register sequence. The frame cells are read off the padded image at their addresses
and are what the interpreter writes (`cpu/filler.rs:73-87`, `execute.rs:389-391`): the destination
is `g^{pc}`, the frame is `g^{base}`, the pointer is `1`, the `DEREF` frame's scratch cell is the
word at memory cell `0` while every other frame's is zero, and the `BLAKE2S` frame holds the
compression of zero, which is not the pair of zero cells. The cells past the forty-eight frames are
zero.
-/

namespace LeanerVMTests.Semantics.PaddedImage

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Execution LeanerVMTests.Semantics.PaddedRun

/-- Any assignment of starting slots will do for the layout. -/
def pcsAny : Opcode → ℕ → ℕ := fun t s ↦ 7 * tableIdx t + s

/-! ## The padded trace -/

/-- The padded trace of the executor's run is a padding of it, with one more doubling of memory. -/
example : (padTrace mulTrace pcsAny).κ = minLogMem + 1 := rfl

/-- The padded trace is a padding of the executor's trace. -/
theorem mulPad_from : (padTrace mulTrace pcsAny).PaddedFrom mulTrace := padTrace_from mulTrace pcsAny

/-- It is a valid execution, and its register sequence is the executor's. -/
theorem mulPad_valid : ValidExecution mulProg mulInput (padTrace mulTrace pcsAny) :=
  mulPad_from.valid (by decide) mul_valid

/-- Padding leaves the register sequence of the executor's run unchanged. -/
theorem mulPad_regs : (padTrace mulTrace pcsAny).regs = mulTrace.regs :=
  mulPad_from.regs_eq (by decide) mul_valid

/-! ## The frame cells, read at their addresses -/

/-- The destination cell of the `XOR` frame of the largest block holds the block's first slot as a
power of `g`. -/
example : (padImage mulImage pcsAny).read
    (gpow (frameBase minLogMem (8 * tableIdx .xor + 0) + FillFrame.dest)) =
      some (ofK (gpow (pcsAny .xor 128))) := by
  rw [padImage_read_frame (by decide) (by decide) mulImage pcsAny .xor (by decide) (by decide)]
  simp [frameCell, sizeAt, fillSizes, FillFrame.dest]

/-- The frame cell of the next frame holds this frame's own pointer. -/
example : (padImage mulImage pcsAny).read
    (gpow (frameBase minLogMem (8 * tableIdx .jump + 3) + FillFrame.nextFp)) =
      some (ofK (gpow (frameBase minLogMem (8 * tableIdx .jump + 3)))) := by
  rw [padImage_read_frame (by decide) (by decide) mulImage pcsAny .jump (by decide) (by decide)]
  simp [frameCell, FillFrame.dest, FillFrame.nextFp]

/-- The `DEREF` frame's scratch cell is the word at memory cell `0`, the public input's first
word, and the `XOR` frame's is zero. -/
example (w0 : E) (pc base : ℕ) :
    frameCell w0 pc base .deref FillFrame.scratch = w0 ∧
      frameCell w0 pc base .xor FillFrame.scratch = 0 := by
  simp [frameCell, FillFrame.dest, FillFrame.nextFp, FillFrame.ptr, FillFrame.scratch]

/-- The pointer cell holds `1`, the address of memory cell `0`. -/
example (w0 : E) (pc base : ℕ) (t : Opcode) : frameCell w0 pc base t FillFrame.ptr = ofK 1 := by
  simp [frameCell, FillFrame.dest, FillFrame.nextFp, FillFrame.ptr]

/-- The `BLAKE2S` frame holds the digest of zero in its output pair; no other table's frame does. -/
example (w0 : E) (pc base : ℕ) :
    frameCell w0 pc base .blake2s FillFrame.digest = zeroDigest.1 ∧
      frameCell w0 pc base .blake2s (FillFrame.digest + 1) = zeroDigest.2 ∧
      frameCell w0 pc base .xor FillFrame.digest = 0 := by
  simp [frameCell, FillFrame.dest, FillFrame.nextFp, FillFrame.ptr, FillFrame.scratch,
    FillFrame.digest]

/-- The digest of zero is not the pair of zero cells, so a frame left all zero would not satisfy
`CompressCells`: the digest cells are what the frame must hold. -/
theorem zeroDigest_ne_zero : ¬ (zeroDigest.1 = 0 ∧ zeroDigest.2 = 0) := by
  rintro ⟨h1, h2⟩
  have h := zeroDigest_spec
  rw [h1, h2] at h
  revert h
  decide +kernel

/-- The cells past the forty-eight frames are zero. -/
example (w0 : E) (κ : ℕ) : padCell w0 pcsAny κ (12 * 48) = 0 := by
  simp [padCell]

/-- The frames fit above a memory of `2^10` cells and not above one of `2^9`: `576` cells need
`κ ≥ 10`, and the verifier's floor is above that. -/
example : frameBase 10 47 + 11 < 2 ^ (10 + 1) := by decide

example : ¬ (frameBase 9 47 + 11 < 2 ^ (9 + 1)) := by decide

/-- Frames are adjacent and none shares a cell: the second starts twelve cells after the first. -/
example (κ : ℕ) : frameBase κ 1 = frameBase κ 0 + 12 := frameBase_succ κ 0

end LeanerVMTests.Semantics.PaddedImage
