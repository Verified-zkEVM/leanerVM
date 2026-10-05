import LeanerVM.Semantics.PaddedTrace
import LeanerVMTests.Semantics.Execution

/-!
# Layer 10 tests: padded traces and what fits

The executor's `mul_192bit_word` (`tests/LeanerVMTests/Semantics/Execution.lean`) is a short valid
trace with room above its image, so it fits (`Trace.Fits.of_short`); a trace whose memory is at the
cap has no room whatever its run. A proper extension of the image is a padding, and one that
changes a word below `2^κ` is not. The program with a single slot has the empty execution, whose
rows per table are all zero: the final state is not a row.
-/

namespace LeanerVMTests.Semantics.PaddedTrace

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Execution

/-! ## What fits -/

/-- Three steps at the least memory log-size: the trace fits. -/
theorem mulTrace_fits : mulTrace.Fits :=
  Trace.Fits.of_short mul_run (by decide) (by decide)

/-- Fitting includes feasibility of the `JUMP` table. -/
example : JumpFeasible mulTrace.owed := mulTrace_fits.jump

/-- A trace whose memory is at the cap has no room for the fill frames, whatever its run. -/
theorem no_room_at_cap (t : Trace mulProg) (h : t.κ = maxLogMem) : ¬ t.Fits :=
  fun hf ↦ absurd (h ▸ hf.room) (lt_irrefl _)

/-! ## The empty execution -/

/-- A single slot: the sentinel is slot `0`, so the machine starts there and halts at once
(acceptance test 5). -/
def soloProg : Program := ⟨0, by decide, fun _ ↦ .setConstant (gpow 0) 0⟩

/-- The image of the single-slot program: zeros. -/
def soloImage : MemImage minLogMem := fun _ ↦ 0

/-- Its empty execution: no steps. -/
def soloTrace : Trace soloProg := ⟨minLogMem, soloImage, 0⟩

/-- The register sequence of the empty execution is its initial state alone. -/
theorem solo_regs : soloTrace.regs = [Regs.initial] := by
  show (List.range 1).filterMap (fun n ↦ run soloProg soloImage n Regs.initial) = _
  simp [run_zero]

/-- It has no rows: the sentinel state is not stepped from, though a `SET_CONSTANT` sits there.
Without `dropLast` the final state would count as a `SET_CONSTANT` row. -/
theorem solo_runRows (op : Opcode) : soloTrace.runRows op = 0 := by
  unfold Trace.runRows
  rw [solo_regs]
  simp

/-- With no rows, every table is empty and owes its fill: five closing jumps to the `JUMP` table
(one traversal each for `XOR`, `MUL_NATIVE`, `SET_CONSTANT`, `DEREF` and `BLAKE2S`). -/
example : soloTrace.owed = jumpOwed fun _ ↦ 0 := congrArg jumpOwed (funext solo_runRows)

#guard jumpOwed (fun _ ↦ 0) = 5

/-- The empty execution fits. -/
example : soloTrace.Fits := Trace.Fits.of_short (rf := Regs.initial) (run_zero _) (by decide)
  (by decide)

/-! ## Padding -/

/-- The executor's image extended by one doubling of zeros. -/
def mulPadded : Trace mulProg :=
  ⟨minLogMem + 1, fun i ↦ if h : (i : ℕ) < 2 ^ minLogMem then mulImage ⟨i, h⟩ else 0, 3⟩

/-- A proper extension is a padding. -/
theorem mulPadded_from : mulPadded.PaddedFrom mulTrace where
  steps_eq := rfl
  κ_le := Nat.le_succ _
  image_ext := fun i hi hi' ↦ by
    have hi2 : i < 2 ^ minLogMem := hi
    simp only [mulPadded, mulTrace, hi2, ↓reduceDIte]

/-- A trace is padded from itself. -/
example : mulTrace.PaddedFrom mulTrace := Trace.PaddedFrom.refl mulTrace

/-- An extension that changes a word the run reads is not a padding: cell `2` holds the first
operand, `mulX`. -/
def mulAltered : Trace mulProg :=
  ⟨minLogMem + 1, fun i ↦ if (i : ℕ) = 2 then 0 else
    if h : (i : ℕ) < 2 ^ minLogMem then mulImage ⟨i, h⟩ else 0, 3⟩

/-- The altered extension is not a padding of the executor's trace. -/
theorem mulAltered_not_from : ¬ mulAltered.PaddedFrom mulTrace := fun h ↦ by
  have := h.image_ext 2 (by decide) (by decide)
  simp only [mulAltered, mulTrace, mulImage] at this
  exact absurd this.symm (by decide +kernel)

/-- A trace with a smaller memory is not a padding. -/
example : ¬ (⟨minLogMem, mulImage, 3⟩ : Trace mulProg).PaddedFrom mulPadded := fun h ↦
  absurd h.κ_le (by decide)

/-- A different number of steps is not a padding: the run would be another run. -/
example : ¬ ({ mulPadded with steps := 4 } : Trace mulProg).PaddedFrom mulTrace := fun h ↦
  absurd h.steps_eq (by decide)

/-! ## The rows of a run -/

/-- The rows of the six tables add up to the steps: three steps, three rows. -/
example : (fillTables.map mulTrace.runRows).sum = mulTrace.steps := Trace.sum_runRows mul_run

/-- A short trace is far below the most steps a fitting trace can have. -/
example : mulTrace.steps ≤ 6 * 2 ^ maxLogRows :=
  mulTrace_fits.steps_le mul_run

end LeanerVMTests.Semantics.PaddedTrace
