module

public import LeanVM.Cost.DecoderSize
public import LeanVM.Cost.Decoder.TopEq
public import LeanVM.Guest.DecoderProgram

/-!
# The guest decoder program and its specification

`decoderProgram`: the entry (`decoderEntryBody`, `Cost/DecoderProgram.lean`), then the compiled
top's bodies (`decTopC`, `Decoder/Top.lean`). On every valid execution `t` of the guest, its
output is the encoding of the deployed decoder's decoding `End.decode t.memory`: the entry runs
the top on the program, `κ` and the memory vector (`outputWithin_decoderEntry`), the top's spec
gives its value (`decTopC.costSpec`), which is `End.decode` (`decTop_eq`). Its size is within
`guestDecoderSizeBound` (`Cost/DecoderSize.lean`).

**Open**: its price within the budget (`guestDecoderBudget`, a placeholder of the statement):
`decoderProgram_spec` takes it as the hypothesis `hprice`, until the decoder's cost bounds are
proved.
-/

namespace LeanVM.Cost

open LeanVM.Parameters LeanVM.Semantics LeanVM.Cost.Decoder LeanVM.Node

public section

/-- **The guest decoder program**: the entry at `0`, then the compiled top's bodies. -/
@[expose] def decoderProgram : MachineProgram := decoderProgramOf decTopC.costIdx decTopC.costDeps

/-- The program holds the top's bodies. -/
theorem decoderProgram_includes : Includes decoderProgram decTopC.costDeps :=
  decoderProgramOf_includes decoderProgram_indices_increasing

/-- The program's function `0` is the entry. -/
theorem decoderProgram_entry : decoderProgram[0]? = some (decoderEntryBody decTopC.costIdx) :=
  decoderProgramOf_entry decoderProgram_indices_increasing

/-- **The program's size** is within `guestDecoderSizeBound`. -/
theorem decoderProgram_size_le : decoderProgram.size ≤ guestDecoderSizeBound :=
  decoderProgram_size_le_measured.trans (by unfold guestDecoderSizeBound; decide)

/-- **The program's price** on an execution: the top's on the program, `κ` and the memory vector,
and the entry's `8`. -/
noncomputable def decoderProgramPrice (prog : Program) (t : Execution prog) : ℕ :=
  machineCost decoderProgram decTopC.costIdx
    [encodeValue prog, encodeValue t.logMemorySize, encodeValue (memoryVector t.memory)] + 8

/-- **The deployed decoder, on executions**: `End.decode` of the memory. A constant, so that the
specification's field reads `memoryDecoder t` as stated here (the kernel, matching
`encodeValue ((fun t ↦ …) t)` with `encodeValue (End.decode t.memory)`, would unfold the
encoding, then the decoder, before reducing the redex). -/
noncomputable def memoryDecoder (t : Execution LeanVM.Guest.guest) : Decoded :=
  LeanVM.Guest.End.decode t.memory

/-- **The program computes the deployed decoder**, within any budget covering its price. -/
theorem outputWithin_decoderProgram (t : Execution LeanVM.Guest.guest) {b : ℕ}
    (hb : decoderProgramPrice LeanVM.Guest.guest t ≤ b) :
    outputWithin decoderProgram (encodeDecoderInput LeanVM.Guest.guest t) b =
      some (encodeValue (memoryDecoder t)) := by
  have h : memoryDecoder t = decTop LeanVM.Guest.guest t.logMemorySize (memoryVector t.memory) :=
    (decTop_eq t.memory).symm
  rw [h]
  exact outputWithin_decoderEntry decoderProgram_entry LeanVM.Guest.guest t
    (decTopC.costSpec decoderProgram decoderProgram_includes LeanVM.Guest.guest t.logMemorySize
      (memoryVector t.memory)) hb

/-- The specification for `memoryDecoder`. -/
theorem decoderProgram_spec_memoryDecoder
    (hprice : ∀ input (t : Execution LeanVM.Guest.guest),
      ValidExecution LeanVM.Guest.guest input t →
        decoderProgramPrice LeanVM.Guest.guest t ≤ guestDecoderBudget t) :
    LeanVM.Guest.End.DecoderProgramSpec decoderProgram memoryDecoder :=
  ⟨decoderProgram_size_le, fun input t hv ↦ outputWithin_decoderProgram t (hprice input t hv)⟩

/-- **The decoder program's specification**, its price within the budget on every valid execution
given (open: the decoder's cost bounds). -/
theorem decoderProgram_spec
    (hprice : ∀ input (t : Execution LeanVM.Guest.guest),
      ValidExecution LeanVM.Guest.guest input t →
        decoderProgramPrice LeanVM.Guest.guest t ≤ guestDecoderBudget t) :
    LeanVM.Guest.End.DecoderProgramSpec decoderProgram fun t ↦ LeanVM.Guest.End.decode t.memory :=
  (show memoryDecoder = fun t ↦ LeanVM.Guest.End.decode t.memory from rfl) ▸
    decoderProgram_spec_memoryDecoder hprice

end

end LeanVM.Cost
