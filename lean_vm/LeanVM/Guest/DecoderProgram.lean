module

public import LeanVM.Guest.EndFinal
public import Statement.Theorems

/-!
# The guest decoder as a program: from its specification to `GuestKnowledge`

`GuestKnowledge guest D` (`Statement/Theorems.lean`) takes the decoder as a cost-machine
program `D`, run within `guestDecoderBudget` on the encoded execution, its output the encoding of
a decoding. The proofs read a decoding off an execution (`decoder : Execution guest → Decoded`;
`guest_knowledge` for `decode`, which reads it off the memory). Two facts relate them:

* **`DecoderProgramSpec D decoder`**: `D`'s size is within `guestDecoderSizeBound`, and on
  every valid execution `D` outputs, within its budget, the encoding of `decoder`'s decoding;
* **`DecoderExplains decoder`**: on every valid execution, `decoder`'s decoding explains the public
  input (`ExplainsInput`); for `decode` it is `guest_knowledge` (`decoderExplains_decode`).

From them, **`guestKnowledge_of_spec : GuestKnowledge guest D`**, the decoding `decoder t`. For
the compiled decoder `LeanVM.Cost.decoderProgram` and `decode`, both are proved
(`Cost/DecoderSpec.lean`'s `decoderProgram_spec` with `Cost/Bounds/Guest/Budget.lean`'s
`decoderPriceWithinBudget`; `decoderExplains_decode`), and `LeanVM.theorems_hold` takes no
hypothesis.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Cost

@[expose] public section

/-- **What the guest decoder program must satisfy**, for a decoder of executions
`decoder`: its size is within `guestDecoderSizeBound`, and on every valid execution of the guest
it outputs, within its budget, the encoding of `decoder`'s decoding. -/
structure DecoderProgramSpec (decoderProgram : Cost.MachineProgram) (decoder : Execution guest → Decoded) :
    Prop where
  /-- The size bound. -/
  size : decoderProgram.size ≤ guestDecoderSizeBound
  /-- The program computes `decoder` within its budget on every valid execution. -/
  computes : ∀ input (t : Execution guest), ValidExecution guest input t →
    outputWithin decoderProgram (encodeDecoderInput guest t) (guestDecoderBudget t) =
      some (encodeValue (decoder t))

/-- **The decoder's decodings explain the public input**: on every valid execution of the guest
on a public input, `decoder`'s decoding explains it (`ExplainsInput`). -/
def DecoderExplains (decoder : Execution guest → Decoded) : Prop :=
  ∀ input (t : Execution guest), ValidExecution guest input t → ExplainsInput guest input (decoder t)

/-- `decode`, read off the memory, explains the public input: `guest_knowledge`. -/
theorem decoderExplains_decode : DecoderExplains fun t ↦ decode t.memory := guest_knowledge

/-- **`GuestKnowledge` of the decoder program**, from its spec and its decoder's decodings
explaining the input. -/
theorem guestKnowledge_of_spec {decoderProgram : Cost.MachineProgram}
    {decoder : Execution guest → Decoded} (h : DecoderProgramSpec decoderProgram decoder)
    (hx : DecoderExplains decoder) : GuestKnowledge guest decoderProgram :=
  fun input t hv ↦ ⟨decoder t, h.computes input t hv, hx input t hv⟩

/-- **`GuestKnowledge` of a program that computes `decode`**: its spec alone. -/
theorem guestKnowledge_of_decode {decoderProgram : Cost.MachineProgram}
    (h : DecoderProgramSpec decoderProgram fun t ↦ decode t.memory) :
    GuestKnowledge guest decoderProgram :=
  guestKnowledge_of_spec h decoderExplains_decode

end

end LeanVM.Guest.End
