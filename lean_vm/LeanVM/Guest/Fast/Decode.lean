module

public import LeanVM.Guest.Fast.Main
public import LeanVM.Guest.EndFinal

/-!
# The guest's decoder, its frames numbered

`decode` (`Guest/EndFinal.lean`) reads `main`'s witness through the memory's frame map
`Located.frameV L`, keyed by the callee's name. `decode_eq_numbered`: it is the decoder reading
`decWitN` (`Fast/Main.lean`) through the frame map re-keyed by number,
`fun k ↦ Located.frameV L (decoderFunctionName k)`. A frame map built by number (a replay of the
calls, say) replaces that one where it is equal to it (`decodeWithN_congr`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Node
open LeanVM.Guest.End LeanVM.Guest.Check

@[expose] public section

/-- **The decoder at a numbered frame map** `F L` of each memory image `L`. -/
noncomputable def decodeWithN (F : ∀ {κ : ℕ}, MemoryImage κ → NFrames) : Decoder := fun {_} L ↦
  let σ := valG L 1 (certOf 1)
  ⟨B1.Main.decSeed σ, B1.Main.decStmt σ L.read, decWitN σ L.read (F L) VerifySub.cursorLen⟩

/-- **The deployed decoder reads the frames by number.** -/
theorem decode_eq_numbered {κ : ℕ} (L : MemoryImage κ) :
    decode L = decodeWithN (fun L k ↦ Located.frameV L (decoderFunctionName k)) L := by
  simp only [decodeWithN, decWitN_eq]
  rfl

/-- **Any numbered frame map that agrees with the memory's on the table decodes the same.** -/
theorem decodeWithN_congr {F G : ∀ {κ : ℕ}, MemoryImage κ → NFrames}
    (h : ∀ {κ : ℕ} (L : MemoryImage κ), F L = G L) {κ : ℕ} (L : MemoryImage κ) :
    decodeWithN F L = decodeWithN G L := by
  simp only [decodeWithN, h]

end
end LeanVM.Guest.Fast
