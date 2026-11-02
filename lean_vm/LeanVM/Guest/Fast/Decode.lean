module

public import LeanVM.Guest.Fast.Main
public import LeanVM.Guest.Fast.DiscreteLog
public import LeanVM.Guest.EndFinal

/-!
# The guest's decoder, its frames by index

`decode` (`Guest/EndFinal.lean`) reads `main`'s witness through the replayed frame map
`Located.frameVFast`, keyed by the callee's name: it looks the call up in the entry table at the
name's index (`nameIndex`) and reads the frame through the certificate of that name.

* `frameVFastN pre states rd j`: the same lookup keyed by the index `j` (through `canonIndex`),
  no name read; `frameVFastN_eq`: it is `frameVFast` at `decoderFunctionName j`, for every `j`;
* `decode_eq_numbered`: the deployed decoder is the one reading `decWitN` (`Fast/Main.lean`, the
  restated readers) through `frameVFastN`, the cursor's length by a discrete logarithm
  (`cursorLenWith dl`, `Fast/DiscreteLog.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Node
open LeanVM.Guest.Located LeanVM.Extraction.Fast

attribute [local instance] lexOrd

@[expose] public section

/-- **The replayed frame map, keyed by index** (`frameVFast`): the call of function
`canonIndex j` looked up in the entry table, its frame read through `certOf`. -/
noncomputable def frameVFastN (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    NFrames :=
  let table := entryTable pre states rd
  fun j args rets ↦ match table.get? (callKey (canonIndex j) args rets) with
    | some fp => fun v ↦ wordWith rd fp ((certOf (canonIndex j)).locs.getD v.idx 0)
    | none => fun _ ↦ 0

/-- **Keyed by index, the replayed frame map is the one keyed by name.** -/
theorem frameVFastN_eq (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) (j : ℕ) :
    frameVFastN pre states rd j = frameVFast pre states rd (decoderFunctionName j) := by
  have h1 : nameIndex (decoderFunctionName j) = canonIndex j := nameIndex_decoderFunctionName j
  have h2 : certByName (decoderFunctionName j) = certOf (canonIndex j) := congrArg certOf h1
  unfold frameVFastN frameVFast
  rw [h1, h2]
  funext args rets
  cases (entryTable pre states rd).get? (callKey (canonIndex j) args rets) <;> rfl

/-- **The deployed decoder reads the frames by index**, through the restated readers, the
cursor's length by any discrete logarithm `dl` (`discreteLog`, `Fast/DiscreteLog.lean`). -/
theorem decode_eq_numbered {dl : K → Option ℕ} (hdl : DiscreteLogSpec dl) {κ : ℕ}
    (L : MemoryImage κ) :
    End.decode L =
      let memT := Extraction.Fast.powTable κ
      let rd := readTable memT L
      let states := statesTable memT (Extraction.Fast.powTable guestProgram.logSize) guestProgram L
        replayFuel ⟨gpow 0, 1⟩
      let σ := End.mainValWith rd
      ⟨B1.Main.decSeed σ, B1.Main.decStmt σ rd,
        decWitN σ rd (frameVFastN (preTest rd) states rd) (cursorLenWith dl)⟩ := by
  have hV (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
      frameVFastN pre states rd = fun j ↦ frameVFast pre states rd (decoderFunctionName j) :=
    funext (frameVFastN_eq pre states rd)
  simp only [End.decode, hV, cursorLenWith_eq hdl, decWitN_eq]

end
end LeanVM.Guest.Fast
