module

public import LeanVM.Cost.Decoder.Replay
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the staged functions are the decoder's

The staged forms the chain compiles are the deployed decoder's functions, proved apart from the
compiled modules (their kernel checks stay small):

* `decWitStaged_eq : decWitStaged = B1.Main.decWit`;
* `decWitNStaged_eq : decWitNStaged = Guest.Fast.decWitN`, the deployed decoder's witness at the
  frame map keyed by index (`Guest.Fast.decode_eq_numbered`);
* `replayStatesOf_eq : replayStatesOf memT codeT prog mem = Located.statesTable memT codeT prog
  mem.get replayFuel ⟨gpow 0, 1⟩`, the replay `decode_eq_numbered` reads, on the memory vector
  (`statesVec_eq`: each step `stepVec`, which is `stepTable` at `mem.get`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **The staged witness is `decWit`.** -/
theorem decWitStaged_eq : decWitStaged = decWit := by
  funext σ rd wX wS wD wV wA
  unfold decWitStaged decWit
  congr 1

/-- **The staged witness is `decWitN`.** -/
theorem decWitNStaged_eq : decWitNStaged = LeanVM.Guest.Fast.decWitN := by
  funext σ rd Vn cl
  unfold decWitNStaged LeanVM.Guest.Fast.decWitN
  rw [decWitStaged_eq]
  rfl

open LeanVM.Semantics LeanVM.Extraction.Fast LeanVM.Guest.Located in
/-- **On the memory vector, `statesVec` is `statesTable`**, the final registers given. -/
theorem statesVec_eq (memT codeT : Array (ℕ × ℕ)) (prog : LeanVM.Semantics.Program) {κ : ℕ}
    (mem : Vector E (2 ^ κ)) :
    ∀ fuel r, statesVec memT codeT prog mem (Registers.final prog) fuel r =
      statesTable memT codeT prog mem.get fuel r
  | 0, r => rfl
  | fuel + 1, r => by
    rw [statesVec, statesTable, stepVec_eq]
    congr 1
    split
    · rfl
    · cases stepTable memT codeT prog mem.get r with
      | none => rfl
      | some r' => exact statesVec_eq memT codeT prog mem fuel r'

open LeanVM.Semantics LeanVM.Guest.Located in
/-- **The compiled replay is the decoder's**: the run from `(g^0, 1)` over `replayFuel`
(`Guest.Fast.decode_eq_numbered`'s `states`), the memory image `mem.get`. -/
theorem replayStatesOf_eq (memT codeT : Array (ℕ × ℕ)) (prog : LeanVM.Semantics.Program) {κ : ℕ}
    (mem : Vector E (2 ^ κ)) :
    replayStatesOf memT codeT prog mem = statesTable memT codeT prog mem.get replayFuel ⟨gpow 0, 1⟩ :=
  statesVec_eq memT codeT prog mem replayFuel _

end

end LeanVM.Cost.Decoder
