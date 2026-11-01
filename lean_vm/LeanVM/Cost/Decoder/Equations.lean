module

public import LeanVM.Cost.Decoder.Witness
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the staged functions are the decoder's

The staged forms the chain compiles are the deployed decoder's functions, proved apart from the
compiled modules (their kernel checks stay small):

* `decWitStaged_eq : decWitStaged = B1.Main.decWit`;
* `decWitNStaged_eq : decWitNStaged = Guest.Fast.decWitN`, the deployed decoder's witness at the
  frame map keyed by index (`Guest.Fast.decode_eq_numbered`).
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

end

end LeanVM.Cost.Decoder
