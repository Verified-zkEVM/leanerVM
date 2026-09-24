/-
  LeanerVMTests.Protocol.PowerBatching

  Regression controls for zero-based power batching.
-/

module

public import LeanerVM.Protocol.Generic.PowerBatching
public import Mathlib.Data.ZMod.Defs
meta import LeanerVM.Protocol.Generic.PowerBatching
meta import Mathlib.Data.ZMod.Defs

/-!
# Power-batching controls

Zero challenge detects the exponent origin. Two false components may cancel at one challenge,
while a singleton has no such challenge. Empty batching is the zero claim.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Protocol

@[expose] public section

#guard powerBatch (fun _ : Fin 1 ↦ (1 : ZMod 5)) 0 = 1
#guard (∑ j : Fin 1, (1 : ZMod 5) * 0 ^ (j.val + 1)) = 0
#guard powerBatch (![1, -1] : Fin 2 → ZMod 5) 1 = 0
#guard powerBatch (![1, -1] : Fin 2 → ZMod 5) 0 = 1
#guard powerBatch (Fin.elim0 : Fin 0 → ZMod 5) 3 = 0

example (ρ : ZMod 5) : powerBatch (fun _ : Fin 1 ↦ (1 : ZMod 5)) ρ ≠
    powerBatch (fun _ : Fin 1 ↦ (0 : ZMod 5)) ρ :=
  singleton_batch_ne _ _ (by decide) ρ

end
end LeanerVMTests.Protocol
