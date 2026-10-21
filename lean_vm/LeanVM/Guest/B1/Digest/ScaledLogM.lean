/-
  LeanVM.Guest.B1.Digest.ScaledLogM

  `scaled_log__L11` and `scaled_log__L6` under any semantics of `BLAKE2S`: they do not hash, so
  their deployed meanings carry over.
-/

module

public import LeanVM.Guest.B1.Digest.ScaledLog
public import LeanVM.Guest.CoreB

/-!
# `scaled_log__L{shift}` under any semantics

The two `scaled_log` specializations have no `BLAKE2S` and call nothing, so their relation is the
same under every `S : BlakeSem` (`Core.relB_iff_rel_of_freeOn`, the kernel checking their bodies):
`scaled_log_11_iffB`, `scaled_log_6_iffB` (pattern A, transfer).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The two `scaled_log` specializations are free of `BLAKE2S` and call nothing. -/
theorem freeOn_scaled_log : coreProgram.FreeOn ["scaled_log__L11", "scaled_log__L6"] = true := by
  decide +kernel

/-- **`scaled_log__L11` under any semantics.** -/
theorem scaled_log_11_iffB {S : BlakeSem} {rd : Reader} {gsq : E} (hT : SquaresAt rd gsq) (x : E)
    (rets : List E) :
    coreProgram.RelB S rd "scaled_log__L11" [x, gsq] rets ↔
      ∃ v, rets = [v] ∧ ∃ N < 2 ^ 16, x = gen ^ N ∧ v = eOfNat (2 ^ 11 * N) := by
  rw [relB_iff_rel_of_freeOn freeOn_scaled_log (by simp)]
  exact scaled_log_11_iff hT x rets

/-- **`scaled_log__L6` under any semantics.** -/
theorem scaled_log_6_iffB {S : BlakeSem} {rd : Reader} {gsq : E} (hT : SquaresAt rd gsq) (x : E)
    (rets : List E) :
    coreProgram.RelB S rd "scaled_log__L6" [x, gsq] rets ↔
      ∃ v, rets = [v] ∧ ∃ N < 2 ^ 16, x = gen ^ N ∧ v = eOfNat (2 ^ 6 * N) := by
  rw [relB_iff_rel_of_freeOn freeOn_scaled_log (by simp)]
  exact scaled_log_6_iff hT x rets

end
end LeanVM.Guest.B1.Digest
