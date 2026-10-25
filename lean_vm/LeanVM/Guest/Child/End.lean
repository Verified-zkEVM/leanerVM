/-
  LeanVM.Guest.Child.End

  The end theorems of honest children and of the covered nodes: `GuestChildComplete` and
  `GuestCompleteCovered`.
-/

import LeanVM.Guest.Child.NZRpm
import LeanVM.Guest.Child.Deployed
import LeanVM.Guest.Child.Covered

/-!
# Honest children

`guest_child_complete : GuestChildComplete`, with the child prover (`childProver`): in the
random-permutation model its proof is rejected by the verifier refusing a zero challenge with
probability at most `2^-126` (`rpmChild_126`), and its proof with the deployed Keccak, accepted by
that verifier, is a child the guest accepts (`childOk_of_verifierNZ`).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Child

/-- **The honest proof of a guest execution is a child the guest accepts.** -/
theorem guest_child_complete : GuestChildComplete :=
  ⟨childProver, fun _ _ _ _ hv hb hρ ↦ rpmChild_126 hv hb hρ,
    fun _ _ _ h22 hsh hacc ↦ childOk_of_verifierNZ h22 hsh hacc⟩

end LeanVM.Guest.Budget
