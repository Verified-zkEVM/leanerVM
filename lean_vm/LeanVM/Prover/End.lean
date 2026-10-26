/-
  LeanVM.Prover.End

  The completeness end theorems, for the statement's honest prover `LeanVM.prover`
  (`LeanVM.Prover.prove`, `Statement/Prover/Prove.lean`).
-/

import LeanVM.Prover.Assemble

/-!
# The completeness end theorems

`LeanVM.prover`, the statement's executable honest prover with the oracle calls, is the
specification's honest prover at the execution's witness (`LeanVM.Prover.prove_eq_honestComp`,
`specOnValid_prove`, `childSpec_prove`, `LeanVM/Prover/Assemble.lean`), so the completeness
theorems for such a prover (`completeness_of_spec`, `guestChildComplete_of_spec`,
`LeanVM/Prover/Complete.lean`) prove the end statements:

* `LeanVM.completeness_holds : Completeness`;
* `LeanVM.Guest.Budget.guest_child_complete : GuestChildComplete`.
-/

namespace LeanVM

open LeanVM.Prover

/-- **Completeness holds** (in the random-permutation model), for the honest prover
`LeanVM.prover`. -/
theorem completeness_holds : Completeness :=
  completeness_of_spec LeanVM.prover specOnValid_prove_honest

/-- **The honest prover's proofs of guest executions are children the guest accepts**: both parts
of `GuestChildComplete` for `LeanVM.prover`. -/
theorem Guest.Budget.guest_child_complete : Guest.Budget.GuestChildComplete :=
  guestChildComplete_of_spec LeanVM.prover specOnValid_prove childSpec_prove

end LeanVM
