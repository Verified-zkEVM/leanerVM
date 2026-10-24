/-
  LeanVM.Guest.Budget.Closed

  **The guest is complete within the deployed budget**, with no hypothesis left: each child's
  `verify_sub` within `vsBound Count.vsWords vkBound` words (B1-d's `verify_sub_completeB`, B1-f's
  `verifySubGoalsTB_of`).
-/

module

public import LeanVM.Guest.Budget.DeployedBudget
public import LeanVM.Guest.Count.VsWords
public import LeanVM.Guest.B1.Main.VerifySubGoals
public import LeanVM.Guest.B1.VerifySub.CompleteAll

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.End (GuestCompleteWithin bytecode bytecode_length)

@[expose] public section

/-- **`verify_sub`'s words per child** at the deployed instance. -/
noncomputable def deployedBv : ℕ := B1.VerifySub.vsBound Count.vsWords B1.VerifySub.vkBound

/-- **The aggregation guest is complete within the deployed budget**: for every seed, statement
and witness with `NodeRel`, within the deployed limits, the caps agreeing, no zero challenge where
the guest divides, and the node's committed size at the budget at most `2^28`, there is a valid
execution of the guest on the statement's digest within the verifier's size cap. -/
theorem guest_complete : GuestCompleteWithin (deployedBudget deployedBv) :=
  guest_complete_deployed (Pvs := fun _ _ => True) fun _ _ _ hr hl hca hnz =>
    B1.Main.verifySubGoalsTB_of bytecode_length B2C.runsFit B2C.runsApart Count.vsWords
      (B1.VerifySub.verify_keccak_completeAtB_fs 16) hr hl hca hnz

end
end LeanVM.Guest.Budget
