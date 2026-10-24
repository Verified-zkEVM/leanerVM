/-
  LeanVM.Guest.Budget.DeployedBudget

  The deployed budget (`deployedBudget Bv`): `mainBudget` at the deployed frame sizes, the static
  certificates' words (`Count.wSB`, `Count.wSK`) and counts (`Count.mainCounts`), the jump table's
  `SET`s and `verify_lean_xmss`'s arms (`B2C.xmssArmC`); and the guest's completeness within it,
  from each child's `verify_sub` within `Bv`.
-/

module

public import LeanVM.Guest.Budget.Deployed
public import LeanVM.Guest.Count.Instances
public import LeanVM.Guest.B2C.ArmBound

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node
open LeanVM.Guest.End (GuestCompleteWithin Budget bytecode)
open LeanVM.Guest.B1.Main (VerifySubGoalsTB)

@[expose] public section

/-- **The deployed budget**, `verify_sub`'s words `Bv` per child. -/
noncomputable def deployedBudget (Bv : ℕ) : Budget :=
  mainBudget B2C.fs Count.wSB Count.wSK Bv (B2C.ωArm B2C.xmssArmC) Count.mainCounts B2C.jtSets

/-- **The guest is complete within the deployed budget**, each child's `verify_sub` complete within
`Bv` words. -/
theorem guest_complete_deployed {Pvs : ℕ → Tree → Prop} {Bv : ℕ}
    (hV : ∀ seed s w, NodeRel bytecode seed s w → Limits bytecode s w →
      CapsAgree bytecode seed w → NoZeroChallenge bytecode seed w →
      VerifySubGoalsTB B2C.fs B2C.cert 0 seed s w Pvs Bv) :
    GuestCompleteWithin (deployedBudget Bv) :=
  guest_complete_budget B2C.xmssArmC B2C.xmssArmC_spec Count.mainCounts Count.mainStatics hV

end
end LeanVM.Guest.Budget
