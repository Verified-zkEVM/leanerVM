/-
  LeanVM.Guest.Budget.Deployed

  The guest's completeness within the explicit budget `mainBudget` at the deployed frame sizes,
  certificates and counts (`B2C`), from what is still supplied by hypothesis: the static callees'
  words (`MainStatics`), `main`'s callees' weights (`MainCounts`), `verify_lean_xmss`'s arms within
  `C`, and each child's `verify_sub` within `Bvf` at its announced stack log and rate.
-/

module

public import LeanVM.Guest.Budget.Final
public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.B2C.RunsFit
public import LeanVM.Guest.B2C.CntWeight
public import LeanVM.Guest.B1.Sig.XmssComplete
public import LeanVM.Guest.B1.Sig.SphincsLoads

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node
open LeanVM.Guest.End (GuestCompleteWithin bytecode)
open LeanVM.Guest.B1.Main (VerifySubGoalsTB MainStatics childBv)

@[expose] public section

/-- **The guest is complete within `mainBudget`** at the deployed instance. -/
theorem guest_complete_budget {SB SK : String → ℕ} {Pvs : NodeWitness → ℕ → Tree → Prop} {Bvf : ℕ → ℕ → ℕ}
    (C : Opcode → ℕ)
    (hC : ∀ op σ bufs kids rd args rets,
      (Memory.Tree.node "verify_lean_xmss" σ bufs kids).Valid coreProgram rd args rets →
        B2C.costW (nth Data.cplArms 20 []) σ (coreOf 20).body op ≤ C op)
    (H : ∀ op, MainCounts (B2C.ωArm C op) B2C.fs) (hS : MainStatics B2C.fs SB SK)
    (hV : ∀ seed s w, NodeRel bytecode seed s w → Limits bytecode s w →
      CapsAgree bytecode seed w → NoZeroChallenge bytecode seed w →
      VerifySubGoalsTB B2C.fs B2C.cert 0 seed s w (Pvs w) (childBv Bvf w)) :
    GuestCompleteWithin (mainBudget B2C.fs SB SK Bvf (B2C.ωArm C) H B2C.jtSets) :=
  B2C.guest_complete_b2c (mainComplete_budget B2C.fs B2C.cert B2C.cnt (B2C.ωArm C) B2C.jtSets H
    (B2C.two_le_fs _) B1.Sig.verify_lean_xmss_complete_holds
    B1.Sig.verify_sig_lean_sphincs_complete_loads B2C.runsFit hS hV (B2C.cnt_le_weight_arm C hC))

end
end LeanVM.Guest.Budget
