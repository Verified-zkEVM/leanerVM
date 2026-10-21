import LeanVM.E2E.Complete.GuestModelDeployed
import LeanVM.E2E.Complete.GuestModelAll
import LeanVM.E2E.Complete.DecodeSplit
import LeanVM.E2E.Complete.DecodeMain
import LeanVM.Guest.EndCompleteCT
import LeanVM.E2E.Complete.DecodeImage
import LeanVM.E2E.Complete.DecodeVsAgree
import LeanVM.E2E.Complete.DecodeCount
import LeanVM.E2E.Complete.DecodeVsArgs

/-!
# Tests: `main`'s completeness over a completeness model (L2, Main and End)

* The generic lemmas of the Main layer (`Guest/B1/Main/*C.lean`, `*S.lean`, `HashH.lean`,
  `RowsC.lean`), the End layer (`Guest/EndCompleteC.lean`) and the assembly
  (`E2E/Complete/GuestModel.lean`) rest on Lean's three axioms.
* **At the deployed model they re-derive the deployed completeness**: `guest_complete_of_model` is
  `End.guest_complete`'s statement, from `guestCompleteModelExec_at` at `CompModel.deployed` with
  `b1CompHyps_deployed`.
-/

namespace LeanVMTests.Guest.CompMain

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.E2E.Complete

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.B2C.runCountB_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.runCountB_eq

/-- info: 'LeanVM.Guest.B1.Main.batchWith_ans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.batchWith_ans

/-- info: 'LeanVM.Guest.B1.Main.batchWith_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.batchWith_steps

/-- info: 'LeanVM.Guest.B1.Main.fsRowsC_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.fsRowsC_model

/-- info: 'LeanVM.Guest.B1.Main.bsRowsC_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.bsRowsC_model

/-- info: 'LeanVM.Guest.B1.kidsFromInS_of_kidsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.kidsFromInS_of_kidsB

/-- info: 'LeanVM.Guest.B1.Main.relAtInWS_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.relAtInWS_of_walk

/-- info: 'LeanVM.Guest.B1.Main.aggregateC_claims_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.aggregateC_claims_complete

/-- info: 'LeanVM.Guest.B1.Main.aggregateC_claims_completeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.aggregateC_claims_completeAt

/-- info: 'LeanVM.Guest.B1.Main.loop5C_completeAtW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop5C_completeAtW

/-- info: 'LeanVM.Guest.B1.Main.mainS_relAtInW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.mainS_relAtInW

/-- info: 'LeanVM.Guest.B1.Main.honestC_wordsOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.honestC_wordsOk

/-- info: 'LeanVM.Guest.B1.Main.mainC_completeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.mainC_completeW

/-- info: 'LeanVM.Guest.B1.Main.mainCompleteC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.mainCompleteC_of

/-- info: 'LeanVM.Guest.End.honest_of_mainC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.honest_of_mainC

/-- info: 'LeanVM.Guest.End.validB_of_honestC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.validB_of_honestC

/-- info: 'LeanVM.E2E.Complete.mainCompleteC_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.mainCompleteC_b2c

/-- info: 'LeanVM.E2E.Complete.guestCompleteModelExec_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.guestCompleteModelExec_at

/-- info: 'LeanVM.E2E.Complete.guestCompleteModelExec_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.guestCompleteModelExec_of

/-- info: 'LeanVM.Guest.B1.Main.calleesAtC_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.calleesAtC_of_open

/-- info: 'LeanVM.E2E.Complete.calleesOpenC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.calleesOpenC_deployed

/-- info: 'LeanVM.E2E.Complete.calleesAtC_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.calleesAtC_deployed

/-- info: 'LeanVM.E2E.Complete.b1CompHyps_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.b1CompHyps_deployed

/-- info: 'LeanVM.E2E.Complete.guest_complete_of_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.guest_complete_of_model

/-! ## The deployed re-derivation -/

/-- `End.guest_complete`'s statement, from the model theorem at the deployed model. -/
example : End.GuestCompleteWithin B2C.b2cBudget' := guest_complete_of_model

/-- The model theorem's statement, from group B1's facts over every model. -/
example (h : ∀ CM, B1CompHyps CM) : GuestCompleteModelExec := guestCompleteModelExec_of h

end LeanVMTests.Guest.CompMain

/-! The execution half of L2 over every completeness model, unconditional, and the decode layer's
pieces so far. -/

/-- info: 'LeanVM.E2E.Complete.guestCompleteModelExec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.guestCompleteModelExec

/-- info: 'LeanVM.E2E.Complete.decodeHonest_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.decodeHonest_of

/-- info: 'LeanVM.E2E.Complete.mainFrame_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.mainFrame_eq

/-- info: 'LeanVM.Guest.End.mainCompleteC_ofT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.mainCompleteC_ofT

/-- info: 'LeanVM.E2E.Complete.honest_read_loadEqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_read_loadEqns

/-- info: 'LeanVM.E2E.Complete.vsProofOf_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.vsProofOf_of_agree

/-- info: 'LeanVM.E2E.Complete.vsOpen_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.vsOpen_of_agree

/-- info: 'LeanVM.Guest.B2C.NodeAgree.eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.NodeAgree.eq

/-- info: 'LeanVM.E2E.Complete.loop5Q_insts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.loop5Q_insts

/-- info: 'LeanVM.E2E.Complete.honest_read_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_read_inst

/-- info: 'LeanVM.E2E.Complete.vsArgsAt_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.vsArgsAt_honest
