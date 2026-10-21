import LeanVM.Guest.EndCompleteCTI
import LeanVM.E2E.Complete.DecodeInsts

/-!
# Tests: the honest memory's words and `main`'s callees' trees (T6-det, L2 D2 (I), (III))

The image lemma (`honestAtB_retemp_F`, `honest_of_mainCT'`), `__loop100` in tree form and `main`'s
tree form with its statement-digest and DA-roots callees rest on Lean's three axioms.
-/

namespace LeanVMTests.Guest.CompDecodeTree

/-- info: 'LeanVM.Guest.Memory.honestAtB_retemp_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.honestAtB_retemp_F

/-- info: 'LeanVM.Guest.Memory.honestAtB_retemp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.honestAtB_retemp

/-- info: 'LeanVM.Guest.End.honest_of_mainCT'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.honest_of_mainCT'

/-- info: 'LeanVM.Guest.End.honest_of_mainCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.honest_of_mainCT

/-- info: 'LeanVM.Guest.End.mainCompleteC_ofT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.End.mainCompleteC_ofT

/-- info: 'LeanVM.Guest.B1.Main.loadsAll_covA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loadsAll_covA

/-- info: 'LeanVM.Guest.B1.Main.loop100_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop100_events

/-- info: 'LeanVM.Guest.B1.Main.loop100S_iterBST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop100S_iterBST

/-- info: 'LeanVM.Guest.B1.Main.loop100S_completeAtBST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop100S_completeAtBST

/-- info: 'LeanVM.Guest.B1.Main.CompleteAtBST.toWST_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.CompleteAtBST.toWST_valid

/-- info: 'LeanVM.Guest.B1.Main.loop5C_completeAtWT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.loop5C_completeAtWT

/-- info: 'LeanVM.Guest.B1.Main.mainS_relAtInWT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.mainS_relAtInWT

/-- info: 'LeanVM.Guest.B1.Main.mainC_completeWT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.mainC_completeWT

/-- info: 'LeanVM.E2E.Complete.loop5Q_insts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.loop5Q_insts

/-- info: 'LeanVM.E2E.Complete.loop5H_vs_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.loop5H_vs_inst

end LeanVMTests.Guest.CompDecodeTree
