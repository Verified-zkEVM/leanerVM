import LeanVM.E2E.Complete.Count.FinalWitness

/-!
# Tests: L17's count, proved (packages C, D, E)

The statement digests, the batching, a DA opening and the node's whole log are counted
(`prefixCount_statementDigestWith_le`, `prefixCount_batchWith`, `prefixCount_daLog_le`,
`prefixCount_nodeLog_le`); under the deployed limits and the node relation the count is below
`2^64` (`nodeLog_count_lt`), so T6-det holds under the deployed limits and budget alone
(`idealVerify_complete_final`), here at the leaf `wTree` too. All rest on Lean's three axioms.
-/

namespace LeanVMTests.Guest.CompCountNode

open LeanVM.E2E.Complete

/-- A DA opening's bound, evaluated. -/
example : daOpenBlocks = 6138880 := rfl

/-- A child's deferring verifier's bound, evaluated: `368` leaves of at most `23` blocks. -/
example : whirLeaves * leafBlocks whirLeafWidth = 8464 := by decide

/-- info: 'LeanVM.E2E.Complete.prefixCount_statementDigestWith_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.prefixCount_statementDigestWith_le

/-- info: 'LeanVM.E2E.Complete.prefixCount_batchWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.prefixCount_batchWith

/-- info: 'LeanVM.E2E.Complete.prefixCount_daLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.prefixCount_daLog_le

/-- info: 'LeanVM.E2E.Complete.prefixCount_nodeLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.prefixCount_nodeLog_le

/-- info: 'LeanVM.E2E.Complete.nodeLog_count_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.nodeLog_count_lt

/-- info: 'LeanVM.E2E.Complete.HonestTree.withinLimits'_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.HonestTree.withinLimits'_of_budget

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_final

/-- info: 'LeanVM.E2E.Complete.hyps_final_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.hyps_final_wTree

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_final_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_final_wTree

end LeanVMTests.Guest.CompCountNode
