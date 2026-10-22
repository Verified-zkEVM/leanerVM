import LeanVM.E2E.Complete.DecodeD3

/-!
# Tests: the children's proofs' frames and L2's assembly (T6-det, L2 D3)

The D3 infrastructure and `guestCompleteModel_of` rest on Lean's three axioms.
-/

namespace LeanVMTests.Guest.CompDecodeD3

/-- info: 'LeanVM.E2E.Complete.loop5Q_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.loop5Q_iter

/-- info: 'LeanVM.E2E.Complete.loop5Q_vs_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.loop5Q_vs_disjoint

/-- info: 'LeanVM.E2E.Complete.loop5Q_insts_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.loop5Q_insts_pos

/-- info: 'LeanVM.E2E.Complete.loop5H_vs_inst_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.loop5H_vs_inst_pos

/-- info: 'LeanVM.E2E.Complete.insts_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.insts_sub

/-- info: 'LeanVM.E2E.Complete.frOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.frOf_eq

/-- info: 'LeanVM.E2E.Complete.loop5_vs_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.loop5_vs_valid

/-- info: 'LeanVM.E2E.Complete.vs_child_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.vs_child_inst

/-- info: 'LeanVM.E2E.Complete.vs_proof_of_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.vs_proof_of_inst

/-- info: 'LeanVM.E2E.Complete.vs_completeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.vs_completeT

/-- info: 'LeanVM.E2E.Complete.ccl_completeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.ccl_completeT

/-- info: 'LeanVM.E2E.Complete.sd_completeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.sd_completeT

/-- info: 'LeanVM.E2E.Complete.cover_completeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.cover_completeT

/-- info: 'LeanVM.E2E.Complete.vrOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.vrOf_spec

/-- info: 'LeanVM.E2E.Complete.guestCompleteModel_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.guestCompleteModel_of

/-- info: 'LeanVM.E2E.Complete.mainFrame_133' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.mainFrame_133

/-- info: 'LeanVM.E2E.Complete.vsArgsAt_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.vsArgsAt_inj

end LeanVMTests.Guest.CompDecodeD3
