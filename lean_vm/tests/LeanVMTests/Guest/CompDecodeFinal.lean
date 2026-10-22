import LeanVM.E2E.Complete.DecodeFinal

/-!
# Tests: L2 and T6-det without L2 (T6-det, L2)

`guestCompleteModel` (L2), the end theorem `idealVerify_complete_det` and D3's pieces rest on Lean's three axioms.
-/

namespace LeanVMTests.Guest.CompDecodeFinal

/-- info: 'LeanVM.E2E.Complete.guestCompleteModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.guestCompleteModel

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_det

/-- info: 'LeanVM.E2E.Complete.d3HypO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.d3HypO

/-- info: 'LeanVM.E2E.Complete.guestCompleteModel_ofO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.guestCompleteModel_ofO

/-- info: 'LeanVM.E2E.Complete.vs_completeTO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.vs_completeTO

/-- info: 'LeanVM.E2E.Complete.validB_instArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.validB_instArgs

/-- info: 'LeanVM.E2E.Complete.names_disjoint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.names_disjoint

/-- info: 'LeanVM.E2E.Complete.vagree_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.vagree_honest

/-- info: 'LeanVM.E2E.Complete.open_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.open_child

/-- info: 'LeanVM.E2E.Complete.insts_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.insts_total

/-- info: 'LeanVM.E2E.Complete.honest_nodeAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_nodeAgree

/-- info: 'LeanVM.E2E.Complete.honest_inst_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honest_inst_valid

end LeanVMTests.Guest.CompDecodeFinal
