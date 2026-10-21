import LeanVM.E2E.Complete.TreeLog

/-!
# Tests: L17 reduced to a count (T6-det)

The node's log of hashed strings supports its digest and relation (`nodeSupport_of_count`), and
T6-det holds with the tree within the limits as `WithinLimits'` (`idealVerify_complete''`); they
rest on Lean's three axioms.
-/

namespace LeanVMTests.Guest.CompTreeLog

/-- info: 'LeanVM.E2E.Complete.nodeSupport_of_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.nodeSupport_of_count

/-- info: 'LeanVM.E2E.Complete.nodeRelWith_answeredOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.nodeRelWith_answeredOn

/-- info: 'LeanVM.E2E.Complete.statementDigestWith_answeredOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.statementDigestWith_answeredOn

/-- info: 'LeanVM.E2E.Complete.rel_batchWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.rel_batchWith

/-- info: 'LeanVM.E2E.Complete.rel_simulateQ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.rel_simulateQ

/-- info: 'LeanVM.E2E.Complete.rel_commitCodewordsWith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.rel_commitCodewordsWith

/-- info: 'LeanVM.E2E.Complete.HonestTree.withinLimits_of'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.HonestTree.withinLimits_of'

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete''' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete''

end LeanVMTests.Guest.CompTreeLog
