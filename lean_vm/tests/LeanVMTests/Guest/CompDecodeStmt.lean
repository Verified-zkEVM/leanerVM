import LeanVM.E2E.Complete.DecodeStmt

/-!
# Tests: the decoder reads an honest child's statement (T6-det, D2 piece (IV))

`kidStmt_honest` and its pieces rest on Lean's three axioms.
-/

namespace LeanVMTests.Guest.CompDecodeStmt

/-- info: 'LeanVM.E2E.Complete.kidStmt_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.kidStmt_honest

/-- info: 'LeanVM.E2E.Complete.take4_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.take4_flatMap

/-- info: 'LeanVM.E2E.Complete.entryX_of_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.entryX_of_cells

/-- info: 'LeanVM.E2E.Complete.entryS_of_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.entryS_of_cells

/-- info: 'LeanVM.E2E.Complete.nodup_getElem?_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.nodup_getElem?_inj

end LeanVMTests.Guest.CompDecodeStmt
