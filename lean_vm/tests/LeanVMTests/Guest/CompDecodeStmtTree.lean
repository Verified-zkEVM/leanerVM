import LeanVM.E2E.Complete.DecodeStmtTree

/-!
# Tests: the children's statements from the trees (T6-det, L2 D2)

D2's assembly rests on Lean's three axioms.
-/

namespace LeanVMTests.Guest.CompDecodeStmtTree

/-- info: 'LeanVM.E2E.Complete.childLoads_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.childLoads_tables

/-- info: 'LeanVM.E2E.Complete.mainBuf_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.mainBuf_read

/-- info: 'LeanVM.E2E.Complete.loop5Q_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.loop5Q_nodes

/-- info: 'LeanVM.E2E.Complete.loop5_count_eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.loop5_count_eqns

/-- info: 'LeanVM.E2E.Complete.child_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.child_words

/-- info: 'LeanVM.E2E.Complete.child_words_of_mainQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.child_words_of_mainQ

/-- info: 'LeanVM.E2E.Complete.cover_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.cover_image

/-- info: 'LeanVM.E2E.Complete.main_bufs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.main_bufs_eq

/-- info: 'LeanVM.E2E.Complete.decode_stmts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.decode_stmts

end LeanVMTests.Guest.CompDecodeStmtTree
