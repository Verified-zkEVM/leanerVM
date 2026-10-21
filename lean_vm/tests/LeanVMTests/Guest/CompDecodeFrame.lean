import LeanVM.E2E.Complete.DecodeFrame

/-!
# Tests: `main`'s frame on the honest memory, decoded (T6-det, D2 piece (IV))

`mainFrame_words`, `countOf_honest` and their pieces rest on Lean's three axioms.
-/

namespace LeanVMTests.Guest.CompDecodeFrame

/-- info: 'LeanVM.E2E.Complete.mainFrame_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.mainFrame_words

/-- info: 'LeanVM.E2E.Complete.countOf_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.countOf_honest

/-- info: 'LeanVM.E2E.Complete.mainVal_frameWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.mainVal_frameWords

/-- info: 'LeanVM.E2E.Complete.frameVals_named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.frameVals_named

end LeanVMTests.Guest.CompDecodeFrame
