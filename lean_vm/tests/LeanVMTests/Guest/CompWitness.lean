import LeanVM.E2E.Complete.Witness

/-!
# Tests: T6-det's hypotheses hold together (T6-det, non-vacuity)

The leaf `wTree`, one leanXMSS claim held directly, at the constant hash `wH`, the rate `1` and
the fuel `1`: `idealVerify_complete_det`'s hypotheses and its conclusion, on Lean's three axioms.
-/

namespace LeanVMTests.Guest.CompWitness

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_wTree

/-- info: 'LeanVM.E2E.Complete.hyps_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.hyps_wTree

/-- info: 'LeanVM.E2E.Complete.valid_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.valid_wTree

/-- info: 'LeanVM.E2E.Complete.xmssHeld_wSig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.xmssHeld_wSig

/-- info: 'LeanVM.E2E.Complete.powFound_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.powFound_wTree

/-- info: 'LeanVM.E2E.Complete.limits_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.limits_wTree

/-- info: 'LeanVM.E2E.Complete.budget_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.budget_wTree

/-- info: 'LeanVM.E2E.Complete.count_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.count_wTree

/-- info: 'LeanVM.E2E.Complete.withinLimits_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.withinLimits_wTree

/-- info: 'LeanVM.E2E.Complete.weightsNonzero_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.weightsNonzero_wTree

/-- info: 'LeanVM.E2E.Complete.rootsInjAt_wTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.rootsInjAt_wTree

end LeanVMTests.Guest.CompWitness
