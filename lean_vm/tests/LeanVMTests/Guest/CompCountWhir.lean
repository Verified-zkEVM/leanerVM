import LeanVM.E2E.Complete.Count.Whir

/-!
# Tests: the deferring verifier's leaves (L17, package A)

The deferring verifier opens at most `whirLeaves = 368` leaves of at most `whirLeafWidth = 192`
words (`leafBound_deferredProgram`), through the ladder's bounds and WHIR's levels; they rest on
Lean's three axioms, the ladder's bounds on `propext` and `Quot.sound` only. The query bound is
reached: the ladder at stack size 28 and rate exponent 1 queries 368 positions, and its first
level folds 6 variables.
-/

namespace LeanVMTests.Guest.CompCountWhir

open LeanVM.Parameters

/-- The deployed query bound is tight: stack size 28, rate exponent 1. -/
example : (Whir.ladder 28 1).map (fun ls ↦ (ls.map (·.queries)).sum) = some 368 := by decide

/-- The first level folds 6 variables, so the stack's leaves have 64 words. -/
example : (Whir.ladder 28 1).map (fun ls ↦ ls.map (·.fold)) = some [6, 4, 4, 4, 4, 4] := by
  decide

/-- info: 'LeanVM.E2E.Complete.ladder_fold_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.ladder_fold_le

/-- info: 'LeanVM.E2E.Complete.ladder_queries_sum_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.ladder_queries_sum_le

/-- info: 'LeanVM.E2E.Complete.allRet_sampleQueriesAux_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.allRet_sampleQueriesAux_length

/-- info: 'LeanVM.E2E.Complete.leafBound_whirLevels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.leafBound_whirLevels

/-- info: 'LeanVM.E2E.Complete.leafBound_verifyExecution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.leafBound_verifyExecution

/-- info: 'LeanVM.E2E.Complete.leafBound_deferredProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.leafBound_deferredProgram

end LeanVMTests.Guest.CompCountWhir
