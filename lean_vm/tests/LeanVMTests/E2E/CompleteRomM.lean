import LeanVM.E2E.Complete.Rom.CountM

/-!
# Tests: the honest prover's monadic pieces (T6-prob, P3a)

The monadic pieces of `LeanVM/E2E/Complete/Rom/MonadicM.lean` are the pure functions of T6-det at
`Id` (`fsRunM_id`, `freshRunM_id`, `seedOfM_id`, `digestOfM_id`, `honestBatchM_id`,
`nodeLogPairsM_id`, …), and their query counts at the random oracle
(`LeanVM/E2E/Complete/Rom/CountM.lean`) rest on Lean's three axioms (the closed bound's value on
`propext` alone).
-/

namespace LeanVMTests.E2E.CompleteRomM

/-- info: 'LeanVM.E2E.Complete.fsRunM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.fsRunM_id

/-- info: 'LeanVM.E2E.Complete.freshRunM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.freshRunM_id

/-- info: 'LeanVM.E2E.Complete.seedOfM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.seedOfM_id

/-- info: 'LeanVM.E2E.Complete.digestOfM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.digestOfM_id

/-- info: 'LeanVM.E2E.Complete.honestRoundsM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestRoundsM_id

/-- info: 'LeanVM.E2E.Complete.honestBatchM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestBatchM_id

/-- info: 'LeanVM.E2E.Complete.honestHintsM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestHintsM_id

/-- info: 'LeanVM.E2E.Complete.honestWeightsM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestWeightsM_id

/-- info: 'LeanVM.E2E.Complete.rel_nodeChecksWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.rel_nodeChecksWith

/-- info: 'LeanVM.E2E.Complete.nodeChecksWith_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.nodeChecksWith_log

/-- info: 'LeanVM.E2E.Complete.nodeLogPairsWithM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.nodeLogPairsWithM_id

/-- info: 'LeanVM.E2E.Complete.nodeLogPairsM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.nodeLogPairsM_id

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_fsRunM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_fsRunM

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_fsRunM_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_fsRunM_nil

/-- info: 'LeanVM.E2E.Complete.costLE_claimsProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.costLE_claimsProg

/-- info: 'LeanVM.E2E.Complete.costLE_deferredProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.costLE_deferredProgram

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_freshRunM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_freshRunM

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_seedOfM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_seedOfM

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_statementDigestWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_statementDigestWith

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_digestOfM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_digestOfM

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_honestBatchM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_honestBatchM

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_verifyDeferredWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_verifyDeferredWith

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_commitCodewordsWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_commitCodewordsWith

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_batchWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_batchWith

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_nodeChecksWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_nodeChecksWith

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_nodeLogPairsWithM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_nodeLogPairsWithM

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_nodeLogPairsM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_nodeLogPairsM

/-- info: 'LeanVM.E2E.Complete.nodeChecksQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.nodeChecksQueries_le

/-- info: 'LeanVM.E2E.Complete.nodeChecksBound_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.nodeChecksBound_eq

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_nodeLogPairsM_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_nodeLogPairsM_le

end LeanVMTests.E2E.CompleteRomM
