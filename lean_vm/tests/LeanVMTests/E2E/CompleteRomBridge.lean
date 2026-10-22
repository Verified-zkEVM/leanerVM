import LeanVM.E2E.Complete.Rom.CompBridge

/-!
# Tests: the bridge from the oracle prover to the H-oblivious prover (T6-prob)

Interpreting the queries of the honest prover of the random-oracle model (`honestProverComp`)
commutes with the monadic prover (`simulateQ_honestProverM`), its `Id` instance is `honestOutN`
(`honestProverM_id`), and a run answered by a log's answers is `honestOutN` at every agreeing hash
(`honestProverComp_look`) — on Lean's three axioms, the seed's naturality on `propext` and
`Quot.sound` alone (`LeanVM/E2E/Complete/Rom/CompBridge.lean`).
-/

namespace LeanVMTests.E2E.CompleteRomBridge

/-- info: 'LeanVM.E2E.Complete.simulateQ_digestOfM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.simulateQ_digestOfM

/-- info: 'LeanVM.E2E.Complete.simulateQ_seedOfM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.simulateQ_seedOfM

/-- info: 'LeanVM.E2E.Complete.simulateQ_claimsOfM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.simulateQ_claimsOfM

/-- info: 'LeanVM.E2E.Complete.simulateQ_honestBatchM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.simulateQ_honestBatchM

/-- info: 'LeanVM.E2E.Complete.simulateQ_nodeLogPairsM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.simulateQ_nodeLogPairsM

/-- info: 'LeanVM.E2E.Complete.simulateQ_fsRunM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.simulateQ_fsRunM

/-- info: 'LeanVM.E2E.Complete.simulateQ_freshRunM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.simulateQ_freshRunM

/-- info: 'LeanVM.E2E.Complete.simulateQ_batchWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.simulateQ_batchWith

/-- info: 'LeanVM.E2E.Complete.simulateQ_seedWith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.simulateQ_seedWith

/-- info: 'LeanVM.E2E.Complete.simulateQ_honestProverM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.simulateQ_honestProverM

/-- info: 'LeanVM.E2E.Complete.honestProverComp_lookImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestProverComp_lookImpl

/-- info: 'LeanVM.E2E.Complete.honestProverM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestProverM_id

/-- info: 'LeanVM.E2E.Complete.honestProverComp_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestProverComp_at

/-- info: 'LeanVM.E2E.Complete.honestProverComp_look' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestProverComp_look

end LeanVMTests.E2E.CompleteRomBridge
