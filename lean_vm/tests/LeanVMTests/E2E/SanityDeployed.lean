import LeanVM.E2E.SanityDeployed.Witness
import LeanVM.E2E.SanityDeployedBudget

/-!
# Tests: S1, the honest deployed sanity theorem

* The deployed honest prover's pieces (`LeanVM/E2E/SanityDeployed/`: the full proof's head and
  its deferred claims, the deployed batching's honest hints, the prover and its output), S1
  (`sanity_deployed`, `sanity_deployed_of_tree`) and its leanXMSS inhabitant rest on Lean's three
  axioms.
* The statements, restated: S1's conclusions are the tree's claims, the deployed outer verifier
  accepting, and V_I with BLAKE2s accepting or a compression collision.
* S1 with V_I's budget (`SanityDeployed/Count.lean`, `SanityDeployedBudget.lean`): its pieces and
  theorems rest on Lean's three axioms; the per-node bound is `134,742,095`, within `viStepBound`;
  V_I's count on the deployed proof is within `viCost N`, and the game's budgeted V_I from
  `SignState.init`, its hash answered by BLAKE2s (`hashImplOf blake2sBytes`), accepts.
-/

namespace LeanVMTests.E2E.SanityDeployed

open LeanVM LeanVM.E2E LeanVM.E2E.SanityDeployed LeanVM.E2E.Complete LeanVM.E2E.Sanity
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.LeanIsa

/-! ## Axioms -/

/-- info: 'LeanVM.E2E.SanityDeployed.nodeHead_prove_dep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeHead_prove_dep

/-- info: 'LeanVM.E2E.SanityDeployed.exists_deferred_dep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_deferred_dep

/-- info: 'LeanVM.E2E.SanityDeployed.batchWith_honestHintsDep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batchWith_honestHintsDep

/-- info: 'LeanVM.E2E.SanityDeployed.leafDeferDep_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leafDeferDep_holds

/-- info: 'LeanVM.E2E.SanityDeployed.deployedOut_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedOut_child

/-- info: 'LeanVM.E2E.SanityDeployed.deployedProve_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedProve_isSome

/-- info: 'LeanVM.E2E.SanityDeployed.deployedOut_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedOut_good

/-- info: 'LeanVM.E2E.SanityDeployed.count_tableOKWith_le_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms count_tableOKWith_le_length

/-- info: 'LeanVM.E2E.SanityDeployed.length_blakeRows_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms length_blakeRows_le

/-- info: 'LeanVM.E2E.SanityDeployed.count_blake2s_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms count_blake2s_le

/-- info: 'LeanVM.E2E.SanityDeployed.count_nodeStep_dep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms count_nodeStep_dep

/-- info: 'LeanVM.E2E.SanityDeployed.nodeStep_entry_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeStep_entry_kids

/-- info: 'LeanVM.E2E.SanityDeployed.deployedOut_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedOut_cost

/-- info: 'LeanVM.E2E.SanityDeployed.queryCount_deployed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms queryCount_deployed_le

/-- info: 'LeanVM.E2E.SanityDeployed.queryCount_deployed_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms queryCount_deployed_le_mul

/-- info: 'LeanVM.E2E.SanityDeployed.queryCount_deployed_le_viCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms queryCount_deployed_le_viCost

/-- info: 'LeanVM.E2E.SanityDeployed.sanity_deployed_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sanity_deployed_budget

/-- info: 'LeanVM.E2E.SanityDeployed.sanity_deployed_budget_of_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sanity_deployed_budget_of_tree

/-- info: 'LeanVM.E2E.SanityDeployed.sanity_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sanity_deployed

/-- info: 'LeanVM.E2E.SanityDeployed.sanity_deployed_of_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sanity_deployed_of_tree

/-- info: 'LeanVM.E2E.SanityDeployed.sanity_deployed_xmssLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sanity_deployed_xmssLeaf

/-- info: 'LeanVM.E2E.SanityDeployed.sanity_deployed_honestXmss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sanity_deployed_honestXmss

/-! ## The statements -/

/-- S1: from the prover's output, the claims, the deployed verifier, and V_I or a collision. -/
example (ρ pfuel : ℕ) (T : HonestTree) (hρ : validRate ρ) (hv : T.Valid blake2sBytes)
    {s : Node.NodeStatement} {π : Proof} {ip : IdealProof}
    (hout : deployedProve ρ pfuel T = some (s, π, ip)) {fuel : ℕ} (hfuel : T.size ≤ fuel) :
    s.claims = T.claims ∧ Node.verifyAggregate Guest.guest s π ∧
      (idealVerify (m := Id) blakeId Guest.guest ip fuel s = true ∨ CompressionCollision) :=
  sanity_deployed ρ pfuel T hρ hv hout hfuel

/-- S1 from the tree's conditions: validity, the limits and budget, the proofs of work. -/
example (ρ pfuel : ℕ) (T : HonestTree) (hρ : validRate ρ) (hv : T.Valid blake2sBytes)
    (hlim : T.WithinLimitsDep ρ pfuel) (hpow : T.PowFoundDep ρ pfuel) {fuel : ℕ}
    (hfuel : T.size ≤ fuel) :
    ∃ s π ip, deployedProve ρ pfuel T = some (s, π, ip) ∧ s.claims = T.claims ∧
      Node.verifyAggregate Guest.guest s π ∧
      (idealVerify (m := Id) blakeId Guest.guest ip fuel s = true ∨ CompressionCollision) :=
  sanity_deployed_of_tree ρ pfuel T hρ hv hlim hpow hfuel

/-- The deployed per-node bound: `2^27 − 1 + 2^19 + 80`, within the H-oblivious prover's. -/
example : depStepBound = 134742095 ∧ depStepBound ≤ viStepBound :=
  ⟨depStepBound_eq, depStepBound_le⟩

/-- `viCost N` covers V_I's queries on the deployed honest proof. -/
example (ρ pfuel : ℕ) (T : HonestTree) (hρ : validRate ρ) (hlim : T.WithinLimitsDep ρ pfuel)
    {s : Node.NodeStatement} {π : Proof} {ip : IdealProof}
    (hout : deployedProve ρ pfuel T = some (s, π, ip)) {N : ℕ} (hN : T.size ≤ N) :
    queryCount blake2sBytes Guest.guest ip N s ≤ viCost N :=
  queryCount_deployed_le_viCost hρ hlim hout hN

/-- S1 with V_I's budget, the game's oracle a fixed BLAKE2s: the claims, the deployed verifier,
the count within `viCost N`, and the budgeted V_I from the initial state accepting, `spent` its
count, or a collision. -/
example {nx ns : ℕ} (ρ pfuel : ℕ) (T : HonestTree) (hρ : validRate ρ)
    (hv : T.Valid blake2sBytes) (hlim : T.WithinLimitsDep ρ pfuel) {s : Node.NodeStatement}
    {π : Proof} {ip : IdealProof} (hout : deployedProve ρ pfuel T = some (s, π, ip)) {N : ℕ}
    (hN : T.size ≤ N) :
    s.claims = T.claims ∧ Node.verifyAggregate Guest.guest s π ∧
      queryCount blake2sBytes Guest.guest ip N s ≤ viCost N ∧
      (simulateQ (hashImplOf blake2sBytes) (((idealVerify (budgetedQuery (viCost N)) Guest.guest
          ip N s).run).run (SignState.init nx ns)) =
        pure (some true,
          { SignState.init nx ns with spent := queryCount blake2sBytes Guest.guest ip N s }) ∨
        CompressionCollision) :=
  sanity_deployed_budget (hashImplOf blake2sBytes) (simulateQ_hashImplOf blake2sBytes) ρ pfuel T
    hρ hv hlim hout hN

/-- S1 with V_I's budget from the tree's conditions. -/
example {nx ns : ℕ} (ρ pfuel : ℕ) (T : HonestTree) (hρ : validRate ρ)
    (hv : T.Valid blake2sBytes) (hlim : T.WithinLimitsDep ρ pfuel)
    (hpow : T.PowFoundDep ρ pfuel) {N : ℕ} (hN : T.size ≤ N) :
    ∃ s π ip, deployedProve ρ pfuel T = some (s, π, ip) ∧ s.claims = T.claims ∧
      Node.verifyAggregate Guest.guest s π ∧
      queryCount blake2sBytes Guest.guest ip N s ≤ viCost N ∧
      (simulateQ (hashImplOf blake2sBytes) (((idealVerify (budgetedQuery (viCost N)) Guest.guest
          ip N s).run).run (SignState.init nx ns)) =
        pure (some true,
          { SignState.init nx ns with spent := queryCount blake2sBytes Guest.guest ip N s }) ∨
        CompressionCollision) :=
  sanity_deployed_budget_of_tree (hashImplOf blake2sBytes) (simulateQ_hashImplOf blake2sBytes) ρ
    pfuel T hρ hv hlim hpow hN

/-- The collision is two rows of the compression function with distinct inputs and equal
outputs. -/
example : CompressionCollision ↔ ∃ r₁ r₂ : Semantics.BlakeRow, Semantics.blakeDeployed.row r₁ ∧
    Semantics.blakeDeployed.row r₂ ∧ ¬ RowFinal r₁ ∧ ¬ RowFinal r₂ ∧ r₁.out = r₂.out ∧
    rowInput r₁ ≠ rowInput r₂ := Iff.rfl

end LeanVMTests.E2E.SanityDeployed
