import LeanVM.E2E.Headline

/-!
# Tests: V_I's budget covers honest proofs

* V_I's query count, piece by piece (`LeanVM/E2E/BudgetCount.lean`), on an honest node
  (`LeanVM/E2E/Complete/NodeCount.lean`) and on the honest proof
  (`LeanVM/E2E/Complete/Rom/ViCost.lean`), and T6-prob with the game's budget
  (`LeanVM/E2E/Complete/Rom/EndBudget.lean`, `aggregate_complete_final`) rest on Lean's three
  axioms.
* The constants: `13,508` at the root, `179,719,581 ≈ 2^27.42` per node, `179,733,089` the
  headline's `viNodeCost`; the pieces' counts (the IV `2`, a statement's digest `5`, a DA root's
  vector digest `18`).
* The budgeted T6-prob is not vacuous: the honest leanXMSS leaf generator at rate `1`, a
  proof-of-work fuel of `2^25` nonces, V_I on one node with the budget `viCost 1`: the honest proof
  is rejected with probability at most `2^-124`.
-/

namespace LeanVMTests.E2E.ViBudget

open OracleComp OracleSpec LeanVM LeanVM.E2E LeanVM.Protocol.Verifier
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Blake2sHash
open scoped ENNReal

/-! ## Axioms -/

/-- info: 'LeanVM.E2E.count_simulateQ_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms count_simulateQ_le

/-- info: 'LeanVM.E2E.count_verifyBlindWith_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms count_verifyBlindWith_le

/-- info: 'LeanVM.E2E.stackShape_height_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stackShape_height_le

/-- info: 'LeanVM.E2E.count_closure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms count_closure_le

/-- info: 'LeanVM.E2E.queryCount_le_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms queryCount_le_of

/-- info: 'LeanVM.E2E.Complete.count_nodeStep_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complete.count_nodeStep_honest

/-- info: 'LeanVM.E2E.Complete.length_nodeLogWith_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complete.length_nodeLogWith_le

/-- info: 'LeanVM.E2E.Complete.honestOutN_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complete.honestOutN_cost

/-- info: 'LeanVM.E2E.Complete.queryCount_honest_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complete.queryCount_honest_le

/-- info: 'LeanVM.E2E.Complete.queryCount_honest_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complete.queryCount_honest_le_mul

/-- info: 'LeanVM.E2E.Complete.exactRel_idealVerify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complete.exactRel_idealVerify

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complete.idealVerify_complete_rom_budget

/-- info: 'LeanVM.E2E.queryCount_honest_le_viCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms queryCount_honest_le_viCost

/-- info: 'LeanVM.E2E.aggregate_complete_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_complete_final

/-! ## The constants -/

example : Complete.viRootBound = 13508 := Complete.viRootBound_eq
example : Complete.viStepBound = 179719581 := Complete.viStepBound_eq
example : Complete.viNodeBound = 179733089 := Complete.viNodeBound_eq
example : viNodeCost = Complete.viNodeBound := viNodeCost_eq
example : viCost (2 ^ 20) = 2 ^ 20 * 179733089 := rfl

/-- Per node, the stack's tree (`2^27 − 1`), the table check (`checksBound`) and sixteen children's
digests. -/
example : Complete.viStepBound = 2 ^ 27 - 1 + 45501774 + 80 := by
  rw [Complete.viStepBound_eq]
  norm_num

/-- At the root, the IV, the root's digest, V° and sixteen DA claims' vector digests. -/
example : Complete.viRootBound = 2 + 5 + 13213 + 16 * 18 := by
  rw [Complete.viRootBound_eq]

example (H : Bytes → Digest) (bc : List LeanVM.Parameters.K) :
    (fiatShamirIvWith (countQuery H) bc).count = 2 := count_fiatShamirIvWith H bc

example (H : Bytes → Digest) (seed : Digest) (s : LeanVM.Node.NodeStatement) :
    (LeanVM.Node.statementDigestWith (countQuery H) seed s).count = 5 :=
  count_statementDigestWith H seed s

example (H : Bytes → Digest) (root : Digest) :
    (Da.vectorDigestOfWith (countQuery H) root).count = 18 := count_vectorDigestOfWith H root

/-! ## Not vacuous -/

open LeanVM.E2E.Complete in

/-- **The budgeted T6-prob at the honest leanXMSS leaf generator**: rate `1`, `2^25` nonces, V_I on
one node with the budget `viCost 1`, error at most `2^-124`. -/
example {nx ns : ℕ} :
    Pr{let z ← Complete.completeRunGame (nx := nx) (ns := ns) 1 (2 ^ 25) xmssLeafGen 1 (viCost 1)}[
      z.1 = some false] ≤ (2 : ℝ≥0∞)⁻¹ ^ 124 :=
  (aggregate_complete_final Complete.hyps_wTree.1 (by norm_num) Complete.xmssLeafGen
    Complete.isTotalQueryBound_xmssLeafGen (Complete.validGen_xmssLeafGen 1 (2 ^ 25))).trans
    (Complete.completeError_le Complete.xmssLeaf_queries_le)

end LeanVMTests.E2E.ViBudget
