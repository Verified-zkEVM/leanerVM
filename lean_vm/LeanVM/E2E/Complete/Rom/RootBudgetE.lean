/-
  LeanVM.E2E.Complete.Rom.RootBudgetE

  T6-prob's two-level inhabitant: the deployed budget's instructions of `SET` and `DEREF`,
  at the work of a node with one child, by kernel evaluation one coefficient at a time.
-/

module

public import LeanVM.E2E.Complete.Rom.RootBudgetD

/-!
# The instructions of `SET` and `DEREF` at `rootWork`

The six opcodes' evaluations are split over `RootBudgetD.lean`, `RootBudgetE.lean` and
`RootBudgetF.lean`, two each. At `rootWork` an opcode's bound is the sum of five coefficients
(`Linear.eval_rootWork`); each is evaluated alone, so that the kernel never evaluates the four
weighted by `0` (a whole `eval` would, at about 17 GB), and a module's peak stays below 10 GB. The
budget modules import one another in a chain (`A` → … → `F`), so that no two of them build at once.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B2C

@[expose] public section

/-! ## `SET` -/

theorem rootInstrs_setConstant_base : (b2cBudget'.instrs .setConstant).base ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_setConstant_declared : (b2cBudget'.instrs .setConstant).declared ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_setConstant_coverage : (b2cBudget'.instrs .setConstant).coverage ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_setConstant_children : (b2cBudget'.instrs .setConstant).children ≤ 2 ^ 16 := by
  decide +kernel

theorem rootInstrs_setConstant_childClaims :
    (b2cBudget'.instrs .setConstant).childClaims ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_setConstant : (b2cBudget'.instrs .setConstant).eval rootWork ≤ 2 ^ 20 := by
  rw [Linear.eval_rootWork]
  have := rootInstrs_setConstant_base
  have := rootInstrs_setConstant_declared
  have := rootInstrs_setConstant_coverage
  have := rootInstrs_setConstant_children
  have := rootInstrs_setConstant_childClaims
  omega

/-! ## `DEREF` -/

theorem rootInstrs_deref_base : (b2cBudget'.instrs .deref).base ≤ 2 ^ 13 := by decide +kernel

theorem rootInstrs_deref_declared : (b2cBudget'.instrs .deref).declared ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_deref_coverage : (b2cBudget'.instrs .deref).coverage ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_deref_children : (b2cBudget'.instrs .deref).children ≤ 2 ^ 17 := by
  decide +kernel

theorem rootInstrs_deref_childClaims : (b2cBudget'.instrs .deref).childClaims ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_deref : (b2cBudget'.instrs .deref).eval rootWork ≤ 2 ^ 20 := by
  rw [Linear.eval_rootWork]
  have := rootInstrs_deref_base
  have := rootInstrs_deref_declared
  have := rootInstrs_deref_coverage
  have := rootInstrs_deref_children
  have := rootInstrs_deref_childClaims
  omega

end
end LeanVM.E2E.Complete
