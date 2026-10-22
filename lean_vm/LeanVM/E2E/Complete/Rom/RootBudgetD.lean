/-
  LeanVM.E2E.Complete.Rom.RootBudgetD

  T6-prob's two-level inhabitant: the deployed budget's instructions of `XOR` and `MUL`,
  at the work of a node with one child, by kernel evaluation one coefficient at a time.
-/

module

public import LeanVM.E2E.Complete.Rom.RootBudgetC

/-!
# The instructions of `XOR` and `MUL` at `rootWork`

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

/-- Bounds on the budget's instructions of each opcode at the root's work. -/
def rootInstrsBound : Opcode → ℕ
  | .xor => 2 ^ 20
  | .mulNative => 2 ^ 20
  | .setConstant => 2 ^ 20
  | .deref => 2 ^ 20
  | .jump => 2 ^ 20
  | .blake2s => 2 ^ 17

/-! ## `XOR` -/

theorem rootInstrs_xor_base : (b2cBudget'.instrs .xor).base ≤ 2 ^ 13 := by decide +kernel

theorem rootInstrs_xor_declared : (b2cBudget'.instrs .xor).declared ≤ 2 ^ 13 := by decide +kernel

theorem rootInstrs_xor_coverage : (b2cBudget'.instrs .xor).coverage ≤ 2 ^ 13 := by decide +kernel

theorem rootInstrs_xor_children : (b2cBudget'.instrs .xor).children ≤ 2 ^ 17 := by decide +kernel

theorem rootInstrs_xor_childClaims : (b2cBudget'.instrs .xor).childClaims ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_xor : (b2cBudget'.instrs .xor).eval rootWork ≤ 2 ^ 20 := by
  rw [Linear.eval_rootWork]
  have := rootInstrs_xor_base
  have := rootInstrs_xor_declared
  have := rootInstrs_xor_coverage
  have := rootInstrs_xor_children
  have := rootInstrs_xor_childClaims
  omega

/-! ## `MUL` -/

theorem rootInstrs_mulNative_base : (b2cBudget'.instrs .mulNative).base ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_mulNative_declared : (b2cBudget'.instrs .mulNative).declared ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_mulNative_coverage : (b2cBudget'.instrs .mulNative).coverage ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_mulNative_children : (b2cBudget'.instrs .mulNative).children ≤ 2 ^ 18 := by
  decide +kernel

theorem rootInstrs_mulNative_childClaims : (b2cBudget'.instrs .mulNative).childClaims ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_mulNative : (b2cBudget'.instrs .mulNative).eval rootWork ≤ 2 ^ 20 := by
  rw [Linear.eval_rootWork]
  have := rootInstrs_mulNative_base
  have := rootInstrs_mulNative_declared
  have := rootInstrs_mulNative_coverage
  have := rootInstrs_mulNative_children
  have := rootInstrs_mulNative_childClaims
  omega

end
end LeanVM.E2E.Complete
