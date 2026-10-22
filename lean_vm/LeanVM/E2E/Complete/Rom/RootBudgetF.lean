/-
  LeanVM.E2E.Complete.Rom.RootBudgetF

  T6-prob's two-level inhabitant: the deployed budget's instructions of `JUMP` and `BLAKE2S`,
  at the work of a node with one child, by kernel evaluation one coefficient at a time.
-/

module

public import LeanVM.E2E.Complete.Rom.RootBudgetE

/-!
# The instructions of `JUMP` and `BLAKE2S` at `rootWork`

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

/-! ## `JUMP` -/

theorem rootInstrs_jump_base : (b2cBudget'.instrs .jump).base ≤ 2 ^ 13 := by decide +kernel

theorem rootInstrs_jump_declared : (b2cBudget'.instrs .jump).declared ≤ 2 ^ 13 := by decide +kernel

theorem rootInstrs_jump_coverage : (b2cBudget'.instrs .jump).coverage ≤ 2 ^ 13 := by decide +kernel

theorem rootInstrs_jump_children : (b2cBudget'.instrs .jump).children ≤ 2 ^ 15 := by decide +kernel

theorem rootInstrs_jump_childClaims : (b2cBudget'.instrs .jump).childClaims ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_jump : (b2cBudget'.instrs .jump).eval rootWork ≤ 2 ^ 20 := by
  rw [Linear.eval_rootWork]
  have := rootInstrs_jump_base
  have := rootInstrs_jump_declared
  have := rootInstrs_jump_coverage
  have := rootInstrs_jump_children
  have := rootInstrs_jump_childClaims
  omega

/-! ## `BLAKE2S` -/

theorem rootInstrs_blake2s_base : (b2cBudget'.instrs .blake2s).base ≤ 2 ^ 13 := by decide +kernel

theorem rootInstrs_blake2s_declared : (b2cBudget'.instrs .blake2s).declared ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_blake2s_coverage : (b2cBudget'.instrs .blake2s).coverage ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_blake2s_children : (b2cBudget'.instrs .blake2s).children ≤ 2 ^ 14 := by
  decide +kernel

theorem rootInstrs_blake2s_childClaims : (b2cBudget'.instrs .blake2s).childClaims ≤ 2 ^ 13 := by
  decide +kernel

theorem rootInstrs_blake2s : (b2cBudget'.instrs .blake2s).eval rootWork ≤ 2 ^ 17 := by
  rw [Linear.eval_rootWork]
  have := rootInstrs_blake2s_base
  have := rootInstrs_blake2s_declared
  have := rootInstrs_blake2s_coverage
  have := rootInstrs_blake2s_children
  have := rootInstrs_blake2s_childClaims
  omega

end
end LeanVM.E2E.Complete
