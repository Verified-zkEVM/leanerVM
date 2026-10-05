import LeanerVM.Semantics.PaddedRows
import LeanerVMTests.Semantics.FillPlan

/-!
# Layer 10 tests: the rows of a padded trace

The plan of a small trace, the rows of the multiplication gadget (`mulRows`: two `SET_CONSTANT`s
and a `MUL_NATIVE`), with the `JUMP` table filled to `2^3`: the heights, the traversal counts and
the per-table sums, run as plain arithmetic, and the counting theorem on the same rows. A traversal
of a block counts its dummies on its own table and the closing jump on the `JUMP` table. Three
mutations: a `JUMP` gap of one, a `JUMP` table below what it owes, and no closing jumps at all each
break the count.
-/

namespace LeanerVMTests.Semantics.PaddedRows

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.FillPlan

/-! ## The rows of a cycle -/

/-- A traversal of the size-sixteen `DEREF` block: sixteen rows of `DEREF` and one of `JUMP`. -/
example (κ : ℕ) (pcs : Opcode → ℕ → ℕ) :
    Skel.count .deref (cycleSkels κ pcs .deref 3) = 16 ∧
      Skel.count .jump (cycleSkels κ pcs .deref 3) = 1 ∧
      Skel.count .xor (cycleSkels κ pcs .deref 3) = 0 := by
  simp [Skel.count_cycleSkels, sizeAt, fillSizes]

/-- A traversal of the `JUMP` table's own size-one block has two `JUMP` rows (a dummy jump that
falls through, and the closing jump), the size-two block three. -/
example (κ : ℕ) (pcs : Opcode → ℕ → ℕ) :
    Skel.count .jump (cycleSkels κ pcs .jump 7) = 2 ∧
      Skel.count .jump (cycleSkels κ pcs .jump 6) = 3 := by
  simp [Skel.count_cycleSkels, sizeAt, fillSizes]

/-! ## The plan of the multiplication gadget -/

-- The heights: `JUMP` owes three rows, and `2^2` is one more, so it is filled to `2^3`.
#guard (fillTables.map (tableHeight mulRows 3)) = [1, 1, 2, 1, 8, 8]

-- The gap of five is one traversal of each of the size-one and the size-two blocks.
#guard jumpMix (2 ^ 3 - jumpOwed mulRows) = (1, 1)
#guard planCount mulRows 3 .jump 7 = 1
#guard planCount mulRows 3 .jump 6 = 1
#guard planCount mulRows 3 .jump 5 = 0

-- `XOR`, `DEREF` and the `BLAKE2S` floor are filled by one traversal each.
#guard planCount mulRows 3 .xor 7 = 1
#guard planCount mulRows 3 .deref 7 = 1
#guard planCount mulRows 3 .blake2s 4 = 1
#guard planCount mulRows 3 .mulNative 7 = 0

/-- The rows of every table once filled: its run rows, the dummies of its traversals, and for
`JUMP` the closing jump of every traversal. -/
def filledRows (τ : ℕ) (op : Opcode) : ℕ :=
  mulRows op + planDummies (planCount mulRows τ) op +
    if op = .jump then (fillTables.map (planTraversals (planCount mulRows τ))).sum else 0

#guard fillTables.map (filledRows 3) = fillTables.map (tableHeight mulRows 3)

/-- The counting theorem on the same rows, with the `JUMP` table filled to `2^6` (which the bound
`jumpOwed_le` shows is feasible, without evaluating the owed rows). -/
example (κ : ℕ) (pcs : Opcode → ℕ → ℕ) (op : Opcode) :
    mulRows op + Skel.count op (padSkels κ pcs (planCount mulRows 6)) =
      tableHeight mulRows 6 op := by
  have h := jumpOwed_le (rows := mulRows) (k := 3) le_rfl (fun op ↦ by cases op <;> simp [mulRows])
  exact plan_rows κ pcs mulRows (by omega) (by omega) op

/-! ## Each condition is load-bearing -/

-- A `JUMP` gap of one: `2^2` is one more than the three rows owed. The size-two block delivers
-- three rows, not one, and the table overshoots to six rows, not four.
#guard filledRows 2 .jump = 6
#guard filledRows 2 .jump ≠ 2 ^ 2

-- Below what it owes: `2^1` is less than three. The gap truncates to zero and the table keeps the
-- three rows it owes, not two.
#guard filledRows 1 .jump = 3
#guard filledRows 1 .jump ≠ 2 ^ 1

-- Without the closing jumps the table would not be filled: only its own dummies (three rows).
#guard planDummies (planCount mulRows 3) .jump = 3
#guard planDummies (planCount mulRows 3) .jump ≠ 2 ^ 3

end LeanerVMTests.Semantics.PaddedRows
