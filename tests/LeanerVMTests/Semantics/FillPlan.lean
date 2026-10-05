import LeanerVM.Semantics.FillPlan

/-!
# Layer 10 tests: the fill plan arithmetic

Concrete values of the targets and the traversals, including the row mix the Rust's own filler
test uses (`crates/lean_vm/src/cpu/filler.rs:228-246` at leanVM `a386121f`), and the `JUMP`
feasibility cases around the row cap. The cap cases show the exclusion of a one-row gap is
load-bearing: a `JUMP` table owing `2^32 - 1` rows has no plan, and one owing `2^31 - 1` does,
by taking the next power of two.
-/

namespace LeanerVMTests.Semantics.FillPlan

open LeanerVM.Parameters LeanerVM.Semantics

/-! ## Targets -/

#guard minRows .blake2s = 8
#guard minRows .xor = 1
#guard minRows .jump = 1

-- A table with no rows is filled to its floor.
#guard fillTarget 0 1 = 1
#guard fillTarget 0 8 = 8

-- A table already on a power of two is not entered.
#guard fillTarget 1 1 = 1
#guard fillTarget 128 1 = 128
#guard fillGreedy (fillTarget 128 1 - 128) = [0, 0, 0, 0, 0, 0, 0, 0]

#guard fillTarget 5 1 = 8
#guard fillTarget 125000 1 = 131072
#guard fillTarget 130000 8 = 131072

/-! ## Traversals -/

#guard fillGreedy 0 = [0, 0, 0, 0, 0, 0, 0, 0]
#guard fillGreedy 255 = [1, 1, 1, 1, 1, 1, 1, 1]
#guard fillGreedy 1000 = [7, 1, 1, 0, 1, 0, 0, 0]
#guard fillTraversals 1000 = 10

-- The `XOR` table of the Rust test's mix, `125000` rows, is filled by `6072` rows: forty-seven
-- traversals of the largest block and one each of the sizes `32`, `16` and `8`.
#guard fillGreedy (fillTarget 125000 1 - 125000) = [47, 0, 1, 1, 1, 0, 0, 0]
#guard fillTraversals (fillTarget 125000 1 - 125000) = 50

/-- The bulk rides the largest block: the same bound the Rust asserts. -/
example : fillTraversals 6072 ≤ 6072 / 128 + 7 := fillTraversals_le 6072

-- The traversals add up to the fill, and the table reaches its target.
#guard (List.zipWith (· * ·) (fillGreedy 6072) fillSizes).sum = 6072
example : 125000 + (List.zipWith (· * ·) (fillGreedy (fillTarget 125000 1 - 125000))
    fillSizes).sum = fillTarget 125000 1 := fill_rows_sum 125000 1

/-! ## The rows the `JUMP` table owes -/

/-- The rows of the executor's `mul_192bit_word` per table: two `SET_CONSTANT`s and a
`MUL_NATIVE`. -/
def mulRows : Opcode → ℕ
  | .setConstant => 2
  | .mulNative => 1
  | _ => 0

-- `XOR`, `DEREF` and `BLAKE2S` are filled by one traversal each (a size-one block, a size-one
-- block, a size-eight block), so the `JUMP` table owes three closing jumps.
#guard jumpOwed mulRows = 3

example : JumpFeasible (jumpOwed mulRows) :=
  jumpFeasible_of_le ((jumpOwed_le (k := 3) le_rfl (fun op ↦ by cases op <;> simp [mulRows])).trans
    (by norm_num))

/-! ## Bounds -/

example : fillTarget 0 8 = 2 ^ 3 := fillTarget_eq (by norm_num)

example : fillTarget 125000 1 ≤ 2 ^ 17 := fillTarget_le (by norm_num) (by norm_num)

/-! ## The `JUMP` table -/

/-- A gap of one row is not a sum of twos and threes: no traversal delivers it. -/
theorem no_gap_of_one : ¬ ∃ a b : ℕ, 1 = 2 * a + 3 * b := by
  rintro ⟨a, b, h⟩
  omega

/-- Every other gap is. -/
example : ∃ a b : ℕ, 7 = 2 * a + 3 * b := jump_gap_decomp 7 (by norm_num)

-- The mix delivers every gap but one: all twos when even, one three when odd.
#guard jumpMix 0 = (0, 0)
#guard jumpMix 2 = (1, 0)
#guard jumpMix 3 = (0, 1)
#guard jumpMix 7 = (2, 1)
#guard jumpMix 10 = (5, 0)

-- A gap of one is the exception: the mix would deliver three rows, not one.
#guard 2 * (jumpMix 1).1 + 3 * (jumpMix 1).2 ≠ 1

/-- The mix delivers the gap, at the sizes the tests use. -/
example : 2 * (jumpMix 7).1 + 3 * (jumpMix 7).2 = 7 := jumpMix_spec (by norm_num)

/-- Owing nothing, the `JUMP` table is filled to two rows, not one: a gap of one is not
deliverable, and a table needs at least one row. -/
example : JumpFeasible 0 := ⟨1, by decide, by decide, by decide⟩

example : JumpFeasible 1 := ⟨0, by decide, by decide, by decide⟩

/-- Owing exactly the cap is fine. -/
example : JumpFeasible (2 ^ 32) := ⟨32, by decide, le_rfl, by norm_num⟩

/-- Owing one row short of a power of two means taking the next one. -/
example : JumpFeasible (2 ^ 31 - 1) := ⟨32, by decide, by norm_num, by norm_num⟩

/-- Owing one row short of the cap has no plan: the next power of two is past the cap. -/
theorem no_plan_one_below_cap : ¬ JumpFeasible (2 ^ 32 - 1) := by
  rintro ⟨τ, hτ, h1, h2⟩
  by_cases h : τ = 32
  · subst h
    exact h2 (by norm_num)
  · have h31 : τ ≤ 31 := by
      have : τ ≤ 32 := hτ
      omega
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h31
    omega

/-- Owing more than the cap has no plan either. -/
theorem no_plan_above_cap : ¬ JumpFeasible (2 ^ 32 + 1) := by
  rintro ⟨τ, hτ, h1, -⟩
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show τ ≤ 32 from hτ)
  omega

end LeanerVMTests.Semantics.FillPlan
