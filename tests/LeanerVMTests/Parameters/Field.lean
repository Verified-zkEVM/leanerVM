/-
  LeanerVMTests.Parameters.Field

  Differential vectors and non-vacuity guards for the leanVM base field.
-/

module

public import LeanerVM

/-!
# Base-field tests

Reference vectors transcribed from the pinned leanVM Rust, plus guards that the
definitions are not degenerate.

Source revision: leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`.
-/

namespace LeanerVMTests.Parameters.Field

open LeanerVM.Parameters.Field

public section

/-! ## Differential vectors

Transcribed verbatim from `crates/primitives/src/field/gf2_64.rs` lines 271-275, the
`VECTORS` array of `(a, b, a * b)` triples.
-/

/-- The pinned Rust's base-field multiplication vectors. -/
def multiplicationVectors : List (BitVec 64 × BitVec 64 × BitVec 64) :=
  [(0x01090913877ed8ed, 0x66ab35ac2768468f, 0x50c4519dc383744a),
   (0xa7715ae18f12a3b5, 0x05743059f43fa4f5, 0xeb64cd9cd9cda6df),
   (0xbd3efb4705e79ddd, 0x3aff618604de4ae0, 0xc3d7a95fa9cb59bb)]

/-- The Lean multiplication agrees with the pinned Rust on every reference vector.

This also pins computability: the kernel has to evaluate the carry-less product and the
reduction to check it. -/
theorem multiplication_matches_reference :
    multiplicationVectors.all
      (fun v => reduce (carryLessMul (w := 128) v.1 v.2.1) == v.2.2) = true := by
  decide +kernel

/-! ## Non-vacuity guards -/

/-- The generator is not zero. -/
theorem generator_ne_zero : (0x2 : Base) ≠ 0 := by decide +kernel

/-- The generator is not one, so it is not a degenerate choice. -/
theorem generator_ne_one : (0x2 : Base) ≠ 1 := by decide +kernel

/-- Multiplication by one is the identity on a sample element, so `reduce` is not
collapsing everything to a constant. -/
theorem one_mul_sample : ((1 : Base) * 0x01090913877ed8ed : Base) = 0x01090913877ed8ed := by
  rw [Base.mul_def]; decide +kernel

/-- A product that genuinely wraps: the reduction is exercised, not bypassed. -/
theorem reduction_is_exercised :
    ((0x8000000000000000 : Base) * 0x2 : Base) = 0x1B := by
  rw [Base.mul_def]; decide +kernel

end
end LeanerVMTests.Parameters.Field
