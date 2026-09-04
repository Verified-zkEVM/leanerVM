/-
  LeanerVMTests.Parameters.Field

  Differential vectors and non-vacuity guards for the leanVM base field.
-/

module

public meta import LeanerVM
public import LeanerVM

/-!
# Base-field tests

Reference vectors transcribed from the pinned leanVM Rust, plus guards that the
definitions are not degenerate.

Source revision: leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`.
-/

namespace LeanerVMTests.Parameters.Field

open LeanerVM.Parameters.Field

public meta section

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

/-! ## Extension-field vectors

Transcribed from `crates/primitives/src/field/gf2_64x3.rs` lines 990-1016 (the `VECTORS`
array of `(a, b, a * b, a^2)` quadruples) and line 1026 (the modulus check).

These use `#guard`, which runs the *compiled* arithmetic at elaboration time, following
`CompPolyTests.Fields.Extension`. That is deliberate: it checks the operations actually
evaluate, so a noncomputable instance would fail the build rather than pass silently.
-/

section Vectors

open CompPoly.Extension

private def limbs (c0 c1 c2 : Base) : Extension :=
  Ext.ofFn (fun i => if (i : ℕ) = 0 then c0 else if (i : ℕ) = 1 then c1 else c2)

/-- The adjoined root `y`. -/
private def y : Extension := limbs 0 1 0

-- The defining relation `y^3 = y + 1` (`gf2_64x3.rs:1026`).
#guard y * y * y == y + 1

-- First reference vector: product and square (`gf2_64x3.rs:990-1016`).
#guard limbs 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923
         * limbs 0x6dbca290a9eab706 0x4c10a4fe30cffdda 0xf26fff4cc4fd394d
       == limbs 0x888a0fc35abaf5f6 0x68a84cbc132b0649 0x9fdeaf613003cabe

#guard limbs 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923
         * limbs 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923
       == limbs 0x8fba131ad5d46b8c 0x1c170457f537a805 0x3632cc098ca15135

-- Second reference vector.
#guard limbs 0x6814a2bc786a6d2d 0xa26b351e6c8042c5 0x54760e7fbc051c6c
         * limbs 0xd4c08880a5a4666d 0x29610ae0eed8f1e7 0xc34bd8e2fe5213e5
       == limbs 0x2ad322ebf2f9043b 0x8ac800aa67154c80 0x6d0f76651d3c4d0c

-- Inversion evaluates in both fields.
#guard (0x01090913877ed8ed : Base) * (0x01090913877ed8ed : Base)⁻¹ == 1
#guard (0 : Base)⁻¹ == 0
#guard y * y⁻¹ == 1

end Vectors

end
end LeanerVMTests.Parameters.Field
