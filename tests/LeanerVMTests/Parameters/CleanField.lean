import LeanerVM.Parameters.Field
import Clean.Utils.BinaryField

/-!
# Layer 0 tests: Clean's field interface, and what a plain file can decide

A classic test for kernel evaluation. Guards on Clean's `FiniteField BF64` instance at `K`, whose
`val` is the word's value and `fromNat` is `K.ofBits`; the check that its field structure, and
instance search for `Field K`, are CompPoly's now that Clean's `FiniteField.toField` is in scope;
and kernel checks of `E` arithmetic that only a plain file can run (roadmap status finding P1).
-/

namespace LeanerVMTests.Parameters

open LeanerVM.Parameters

/-! ## Clean's interface -/

#guard FiniteField.val (K.ofBits 0x2a : K) = 42
#guard (FiniteField.fromNat 42 : K) = K.ofBits 0x2a

/-- The size Clean sees is `2^64`. -/
example : FiniteField.size K = 2 ^ 64 := rfl

/-- `fromNat` is the wire decoding `K.ofBits`. -/
example : (FiniteField.fromNat : ℕ → K) = K.ofBits := rfl

/-- The interface introduces no second field structure: its `Field K` is CompPoly's. -/
example : (instFiniteFieldBF64.toField : Field K) = BF64.instField := rfl

/-- With Clean's `FiniteField.toField` in scope, instance search still finds CompPoly's field. -/
example : (inferInstance : Field K) = BF64.instField := rfl

/-- `fromNat` inverts `val`, through the interface's own lemma. -/
example (x : K) : FiniteField.fromNat (FiniteField.val x) = x := FiniteField.fromNat_val x

/-! ## Kernel reduction in a plain file -/

/-- `y^3 = y + 1` computes in the kernel to the word with limbs `(1, 1, 0)`; in a `module` the
same `decide` is stuck on CompPoly's `Ext.ofFn` (finding P1). -/
example : y ^ 3 = E.ofLimbs 1 1 0 := by decide +kernel

/-- The predicates decide on words built through `ofK` and `y`. -/
example : IsInK (ofK (K.ofBits 5)) ∧ ¬ IsInK y ∧ IsCanonical128 y ∧ ¬ IsCanonical128 (y ^ 2) := by
  decide +kernel

end LeanerVMTests.Parameters
