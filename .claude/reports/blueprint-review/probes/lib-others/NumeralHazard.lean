import LeanerVM.Parameters.Field

/-!
Probe `NumeralHazard`: `K` is an abbreviation of `BitVec 64`, so core's `BitVec` simprocs
fire on terms of `K`, reading the field's `+` (XOR) as addition modulo `2^64`. Does that let
`simp` prove a false statement about `K`? Each `example` below is run separately; the ones
marked EXPECTED TO FAIL must be rejected.
-/

open LeanerVM.Parameters

-- true in `K`: characteristic two
example : (1 : K) + 1 = 0 := by decide

-- EXPECTED TO FAIL: `simp` cannot prove the true statement (it rewrites `1 + 1` to `2#64`)
example : (1 : K) + 1 = 0 := by simp

-- EXPECTED TO FAIL (the soundness probe): the negation is false in `K`; if `simp` closes the
-- goal, the kernel must reject the proof term
theorem bad : ¬ ((1 : K) + 1 = 0) := by simp

-- EXPECTED TO FAIL: the same through a product, `x · x^63 = 0x1B` in `K`, not `0` (the low
-- 64 bits of `2^64`)
theorem bad_mul : (2 : K) * 0x8000000000000000 = 0 := by simp

#print axioms bad
#print axioms bad_mul
