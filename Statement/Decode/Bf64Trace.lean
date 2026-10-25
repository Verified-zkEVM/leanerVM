module

public import Statement.Decode.Words
public import CompPoly.Univariate.Roots.Shoup.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The trace facts of `K = GF(2^64)` (theorems only)

The two field-theoretic obligations of CompPoly's `SmallPrimeTraceContext` at `p = 2`, `k = 64`,
over `K = BF64` with the basis `x^i = K.ofBits (2^i)`, `i < 64`, and the trace
`Tr(z) = Σ_{i<64} z^(2^i)` (CompPoly's `tracePowerSum 2 64`):

* `tracePowerSum_mem_base`: `Tr(z) ∈ {0, 1}`, since `Tr(z)^2 = Tr(z) − z + z^(2^64) = Tr(z)`;
* `tracePowerSum_separates`: for `a ≠ b` some basis element `β` has `Tr(β·(a − b)) ≠ 0`. With
  `c = a − b ≠ 0`, the map `β ↦ Tr(β·c)` is additive. Were it zero on the basis, it would be zero
  on every element (each is a sum of basis elements, `ofBits_eq_sum`), so `Tr` would vanish on all
  of `K`; but `Σ_{i<64} X^(2^i)` is a nonzero polynomial of degree at most `2^63` and cannot have
  `2^64` roots.

Every declaration here is a theorem: the two facts are proof fields of the extractor's trace
context (`traceCtx`, `Statement/Extractor.lean`), and nothing here can change what the extractor
computes, so this file needs no review.

Credits: the obligations are those of `SmallPrimeTraceContext` and `tracePowerSum`
(`CompPoly/Univariate/Roots/Shoup/Basic.lean`, Valerii Huhnin), and `K` is `BF64`
(`CompPoly/Fields/Binary/BF64/Impl.lean`, Nicolas Schleicher), both from CompPoly
(github.com/Verified-zkEVM/CompPoly) at `572f997390aa4fc131ef30b1186fa1dcf292ca10`, Apache-2.0.
-/

namespace LeanVM.Extraction.Bf64Trace

open LeanVM.Parameters LeanVM.Extraction.Words Polynomial
open CompPoly.CPolynomial.Roots.FiniteField

public section

/-- Frobenius fixes `K`: `a^(2^64) = a`. -/
theorem pow_two_pow_64 (a : K) : a ^ 2 ^ 64 = a := by
  let _ : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card a
  rwa [BF64.card_bf64] at h

/-- The trace as a sum. -/
theorem trace_eq_sum (z : K) : tracePowerSum 2 64 z = ∑ i ∈ Finset.range 64, z ^ 2 ^ i :=
  tracePowerSum_eq_sum_range 2 64 z

/-- The trace is additive. -/
theorem trace_add (a b : K) :
    tracePowerSum 2 64 (a + b) = tracePowerSum 2 64 a + tracePowerSum 2 64 b := by
  simp only [trace_eq_sum, add_pow_char_pow, Finset.sum_add_distrib]

/-- The trace of a finite sum. -/
theorem trace_sum {ι : Type*} (s : Finset ι) (f : ι → K) :
    tracePowerSum 2 64 (∑ i ∈ s, f i) = ∑ i ∈ s, tracePowerSum 2 64 (f i) :=
  map_sum (AddMonoidHom.mk' (tracePowerSum 2 64) trace_add) f s

/-- `Tr(z)^2 = Tr(z)`. -/
theorem trace_sq (z : K) : tracePowerSum 2 64 z ^ 2 = tracePowerSum 2 64 z := by
  rw [trace_eq_sum, sum_pow_char]
  have hshift : ∑ i ∈ Finset.range 64, (z ^ 2 ^ i) ^ 2 = ∑ i ∈ Finset.range 64, z ^ 2 ^ (i + 1) :=
    Finset.sum_congr rfl fun i _ ↦ by rw [← pow_mul, pow_succ]
  rw [hshift]
  have h := Finset.sum_range_succ' (fun i ↦ z ^ 2 ^ i) 64
  rw [Finset.sum_range_succ, pow_two_pow_64, pow_zero, pow_one] at h
  exact add_right_cancel h.symm

/-- **The trace lies in the base field** `{0, 1}`. -/
theorem tracePowerSum_mem_base (z : K) : tracePowerSum 2 64 z ∈ (#[0, 1] : Array K).toList := by
  have h := trace_sq z
  have h' : tracePowerSum 2 64 z * (tracePowerSum 2 64 z - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_two, h, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h1
  · simp [h0]
  · simp [sub_eq_zero.mp h1]

/-- The trace polynomial `Σ_{i<64} X^(2^i)` evaluates to the trace. -/
theorem eval_tracePoly (z : K) :
    (∑ i ∈ Finset.range 64, (X : K[X]) ^ 2 ^ i).eval z = tracePowerSum 2 64 z := by
  simp [eval_finsetSum, trace_eq_sum]

/-- The trace polynomial is not zero: its coefficient of `X` is `1`. -/
theorem tracePoly_ne_zero : (∑ i ∈ Finset.range 64, (X : K[X]) ^ 2 ^ i) ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : K[X] ↦ p.coeff 1) h
  simp only [finsetSum_coeff, coeff_X_pow, coeff_zero] at h1
  rw [Finset.sum_range_succ'] at h1
  have hrest : ∑ i ∈ Finset.range 63, (if 1 = 2 ^ (i + 1) then (1 : K) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by
      rw [ite_eq_right_iff]
      intro h1
      have : 2 ≤ 2 ^ (i + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rw [hrest] at h1
  simp at h1

/-- The trace polynomial has degree at most `2^63`. -/
theorem natDegree_tracePoly_le :
    (∑ i ∈ Finset.range 64, (X : K[X]) ^ 2 ^ i).natDegree ≤ 2 ^ 63 := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  rw [natDegree_X_pow]
  exact Nat.pow_le_pow_right (by norm_num) (by simpa [Nat.lt_succ_iff] using hi)

/-- The trace is not identically zero. -/
theorem exists_trace_ne_zero : ∃ z : K, tracePowerSum 2 64 z ≠ 0 := by
  by_contra! h
  let _ : Fintype K := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K).val ⊆
      (∑ i ∈ Finset.range 64, (X : K[X]) ^ 2 ^ i).roots := by
    intro z _
    rw [mem_roots tracePoly_ne_zero, IsRoot, eval_tracePoly, h z]
  have hcard := card_le_degree_of_subset_roots hsub
  rw [Finset.card_univ, BF64.card_bf64] at hcard
  have := hcard.trans natDegree_tracePoly_le
  norm_num at this

/-- **The trace separates** distinct elements on the basis `x^i`. -/
theorem tracePowerSum_separates {a b : K} (hab : a ≠ b) :
    ∃ beta, beta ∈ (Array.ofFn fun i : Fin 64 ↦ K.ofBits (2 ^ i.val)).toList ∧
      tracePowerSum 2 64 (beta * (a - b)) ≠ 0 := by
  have hc : a - b ≠ 0 := sub_ne_zero.mpr hab
  by_contra! h
  have hbasis : ∀ c < 64, tracePowerSum 2 64 (K.ofBits (2 ^ c) * (a - b)) = 0 := by
    intro c hc64
    refine h _ ?_
    rw [Array.mem_toList_iff, Array.mem_ofFn]
    exact ⟨⟨c, hc64⟩, Eq.refl (K.ofBits (2 ^ c))⟩
  have hall : ∀ y : K, tracePowerSum 2 64 (y * (a - b)) = 0 := by
    intro y
    rw [← ofBits_toNat y, ofBits_eq_sum (toNat_lt y), Finset.sum_mul, trace_sum]
    refine Finset.sum_eq_zero fun c hc64 ↦ ?_
    split
    · exact hbasis c (Finset.mem_range.mp hc64)
    · simp [trace_eq_sum]
  obtain ⟨z, hz⟩ := exists_trace_ne_zero
  apply hz
  have := hall (z * (a - b)⁻¹)
  rw [inv_mul_cancel_right₀ hc] at this
  exact this

end
end LeanVM.Extraction.Bf64Trace
