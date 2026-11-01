module

public import LeanVM.Cost.Library
public import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Data.Array.Lemmas
import all Init.Data.Array.Basic

/-!
# CompPoly, for the compiler

CompPoly (github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly
Contributors") is compiled, not copied. Here: the encoding of its shifted leading terms, and three
equations through which the compiler compiles its definitions (each a definition of CompPoly
restated in a form the compiler handles: no `Fin`-indexed recursion, no `Array.ofFn`):

* `beqZero`: `p == 0` is `p`'s size being `0`;
* `trim_eq`: trimming is extracting the prefix up to the last nonzero coefficient, found by a
  recursion on ℕ (`trimLen`);
* `subMulMonomial_eq`: the fused `a - c·X^d·b` through `List.range`.
-/

namespace LeanVM.Cost.CompPolyLib

open LeanVM.Cost CompPoly

@[expose] public section

instance {F : Type} [Enc F] : Enc (PolynomialMatrix.ShiftedLeadingTerm F) :=
  ⟨fun t ↦ .ctor 0 [enc t.position, enc t.degree, enc t.shiftedDegree, enc t.coeff]⟩

theorem beqZero {R : Type} [Zero R] [BEq R] (p : CPolynomial R) :
    (p == 0) = decide (p.val.size = 0) := by
  obtain ⟨⟨l⟩, h⟩ := p
  show (Array.mk l == #[]) = _
  cases l <;> simp [BEq.beq, Array.isEqv, Array.isEqvAux]

cost_rewrite beqZero

/-- The length of `p`'s prefix up to its last nonzero coefficient among the first `i`. -/
def trimLen {R : Type} [Zero R] [BEq R] (p : Array R) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if p.getD i 0 != 0 then i + 1 else trimLen p i

theorem find_trimLen {R : Type} [Zero R] [BEq R] (p : CPolynomial.Raw R) :
    ∀ i : Fin (p.size + 1),
      ((Array.findIdxRev?.find (· != 0) p i).map (·.val + 1)).getD 0 = trimLen p i.val := by
  intro i
  induction i using Array.findIdxRev?.find.induct (· != 0) p with
  | case1 =>
    unfold Array.findIdxRev?.find
    simp [trimLen]
  | case2 i h hc =>
    rw [Array.findIdxRev?.find]
    simp [hc, trimLen, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (Nat.lt_of_succ_lt_succ h)]
  | case3 i h hc ih =>
    rw [Array.findIdxRev?.find]
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at ih ⊢
    rw [ih]
    simp [trimLen, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (Nat.lt_of_succ_lt_succ h),
      hc]

theorem trim_eq {R : Type} [Zero R] [BEq R] (p : CPolynomial.Raw R) :
    p.trim = p.extract 0 (trimLen p p.size) := by
  have h := find_trimLen p ⟨p.size, Nat.lt_succ_self _⟩
  simp only [CPolynomial.Raw.trim, CPolynomial.Raw.lastNonzero, Array.findIdxRev?] at h ⊢
  cases hf : Array.findIdxRev?.find (· != 0) p ⟨p.size, Nat.lt_succ_self _⟩ with
  | none => simp [hf] at h; simp [← h]
  | some i => simp [hf] at h; simp [← h]

cost_rewrite trim_eq

theorem subMulMonomial_eq {R : Type} [Ring R] [BEq R] [LawfulBEq R] (a : CPolynomial R) (c : R)
    (d : ℕ) (b : CPolynomial R) :
    CPolynomial.subMulMonomial a c d b = if (c == 0 || b == 0) then a else
      CPolynomial.ofArray ((List.range (max a.val.size (d + b.val.size))).map fun j ↦
        a.coeff j - if d ≤ j then c * b.coeff (j - d) else 0).toArray := by
  simp only [CPolynomial.subMulMonomial]
  split
  · rfl
  · congr 1
    ext j hj hj'
    · simp
    · simp

cost_rewrite subMulMonomial_eq

end

end LeanVM.Cost.CompPolyLib
