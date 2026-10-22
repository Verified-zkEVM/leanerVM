/-
  LeanerVM.Parameters.ToCompPoly.ExtensionFast

  Faster compiled arithmetic for CompPoly's field extensions: Karatsuba multiplication and
  Cramer's-rule inversion in degree three, and powers over them, with the instances registered
  for compilation. Candidate for CompPoly.
-/

module

public import CompPoly.Fields.Extension
import Mathlib.Algebra.Ring.Ext
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# Fast extension-field arithmetic

CompPoly's `Ext P` multiplies by `mulTbl`, which rebuilds the reduction table `red P` on every
product unless the call is specialised at a constant `P`, and performs `d^2 + (2d - 1)·d`
coefficient products. In degree three, `mulDeg3` performs six (Karatsuba) and folds `X^4` and
`X^3` by the modulus with six more, products by the modulus's lower coefficients. `mulDeg3_eq`
proves it equal to the product over every ring, commutative or not. Over a field, `invDeg3`
inverts by Cramer's rule on the matrix of multiplication (`mulMatrix`): eighteen coefficient
products and one coefficient inverse, where `x ^ (q^d - 2)` takes about `2·d·log q` products of
the extension (`invDeg3_eq`).

As for `BF64` in `LeanerVM.Parameters.ToCompPoly.BF64Fast`, the `@[csimp]` theorems replace the
instance constants a compiled call site names: `Ext.instMul`, `Ext.instPowNat`, `Ext.instInv`,
`Ext.instDiv`, `Ext.instCommRing` and `Ext.instField`. Their multiplication is `mulFast`
(`mulDeg3` when `P.d = 3`, the existing product otherwise) and their powers are binary
exponentiation over it. The field's inverse is `fieldInv` (`invDeg3` in degree three) and its
integer powers are `zpowFast`; its rational casts and scalar products stay those of
`Ext.instField`. The
ring-level `Ext.instInv`, which a monomorphic `x⁻¹` names, has only a ring to work with and keeps
`x ^ (q^d - 2)`, over `mulFast`. A compiled call site cannot see the coefficient field or the
modulus, so every substitution is generic: the coefficient operations stay those of the
dictionary the call site passes.

Upstream, CompPoly would carry `mulDeg3`, `invDeg3` and their proofs, and attach them to `Ext.mul`
and `Ext.instField` where those are defined, after which the instance-level theorems here are
unnecessary.
-/

namespace LeanerVM.Parameters.FastExt

open CompPoly.Extension Ext

universe u

variable {F : Type u}

@[expose] public section

/-- The product in a degree-three extension: the five coefficients of the product of the two
coefficient vectors by Karatsuba's six products, then `X^4` and `X^3` folded down by the
modulus `X^3 = -(l₀ + l₁·X + l₂·X²)`. -/
@[inline] def mulDeg3 [Ring F] {P : ExtensionParams F} (h : P.d = 3) (x y : Ext P) : Ext P :=
  let a0 := x.coeffs[0]'(by omega)
  let a1 := x.coeffs[1]'(by omega)
  let a2 := x.coeffs[2]'(by omega)
  let b0 := y.coeffs[0]'(by omega)
  let b1 := y.coeffs[1]'(by omega)
  let b2 := y.coeffs[2]'(by omega)
  let l0 := P.lower[0]'(by omega)
  let l1 := P.lower[1]'(by omega)
  let l2 := P.lower[2]'(by omega)
  let p00 := a0 * b0
  let p11 := a1 * b1
  let p22 := a2 * b2
  let c1 := (a0 + a1) * (b0 + b1) - p00 - p11
  let c2 := (a0 + a2) * (b0 + b2) - p00 - p22 + p11
  let c3 := (a1 + a2) * (b1 + b2) - p11 - p22
  let c3' := c3 - p22 * l2
  ofVector ⟨#[p00 - c3' * l0, c1 - p22 * l0 - c3' * l1, c2 - p22 * l1 - c3' * l2],
    by simp [h]⟩

/-- The degree-three product is the product, over every ring. -/
theorem mulDeg3_eq [Ring F] {P : ExtensionParams F} (h : P.d = 3) (x y : Ext P) :
    mulDeg3 h x y = x * y := by
  obtain ⟨d, two_le, lower, q⟩ := P
  simp only at h
  subst h
  apply Ext.ext; intro m
  rw [coeff_mul]
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, monomialMod,
    Function.iterate_succ_apply', Function.iterate_zero, id, coeff_shiftReduce, coeff_one,
    coeffNat, Nat.reduceAdd]
  fin_cases m <;> simp [mulDeg3, coeff, ofVector, ExtensionParams.lowerCoeff] <;> noncomm_ring

/-- Multiplication: Karatsuba in degree three, the reduction table otherwise. -/
def mulFast [Ring F] {P : ExtensionParams F} (x y : Ext P) : Ext P :=
  if h : P.d = 3 then mulDeg3 h x y else x * y

/-- `mulFast` is the product. -/
theorem mulFast_eq [Ring F] {P : ExtensionParams F} (x y : Ext P) : mulFast x y = x * y := by
  unfold mulFast; split_ifs with h
  · exact mulDeg3_eq h x y
  · rfl

/-- Multiplication through `mulFast`. -/
@[instance_reducible] def instMulFast [Ring F] {P : ExtensionParams F} : Mul (Ext P) := ⟨mulFast⟩

/-- `instMulFast` is `Ext.instMul`. -/
theorem instMulFast_eq [Ring F] {P : ExtensionParams F} :
    (instMulFast : Mul (Ext P)) = instMul := by
  show (⟨mulFast⟩ : Mul (Ext P)) = ⟨mul⟩
  congr 1; funext x y; exact mulFast_eq x y

/-- Compiled code multiplies through `instMulFast`. -/
@[csimp] theorem instMul_eq_instMulFast : @Ext.instMul.{u} = @instMulFast.{u} := by
  funext F _ P; exact instMulFast_eq.symm

/-- Natural powers by binary exponentiation over `mulFast`. -/
def powFast [Ring F] {P : ExtensionParams F} (x : Ext P) (n : ℕ) : Ext P :=
  @npowBinRec (Ext P) _ instMulFast n x

/-- `powFast` is the natural power. -/
theorem powFast_eq [Ring F] {P : ExtensionParams F} (x : Ext P) (n : ℕ) : powFast x n = x ^ n := by
  rw [powFast, instMulFast_eq]; rfl

/-- Natural powers through `powFast`. -/
@[instance_reducible] def instPowNatFast [Ring F] {P : ExtensionParams F} : Pow (Ext P) ℕ :=
  ⟨powFast⟩

/-- Compiled code takes powers through `instPowNatFast`. -/
@[csimp] theorem instPowNat_eq_instPowNatFast : @Ext.instPowNat.{u} = @instPowNatFast.{u} := by
  funext F _ P
  show (⟨fun x n ↦ npowBinRec n x⟩ : Pow (Ext P) ℕ) = ⟨powFast⟩
  congr 1; funext x n; exact (powFast_eq x n).symm

/-- The inverse candidate `x ^ (q^d - 2)` through `powFast`. -/
def invFast [Ring F] {P : ExtensionParams F} (x : Ext P) : Ext P := powFast x (P.q ^ P.d - 2)

/-- `invFast` is the inverse candidate. -/
theorem invFast_eq [Ring F] {P : ExtensionParams F} (x : Ext P) : invFast x = inv x := by
  rw [invFast, powFast_eq]; rfl

/-- The inverse candidate through `invFast`. -/
@[instance_reducible] def instInvFast [Ring F] {P : ExtensionParams F} : Inv (Ext P) := ⟨invFast⟩

/-- Compiled code takes the inverse candidate through `instInvFast`. -/
@[csimp] theorem instInv_eq_instInvFast : @Ext.instInv.{u} = @instInvFast.{u} := by
  funext F _ P
  show (⟨inv⟩ : Inv (Ext P)) = ⟨invFast⟩
  congr 1; funext x; exact (invFast_eq x).symm

/-- Division through `mulFast` and `invFast`. -/
@[instance_reducible] def instDivFast [Ring F] {P : ExtensionParams F} : Div (Ext P) :=
  ⟨fun x y ↦ mulFast x (invFast y)⟩

/-- Compiled code divides through `instDivFast`. -/
@[csimp] theorem instDiv_eq_instDivFast : @Ext.instDiv.{u} = @instDivFast.{u} := by
  funext F _ P
  show (⟨fun x y ↦ x * inv y⟩ : Div (Ext P)) = ⟨fun x y ↦ mulFast x (invFast y)⟩
  congr 1; funext x y; rw [mulFast_eq, invFast_eq]

/-- The commutative ring with `mulFast` and `powFast`. -/
@[instance_reducible] def commRingFast [Field F] {P : ExtensionParams F} : CommRing (Ext P) :=
  { instCommRing with
    mul := mulFast
    npow := fun n x ↦ powFast x n
    mul_assoc := fun a b c ↦ by
      show mulFast (mulFast a b) c = mulFast a (mulFast b c)
      simp only [mulFast_eq]; exact mul_assoc a b c
    one_mul := fun a ↦ by show mulFast 1 a = a; rw [mulFast_eq, one_mul]
    mul_one := fun a ↦ by show mulFast a 1 = a; rw [mulFast_eq, mul_one]
    npow_zero := fun a ↦ by show powFast a 0 = 1; rw [powFast_eq, pow_zero]
    npow_succ := fun n a ↦ by
      show powFast a (n + 1) = mulFast (powFast a n) a
      rw [powFast_eq, powFast_eq, mulFast_eq, pow_succ]
    zero_mul := fun a ↦ by show mulFast 0 a = 0; rw [mulFast_eq, zero_mul]
    mul_zero := fun a ↦ by show mulFast a 0 = 0; rw [mulFast_eq, mul_zero]
    left_distrib := fun a b c ↦ by
      show mulFast a (b + c) = mulFast a b + mulFast a c
      simp only [mulFast_eq]; exact mul_add a b c
    right_distrib := fun a b c ↦ by
      show mulFast (a + b) c = mulFast a c + mulFast b c
      simp only [mulFast_eq]; exact add_mul a b c
    mul_comm := fun a b ↦ by
      show mulFast a b = mulFast b a
      simp only [mulFast_eq]; exact mul_comm a b }

/-- Compiled code passes `commRingFast` for an extension's ring. -/
@[csimp] theorem instCommRing_eq_commRingFast : @Ext.instCommRing.{u} = @commRingFast.{u} := by
  funext F _ P
  exact CommRing.ext rfl (funext₂ fun a b ↦ (mulFast_eq a b).symm)

section Inverse

variable [Field F] {P : ExtensionParams F}

/-- The matrix of multiplication by `x` in the basis `1, X, X²` of a degree-three extension:
column `j` holds the coefficients of `x · X^j`. -/
def mulMatrix (h : P.d = 3) (x : Ext P) : Matrix (Fin 3) (Fin 3) F :=
  let a0 := x.coeffs[0]'(by omega)
  let a1 := x.coeffs[1]'(by omega)
  let a2 := x.coeffs[2]'(by omega)
  let l0 := P.lower[0]'(by omega)
  let l1 := P.lower[1]'(by omega)
  let l2 := P.lower[2]'(by omega)
  let c0 := -(a2 * l0)
  let c1 := a0 - a2 * l1
  let c2 := a1 - a2 * l2
  !![a0, c0, -(c2 * l0); a1, c1, c0 - c2 * l1; a2, c2, c1 - c2 * l2]

/-- The inverse in a degree-three extension field: the first column of the adjugate of
`mulMatrix`, divided by its determinant (Cramer's rule). Six base-field products build the
matrix, nine the cofactors and the determinant, one inverse and three products the result. -/
def invDeg3 (h : P.d = 3) (x : Ext P) : Ext P :=
  let M := mulMatrix h x
  let w0 := M 1 1 * M 2 2 - M 1 2 * M 2 1
  let w1 := M 1 2 * M 2 0 - M 1 0 * M 2 2
  let w2 := M 1 0 * M 2 1 - M 1 1 * M 2 0
  let di := (M 0 0 * w0 + M 0 1 * w1 + M 0 2 * w2)⁻¹
  (ofVector ⟨#[di * w0, di * w1, di * w2], by simp [h]⟩ : Ext P)

/-- `mulMatrix` is the matrix of multiplication by `x`. -/
theorem mul_ofVector_eq_mulVec (h : P.d = 3) (x : Ext P) (v : Fin 3 → F) :
    x * (ofVector ⟨#[v 0, v 1, v 2], by simp [h]⟩ : Ext P) =
      (ofVector ⟨#[(mulMatrix h x).mulVec v 0, (mulMatrix h x).mulVec v 1,
        (mulMatrix h x).mulVec v 2], by simp [h]⟩ : Ext P) := by
  rw [← mulDeg3_eq h]
  obtain ⟨d, two_le, lower, q⟩ := P
  simp only at h
  subst h
  apply Ext.ext; intro m
  fin_cases m <;>
    simp [mulDeg3, mulMatrix, coeff, ofVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- Cramer's rule inverts, including `0⁻¹ = 0`: a zero determinant means `x = 0`, since a
nonzero kernel vector of `mulMatrix` would be a zero divisor. -/
theorem invDeg3_eq (h : P.d = 3) [Finite F] [Fact (Nat.card F = P.q)]
    [Fact (Irreducible P.poly)] (x : Ext P) : invDeg3 h x = x⁻¹ := by
  set M := mulMatrix h x with hM
  have hdet : M.det = M 0 0 * (M 1 1 * M 2 2 - M 1 2 * M 2 1) +
      M 0 1 * (M 1 2 * M 2 0 - M 1 0 * M 2 2) + M 0 2 * (M 1 0 * M 2 1 - M 1 1 * M 2 0) := by
    rw [Matrix.det_fin_three]; ring
  have hinv : invDeg3 h x = (ofVector ⟨#[M.det⁻¹ * (M 1 1 * M 2 2 - M 1 2 * M 2 1),
      M.det⁻¹ * (M 1 2 * M 2 0 - M 1 0 * M 2 2), M.det⁻¹ * (M 1 0 * M 2 1 - M 1 1 * M 2 0)],
      by simp [h]⟩ : Ext P) := by
    rw [hdet]; rfl
  by_cases hd : M.det = 0
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    have hx := mul_ofVector_eq_mulVec h x v
    rw [← hM, hv] at hx
    have hV : (ofVector ⟨#[v 0, v 1, v 2], by simp [h]⟩ : Ext P) ≠ 0 := by
      intro hV0
      apply hv0
      funext i
      have := congrArg (fun z : Ext P ↦ z.coeffs.toArray) hV0
      fin_cases i <;> simp_all [ofVector]
    have h0 : (ofVector ⟨#[(0 : Fin 3 → F) 0, (0 : Fin 3 → F) 1, (0 : Fin 3 → F) 2],
        by simp [h]⟩ : Ext P) = 0 := by
      apply Ext.ext; intro m
      obtain ⟨d, two_le, lower, q⟩ := P
      simp only at h
      subst h
      rw [coeff_zero]
      fin_cases m <;> simp [coeff, ofVector]
    rw [h0] at hx
    have hx0 : x = 0 := (mul_eq_zero.mp hx).resolve_right hV
    rw [hinv, hd, inv_zero, hx0, inv_zero']
    apply Ext.ext; intro m
    obtain ⟨d, two_le, lower, q⟩ := P
    simp only at h
    subst h
    rw [coeff_zero]
    fin_cases m <;> simp [coeff, ofVector]
  · have hw0 : M.mulVec ![M 1 1 * M 2 2 - M 1 2 * M 2 1,
        M 1 2 * M 2 0 - M 1 0 * M 2 2, M 1 0 * M 2 1 - M 1 1 * M 2 0] = ![M.det, 0, 0] := by
      ext i
      fin_cases i
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        simp [Matrix.cons_val_one, Matrix.cons_val_two]
        linear_combination -hdet
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        simp [Matrix.cons_val_one, Matrix.cons_val_two]
        ring
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        simp [Matrix.cons_val_one, Matrix.cons_val_two]
        ring
    have hw : M.mulVec (M.det⁻¹ • ![M 1 1 * M 2 2 - M 1 2 * M 2 1,
        M 1 2 * M 2 0 - M 1 0 * M 2 2, M 1 0 * M 2 1 - M 1 1 * M 2 0]) = ![1, 0, 0] := by
      rw [Matrix.mulVec_smul, hw0]
      ext i
      fin_cases i <;> simp [inv_mul_cancel₀ hd]
    have hx := mul_ofVector_eq_mulVec h x (M.det⁻¹ • ![M 1 1 * M 2 2 - M 1 2 * M 2 1,
        M 1 2 * M 2 0 - M 1 0 * M 2 2, M 1 0 * M 2 1 - M 1 1 * M 2 0])
    rw [← hM, hw] at hx
    have h1 : x * invDeg3 h x = 1 := by
      have hv : invDeg3 h x = (ofVector ⟨#[(M.det⁻¹ • ![M 1 1 * M 2 2 - M 1 2 * M 2 1,
          M 1 2 * M 2 0 - M 1 0 * M 2 2, M 1 0 * M 2 1 - M 1 1 * M 2 0]) 0,
          (M.det⁻¹ • ![M 1 1 * M 2 2 - M 1 2 * M 2 1,
          M 1 2 * M 2 0 - M 1 0 * M 2 2, M 1 0 * M 2 1 - M 1 1 * M 2 0]) 1,
          (M.det⁻¹ • ![M 1 1 * M 2 2 - M 1 2 * M 2 1,
          M 1 2 * M 2 0 - M 1 0 * M 2 2, M 1 0 * M 2 1 - M 1 1 * M 2 0]) 2],
          by simp [h]⟩ : Ext P) := by
        rw [hinv]; rfl
      rw [hv, hx]
      apply Ext.ext; intro m
      obtain ⟨d, two_le, lower, q⟩ := P
      simp only at h
      subst h
      rw [coeff_one]
      fin_cases m <;> simp [coeff, ofVector]
    exact (inv_eq_of_mul_eq_one_right h1).symm

/-- The inverse of a field extension: Cramer's rule in degree three, `invFast` otherwise. -/
def fieldInv (x : Ext P) : Ext P := if h : P.d = 3 then invDeg3 h x else invFast x

/-- `fieldInv` is the field's inverse. -/
theorem fieldInv_eq [Finite F] [Fact (Nat.card F = P.q)] [Fact (Irreducible P.poly)]
    (x : Ext P) : fieldInv x = inv x := by
  unfold fieldInv; split_ifs with h
  · exact invDeg3_eq h x
  · exact invFast_eq x

end Inverse

section Field

variable [Field F] {P : ExtensionParams F} [Finite F] [Fact (Nat.card F = P.q)]
  [Fact (Irreducible P.poly)]

/-- `instField` with its ring, inverse, division and integer powers replaced by equal ones. The
rational casts and scalar products stay those of `instField`, over CompPoly's product. -/
@[instance_reducible] def fieldWith (cr : CommRing (Ext P)) (hcr : cr = instCommRing)
    (i : Ext P → Ext P) (hi : i = inv) (d : Ext P → Ext P → Ext P)
    (hd : d = fun x y ↦ x * inv y) (z : ℤ → Ext P → Ext P) (hz : z = fun n x ↦ x ^ n) :
    Field (Ext P) :=
  { instField with
    toCommRing := cr
    inv := i
    div := d
    zpow := z
    div_eq_mul_inv := by subst hcr hi hd; exact instField.div_eq_mul_inv
    zpow_zero' := by subst hcr hi hz; exact instField.zpow_zero'
    zpow_succ' := by subst hcr hi hz; exact instField.zpow_succ'
    zpow_neg' := by subst hcr hi hz; exact instField.zpow_neg'
    exists_pair_ne := instField.exists_pair_ne
    mul_inv_cancel := by subst hcr hi hd; exact instField.mul_inv_cancel
    inv_zero := by subst hcr hi hd; exact instField.inv_zero
    nnratCast_def := by subst hcr hi hd; exact instField.nnratCast_def
    nnqsmul_def := by subst hcr hi hd; exact instField.nnqsmul_def
    ratCast_def := by subst hcr hi hd; exact instField.ratCast_def
    qsmul_def := by subst hcr hi hd; exact instField.qsmul_def }

/-- `fieldWith` is `Ext.instField`. -/
theorem fieldWith_eq (cr : CommRing (Ext P)) (hcr : cr = instCommRing)
    (i : Ext P → Ext P) (hi : i = inv) (d : Ext P → Ext P → Ext P)
    (hd : d = fun x y ↦ x * inv y) (z : ℤ → Ext P → Ext P) (hz : z = fun n x ↦ x ^ n) :
    fieldWith cr hcr i hi d hd z hz = instField := by
  subst hcr hi hd hz; rfl

/-- Integer powers: `powFast`, and `fieldInv` of it for a negative exponent. -/
def zpowFast : ℤ → Ext P → Ext P
  | Int.ofNat n, x => powFast x n
  | Int.negSucc n, x => fieldInv (powFast x (n + 1))

/-- `zpowFast` is the field's integer power. -/
theorem zpowFast_eq (n : ℤ) (x : Ext P) : zpowFast n x = x ^ n := by
  cases n with
  | ofNat n =>
    show powFast x n = x ^ (n : ℤ)
    rw [zpow_natCast, powFast_eq]
  | negSucc n =>
    show fieldInv (powFast x (n + 1)) = x ^ Int.negSucc n
    rw [zpow_negSucc, powFast_eq, fieldInv_eq]
    rfl

end Field

/-- The field with `mulFast`, `powFast`, `fieldInv` and `zpowFast`. -/
@[instance_reducible] def fieldFast [Field F] {P : ExtensionParams F} [Finite F]
    [Fact (Nat.card F = P.q)] [Fact (Irreducible P.poly)] : Field (Ext P) :=
  fieldWith commRingFast (instCommRing_eq_commRingFast ▸ rfl) fieldInv (funext fieldInv_eq)
    (fun x y ↦ mulFast x (fieldInv y)) (funext₂ fun x y ↦ by rw [mulFast_eq, fieldInv_eq])
    zpowFast (funext₂ zpowFast_eq)

/-- Compiled code passes `fieldFast` for an extension's field. -/
@[csimp] theorem instField_eq_fieldFast : @Ext.instField.{u} = @fieldFast.{u} := by
  funext F _ P _ _ _
  exact (fieldWith_eq _ _ _ _ _ _ _ _).symm

end
end LeanerVM.Parameters.FastExt
