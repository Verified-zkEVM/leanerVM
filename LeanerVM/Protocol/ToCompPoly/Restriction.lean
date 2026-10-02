/-
  LeanerVM.Protocol.ToCompPoly.Restriction

  A table restricted to the coordinates of a partial point, and when that restriction is
  identically zero: the notion a knowledge state function tracks while the coordinates of a
  point are drawn one at a time. Candidate for CompPoly.
-/

module

public import LeanerVM.Protocol.ToCompPoly.Multilinear
import Mathlib.Tactic.LinearCombination

/-!
# A table on a partial point

A *partial point* (`Partial R`) fixes some coordinates and leaves the others free. A table is
*zero on* a partial point (`RestrictedZero`) when its multilinear extension vanishes at every
completion of the fixed coordinates by a cube point: the restriction of the extension to the
fixed coordinates is identically zero as a polynomial in the free ones. On the empty partial
point this says the table is zero (`restrictedZero_empty_iff`); with every coordinate fixed it
says the extension vanishes at the point (`restrictedZero_of_all`).

The one fact a proof system uses: a table that is not zero on a partial point is zero on it with
one more coordinate fixed for at most one value of that coordinate
(`card_filter_restrictedZero_update_le`). The extension is affine in the new coordinate, so
vanishing at two values is vanishing at every value, the cube's included.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type} [CommRing R]

/-- A partial point: for each coordinate, its value if fixed. -/
abbrev Partial (R : Type) : Type := ℕ → Option R

/-- The point of a partial point at a completion `b`: the fixed coordinates, the others the bits
of `b`. -/
def Partial.point {n : ℕ} (σ : Partial R) (b : Fin (2 ^ n)) : Vector R n :=
  Vector.ofFn fun k ↦ (σ k).getD (boolVec b)[k]

/-- A table is zero on a partial point when its extension vanishes at every completion of the
fixed coordinates by a cube point. -/
def RestrictedZero {n : ℕ} (t : CMlPolynomialEval R n) (σ : Partial R) : Prop :=
  ∀ b : Fin (2 ^ n), evalMle t (σ.point b) = 0

/-- The empty partial point: nothing fixed. -/
def Partial.empty : Partial R := fun _ ↦ Option.none

/-- The point of the empty partial point at a completion is the cube point itself. -/
@[simp] theorem Partial.point_empty {n : ℕ} (b : Fin (2 ^ n)) :
    (Partial.empty : Partial R).point b = boolVec b := by
  apply Vector.ext
  intro k hk
  simp [Partial.point, Partial.empty]

/-- On the empty partial point, zero means the table is zero. -/
theorem restrictedZero_empty_iff {n : ℕ} (t : CMlPolynomialEval R n) :
    RestrictedZero t Partial.empty ↔ ∀ i : Fin (2 ^ n), t[i] = 0 := by
  simp only [RestrictedZero, Partial.point_empty, evalMle_boolVec]

/-- The difference of two tables, entry by entry. -/
def diffTable {n : ℕ} (t t' : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  Vector.ofFn fun i ↦ t[i] - t'[i]

/-- The extension of a difference is the difference of the extensions. -/
theorem evalMle_diffTable {n : ℕ} (t t' : CMlPolynomialEval R n) (p : Vector R n) :
    evalMle (diffTable t t') p = evalMle t p - evalMle t' p := by
  simp only [evalMle_eq_sum, diffTable, Fin.getElem_fin, Vector.getElem_ofFn, sub_mul,
    Finset.sum_sub_distrib]

/-- A difference zero on the empty partial point means the two tables are equal. -/
theorem diffTable_restrictedZero_empty_iff {n : ℕ} (t t' : CMlPolynomialEval R n) :
    RestrictedZero (diffTable t t') Partial.empty ↔ t = t' := by
  rw [restrictedZero_empty_iff]
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    have := h ⟨i, hi⟩
    simp only [diffTable, Fin.getElem_fin, Vector.getElem_ofFn] at this
    exact sub_eq_zero.mp this
  · rintro rfl i
    simp [diffTable]

/-- When every coordinate is fixed, zero means the extension vanishes at the point. -/
theorem restrictedZero_of_all {n : ℕ} (t : CMlPolynomialEval R n) (σ : Partial R) (p : Vector R n)
    (hp : ∀ k (hk : k < n), σ k = some p[k]) :
    RestrictedZero t σ ↔ evalMle t p = 0 := by
  have hpoint : ∀ b : Fin (2 ^ n), σ.point b = p := fun b ↦ by
    apply Vector.ext
    intro k hk
    simp [Partial.point, hp k hk]
  simp only [RestrictedZero, hpoint]
  exact ⟨fun h ↦ h ⟨0, Nat.two_pow_pos n⟩, fun h _ ↦ h⟩

/-- The point of a partial point with one more coordinate fixed. -/
theorem Partial.point_update {n : ℕ} (σ : Partial R) (k : ℕ) (hk : k < n) (c : R)
    (b : Fin (2 ^ n)) :
    Partial.point (Function.update σ k (some c)) b = (σ.point b).set k c := by
  apply Vector.ext
  intro j hj
  by_cases hjk : j = k
  · subst hjk
    simp [Partial.point]
  · simp [Partial.point, Function.update_of_ne hjk, Vector.getElem_set_ne hk hj (Ne.symm hjk)]

/-- Fixing a coordinate beyond the table's variables changes nothing. -/
theorem Partial.point_update_of_le {n : ℕ} (σ : Partial R) (k : ℕ) (hk : n ≤ k) (c : R)
    (b : Fin (2 ^ n)) :
    Partial.point (Function.update σ k (some c)) b = σ.point b := by
  apply Vector.ext
  intro j hj
  simp [Partial.point, Function.update_of_ne (show j ≠ k by omega)]

/-- Setting a coordinate of a completion to its own value changes nothing. -/
theorem Partial.point_set_self {n : ℕ} (σ : Partial R) (k : ℕ) (hk : k < n)
    (b : Fin (2 ^ n)) : (σ.point b).set k ((σ.point b)[k]) = σ.point b :=
  Vector.set_getElem_self hk

open scoped Classical in
/-- **One escape at most.** A table that is not zero on a partial point is zero on it with one
more coordinate fixed for at most one value of that coordinate: its extension is affine in
the coordinate, so vanishing at two values is vanishing everywhere. -/
theorem card_filter_restrictedZero_update_le [IsDomain R] [Fintype R] {n : ℕ}
    (t : CMlPolynomialEval R n) (σ : Partial R) (k : ℕ)
    (hne : ¬ RestrictedZero t σ) :
    (Finset.univ.filter fun c ↦ RestrictedZero t (Function.update σ k (some c))).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun c₁ h₁ c₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  by_contra hc
  apply hne
  by_cases hk : k < n
  · intro b
    have e₁ := h₁.2 b
    have e₂ := h₂.2 b
    rw [Partial.point_update σ k hk c₁ b, evalMle_set t _ hk] at e₁
    rw [Partial.point_update σ k hk c₂ b, evalMle_set t _ hk] at e₂
    -- `A + c·(B − A) = 0` at two distinct `c`: both `A` and `B` vanish.
    set A := evalMle t ((σ.point b).set k 0) with hA
    set B := evalMle t ((σ.point b).set k 1) with hB
    have hBA : B = A := by
      have : (c₁ - c₂) * (B - A) = 0 := by linear_combination e₁ - e₂
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) hc
      · exact sub_eq_zero.mp h
    have hA0 : A = 0 := by
      rw [hBA] at e₁
      linear_combination e₁
    have := evalMle_set t (σ.point b) hk ((σ.point b)[k])
    rw [Partial.point_set_self σ k hk b] at this
    rw [this, ← hA, ← hB, hBA, hA0]
    ring
  · intro b
    have := h₁.2 b
    rwa [Partial.point_update_of_le σ k (by omega) c₁ b] at this

end
end LeanerVM.Protocol
