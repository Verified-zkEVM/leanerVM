/-
  LeanerVM.Protocol.ToCompPoly.WeightedCube

  Sums over the Boolean cube against a product of per-coordinate weights, split one coordinate
  at a time. Candidate for CompPoly.
-/

module

public import LeanerVM.Protocol.ToCompPoly.Multilinear

/-!
# Weighted sums over the cube

A weight per coordinate, `w k = (w_k(0), w_k(1))`, weighs the cube point `x` by
`∏_k w_k(x_k)` (`cubeWeight`), and `weightedCubeSum w g` is `Σ_x (∏_k w_k(x_k)) · g(x)` for a
function `g` of the point. Unit weights give the plain sum over the cube
(`weightedCubeSum_one`); the weights `(1 - r_k, r_k)` give `Σ_x eq(r, x) · g(x)`
(`weightedCubeSum_eq`).

`weightedCubeSum_succ` splits off the highest coordinate: the sum on `k + 1` coordinates is
`w_k(0)` times the sum on the first `k` with the last fixed to `0`, plus `w_k(1)` times the sum
with it fixed to `1`. `weightedCubeSum_zero` is the sum on no coordinate, the value at the empty
point. Over an arbitrary commutative ring; nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-- The weight of a coordinate's value: `w.1` at `0`, `w.2` at `1`. -/
def bitWeight (w : R × R) (b : Bool) : R := if b then w.2 else w.1

/-- The weight of the cube point with index `x`: the product of its coordinates' weights. -/
def cubeWeight {k : ℕ} (w : Fin k → R × R) (x : Fin (2 ^ k)) : R :=
  ∏ a : Fin k, bitWeight (w a) (x.val.testBit a)

/-- The weighted sum of `g` over the cube: `Σ_x (∏_k w_k(x_k)) · g(x)`. -/
def weightedCubeSum {k : ℕ} (w : Fin k → R × R) (g : Vector R k → R) : R :=
  ∑ x : Fin (2 ^ k), cubeWeight w x * g (boolVec x)

/-- On no coordinate, the weighted sum is the value at the empty point. -/
theorem weightedCubeSum_zero (w : Fin 0 → R × R) (g : Vector R 0 → R) :
    weightedCubeSum w g = g #v[] := by
  have : Unique (Fin (2 ^ 0)) := ⟨⟨0, by decide⟩, fun x ↦ Fin.ext (by have := x.isLt; omega)⟩
  rw [weightedCubeSum, Fintype.sum_unique, cubeWeight, Finset.univ_eq_empty, Finset.prod_empty,
    one_mul]
  congr 1
  exact Vector.ext fun i hi ↦ absurd hi (Nat.not_lt_zero i)

/-- A point on `k` coordinates followed by one more coordinate. -/
private theorem boolVec_cubeIndex_push {k : ℕ} (i : Fin (2 ^ k)) (b : Fin (2 ^ 1)) :
    (boolVec (cubeIndex i b) : Vector R (k + 1)) =
      (boolVec i : Vector R k).push (if b.val.testBit 0 then 1 else 0) := by
  rw [← boolVec_append]
  apply Vector.ext
  intro a ha
  rw [Vector.getElem_append, Vector.getElem_push]
  by_cases h : a < k
  · simp only [h, dite_true]
  · simp only [h, dite_false, boolVec, Vector.getElem_ofFn]
    have hak : a - k = 0 := by omega
    simp only [hak]

/-- Splitting off the highest coordinate: the weighted sum on `k + 1` coordinates is the
weighted sums with the last coordinate fixed to `0` and to `1`, weighted by that coordinate's
weights. -/
theorem weightedCubeSum_succ {k : ℕ} (w : Fin (k + 1) → R × R) (g : Vector R (k + 1) → R) :
    weightedCubeSum w g =
      (w (Fin.last k)).1 * weightedCubeSum (fun a ↦ w a.castSucc) (fun v ↦ g (v.push 0)) +
        (w (Fin.last k)).2 * weightedCubeSum (fun a ↦ w a.castSucc) (fun v ↦ g (v.push 1)) := by
  rw [weightedCubeSum, sum_cube_split (k := k) (m := 1)]
  erw [Fin.sum_univ_two]
  rw [weightedCubeSum, weightedCubeSum, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ ↦ ?_ <;>
    rw [boolVec_cubeIndex_push, cubeWeight, Fin.prod_univ_castSucc, cubeWeight] <;>
    simp only [testBit_cubeIndex, Fin.val_last, Fin.val_castSucc, Fin.is_lt, ite_true,
      lt_irrefl, ite_false, Nat.sub_self, bitWeight] <;>
    simp <;> ring

/-- The weighted sum on `k` coordinates, read on `k'` coordinates when `k = k'`. -/
theorem weightedCubeSum_cast {k k' : ℕ} (h : k = k') (w : Fin k → R × R) (g : Vector R k → R) :
    weightedCubeSum w g =
      weightedCubeSum (fun a : Fin k' ↦ w (Fin.cast h.symm a)) fun v ↦ g (Vector.cast h.symm v) := by
  subst h
  rfl

/-- With unit weights, the weighted sum is the plain sum over the cube. -/
theorem weightedCubeSum_one {k : ℕ} (g : Vector R k → R) :
    weightedCubeSum (fun _ ↦ ((1 : R), (1 : R))) g = ∑ x : Fin (2 ^ k), g (boolVec x) := by
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [cubeWeight, Finset.prod_eq_one fun a _ ↦ by unfold bitWeight; split <;> rfl, one_mul]

/-- With the weights `(1 - r_k, r_k)`, the weighted sum is `Σ_x eq(r, x) · g(x)`, the weight of
`x` being the Lagrange basis at `r`. -/
theorem weightedCubeSum_eq {k : ℕ} (r : Vector R k) (g : Vector R k → R) :
    weightedCubeSum (fun a ↦ (1 - r[a], r[a])) g =
      ∑ x : Fin (2 ^ k), (lagrangeBasis r)[x] * g (boolVec x) := by
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [cubeWeight, Fin.getElem_fin, lagrangeBasis_getElem_nat _ x.isLt]
  rfl

end
end LeanerVM.Protocol
