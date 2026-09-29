/-
  LeanerVM.Protocol.Padding

  Back-loaded padding: a table lifted to a taller cube by the product of the new variables, so
  that tables of different heights share one sumcheck.
-/

module

public import LeanerVM.Protocol.ToCompPoly.Multilinear

/-!
# Back-loaded padding

leanVM's tables have different heights and one sumcheck runs over all of them. A table on `k`
variables joins a cube of `k + m` variables multiplied by `∏_{c ≥ k} X_c`, the product of the
variables it does not have (specification §5.5): on the cube that product is one where the new
coordinates are all one and zero elsewhere, so the lifted table is the table placed on that one
slice. Its sum over the taller cube is the table's own sum (`sumCube_padHigh`), and its
extension is the table's extension times the product of the new coordinates
(`evalMle_padHigh`).

The slice is the protocol's choice. Placing a table on any slice is `placeSlice`, in
`ToCompPoly/Multilinear.lean`; `padHigh` is `placeSlice` at the all-ones index. Category A:
written from the specification.

## Wrong readings excluded

* Copying the table into every slice of the taller cube multiplies its sum by `2 ^ m`, which is
  zero in characteristic two for `m ≥ 1`.
* The new variables are the high coordinates `k, …, k + m - 1`, not the low ones.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-- The table of `x_0 ⋯ x_{m-1}` on the cube: one at the all-ones point, zero elsewhere. -/
def prodVars (m : ℕ) : CMlPolynomialEval R m :=
  Vector.ofFn fun i ↦ if i = onesIndex m then 1 else 0

/-- `Σ_x x_0 ⋯ x_{m-1} = 1`. -/
theorem sumCube_prodVars (m : ℕ) : sumCube (prodVars m : CMlPolynomialEval R m) = 1 := by
  simp [sumCube, prodVars]

/-- The extension of `x_0 ⋯ x_{m-1}` at `s` is the product of the coordinates of `s`. -/
theorem evalMle_prodVars {m : ℕ} (s : Vector R m) :
    evalMle (prodVars m) s = ∏ b : Fin m, s[b] := by
  rw [evalMle_eq_sum]
  simp only [Fin.getElem_fin, prodVars, Vector.getElem_ofFn, Fin.eta, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact lagrangeBasis_onesIndex s

/-- A table of `k` variables lifted to `k + m` variables by `∏_{c ≥ k} X_c`: its entries sit
where the high coordinates are all ones, and everything else is zero. -/
def padHigh {k : ℕ} (t : CMlPolynomialEval R k) (m : ℕ) : CMlPolynomialEval R (k + m) :=
  placeSlice t (onesIndex m)

/-- Back-loaded padding preserves the sum over the cube. -/
theorem sumCube_padHigh {k : ℕ} (t : CMlPolynomialEval R k) (m : ℕ) :
    sumCube (padHigh t m) = sumCube t :=
  sumCube_placeSlice t (onesIndex m)

/-- The extension of a padded table is the table's extension times the product of the high
coordinates. -/
theorem evalMle_padHigh {k m : ℕ} (t : CMlPolynomialEval R k) (z : Vector R k)
    (s : Vector R m) :
    evalMle (padHigh t m) (z ++ s) = evalMle t z * ∏ b : Fin m, s[b] := by
  rw [padHigh, evalMle_placeSlice, Fin.getElem_fin, lagrangeBasis_onesIndex, mul_comm]

end
end LeanerVM.Protocol
