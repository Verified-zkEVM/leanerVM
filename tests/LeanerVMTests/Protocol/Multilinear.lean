module

public import LeanerVM.Protocol.ToCompPoly.Multilinear
public import LeanerVM.Parameters.Field
meta import LeanerVM.Protocol.ToCompPoly.Multilinear
meta import LeanerVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Hypercube table tests

Compiled checks (`#guard`) over `K` of the generic identities on a two-variable table: cube
points read entries, the Lagrange basis sums to one, evaluation is the weighted sum, a Boolean
high coordinate selects a slice, and a placed table keeps its cube sum and picks up the
Lagrange weight of its slot. The last section derives two special cases a consumer may want
from the generic lemmas, to show they need no lemma of their own.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

/-- The table `[1, 2, 3, 4]` on two variables. -/
def tbl : CMlPolynomialEval K 2 := #v[1, 2, 3, 4]

/-- An off-cube point. -/
def pt : Vector K 2 := #v[5, 9]

-- A cube point reads the entry (`evalMle_boolVec`): index 2 is `(0, 1)`, the third entry.
#guard evalMle tbl (boolVec (⟨2, by decide⟩ : Fin (2 ^ 2))) = 3
-- The Lagrange basis sums to one off the cube (`sumCube_lagrangeBasis`).
#guard sumCube (lagrangeBasis pt) = 1
-- Evaluation is the weighted sum (`evalMle_eq_sumCube_hadamard`).
#guard evalMle tbl pt = sumCube (hadamard (lagrangeBasis pt) tbl)
-- A constant table extends to the constant (`evalMle_replicate`).
#guard evalMle (Vector.replicate (2 ^ 2) (7 : K)) pt = 7
-- Selection (`evalMle_append_boolVec`): high coordinate `1` selects the slice `[3, 4]`.
#guard evalMle tbl (#v[(7 : K)] ++ (boolVec (⟨1, by decide⟩ : Fin (2 ^ 1)) : Vector K 1)) =
  evalMle (#v[3, 4] : CMlPolynomialEval K 1) #v[7]
-- Mutation: high coordinate `0` selects the other slice, which answers differently.
#guard evalMle tbl (#v[(7 : K)] ++ (boolVec (⟨0, by decide⟩ : Fin (2 ^ 1)) : Vector K 1)) ≠
  evalMle (#v[3, 4] : CMlPolynomialEval K 1) #v[7]

/-! ## Placing a table on a slice -/

-- The table at slot 2 of four: entries 4 and 5 of eight, zero elsewhere.
#guard (placeSlice (R := K) (k := 1) (m := 2) #v[3, 4] ⟨2, by decide⟩).toList =
  [0, 0, 0, 0, 3, 4, 0, 0]
-- Reading the slot back returns the table; another slot is empty (`slice_placeSlice`).
#guard slice (k := 1) (m := 2)
    (placeSlice (#v[3, 4] : CMlPolynomialEval K 1) (⟨2, by decide⟩ : Fin (2 ^ 2)))
    (⟨2, by decide⟩ : Fin (2 ^ 2)) = #v[3, 4]
#guard slice (k := 1) (m := 2)
    (placeSlice (#v[3, 4] : CMlPolynomialEval K 1) (⟨2, by decide⟩ : Fin (2 ^ 2)))
    (⟨1, by decide⟩ : Fin (2 ^ 2)) = #v[0, 0]
-- Placing keeps the cube sum, whatever the slot (`sumCube_placeSlice`).
#guard sumCube (placeSlice tbl (⟨1, by decide⟩ : Fin (2 ^ 1))) = sumCube tbl
#guard sumCube (placeSlice tbl (⟨0, by decide⟩ : Fin (2 ^ 1))) = sumCube tbl
-- Its extension is the table's, times the Lagrange weight of the slot (`evalMle_placeSlice`).
#guard evalMle (placeSlice tbl (⟨1, by decide⟩ : Fin (2 ^ 1))) (pt ++ #v[(11 : K)]) =
  (lagrangeBasis (#v[(11 : K)]))[1] * evalMle tbl pt
-- Mutation: the other slot carries the other weight.
#guard evalMle (placeSlice tbl (⟨0, by decide⟩ : Fin (2 ^ 1))) (pt ++ #v[(11 : K)]) ≠
  evalMle (placeSlice tbl (⟨1, by decide⟩ : Fin (2 ^ 1))) (pt ++ #v[(11 : K)])

/-! ## The two corners -/

#guard (boolVec (⟨0, by decide⟩ : Fin (2 ^ 3)) : Vector K 3) = #v[0, 0, 0]
#guard (boolVec (onesIndex 3) : Vector K 3) = #v[1, 1, 1]
-- The Lagrange basis at the corners: the product of the coordinates, and of their complements.
#guard (lagrangeBasis (#v[5, 9, 11] : Vector K 3))[(onesIndex 3).val] = 5 * 9 * 11
#guard (lagrangeBasis (#v[5, 9, 11] : Vector K 3))[0] = (1 - 5) * (1 - 9) * (1 - 11)

/-! ## Special cases are corollaries

Evaluating at a point whose coordinates past the first `k` are all zero reads the first slice:
no lemma about such points is needed, the selection identity at index zero is that statement. -/

example {R : Type} [CommRing R] {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (z : Vector R k) :
    evalMle t (z ++ Vector.replicate m (0 : R)) =
      evalMle (slice t (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m))) z := by
  rw [← boolVec_zero, evalMle_append_boolVec]

-- On a table of two variables, at `(r, 0)`: the line through the first two entries.
#guard evalMle tbl ((#v[(7 : K)] : Vector K 1) ++ Vector.replicate 1 (0 : K)) =
  (1 - 7) * 1 + 7 * 2
-- Mutation: at `(r, 1)` it is the line through the last two.
#guard evalMle tbl ((#v[(7 : K)] : Vector K 1) ++ Vector.replicate 1 (1 : K)) =
  (1 - 7) * 3 + 7 * 4

end
end LeanerVMTests.Protocol
