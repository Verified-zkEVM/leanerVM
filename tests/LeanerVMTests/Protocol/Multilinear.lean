module

public import LeanerVM.Protocol.Multilinear
public import LeanerVM.Parameters.Field
meta import LeanerVM.Protocol.Multilinear
meta import LeanerVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Protocol Layer 1 tests: hypercube tables

Compiled checks (`#guard`) over `K` of the generic identities on a two-variable table: cube
points read entries, the equality kernel sums to one, evaluation is the eq-weighted sum, a
Boolean high coordinate selects a slice, and back-loaded padding keeps the cube sum and
multiplies the extension by the high coordinates.
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
-- The equality kernel sums to one off the cube (`sumCube_eqTable`).
#guard sumCube (eqTable pt) = 1
-- Evaluation is the eq-weighted sum (`eval_eq_sum_eqTable`).
#guard evalMle tbl pt = sumCube (hadamard (eqTable pt) tbl)
-- Selection (`evalMle_append_boolVec`): high coordinate `1` selects the slice `[3, 4]`.
#guard evalMle tbl (#v[(7 : K)] ++ (boolVec (⟨1, by decide⟩ : Fin (2 ^ 1)) : Vector K 1)) =
  evalMle (#v[3, 4] : CMlPolynomialEval K 1) #v[7]
-- Mutation: high coordinate `0` selects the other slice, which answers differently.
#guard evalMle tbl (#v[(7 : K)] ++ (boolVec (⟨0, by decide⟩ : Fin (2 ^ 1)) : Vector K 1)) ≠
  evalMle (#v[3, 4] : CMlPolynomialEval K 1) #v[7]
-- Back-loaded padding keeps the cube sum (`sumCube_padHigh`) ...
#guard sumCube (padHigh tbl 1) = sumCube tbl
-- ... and its extension at `(z, s)` is `tbl(z) · s` (`evalMle_padHigh`).
#guard evalMle (padHigh tbl 1) (pt ++ #v[(11 : K)]) = evalMle tbl pt * 11
-- The product of the variables sums to one over the cube (`sumCube_prodVars`).
#guard sumCube (prodVars 3 : CMlPolynomialEval K 3) = 1

end
end LeanerVMTests.Protocol
