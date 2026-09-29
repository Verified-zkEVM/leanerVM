/-
  Probe (boundary-adaptor): from a Clean expression to the polynomial an `M3Instance` holds.
  The blueprint's Layer 2 produces Mathlib's `MvPolynomial`; the instance holds CompPoly's
  `CMvPolynomial`. CompPoly's conversion from the first to the second is noncomputable at the
  pin; a direct, computable translation exists. Scratch work for the blueprint review.
  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/boundary-adaptor/PolyBridge.lean
-/
import LeanerVM
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Multivariate.Operations

open LeanerVM.Parameters CompPoly CPoly

namespace Probe

-- The two directions of CompPoly's bridge at the pin.
#print CPoly.toCMvPolynomial
#print CPoly.fromCMvPolynomial

/-- A direct translation of a Clean expression over `K` to a computable polynomial in the first
`n` row variables; a variable past the width reads `0`, as Clean's `Environment.fromArray`
reads a missing cell. -/
def exprToCMv (n : ℕ) : Expression K → CMvPolynomial n K
  | .var v => if h : v.index < n then CMvPolynomial.X ⟨v.index, h⟩ else 0
  | .const c => CMvPolynomial.C c
  | .add a b => exprToCMv n a + exprToCMv n b
  | .mul a b => exprToCMv n a * exprToCMv n b

/-- The first `JUMP` residual, `b + v_cond · w`, on a row `(v_cond, w, b)`. -/
def residual : Expression K := .add (.var ⟨2⟩) (.mul (.var ⟨0⟩) (.var ⟨1⟩))

/-- A row. -/
def row : Array K := #[3, 5, 7]

/-- The row as the assignment of the three variables. -/
def rowFn : Fin 3 → K := fun i ↦ row[i.val]?.getD 0

/-- Clean's value of the residual on the row. -/
def cleanValue : K := residual.eval (Environment.fromArray row fun _ _ ↦ #[])

/-- The polynomial's value on the row. -/
def polyValue : K := (exprToCMv 3 residual).eval rowFn

-- The translation runs, agrees with Clean's evaluation on the row, and has the degree the
-- expression shows.
#guard polyValue = cleanValue
#guard (exprToCMv 3 residual).totalDegree = 2

-- A variable past the width is read as zero on both sides.
def wide : Expression K := .add (.var ⟨5⟩) (.var ⟨0⟩)
def wideClean : K := wide.eval (Environment.fromArray row fun _ _ ↦ #[])
def widePoly : K := (exprToCMv 3 wide).eval rowFn
#guard widePoly = wideClean

end Probe
