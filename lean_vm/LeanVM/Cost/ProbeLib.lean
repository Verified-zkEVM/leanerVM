module

public import LeanVM.Cost.CompPolyLib
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Core
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.Recursion
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation.Basic
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Basic

/-!
# Library additions for compiling CompPoly's approximant bases (probe)

Generic additions found while compiling CompPoly's PM-basis over `K` (track probe):

* `for i in [a:b] do …` in `Id` (`Id.run do` with a `for` over a `Std.Legacy.Range`): Init's
  `Std.Legacy.Range.forIn'` loops with a membership proof per index (not data, so not compiled). It is
  compiled through `listForInId` over `List.range' start size step` (`forIn_range_id`, from Init's
  `Std.Legacy.Range.forIn_eq_forIn_range'`): one call of the body per index, an early exit at `.done`.
* Products and sums of polynomials trimmed once: now `CompPolyLib`'s `trim_addRaw_shared`,
  `trim_mulRaw_shared` (probe's `rawAdd_shared`, `rawMul_shared`, moved to the chain's head).
* `Array.reverse` through `List.reverse` (`arrayReverse_list`; CompPoly's `gsModuli`).
* The measure of CompPoly's `adaptiveSolutionLoop` (its fuel).
* The encodings of `ForInStep`, `MProd` (a loop's several mutable variables), and CompPoly's
  `XAdicProblem`, `ScalarRrefResult`, `ModularEquation`, the
  partial-linearization plans and the adaptive solver's state, `GSModularData`.

Credits: CompPoly (github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly
Contributors"), compiled, not copied.
-/

namespace LeanVM.Cost.ProbeLib

open LeanVM.Cost

@[expose] public section

cost_enc ForInStep
cost_enc MProd
cost_enc Std.Legacy.Range

/-- A `for` loop's body over a list, in `Id`: stop at the first `.done`. -/
def listForInId {β : Type} (f : ℕ → β → ForInStep β) : List ℕ → β → β
  | [], b => b
  | a :: l, b =>
    match f a b with
    | .done b => b
    | .yield b => listForInId f l b

theorem forIn_list_id {β : Type} (l : List ℕ) (init : β) (f : ℕ → β → Id (ForInStep β)) :
    forIn (m := Id) l init f = listForInId f l init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, listForInId]
    show (match f a init with | .done b => pure b | .yield b => forIn l b f) = _
    cases f a init with
    | done b => rfl
    | yield b => exact ih b

/-- **`for i in r do …` in `Id`**: the body over `List.range' r.start r.size r.step`. -/
theorem forIn_range_id {β : Type} (r : Std.Legacy.Range) (init : β) (f : ℕ → β → Id (ForInStep β)) :
    forIn (m := Id) r init f = listForInId f (List.range' r.start r.size r.step) init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_list_id]

cost_rewrite forIn_range_id

/-- **An array reversed through its list** (Init's `Array.reverse.loop` swaps in place under a
proof of bounds: its array changes at each call, which the compiler's on-demand recursion keeps
fixed). -/
theorem arrayReverse_list {α : Type} (a : Array α) : a.reverse = a.toList.reverse.toArray := by
  apply Array.toList_inj.1
  simp

cost_rewrite arrayReverse_list

cost_enc CompPoly.PolynomialMatrix.Approximant.XAdicProblem
cost_enc CompPoly.DenseMatrix.ScalarRrefResult
cost_enc CompPoly.PolynomialMatrix.Approximant.ModularEquation
cost_enc CompPoly.PolynomialMatrix.Approximant.PrincipalChunk
cost_enc CompPoly.PolynomialMatrix.Approximant.PartialLinearizationPlan
cost_enc CompPoly.PolynomialMatrix.Approximant.PivotDegreeProfile
cost_enc CompPoly.PolynomialMatrix.Approximant.AdaptiveSolveState
cost_enc CompPoly.GuruswamiSudan.ApproximantBasis.GSModularData

/- The adaptive solver's loop decreases its fuel (the compiler's default measures, tried in the
order of the parameters, start with the size of `degreeBound?`: its decrease's `simp_all` on the
loop's large context exhausts the command's heartbeats instead of failing). -/
cost_measure CompPoly.PolynomialMatrix.Approximant.adaptiveSolutionLoop :=
  fun _ _ _ _ _ _ _ _ _ _ _ fuel _ ↦ fuel

end

end LeanVM.Cost.ProbeLib
