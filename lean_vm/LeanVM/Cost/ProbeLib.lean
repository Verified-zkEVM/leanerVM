module

public import LeanVM.Cost.CompPolyLib
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Core
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.Recursion
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation.Basic

/-!
# Library additions for compiling CompPoly's approximant bases (probe)

Generic additions found while compiling CompPoly's PM-basis over `K` (track probe):

* `for i in [a:b] do …` in `Id` (`Id.run do` with a `for` over a `Std.Legacy.Range`): Init's
  `Std.Legacy.Range.forIn'` loops with a membership proof per index (not data, so not compiled). It is
  compiled through `listForInId` over `List.range' start size step` (`forIn_range_id`, from Init's
  `Std.Legacy.Range.forIn_eq_forIn_range'`): one call of the body per index, an early exit at `.done`.
* Products and sums of polynomials trimmed once: `CPolynomial.Raw.mul p q` is
  `(mulRaw p q).trim`, and CompPolyLib's `trim_eq` (`p.trim = p.extract 0 (trimLen p p.size)`) names
  its argument three times, so the compiled product computed `mulRaw p q` three times (a factor of 3
  on every product and sum, as Phase 3 found). `rawMul_shared`, `rawAdd_shared` bind the untrimmed
  result by a `let` (evaluated once, then read from the environment): the same values, a third of
  the work. A rewrite only: no compiler change, so nothing compiled before changes.
* The encodings of `ForInStep`, `MProd` (a loop's several mutable variables), and CompPoly's
  `XAdicProblem`, `ScalarRrefResult`, `ModularEquation`.

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

/-- **A product trimmed once.** -/
theorem rawMul_shared {R : Type} [Semiring R] [BEq R] (p q : CompPoly.CPolynomial.Raw R) :
    CompPoly.CPolynomial.Raw.mul p q =
      (let r := CompPoly.CPolynomial.Raw.mulRaw p q; r.extract 0 (CompPolyLib.trimLen r r.size)) := by
  rw [CompPoly.CPolynomial.Raw.mul, CompPolyLib.trim_eq]

cost_rewrite rawMul_shared

/-- **A sum trimmed once.** -/
theorem rawAdd_shared {R : Type} [Zero R] [Add R] [BEq R] (p q : CompPoly.CPolynomial.Raw R) :
    CompPoly.CPolynomial.Raw.add p q =
      (let r := CompPoly.CPolynomial.Raw.addRaw p q; r.extract 0 (CompPolyLib.trimLen r r.size)) := by
  rw [CompPoly.CPolynomial.Raw.add, CompPolyLib.trim_eq]

cost_rewrite rawAdd_shared

cost_enc CompPoly.PolynomialMatrix.Approximant.XAdicProblem
cost_enc CompPoly.DenseMatrix.ScalarRrefResult
cost_enc CompPoly.PolynomialMatrix.Approximant.ModularEquation

end

end LeanVM.Cost.ProbeLib
