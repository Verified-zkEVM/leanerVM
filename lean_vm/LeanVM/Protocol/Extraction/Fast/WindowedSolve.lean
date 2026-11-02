module

public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant
public import LeanVM.Protocol.Extraction.Fast.Karatsuba
public import LeanVM.Protocol.Extraction.Fast.PMBasis.PopovCore
public import LeanVM.Protocol.Extraction.Fast.FFT.PlannedEval

/-!
# The modular equations solved once, non-adaptively

CompPoly's solver of the diagonal modular equations `p · F = 0 mod diag(M)`
(`filteredSolutionBasisViaPMBasis`, the solver of `modularSolutionBasisContextViaPMBasis`) runs an
adaptive loop of chunked (partially linearized) X-adic problems, backs it with a certified solve
(`windowedSolutionBasisViaPMBasis`) and a residual repair: the loop's rounds and sizes are
data-dependent, with no a-priori bound.

Here the solver is the certified solve alone: one X-adic problem, unchunked, without partial
linearization, at the caller's degree bound (the Guruswami–Sudan interpolation passes its weighted
degree `W`), its rows filtered by the modular predicate (`windowedFilteredSolutionBasis`). It is a
`ModularSolutionBasisContext` (**`windowedModularSolutionBasisContext`**), so CompPoly's
approximant-basis interpolation on it is sound and complete
(`approximantBasisInterpolate_sound`/`_complete` are generic in the solver):

* sound: the filter keeps only modular solutions;
* complete and minimal: a solution of shifted degree `e ≤ bound` is dominated by a returned row
  (`me_verification_dominates`: the certified window's orders force every dominated row of the
  lifted problem to be an exact solution); without a bound the window is the full pivot window,
  and a solution beyond it is dominated by the fallback `e_p · ∏ M_b` (`me_prodRow_facts`).

The PM-basis context is a parameter. The target one is `popovEvalPMBasisContext T mulCtx lowCtx 1`:
the ordered-weak-Popov PM-basis (`Popov.popovRuntime`: the leaf sorted by pivot, no root pass)
at leaf cutoff `1`, its matrix products on the evaluation domain of a point transform `T`, the
plan built once per product (`FFT.mulEvalP`), proved equal to popov's runtime
(`popovEvalRuntime_eq`).
`pmContextKaratsuba` is popov's on Karatsuba's products, for tests.
-/

namespace LeanVM.Extraction.Fast

open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The certified window: the caller's degree bound, else the full pivot window. -/
@[expose] def solveWindow (equation : ModularEquation F) (shift : Array Nat)
    (degreeBound? : Option Nat) : Nat :=
  degreeBound?.getD (fullWindowDegreeBound equation shift)

/-- **The non-adaptive solver**: one certified solve over `solveWindow`
(`windowedSolutionBasisViaPMBasis`: the reduced exact-nullspace lift, orders
`deg M_b + bound + 2`), the rows filtered by the modular predicate. -/
@[expose] def windowedFilteredSolutionBasis (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (pmCtx : PMBasisContext F)
    (equation : ModularEquation F) (shift : Array Nat) (degreeBound? : Option Nat) :
    PolynomialMatrix F :=
  filterModularSolutionRows mulCtx modCtx equation
    (windowedSolutionBasisViaPMBasis modCtx pmCtx equation shift
      (solveWindow equation shift degreeBound?))

theorem windowedFilteredSolutionBasis_sound {mulCtx : CPolynomial.MulContext F}
    {modCtx : CPolynomial.ModContext F} {pmCtx : PMBasisContext F}
    {equation : ModularEquation F} {shift : Array Nat} {degreeBound? : Option Nat}
    {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows
      (windowedFilteredSolutionBasis mulCtx modCtx pmCtx equation shift degreeBound?)) :
    rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true :=
  rowSatisfiesModularBool_of_mem_filterModularSolutionRows hrow

theorem windowedFilteredSolutionBasis_width {mulCtx : CPolynomial.MulContext F}
    {modCtx : CPolynomial.ModContext F} {pmCtx : PMBasisContext F}
    {equation : ModularEquation F} {shift : Array Nat} {degreeBound? : Option Nat}
    {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows
      (windowedFilteredSolutionBasis mulCtx modCtx pmCtx equation shift degreeBound?)) :
    row.size = equation.solutionWidth :=
  me_principalSolutionRows_width
    (compactNonzeroRows_subset (me_filterModularSolutionRows_subset hrow))

/-- **Completeness and minimality**: a nonzero in-width solution within the bound is dominated
by a returned row. -/
theorem windowedFilteredSolutionBasis_complete_minimal (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (pmCtx : PMBasisContext F)
    (equation : ModularEquation F) (shift : Array Nat) (degreeBound? : Option Nat)
    (row : PolynomialRow F) (d : Nat)
    (hmonic : ∀ b, b < equation.moduli.size → (equation.moduli.getD b 0).monic)
    (hcols : equation.moduli.size ≤ MatrixWidth equation.matrix)
    (hshift : shift.size = equation.solutionWidth)
    (hsat : rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true)
    (hnz : rowIsZero row = false) (hwidth : row.size ≤ equation.solutionWidth)
    (hd : rowShiftedDegree? row shift = some d)
    (hdbound : ∀ bound, degreeBound? = some bound → d ≤ bound) :
    ∃ basisRow degree,
      basisRow ∈ MatrixRows
        (windowedFilteredSolutionBasis mulCtx modCtx pmCtx equation shift degreeBound?) ∧
      rowShiftedDegree? basisRow shift = some degree ∧
      degree ≤ degreeBound?.getD d := by
  obtain ⟨j0, hj0, -⟩ := exists_nonzero_entry_of_rowIsZero_false hnz
  have hpos : 0 < equation.solutionWidth := by omega
  cases hbnd : degreeBound? with
  | some bound =>
    have hdb : d ≤ bound := hdbound bound hbnd
    obtain ⟨bRow, degB, hmem, hdegB, hleB⟩ := me_verification_dominates mulCtx modCtx pmCtx
      equation shift bound hmonic hcols hshift hpos hsat hnz hwidth hd hdb
    exact ⟨bRow, degB, hmem, hdegB, by rw [Option.getD_some]; omega⟩
  | none =>
    have hwin : solveWindow equation shift none =
        pivotWindowCap equation + maxShiftDegree shift := rfl
    by_cases hdw : d ≤ pivotWindowCap equation + maxShiftDegree shift
    · obtain ⟨bRow, degB, hmem, hdegB, hleB⟩ := me_verification_dominates mulCtx modCtx pmCtx
        equation shift _ hmonic hcols hshift hpos hsat hnz hwidth hd (hwin ▸ hdw)
      exact ⟨bRow, degB, hmem, hdegB, by rw [Option.getD_none]; omega⟩
    · obtain ⟨prow, e, hsatP, hnzP, hsizeP, hdegP, heP⟩ :=
        me_prodRow_facts mulCtx modCtx equation shift (p := j0) hmonic hcols (by omega)
      obtain ⟨bRow, degB, hmem, hdegB, hleB⟩ := me_verification_dominates mulCtx modCtx pmCtx
        equation shift _ hmonic hcols hshift hpos hsatP hnzP (le_of_eq hsizeP) hdegP
        (hwin ▸ heP)
      exact ⟨bRow, degB, hmem, hdegB, by rw [Option.getD_none]; omega⟩

/-- **The non-adaptive modular-equation solver** as CompPoly's solution-basis context. -/
@[expose] def windowedModularSolutionBasisContext (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (pmCtx : PMBasisContext F) :
    ModularSolutionBasisContext F where
  mulContext := mulCtx
  modContext := modCtx
  solutionBasis := windowedFilteredSolutionBasis mulCtx modCtx pmCtx
  sound := fun _ _ _ _ hrow ↦ windowedFilteredSolutionBasis_sound hrow
  complete_minimal := by
    intro equation shift degreeBound? row d hmonic hcols hshift hsat hnz hwidth hd hdbound
    exact ⟨fun _ h ↦ le_of_eq (windowedFilteredSolutionBasis_width h),
      windowedFilteredSolutionBasis_complete_minimal mulCtx modCtx pmCtx equation shift
        degreeBound? row d hmonic hcols hshift hsat hnz hwidth hd hdbound⟩

/-! ## The PM-basis contexts

The target: the ordered-weak-Popov PM-basis (`Popov.popovRuntime`, the leaf sorted by pivot, its
core returned with no root pass) with its two matrix products on the evaluation domains of a
point transform, each product's plan built once (`FFT.mulEvalP`, `FFT.mulTruncEvalP`), leaf
cutoff `1`: `popovEvalRuntime`, proved equal
to `Popov.popovRuntime` at every composition cutoff (`popovEvalRuntime_eq`: the products are equal
as functions), so popov's soundness and shifted minimality carry over
(`popovEvalPMBasisContext`). -/

/-- **The ordered-weak-Popov PM-basis runtime on evaluation-domain products.** -/
@[expose] def popovEvalRuntime {Plan : Type} (T : FFT.PointTransform F Plan)
    (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff : Nat) : PMBasisRuntime F where
  mulContext := mulCtx
  lowMulContext := lowCtx
  composeBasis := FFT.mulEvalP T mulCtx
  residualProduct := FFT.mulTruncEvalP T mulCtx
  leafCutoff := leafCutoff
  leafBasis := Popov.popovLeafBasis

/-- **It is popov's runtime**, at every composition cutoff. -/
theorem popovEvalRuntime_eq {Plan : Type} (T : FFT.PointTransform F Plan) (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff composeLeafCutoff : Nat) :
    popovEvalRuntime T mulCtx lowCtx leafCutoff =
      Popov.popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff := by
  rw [popovEvalRuntime, Popov.popovRuntime, Popov.leafRuntime]
  congr 1
  · exact funext fun A ↦ funext fun B ↦ (FFT.mulEvalP_eq T mulCtx A B).trans
      (EvalMat.mulEval_eq_mulStrassenWith T.toEvalMat mulCtx lowCtx _ A B)
  · exact funext fun orders ↦ funext fun A ↦ funext fun B ↦
      (FFT.mulTruncEvalP_eq T mulCtx orders A B).trans
        (EvalMat.mulTruncEval_eq_mulTruncColumnStrassenWith T.toEvalMat mulCtx lowCtx _ orders A B)

/-- **The PM-basis context on `popovEvalRuntime`**: its basis the recursion's core (no root
pass), sound and shifted-minimal (popov's, through `popovEvalRuntime_eq`). -/
@[expose] def popovEvalPMBasisContext {Plan : Type} (T : FFT.PointTransform F Plan)
    (mulCtx : CPolynomial.MulContext F) (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff : Nat) : PMBasisContext F where
  runtime := popovEvalRuntime T mulCtx lowCtx leafCutoff
  basis problem shift := pmBasisWithFuelCore (popovEvalRuntime T mulCtx lowCtx leafCutoff)
    (pmBasisFuel problem) problem shift
  sound := by
    intro problem shift row hrow
    rw [popovEvalRuntime_eq T mulCtx lowCtx leafCutoff leafCutoff] at hrow
    exact (Popov.popovCorePMBasisContextWithLowAndCompose mulCtx lowCtx leafCutoff
      leafCutoff).sound problem shift row hrow
  complete_minimal := by
    intro problem shift row hpos hwf happrox hnz hwidth
    rw [popovEvalRuntime_eq T mulCtx lowCtx leafCutoff leafCutoff]
    exact (Popov.popovCorePMBasisContextWithLowAndCompose mulCtx lowCtx leafCutoff
      leafCutoff).complete_minimal problem shift row hpos hwf happrox hnz hwidth

/-- Its basis is popov's core context's (`popovCorePMBasisContextWithLowAndCompose`), at every
composition cutoff. -/
theorem popovEvalPMBasisContext_basis {Plan : Type} (T : FFT.PointTransform F Plan)
    (mulCtx : CPolynomial.MulContext F) (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat) :
    (popovEvalPMBasisContext T mulCtx lowCtx leafCutoff).basis =
      (Popov.popovCorePMBasisContextWithLowAndCompose mulCtx lowCtx leafCutoff
        composeLeafCutoff).basis := by
  funext problem shift
  show pmBasisWithFuelCore _ _ _ _ = pmBasisWithFuelCore _ _ _ _
  rw [popovEvalRuntime_eq T mulCtx lowCtx leafCutoff composeLeafCutoff]

/-- CompPoly's low-product context on Karatsuba's low products (`MulLowContext.raw`: one low
product, not the full product per coefficient as `MulLowContext.fromMulContext`). -/
@[expose] def karatsubaMatrixLowContext : PolynomialMatrix.MulLowContext F :=
  PolynomialMatrix.MulLowContext.raw karatsubaMulContext karatsubaMulLowContext

/-- The ordered-weak-Popov PM-basis on Karatsuba's products (Strassen's matrix products), leaf
cutoff `1`: a context for testing at small sizes. -/
@[expose] def pmContextKaratsuba : PMBasisContext F :=
  Popov.popovCorePMBasisContextWithLowAndCompose karatsubaMulContext karatsubaMatrixLowContext 1 1

end

end LeanVM.Extraction.Fast
