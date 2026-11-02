module

public import LeanVM.Protocol.Extraction.Fast.FFT.Additive
public import LeanVM.Protocol.Extraction.Fast.FFT.PlannedEval

/-!
# PM-basis on additive-FFT products over `K`

`fftRuntime leafCutoff`: the evaluation-domain PM-basis runtime on the additive-FFT transform,
with the transform's plan built once per matrix product (`evalRuntimeP novelTransform`, equal to
`EvalMat.evalRuntime fftTransform` by definition), with the additive-FFT product and truncated product as
its univariate contexts (`fftMulContext`, `fftMulLowContext`); `fftPMBasisContext leafCutoff`:
CompPoly's PM-basis context on it, its soundness and shifted minimality carried over by
`evalRuntime_eq` (`fftRuntime_eq`: it is CompPoly's kernel-leaf runtime on the same contexts, at
every composition cutoff).
-/

namespace LeanVM.Extraction.Fast.FFT

open CompPoly PolynomialMatrix Approximant LeanVM.Parameters LeanVM.Extraction.Fast.EvalMat

public section

/-- **The PM-basis runtime on additive-FFT products.** -/
@[expose] def fftRuntime (leafCutoff : ℕ) : PMBasisRuntime K :=
  evalRuntimeP novelTransform fftMulContext fftMulLowContext leafCutoff

/-- It is CompPoly's kernel-leaf runtime on the additive-FFT contexts. -/
theorem fftRuntime_eq (leafCutoff composeLeafCutoff : ℕ) :
    fftRuntime leafCutoff =
      kernelLeafRuntimeWithLowAndCompose fftMulContext fftMulLowContext leafCutoff
        composeLeafCutoff := by
  rw [fftRuntime, evalRuntimeP_eq]
  exact evalRuntime_eq _ _ _ _ _

/-- **CompPoly's PM-basis context on additive-FFT products**: its soundness and shifted
minimality, carried over through `fftRuntime_eq`. -/
@[expose] def fftPMBasisContext (leafCutoff : ℕ) : PMBasisContext K where
  runtime := fftRuntime leafCutoff
  basis := pmBasis (fftRuntime leafCutoff)
  sound := by
    intro problem shift row hrow
    rw [fftRuntime_eq leafCutoff 0] at hrow ⊢
    exact pmBasis_kernelLeaf_approximates fftMulContext fftMulLowContext leafCutoff 0 problem
      shift hrow
  complete_minimal := by
    intro problem shift row hpos hwf happrox hnz hwidth
    rw [fftRuntime_eq leafCutoff 0] at happrox ⊢
    exact pmBasis_kernelLeaf_complete_minimal fftMulContext fftMulLowContext leafCutoff 0 problem
      shift row hpos hwf happrox hnz hwidth

/-- Its basis is CompPoly's kernel-leaf PM-basis, at every composition cutoff. -/
theorem fftPMBasisContext_basis (leafCutoff composeLeafCutoff : ℕ) :
    (fftPMBasisContext leafCutoff).basis =
      (kernelLeafPMBasisContextWithLowAndCompose fftMulContext fftMulLowContext leafCutoff
        composeLeafCutoff).basis := by
  show pmBasis _ = pmBasis _
  rw [fftRuntime_eq leafCutoff composeLeafCutoff]

end

end LeanVM.Extraction.Fast.FFT
