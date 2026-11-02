module

public import LeanVM.Protocol.Extraction.Fast.FFT.Additive
public import LeanVM.Protocol.Extraction.Fast.EvalMat.Runtime

/-!
# PM-basis on additive-FFT products over `K`

`fftRuntime leafCutoff`: the evaluation-domain PM-basis runtime (`EvalMat.evalRuntime`) on the
additive-FFT transform (`fftTransform`), with the additive-FFT product and truncated product as
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
  evalRuntime fftTransform fftMulContext fftMulLowContext leafCutoff

/-- It is CompPoly's kernel-leaf runtime on the additive-FFT contexts. -/
theorem fftRuntime_eq (leafCutoff composeLeafCutoff : ℕ) :
    fftRuntime leafCutoff =
      kernelLeafRuntimeWithLowAndCompose fftMulContext fftMulLowContext leafCutoff
        composeLeafCutoff :=
  evalRuntime_eq _ _ _ _ _

/-- **CompPoly's PM-basis context on additive-FFT products.** -/
@[expose] def fftPMBasisContext (leafCutoff : ℕ) : PMBasisContext K :=
  evalPMBasisContext fftTransform fftMulContext fftMulLowContext leafCutoff

end

end LeanVM.Extraction.Fast.FFT
