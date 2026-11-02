import LeanVMTests.Cost.ProbeWin
import LeanVM.Protocol.Extraction.Fast.Extract

/-!
# Probe: CompPoly's whole approximant-basis interpolation over `K`, compiled

`approximantBasisInterpolate` (CompPoly, `GuruswamiSudan/Interpolation/ApproximantBasis/`;
github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly Contributors";
compiled, not copied) at lean_vm's `approxInterpContext` (Karatsuba, kernel leaf, cutoff 8): the
moduli, the relation matrix, the adaptive partial-linearization loop, the certified solve, the
choice of `Q`. The new interpolation keeps all but the solver's loop.
-/

namespace LeanVMTests.Cost.ProbeFull

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction.Fast CompPoly
open CompPoly.PolynomialMatrix.Approximant CompPoly.GuruswamiSudan

cost_compile approxInterpK := ApproximantBasis.approximantBasisInterpolate
  CPolynomial.VanishingPolynomialContext.direct (CPolynomial.BatchEvalContext.horner K)
  (PolynomialMatrix.Approximant.modularSolutionBasisContextViaPMBasis karatsubaMulContext
      karatsubaModContext
      (PolynomialMatrix.Approximant.kernelLeafPMBasisContext karatsubaMulContext 8))

end LeanVMTests.Cost.ProbeFull
