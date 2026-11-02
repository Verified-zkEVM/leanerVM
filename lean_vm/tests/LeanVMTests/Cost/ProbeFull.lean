import LeanVMTests.Cost.ProbeFFT
import LeanVM.Protocol.Extraction.Fast.Extract
import LeanVM.Cost.FastLib

/-!
# Probe: whole approximant-basis interpolations over `K`, compiled (off the chain)

* `approxInterpK`: CompPoly's `approximantBasisInterpolate` (CompPoly,
  `GuruswamiSudan/Interpolation/ApproximantBasis/`; github.com/Verified-zkEVM/CompPoly, Apache-2.0,
  "Copyright (c) 2026 CompPoly Contributors"; compiled, not copied) at lean_vm's
  `approxInterpContext` (Karatsuba, kernel leaf, cutoff 8, the adaptive solver): the moduli, the
  relation matrix, the adaptive partial-linearization loop, the certified solve, the choice of `Q`.
* `targetInterpolate` (a probe's sketch, not proved: the report's change (a), for track a): the same
  positive branch with one certified solve at the bound `W` (`fullWindowExactNullspaceProblem`,
  `pmBasisWithFuelCore` at the target runtime of `ProbeFFT.lean`), filtered, on the FFT contexts.
-/

namespace LeanVMTests.Cost.ProbeFull

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction.Fast CompPoly
open CompPoly.PolynomialMatrix.Approximant CompPoly.GuruswamiSudan CompPoly.PolynomialMatrix
open LeanVM.Extraction.Fast.FFT LeanVMTests.Cost.ProbeFFT

/-- lean_vm's PM-basis context (`approxInterpContext`'s). -/
abbrev pmCtx8 : PMBasisContext K := PolynomialMatrix.Approximant.kernelLeafPMBasisContext karatsubaMulContext 8

-- Staged: each command's heartbeats are its own (one command for the whole interpolation passes
-- the default 200000), the later ones calling the earlier compiled functions.
cost_compile strassenLowK := PolynomialMatrix.mulStrassenWith (F := K)
  (PolynomialMatrix.MulLowContext.fromMulContext karatsubaMulContext)

cost_compile pmBasis8K := pmBasis pmCtx8.runtime

cost_compile filteredK := filteredSolutionBasisViaPMBasis karatsubaMulContext karatsubaModContext pmCtx8

cost_compile gsDataK := ApproximantBasis.buildGSModularDataWithRG (F := K) karatsubaMulContext
  karatsubaModContext

cost_compile approxInterpK := ApproximantBasis.approximantBasisInterpolate
  CPolynomial.VanishingPolynomialContext.direct (CPolynomial.BatchEvalContext.horner K)
  (PolynomialMatrix.Approximant.modularSolutionBasisContextViaPMBasis karatsubaMulContext
      karatsubaModContext
      (PolynomialMatrix.Approximant.kernelLeafPMBasisContext karatsubaMulContext 8))

/-- The certified solve at the bound, on the target runtime, filtered. -/
def targetSolve (equation : ModularEquation K) (shift : Array ℕ) (bound : ℕ) : PolynomialMatrix K :=
  let P := fullWindowExactNullspaceProblem fftModContext equation bound
  let s := exactNullspaceShift shift equation.modularWidth bound
  filterModularSolutionRows fftMulContext fftModContext equation
    (compactNonzeroRows (principalSolutionRows equation.solutionWidth
      (pmBasisWithFuelCore targetRuntime (pmBasisFuel P) P s)))

/-- The positive branch of `approximantBasisPositiveInterpolate` with `targetSolve`. -/
def targetInterpolate (points : Array (K × K)) (params : GSInterpParams) : Option (CBivariate K) :=
  let G := CPolynomial.VanishingPolynomialContext.direct.vanishingPolynomial
    (points.map fun point ↦ point.1)
  let R := CPolynomial.interpolateCoefficientFormWithVanishing (CPolynomial.BatchEvalContext.horner K)
    G points
  let data := ApproximantBasis.buildGSModularDataWithRG fftMulContext fftModContext R G params
  let basis := targetSolve (ApproximantBasis.modularEquation data) data.shift
    params.weightedDegreeBound
  match leastShiftedDegreeChoice? basis data.shift with
  | none => none
  | some choice =>
      if choice.degree ≤ params.weightedDegreeBound then
        ApproximantBasis.normalizeApproximantCandidate? params (CBivariate.ofCoeffRow choice.row)
      else none

cost_compile targetInterpC := targetInterpolate

/-! ## Run tests: lanes of `n` points at `k = 2`, agreement `A` -/

/-- `n` points of distinct abscissas, pseudo-random values. -/
def pts (n : ℕ) : Array (K × K) :=
  Array.ofFn fun v : Fin n ↦ (K.ofBits v.val, K.ofBits ((v.val * 2654435761 + 7) % 1000))

def prm (n A : ℕ) : GSInterpParams := (LeanVM.Extraction.gsParamsFor 2 n A).interp

open MachineEncoding in
def approxRun (n A : ℕ) : Bool × ℕ :=
  check approxInterpK.costDeps approxInterpK.costIdx [encodeValue (pts n), encodeValue (prm n A)]
    (encodeValue (approxInterpContext.interpolate (pts n) (prm n A)))

open MachineEncoding in
def targetRun (n A : ℕ) : Bool × ℕ :=
  check targetInterpC.costDeps targetInterpC.costIdx [encodeValue (pts n), encodeValue (prm n A)]
    (encodeValue (targetInterpolate (pts n) (prm n A)))

#guard (approxRun 16 9).1
#guard (targetRun 16 9).1
#guard (targetInterpolate (pts 16) (prm 16 9)).isSome

-- Prices recorded (dev build; the evaluation takes ≈ 25 min, so not rerun):
-- `(n, A, multiplicity, W, approxInterp price, target price)` =
-- (16, 9, 1, 8, 473640731, 879122165), (16, 8, 1, 7, 421944393, 682745838),
-- (32, 12, 1, 11, 2094554459, 2677896043): at these toy sizes the transforms' fixed costs dominate.

end LeanVMTests.Cost.ProbeFull
