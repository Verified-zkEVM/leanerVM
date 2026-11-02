import LeanVM.Cost.Extractor.PMLane
import LeanVMTests.Extraction.LanePM

/-!
# Tests: the lanes' new interpolation, compiled on the chain

The functions of `Cost/Extractor/PM*.lean` (the additive-FFT product and its plan, the
evaluation-domain matrix products, the ordered-weak-Popov PM-basis, the certified solve, the
approximant-basis interpolation and the lane runner on `pmSolver`) compute their sources' values
on small inputs; their prices on a few sizes, for the per-operation constants.
-/

namespace LeanVMTests.Cost.PMChain

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast
open LeanVM.Extraction.Fast.FFT CompPoly CompPoly.PolynomialMatrix.Approximant
open MachineEncoding

def run (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody (MachineProgram.ofList deps) 1000000000 i args

/-- `(the value is v, the price)` of function `i` on `args`. -/
def check (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) (v : MachineValue) : Bool × ℕ :=
  match run deps i args with
  | some (w, c) => (w == v, c)
  | none => (false, 0)

def rnd (s : ℕ) : K := K.ofBits ((s * 2654435761 + 12345) % 4294967291)

/-- A pseudo-random polynomial of `d` coefficients. -/
def poly (s d : ℕ) : CPolynomial K := CPolynomial.ofArray (Array.ofFn fun j : Fin d ↦ rnd (s * 1000 + j.val))

/-- An `r × c` matrix of polynomials of `d` coefficients. -/
def mat (s r c d : ℕ) : PolynomialMatrix K :=
  Array.ofFn fun i : Fin r ↦ Array.ofFn fun j : Fin c ↦ poly (s * 10000 + i.val * 100 + j.val) d

def prob (s r c d : ℕ) (o : Array ℕ) : XAdicProblem K := { orders := o, matrix := mat s r c d }

/-- A monic polynomial of degree `d`. -/
def monic (s d : ℕ) : CPolynomial K := CPolynomial.ofArray ((poly s d).val.push 1)

/-- A modular equation: `r` coordinates, `c` columns, moduli of degree `d`, entries below. -/
def meq (s r c d : ℕ) : ModularEquation K :=
  { moduli := Array.ofFn fun j : Fin c ↦ monic (s + j.val) d, matrix := mat s r c d }

/-! ## Values -/

#guard (check mkPlanC.costDeps mkPlanC.costIdx [encodeValue (4 : ℕ)] (encodeValue (mkPlan 4))).1
#guard (check planFwdPolyC.costDeps planFwdPolyC.costIdx [encodeValue (mkPlan 4), encodeValue (poly 1 16)]
  (encodeValue (planFwdPoly (mkPlan 4) (poly 1 16)))).1
#guard (check planInvPolyC.costDeps planInvPolyC.costIdx
  [encodeValue (mkPlan 4), encodeValue (planFwdPoly (mkPlan 4) (poly 1 16))]
  (encodeValue (poly 1 16))).1
#guard (check toNovelFastC.costDeps toNovelFastC.costIdx [encodeValue (mkPlan 4), encodeValue (poly 1 16).val]
  (encodeValue (toNovelFast (mkPlan 4) (poly 1 16).val))).1
#guard (check fromNovelFastC.costDeps fromNovelFastC.costIdx [encodeValue (mkPlan 4), encodeValue (poly 1 16).val]
  (encodeValue (fromNovelFast (mkPlan 4) (poly 1 16).val))).1
-- below the schedule's `4096`, Karatsuba's product; above, the transform
#guard (check mulFFTC.costDeps mulFFTC.costIdx [encodeValue (poly 1 100), encodeValue (poly 2 90)]
  (encodeValue (poly 1 100 * poly 2 90))).1
#guard (check mulFFTC.costDeps mulFFTC.costIdx [encodeValue (poly 1 4100), encodeValue (poly 2 4100)]
  (encodeValue (poly 1 4100 * poly 2 4100))).1
#guard (check mulEvalPC.costDeps mulEvalPC.costIdx [encodeValue (mat 1 3 2 3), encodeValue (mat 2 2 4 5)]
  (encodeValue (mulEvalP novelTransform fftMulContext (mat 1 3 2 3) (mat 2 2 4 5)))).1
#guard (check mulTruncEvalPC.costDeps mulTruncEvalPC.costIdx
  [encodeValue #[2, 5, 1, 7], encodeValue (mat 1 3 2 3), encodeValue (mat 2 2 4 5)]
  (encodeValue (mulTruncEvalP novelTransform fftMulContext #[2, 5, 1, 7] (mat 1 3 2 3) (mat 2 2 4 5)))).1
#guard (check popovLeafC.costDeps popovLeafC.costIdx [encodeValue (prob 1 3 2 2 #[1, 1]), encodeValue #[0, 0, 0]]
  (encodeValue (Popov.popovLeafBasis (prob 1 3 2 2 #[1, 1]) #[0, 0, 0]))).1
#guard (check pmCoreC.costDeps pmCoreC.costIdx
  [encodeValue (pmBasisFuel (prob 1 3 2 4 #[3, 2])), encodeValue (prob 1 3 2 4 #[3, 2]), encodeValue #[0, 0, 0]]
  (encodeValue (pmBasisWithFuelCore (popovEvalRuntime novelTransform fftMulContext fftMulLowContext 1)
    (pmBasisFuel (prob 1 3 2 4 #[3, 2])) (prob 1 3 2 4 #[3, 2]) #[0, 0, 0]))).1
#guard (check certifiedSolveC.costDeps certifiedSolveC.costIdx
  [encodeValue (meq 2 3 2 2), encodeValue #[0, 1, 2], encodeValue (3 : ℕ)]
  (encodeValue (certifiedSolutionBasis fftModContext
    (popovEvalPMBasisContext novelTransform fftMulContext fftMulLowContext 1) (meq 2 3 2 2) #[0, 1, 2]
    3))).1
#guard (certifiedSolutionBasis fftModContext
    (popovEvalPMBasisContext novelTransform fftMulContext fftMulLowContext 1) (meq 2 3 2 2) #[0, 1, 2]
    3).size > 0

open LeanVMTests.Extraction.LanePM in
#guard (check interpolatePMC.costDeps interpolatePMC.costIdx
  [encodeValue (wordPoints 16 5), encodeValue (gsParamsFor 4 16 10).interp]
  (encodeValue (interpolateDistinctWith pmSolver (wordPoints 16 5) (gsParamsFor 4 16 10).interp))).1

open LeanVMTests.Extraction.LanePM in
#guard (check gsRunPMC.costDeps gsRunPMC.costIdx
  [encodeValue (wordPoints 16 5), encodeValue (gsParamsFor 4 16 10).interp, encodeValue (6 : ℕ)]
  (encodeValue (gsRunDistinctWith pmSolver (wordPoints 16 5) (gsParamsFor 4 16 10).interp 6))).1

/-! ## Prices -/

def priceOf (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) : ℕ :=
  ((run deps i args).map (·.2)).getD 0

-- `(j, mkPlan, planFwdPoly, planInvPoly, j·2^j)` at `2^j` points.
#eval [4, 6, 8, 10].map fun j ↦
  (j, priceOf mkPlanC.costDeps mkPlanC.costIdx [encodeValue j],
    priceOf planFwdPolyC.costDeps planFwdPolyC.costIdx [encodeValue (mkPlan j), encodeValue (poly 1 (2 ^ j))],
    priceOf planInvPolyC.costDeps planInvPolyC.costIdx
      [encodeValue (mkPlan j), encodeValue (planFwdPoly (mkPlan j) (poly 1 (2 ^ j)))],
    j * 2 ^ j)

-- `(j, toNovelFast, fromNovelFast, planFwd, planInv)` at `2^j` points (measured once at `j = 12`:
-- `51902123, 51028000, 10982697, 9192390`).
#eval [6, 8, 10].map fun j ↦
  (j, priceOf toNovelFastC.costDeps toNovelFastC.costIdx [encodeValue (mkPlan j), encodeValue (poly 1 (2 ^ j)).val],
    priceOf fromNovelFastC.costDeps fromNovelFastC.costIdx [encodeValue (mkPlan j), encodeValue (poly 1 (2 ^ j)).val],
    priceOf planFwdC.costDeps planFwdC.costIdx [encodeValue (mkPlan j), encodeValue (poly 1 (2 ^ j)).val],
    priceOf planInvC.costDeps planInvC.costIdx [encodeValue (mkPlan j), encodeValue (poly 1 (2 ^ j)).val])

-- `(d, mulFFT)` at `d` coefficients each, Karatsuba's (measured once: the transform on `2^14`
-- points at `4100` coefficients each, `978055656`).
#eval [2000].map fun d ↦
  (d, priceOf mulFFTC.costDeps mulFFTC.costIdx [encodeValue (poly 1 d), encodeValue (poly 2 d)])

-- `(n, d, mulEvalP, n³·2^j)`, `n × n` matrices of `d` coefficients.
#eval [(2, 8), (4, 8), (4, 32), (8, 8)].map fun (n, d) ↦
  (n, d, priceOf mulEvalPC.costDeps mulEvalPC.costIdx [encodeValue (mat 1 n n d), encodeValue (mat 2 n n d)],
    n ^ 3 * 2 ^ (Nat.log2 (2 * d - 2) + 1))

-- `(r, c, popovLeaf at order 1, r³)`.
#eval [(4, 1), (8, 2), (16, 4)].map fun (r, c) ↦
  (r, c, priceOf popovLeafC.costDeps popovLeafC.costIdx
    [encodeValue (prob 1 r c 2 (Array.replicate c 1)), encodeValue (Array.replicate r 0)], r ^ 3)

-- `(r, c, order, the PM-basis core)`.
#eval [(2, 1, 4), (4, 2, 4), (4, 2, 8), (4, 2, 16)].map fun (r, c, o) ↦
  (r, c, o, priceOf pmCoreC.costDeps pmCoreC.costIdx
    [encodeValue (pmBasisFuel (prob 1 r c o (Array.replicate c o))), encodeValue (prob 1 r c o (Array.replicate c o)),
      encodeValue (Array.replicate r 0)])

end LeanVMTests.Cost.PMChain
