import LeanVM.Cost.ProbeLib
import LeanVM.Protocol.Extraction.Fast.FFT.PMBasis
import LeanVM.Protocol.Extraction.Fast.PMBasis.PopovCore

/-!
# Probe: the target interpolation's pieces, compiled (off the chain)

The additive-FFT product (`FFT/`: `toNovel`, `fromNovel`, `novelFwdPoly`, `novelInvPoly`, `mulFFT`),
the evaluation-domain matrix products over it (`EvalMat/`: `mulEval`, `mulTruncEval` at
`fftTransform`), the leaf sorted by pivot (`PMBasis/PopovLeaf.lean`: `popovLeafBasis`) and the
recursion at the target runtime: `popovRuntime`'s leaf with the evaluation-domain products,
leaf cutoff 1 (`pmBasisWithFuelCore`). Nothing of the extractor's chain is imported: everything is
compiled here, through `ProbeLib`'s rewrites (products and sums trimmed once).
-/

namespace LeanVMTests.Cost.ProbeFFT

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction.Fast CompPoly
open CompPoly.PolynomialMatrix.Approximant LeanVM.Extraction.Fast.FFT LeanVM.Extraction.Fast.EvalMat
open LeanVM.Extraction.Fast.Popov

cost_compile toNovelC := LeanVM.Extraction.Fast.FFT.toNovel

cost_compile fromNovelC := LeanVM.Extraction.Fast.FFT.fromNovel

cost_compile mulFFTC := mulFFT

cost_compile mulEvalC := mulEval fftTransform fftMulContext

cost_compile mulTruncEvalC := mulTruncEval fftTransform fftMulContext

cost_compile popovLeafC := popovLeafBasis (F := K)

/-- **The target runtime**: the leaf sorted by pivot (`popovRuntime`'s), the evaluation-domain
products over the additive FFT (`evalRuntime fftTransform`'s), leaf cutoff 1. -/
abbrev targetRuntime : PMBasisRuntime K where
  mulContext := fftMulContext
  lowMulContext := fftMulLowContext
  composeBasis := mulEval fftTransform fftMulContext
  residualProduct := mulTruncEval fftTransform fftMulContext
  leafCutoff := 1
  leafBasis := popovLeafBasis

cost_compile targetCoreC := pmBasisWithFuelCore targetRuntime

/-! ## Run tests -/

def run (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody (MachineProgram.ofList deps) 1000000000 i args

def rnd (s : ℕ) : K := K.ofBits ((s * 2654435761 + 12345) % 4294967291)

def poly (s d : ℕ) : CPolynomial K := CPolynomial.ofArray (Array.ofFn fun j : Fin d ↦ rnd (s * 1000 + j.val))

def mat (s r c d : ℕ) : PolynomialMatrix K :=
  Array.ofFn fun i : Fin r ↦ Array.ofFn fun j : Fin c ↦ poly (s * 10000 + i.val * 100 + j.val) d

/-- `(value agrees, price)` of compiled function `i` on `args` against `v`. -/
def check (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) (v : MachineValue) : Bool × ℕ :=
  match run deps i args with
  | some (w, c) => (w == v, c)
  | none => (false, 0)

open MachineEncoding in
#guard (check toNovelC.costDeps toNovelC.costIdx [encodeValue (3 : ℕ), encodeValue (poly 1 8).val]
  (encodeValue (FFT.toNovel 3 (poly 1 8).val))).1

open MachineEncoding in
#guard (check fromNovelC.costDeps fromNovelC.costIdx [encodeValue (3 : ℕ), encodeValue (poly 1 8).val]
  (encodeValue (FFT.fromNovel 3 (poly 1 8).val))).1

open MachineEncoding in
/-- The FFT product at `d` coefficients each. -/
def fftRun (d : ℕ) : Bool × ℕ :=
  check mulFFTC.costDeps mulFFTC.costIdx [encodeValue (poly 1 d), encodeValue (poly 2 d)]
    (encodeValue (poly 1 d * poly 2 d))

open MachineEncoding in
def evalRun (A B : PolynomialMatrix K) : Bool × ℕ :=
  check mulEvalC.costDeps mulEvalC.costIdx [encodeValue A, encodeValue B]
    (encodeValue (mulEval fftTransform fftMulContext A B))

open MachineEncoding in
def truncRun (o : Array ℕ) (A B : PolynomialMatrix K) : Bool × ℕ :=
  check mulTruncEvalC.costDeps mulTruncEvalC.costIdx [encodeValue o, encodeValue A, encodeValue B]
    (encodeValue (mulTruncEval fftTransform fftMulContext o A B))

open MachineEncoding in
def leafRun (P : XAdicProblem K) (shift : Array ℕ) : Bool × ℕ :=
  check popovLeafC.costDeps popovLeafC.costIdx [encodeValue P, encodeValue shift]
    (encodeValue (popovLeafBasis P shift))

open MachineEncoding in
def coreRun (P : XAdicProblem K) (shift : Array ℕ) : Bool × ℕ :=
  check targetCoreC.costDeps targetCoreC.costIdx
    [encodeValue (pmBasisFuel P), encodeValue P, encodeValue shift]
    (encodeValue (pmBasisWithFuelCore targetRuntime (pmBasisFuel P) P shift))

def prob (s r c d : ℕ) (o : Array ℕ) : XAdicProblem K := { orders := o, matrix := mat s r c d }

#guard (fftRun 40).1
#guard (evalRun (mat 1 3 2 3) (mat 2 2 4 5)).1
#guard (truncRun #[2, 5, 1, 7] (mat 1 3 2 3) (mat 2 2 4 5)).1
#guard (leafRun (prob 1 3 2 2 #[1, 1]) #[0, 0, 0]).1
#guard (leafRun (prob 3 4 2 3 #[1, 1]) #[5, 0, 2, 1]).1
#guard (coreRun (prob 1 3 2 4 #[3, 2]) #[0, 0, 0]).1
#guard (coreRun (prob 2 4 1 5 #[6]) #[0, 2, 4, 6]).1


/-! ## Prices -/

cost_compile karatsubaC := @LeanVM.Extraction.Fast.karatsuba K _ _ _

open MachineEncoding in
def priceOf (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) : ℕ :=
  ((run deps i args).map (·.2)).getD 0

open MachineEncoding in
-- `(j, toNovel, fromNovel, novelFwd j 0, j·2^j)`: the conversions and the transform on `2^j`.
#eval [4, 6, 8, 10].map fun j ↦
  (j, priceOf toNovelC.costDeps toNovelC.costIdx [encodeValue j, encodeValue (poly 1 (2 ^ j)).val],
    priceOf fromNovelC.costDeps fromNovelC.costIdx [encodeValue j, encodeValue (poly 1 (2 ^ j)).val],
    j * 2 ^ j)

open MachineEncoding in
-- `(d, FFT product, Karatsuba)` at `d` coefficients each.
#eval [1100, 2100].map fun d ↦
  (d, (fftRun d), priceOf karatsubaC.costDeps karatsubaC.costIdx
    [encodeValue (64 : ℕ), encodeValue (poly 1 d), encodeValue (poly 2 d)])

-- `(n, d, mulEval price, n³·2^j pointwise products)`, `n × n` matrices of `d` coefficients.
#eval [(2, 8), (4, 8), (4, 32), (8, 8)].map fun (n, d) ↦
  (n, d, (evalRun (mat 1 n n d) (mat 2 n n d)), n ^ 3 * 2 ^ (Nat.log2 (2 * d - 2) + 1))

-- `(r, c, popovLeaf price at order 1, r³)`.
#eval [(4, 1), (8, 2), (16, 4), (32, 8)].map fun (r, c) ↦
  (r, c, (leafRun (prob 1 r c 2 (Array.replicate c 1)) (Array.replicate r 0)).2, r ^ 3)

-- `(r, c, order, target core price)`.
#eval [(2, 1, 4), (4, 2, 4), (4, 2, 8), (4, 2, 16), (8, 4, 8)].map fun (r, c, o) ↦
  (r, c, o, (coreRun (prob 1 r c o (Array.replicate c o)) (Array.replicate r 0)).2)

end LeanVMTests.Cost.ProbeFFT
