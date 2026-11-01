import LeanVM.Cost.Extractor.Decode
import LeanVMTests.Cost.Samples
import LeanVMTests.Extraction.Fast

/-!
# Tests: the compiled decoder runs

The decoder's compiled pieces (`LeanVM.Cost.Extractor`: Mulders–Storjohann's reduction, the
interpolation, the roots in `K`, one lane's Guruswami–Sudan run) compute their functions' values
on small inputs, at the prices recorded here.
-/

namespace LeanVMTests.Cost.Decoder

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast
open LeanVMTests.Extraction LeanVMTests.Cost CompPoly CompPoly.GuruswamiSudan

/-- The value and the price of function `i`'s run on `args` in the program of `deps`. -/
def run (deps : List (ℕ × Term)) (i : ℕ) (args : List Val) : Option (Val × ℕ) :=
  evalBody (Program.ofList deps) 1000000 i args

/-- Sixteen points of distinct abscissas, and the parameters of a lane at `k = 2`, `n = 16`. -/
def pts : Array (K × K) := Array.ofFn fun v : Fin 16 ↦ (K.ofBits v.val, K.ofBits (lcg v.val % 1000))
def prm : GSInterpParams := (gsParamsFor 2 16 9).interp

#guard (run msReduceK.costDeps msReduceK.costIdx [Enc.enc msMatrix, Enc.enc #[(0 : ℕ), 0]]).map
    (·.1) == some (Enc.enc (PolynomialMatrix.muldersStorjohannReduceFast msMatrix #[0, 0]))
#guard (run interpolateDistinctC.costDeps interpolateDistinctC.costIdx
    [Enc.enc pts, Enc.enc prm]).map (·.1) == some (Enc.enc (interpolateDistinct pts prm))
#guard (run rootsInFieldC.costDeps rootsInFieldC.costIdx [Enc.enc rootPoly]).map (·.1) ==
  some (Enc.enc (rootsInFieldFast rootPoly))
#guard (run gsRunDistinctNFC.costDeps gsRunDistinctNFC.costIdx
    [Enc.enc pts, Enc.enc prm, Enc.enc (3 : ℕ)]).map (·.1) ==
  some (Enc.enc (gsRunDistinctNF pts prm 3))

end LeanVMTests.Cost.Decoder
