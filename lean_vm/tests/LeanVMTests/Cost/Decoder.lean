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
def run (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody (MachineProgram.ofList deps) 1000000 i args

/-- Sixteen points of distinct abscissas, and the parameters of a lane at `k = 2`, `n = 16`. -/
def pts : Array (K × K) := Array.ofFn fun v : Fin 16 ↦ (K.ofBits v.val, K.ofBits (lcg v.val % 1000))
def prm : GSInterpParams := (gsParamsFor 2 16 9).interp

#guard (run msReduceK.costDeps msReduceK.costIdx [MachineEncoding.encodeValue msMatrix, MachineEncoding.encodeValue #[(0 : ℕ), 0]]).map
    (·.1) == some (MachineEncoding.encodeValue (PolynomialMatrix.muldersStorjohannReduceFast msMatrix #[0, 0]))
#guard (run interpolateDistinctC.costDeps interpolateDistinctC.costIdx
    [MachineEncoding.encodeValue pts, MachineEncoding.encodeValue prm]).map (·.1) == some (MachineEncoding.encodeValue (interpolateDistinct pts prm))
#guard (run rootsInFieldC.costDeps rootsInFieldC.costIdx [MachineEncoding.encodeValue rootPoly]).map (·.1) ==
  some (MachineEncoding.encodeValue (rootsInFieldFast rootPoly))
#guard (run gsRunDistinctNFC.costDeps gsRunDistinctNFC.costIdx
    [MachineEncoding.encodeValue pts, MachineEncoding.encodeValue prm, MachineEncoding.encodeValue (3 : ℕ)]).map (·.1) ==
  some (MachineEncoding.encodeValue (gsRunDistinctNF pts prm 3))

/-! Roth–Ruckenstein's substitution by the butterfly (`substituteBF`, compiled on demand as
`substituteBF.c192`): its value is `substituteFast`'s, and its price, measured. One more
coefficient per row costs `≈ 290` steps per scaled row addition (`axpyRow`: the scaling, the raw
sum, one trim) and `28` per row (the shift by `X^t`); the proved bound (`substituteBFC_cost`)
charges `324` per row and level. -/

/-- The butterfly's price on `ny` rows of `nx` random coefficients. -/
def bfPrice (nx ny : ℕ) : Option ℕ :=
  (run LeanVM.Cost.Auto.LeanVM.Extraction.Fast.substituteBF.c192.costDeps
    LeanVM.Cost.Auto.LeanVM.Extraction.Fast.substituteBF.c192.costIdx
    [MachineEncoding.encodeValue (randomBivariate 7 nx ny), MachineEncoding.encodeValue (K.ofBits 5)]).map
    Prod.snd

/-- The scaled row additions of the butterfly on `n` rows: the bits set below `n`. -/
def bfOps (n : ℕ) : ℕ := ((List.range n).map fun y ↦ (Nat.toDigits 2 y).count '1').sum

#guard (List.range 3).all fun s ↦
  let Q := randomBivariate s 30 33
  (run LeanVM.Cost.Auto.LeanVM.Extraction.Fast.substituteBF.c192.costDeps
    LeanVM.Cost.Auto.LeanVM.Extraction.Fast.substituteBF.c192.costIdx
    [MachineEncoding.encodeValue Q, MachineEncoding.encodeValue (K.ofBits (lcg s))]).map (·.1) ==
    some (MachineEncoding.encodeValue (substituteFast Q (K.ofBits (lcg s))))
#guard bfPrice 100 33 == some 2472528
#guard bfPrice 200 33 == some 4917528
-- per extra coefficient: `81` additions (`bfOps 33`) at `≈ 290`, `33` rows at `28`
#guard bfOps 33 == 81 && (4917528 - 2472528) / 100 == 24450 && (24450 - 28 * 33) / 81 == 290

end LeanVMTests.Cost.Decoder
