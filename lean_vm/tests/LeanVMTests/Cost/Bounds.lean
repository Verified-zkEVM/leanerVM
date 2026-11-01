import LeanVMTests.Cost.Samples
import LeanVM.Cost.Bounds.Decoder.MsReduce

/-!
# Tests: the proved bounds against measured prices

A run on the fixtures of `Cost/Samples.lean`, its price next to the closed form the bound proves:
the bound holds, and how loose it is.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters

/-- The price of function `i`'s run on `args` in the program of `deps`. -/
def price (deps : List (ℕ × Term)) (i : ℕ) (args : List Val) : Option ℕ :=
  (evalBody (Program.ofList deps) 100000 i args).map (·.2)

/-! One Mulders–Storjohann step (`stepFastC_cost`) on a `2 × 2` matrix of entries of at most `3`
coefficients: `23028`, the bound `2 + 740·6 + 970·2 + 30·3 + 21100 = 27572`; its field inverse
alone `19674` (the bound `invK_cost`, `19676`). -/
#guard price msStepDeps msStepIdx
    [Enc.enc msMatrix, Enc.enc #[(0 : ℕ), 0], Enc.enc (0 : ℕ), Enc.enc (1 : ℕ)] == some 23028
#guard msMatrix.all fun row ↦ row.size ≤ 2 && row.all (·.val.size ≤ 3)
#guard 23028 ≤ msMatrix.size + 740 * (3 * 2) + 970 * 2 + 30 * 3 + 21100
#guard price msStepDeps LeanVM.Cost.Auto.BF64.invItohTsujii.c33.costIdx
    [Enc.enc (K.ofBits 7)] == some 19674

end LeanVMTests.Cost
