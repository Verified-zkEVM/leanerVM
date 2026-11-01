import LeanVMTests.Cost.Samples
import LeanVM.Cost.Bounds.Samples.AddRaw
import LeanVM.Cost.Bounds.Samples.CommittedLeaves
import LeanVM.Cost.Bounds.Samples.MsStep

/-!
# Tests: the proved bounds against measured prices

The samples' runs on the fixtures of `Cost/Samples.lean`, their prices next to the closed forms
the bounds prove (`LeanVM.Cost.Bounds.Samples`): the bounds hold, and how loose they are.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Cost.Samples LeanVM.Parameters

/-- The price of function `i`'s run on `args` in the program of `deps`. -/
def price (deps : List (ℕ × Term)) (i : ℕ) (args : List Val) : Option ℕ :=
  (evalBody (Program.ofList deps) 100000 i args).map (·.2)

/-! `addRaw` of sizes `3` and `2`: `124`, the bound `44 + 28·3 = 128`. -/
#guard price addRawK.costDeps 3 [Enc.enc polyA, Enc.enc polyB] == some 124
#guard 124 ≤ 44 + 28 * max polyA.size polyB.size

section
open LeanVM.Extraction LeanVM.Extraction.Fast
attribute [local instance] lexOrd

/-! The committed leaves at `w = h = 1` over an index of `2` levels of at most `2` entries:
`10151`, the bound `2·(2·1228 + 617 + 12060 + 8) + 7 = 30289`. -/
#guard price committedLeavesC.costDeps 6
    [Enc.enc toyIndex, Enc.enc (1 : ℕ), Enc.enc (1 : ℕ), Enc.enc rootD] == some 10151
#guard toyIndex.levels.length == 2 && toyIndex.levels.all (·.entries.size ≤ 2)
#guard 10151 ≤ 2 ^ 1 * (2 * LeanVM.Cost.Bounds.Samples.lookupBound toyIndex 2 + 617 * 1 + 12060 +
  8 * 1) + 7

end

/-! One Mulders–Storjohann step on a `2 × 2` matrix of entries of at most `3` coefficients:
`23192`, the bound `2 + 860·6 + 1110·2 + 30·3 + 21100 = 28572`; its field inverse alone `19674`
(the bound `19700`). -/
#guard price msStepK.costDeps 3
    [Enc.enc msMatrix, Enc.enc #[(0 : ℕ), 0], Enc.enc (0 : ℕ), Enc.enc (1 : ℕ)] == some 23192
#guard msMatrix.all fun row ↦ row.size ≤ 2 && row.all (·.val.size ≤ 3)
#guard 23192 ≤ msMatrix.size + 860 * (3 * 2) + 1110 * 2 + 30 * 3 + 21100
#guard price msStepK.costDeps 25 [Enc.enc (K.ofBits 7)] == some 19674

end LeanVMTests.Cost
