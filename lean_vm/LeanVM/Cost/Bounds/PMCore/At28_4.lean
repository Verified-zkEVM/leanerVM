module

public import LeanVM.Cost.Bounds.PMCore.Leaf
public import LeanVM.Cost.Bounds.PMBasis.At28_4

/-!
# Bounds: the compiled PM-basis core within the model, and at `(28, 4)`

* **`pmCoreC_cost_le_model`**: the compiled core (`pmCoreC` at CompPoly's fuel) on a problem of
  the invariant (`CoreInv`) is at most the model's tree `pmTree 1 (pmLeafPrice p r)
  (pmNodePrice p r m) (maxOrder problem)` (`Bounds/PMBasis/Defs.lean`), given the two products'
  prices (track fft's) and the leaf's price within `pmLeafPrice p r − 18·m − 60`;
* **`pmCoreC_cost_28_4`**: at `(28, 4)` (`2077` rows of width `415`, maximal order at most
  `415·2^26 + W + 2`, the margin prices): at most `19532624819874717385344824 ≈ 2^84.01` steps,
  the leaf's price proved (`leafCost`, `Leaf.lean`; `leafBound_28_4`): no hypothesis left but the
  problem's invariant.
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Extractor LeanVM.Parameters LeanVM.Cost.Bounds.PMBasis
open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

variable (P : MachineProgram)

/-- **The margin prices fit track fft's proved products.** -/
theorem fftPricesOK_margin : PMFFT.FFTPricesOK marginPrices := by decide +kernel

/-- **The leaf's proved price within the model's** at `(28, 4)`:
`leafBound 2077 415 = 148285991936870 ≈ 2^47.08`. -/
theorem leafBound_28_4 : leafBound 2077 415 ≤ pmLeafPrice marginPrices 2077 - 18 * 415 - 60 := by
  decide +kernel

/-- **The compiled PM-basis core within the model's tree.** -/
theorem pmCoreC_cost_le_model (hP : Includes P pmCoreC.costDeps) {p : PMPrices}
    (hp : PMFFT.FFTPricesOK p) {r m SB : ℕ}
    (hr : 2 ≤ r) (hm : m ≤ r) (hr30 : r < 2 ^ 30) (hSB : SB < 2 ^ 39)
    (hL : LeafCost P r m SB (pmLeafPrice p r - 18 * m - 60)) (hLm : 18 * m + 60 ≤ pmLeafPrice p r)
    (problem : XAdicProblem K) (shift : Array ℕ) (hI : CoreInv r m SB problem shift) :
    machineCost P pmCoreC.costIdx
        [encodeValue (pmBasisFuel problem), encodeValue problem, encodeValue shift] ≤
      pmTree 1 (pmLeafPrice p r) (pmNodePrice p r m) (maxOrder problem) := by
  have h := pmCoreC_cost P hP hp hr hm hr30 hSB hL problem shift hI
  exact h.trans (pmTree_mono_leaf 1 _ (by omega) _)

/-- **The compiled PM-basis core at `(28, 4)`**: on the lane's X-adic problem (`2077` rows of
width `415`, `CoreInv`, maximal order at most `pmOrder_28_4 = 415·2^26 + W + 2`), at the margin
prices, at most `19532624819874717385344824 ≈ 2^84.01` steps. -/
theorem pmCoreC_cost_28_4 (hP : Includes P pmCoreC.costDeps)
    {SB : ℕ} (hSB : SB < 2 ^ 39) (problem : XAdicProblem K) (shift : Array ℕ) (hI : CoreInv 2077 415 SB problem shift)
    (ho : maxOrder problem ≤ pmOrder_28_4) :
    machineCost P pmCoreC.costIdx
        [encodeValue (pmBasisFuel problem), encodeValue problem, encodeValue shift] ≤
      19532624819874717385344824 := by
  have hL : LeafCost P 2077 415 SB (pmLeafPrice marginPrices 2077 - 18 * 415 - 60) :=
    fun prob sh hIp h1 ↦ (leafCost P hP (by norm_num) (by norm_num) hSB prob sh hIp h1).trans
      leafBound_28_4
  have h := pmCoreC_cost_le_model P hP fftPricesOK_margin (by norm_num) (by norm_num)
    (by norm_num) hSB hL (by decide) problem shift hI
  rw [← pmTree_28_4]
  exact h.trans (pmTree_mono 1 _ (pmNodePrice_mono marginPrices 2077 415) _ _ ho)

end

end LeanVM.Cost.Bounds.PMCore
