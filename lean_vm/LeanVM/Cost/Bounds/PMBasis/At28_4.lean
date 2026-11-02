module

public import LeanVM.Cost.Bounds.PMBasis.Recursion
public import LeanVM.Cost.Bounds.PMBasis.Values

/-!
# PM-basis's price at `(28, 4)`

The model (`Bounds/PMBasis/Defs.lean`) at `(28, 4)` (`Bounds/PMBasis/Values.lean`):

* **`pmTree_28_4`**: the recursion's tree at the measured prices with their margin
  (`marginPrices`), `19532624819874717385344824 ≈ 2^84.01` steps per lane (at the measured prices
  themselves `≈ 2^82.94`, `pmTree_28_4_measured`);
  **`pmBasisPrice_28_4`** with the fuel's fold; **`pmTree_28_4_le_levels`**: the per-level closed
  form `≈ 2^84.05` above it (`pmTree_le_levels`);
* **`pmBasisFuel_price_28_4`**: any price of CompPoly's recursion (the compiled core's, once
  compiled) whose leaves and nodes are within the model's prices, on a runtime of leaf cutoff `1`
  and a problem of maximal order at most `415·2^26 + W + 2`, is at most that number.
-/

namespace LeanVM.Cost.Bounds.PMBasis

open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

/-- **The recursion's tree at `(28, 4)`**: `≈ 2^84.01` steps per lane. -/
theorem pmTree_28_4 :
    pmTree 1 (pmLeafPrice marginPrices pmRows_28_4) (pmNodePrice marginPrices pmRows_28_4 pmCols_28_4)
      pmOrder_28_4 = 19532624819874717385344824 := by
  have h := pmTreePair_eq 1 (pmLeafPrice marginPrices pmRows_28_4)
    (pmNodePrice marginPrices pmRows_28_4 pmCols_28_4) 36 pmOrder_28_4 pmOrder_28_4_bounds.2
  rw [pmTreePair_28_4] at h
  exact (congrArg Prod.fst h).symm

/-- **The recursion's tree at `(28, 4)`, the measured prices**: `≈ 2^82.94` steps per lane. -/
theorem pmTree_28_4_measured :
    pmTree 1 (pmLeafPrice measuredPrices pmRows_28_4)
      (pmNodePrice measuredPrices pmRows_28_4 pmCols_28_4) pmOrder_28_4 =
      9303084148594118146442494 := by
  have h := pmTreePair_eq 1 (pmLeafPrice measuredPrices pmRows_28_4)
    (pmNodePrice measuredPrices pmRows_28_4 pmCols_28_4) 36 pmOrder_28_4 pmOrder_28_4_bounds.2
  rw [pmTreePair_28_4_measured] at h
  exact (congrArg Prod.fst h).symm

/-- **PM-basis's whole price at `(28, 4)`** (model): `≈ 2^84.01` steps per lane. -/
theorem pmBasisPrice_28_4 :
    pmBasisPrice marginPrices pmRows_28_4 pmCols_28_4 pmOrder_28_4 =
      64 * pmCols_28_4 + 100 + 19532624819874717385344824 := by
  rw [pmBasisPrice, pmTreeEval_eq, pmTree_28_4]

/-- The per-level closed form at `(28, 4)` bounds the tree (`0.07` bit looser). -/
theorem pmTree_28_4_le_levels :
    pmTree 1 (pmLeafPrice marginPrices pmRows_28_4) (pmNodePrice marginPrices pmRows_28_4 pmCols_28_4)
      pmOrder_28_4 ≤ 20118211812944507931745704 := by
  rw [← pmLevels_28_4]
  have := pmOrder_28_4_bounds
  exact pmTree_le_levels 1 _ (pmNodePrice_mono marginPrices pmRows_28_4 pmCols_28_4) 36
    pmOrder_28_4 (by omega) (by omega)

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- **CompPoly's recursion at `(28, 4)`, priced**: on a runtime of leaf cutoff `1` (the target
`popovRuntime mulCtx lowCtx 1 c`), a price `T` whose leaves are within `pmLeafPrice` and whose
nodes are within `pmNodePrice` and their children's (the hypotheses of
`pmBasisWithFuelCore_price_le`), on a problem of maximal order at most `415·2^26 + W + 2`, at
CompPoly's fuel `pmBasisFuel` (where the target's core is its `pmBasis`): at most
`19532624819874717385344824 ≈ 2^84.01`. -/
theorem pmBasisFuel_price_28_4 (rt : PMBasisRuntime F) (hcut : rt.leafCutoff = 1)
    (T : ℕ → XAdicProblem F → Array ℕ → ℕ) (Inv : XAdicProblem F → Array ℕ → Prop)
    (hleaf : ∀ fuel problem shift, Inv problem shift → maxOrder problem ≤ fuel + 1 →
      (maxOrder problem ≤ rt.leafCutoff ∨ maxOrder problem ≤ 1) →
        T fuel problem shift ≤ pmLeafPrice marginPrices pmRows_28_4)
    (hnode : ∀ fuel problem shift, Inv problem shift → maxOrder problem ≤ fuel + 2 →
      rt.leafCutoff < maxOrder problem → 2 ≤ maxOrder problem →
      Inv (pmLower problem) shift ∧
        Inv (pmResidual rt fuel problem shift) (pmShifted rt fuel problem shift) ∧
        T (fuel + 1) problem shift ≤
          pmNodePrice marginPrices pmRows_28_4 pmCols_28_4 (maxOrder problem) +
            T fuel (pmLower problem) shift +
            T fuel (pmResidual rt fuel problem shift) (pmShifted rt fuel problem shift))
    (problem : XAdicProblem F) (shift : Array ℕ) (hI : Inv problem shift)
    (ho : maxOrder problem ≤ pmOrder_28_4) :
    T (pmBasisFuel problem) problem shift ≤ 19532624819874717385344824 := by
  have h := pmBasisFuel_price_le rt T _ _ Inv hleaf hnode problem shift hI
  rw [hcut] at h
  rw [← pmTree_28_4]
  exact h.trans (pmTree_mono 1 _ (pmNodePrice_mono marginPrices pmRows_28_4 pmCols_28_4) _ _ ho)

end

end LeanVM.Cost.Bounds.PMBasis
