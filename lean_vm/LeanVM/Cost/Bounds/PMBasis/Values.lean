module

public import LeanVM.Cost.Bounds.PMBasis.Defs

/-!
# PM-basis's price at `(28, 4)`: the numbers, by kernel evaluation

The model of `Bounds/PMBasis/Defs.lean` at the worst shape `(μ, R) = (28, 4)` (`k = 2^22`,
`n = 2^26`, multiplicity `415`, list size `ℓ = 1661`, `W = 6968845169`): the windowed X-adic
problem of `r = ℓ + 1 + 415 = 2077` rows and `415` columns, orders `deg M_b + W + 2`, the largest
`415·2^26 + W + 2 = 34819023731 ≈ 2^35.02` (`pmOrder_28_4`; `gsProblem_maxOrder`,
`laneProblem_28_4`), at the probes' measured prices (`measuredPrices`) and at those with a margin
of `5/4` (`marginPrices`).

Only the evaluations are here (this file imports only the definitions it evaluates); the
statements about `pmTree` are in `Bounds/PMBasis/At28_4.lean`.
-/

namespace LeanVM.Cost.Bounds.PMBasis

public section

/-- The rows at `(28, 4)`: `ℓ + 1 + m = 1661 + 1 + 415`. -/
@[expose] def pmRows_28_4 : ℕ := 2077

/-- The columns at `(28, 4)`: the multiplicity `m = 415`. -/
@[expose] def pmCols_28_4 : ℕ := 415

/-- The largest order at `(28, 4)`: `deg M_0 + W + 2 = 415·2^26 + 6968845169 + 2`. -/
@[expose] def pmOrder_28_4 : ℕ := 415 * 2 ^ 26 + 6968845169 + 2

/-- **The measured prices** (the probes on the compiled pieces, `LeanVMTests/Cost/Probe*.lean`,
mumbai `f7997a4e`): `305` per pointwise multiply-add (`evalDot`); `520`/`413` per element and
stage of the forward/inverse NTT; `944`/`1037` per `j·2^j` of the conversions to/from the novel
basis; the order-one leaf `444·r³ + 12350·r²`; `316` per schoolbook coefficient product; `64` per
coefficient moved (stated, not measured). -/
@[expose] def measuredPrices : PMPrices :=
  { mac := 305, fwd := 520, inv := 413, toNovel := 944, fromNovel := 1037, leafCube := 444,
    leafSquare := 12350, coeff := 316, ovh := 64 }

/-- **The measured prices with a margin**: each `5/4` of the measured one, rounded up. -/
@[expose] def marginPrices : PMPrices :=
  { mac := 382, fwd := 650, inv := 517, toNovel := 1180, fromNovel := 1297, leafCube := 555,
    leafSquare := 15438, coeff := 395, ovh := 80 }

theorem pmOrder_28_4_eq : pmOrder_28_4 = 34819023731 := by decide +kernel

/-- `≈ 2^35.02`: between `2^35` and `2^36` (`36` levels). -/
theorem pmOrder_28_4_bounds : 2 ^ 35 < pmOrder_28_4 ∧ pmOrder_28_4 + 1 ≤ 2 ^ 36 := by decide +kernel

/-- **The recursion's tree at `(28, 4)`, measured prices**, evaluated in `36` halvings:
`9303084148594118146442494 ≈ 2^82.94`. -/
theorem pmTreePair_28_4_measured :
    pmTreePair 1 (pmLeafPrice measuredPrices pmRows_28_4)
      (pmNodePrice measuredPrices pmRows_28_4 pmCols_28_4) 36 pmOrder_28_4 =
      (9303084148594118146442494, 9303084148611520996184840) := by
  decide +kernel

/-- **The recursion's tree at `(28, 4)`, the prices with their margin**:
`11648617207674066543301263 ≈ 2^83.27`. -/
theorem pmTreePair_28_4 :
    pmTreePair 1 (pmLeafPrice marginPrices pmRows_28_4)
      (pmNodePrice marginPrices pmRows_28_4 pmCols_28_4) 36 pmOrder_28_4 =
      (11648617207674066543301263, 11648617207695852419893540) := by
  decide +kernel

/-- **The per-level closed form at `(28, 4)`**, the prices with their margin:
`Σ_{k<36} 2^k·N(⌈o/2^k⌉) + L·o = 12215213791106017278355823 ≈ 2^83.34` (`pmTree_le_levels`;
`0.07` bit above the tree's exact value). -/
theorem pmLevels_28_4 :
    pmLevels (pmNodePrice marginPrices pmRows_28_4 pmCols_28_4) 36 pmOrder_28_4 +
        pmLeafPrice marginPrices pmRows_28_4 * pmOrder_28_4 =
      12215213791106017278355823 := by
  decide +kernel

end

end LeanVM.Cost.Bounds.PMBasis
