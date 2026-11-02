module

public import LeanVM.Cost.Bounds.PMBasis.Defs

/-!
# PM-basis's price at `(28, 4)`: the numbers, by kernel evaluation

The model of `Bounds/PMBasis/Defs.lean` at the worst shape `(μ, R) = (28, 4)` (`k = 2^22`,
`n = 2^26`, multiplicity `415`, list size `ℓ = 1661`, `W = 6968845169`): the windowed X-adic
problem of `r = ℓ + 1 + 415 = 2077` rows and `415` columns, orders `deg M_b + W + 2`, the largest
`415·2^26 + W + 2 = 34819023731 ≈ 2^35.02` (`pmOrder_28_4`); stated prices `mac = 320` steps per
multiply-add in `K` (a product, `258`, its sum and the array's reads and loop), `ovh = 64` per
coefficient moved; the transforms at `lean_vm`'s proved `novelFwd`/`novelInv` prices.

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

/-- The stated price of a multiply-add in `K`. -/
@[expose] def pmMac : ℕ := 320

/-- The stated price of a coefficient moved. -/
@[expose] def pmOvh : ℕ := 64

theorem pmOrder_28_4_eq : pmOrder_28_4 = 34819023731 := by decide +kernel

/-- `≈ 2^35.02`: between `2^35` and `2^36` (`36` levels). -/
theorem pmOrder_28_4_bounds : 2 ^ 35 < pmOrder_28_4 ∧ pmOrder_28_4 + 1 ≤ 2 ^ 36 := by decide +kernel

/-- **The recursion's tree at `(28, 4)`**, evaluated in `36` halvings:
`pmTree = 11539379281308906874275088 ≈ 2^83.25`. -/
theorem pmTreePair_28_4 :
    pmTreePair 1 (pmLeafPrice pmMac pmRows_28_4) (pmNodePrice pmMac pmOvh pmRows_28_4 pmCols_28_4)
      36 pmOrder_28_4 =
      (11539379281308906874275088, 11539379281346533240061732) := by
  decide +kernel

/-- **The per-level closed form at `(28, 4)`**: `Σ_{k<36} 2^k·N(⌈o/2^k⌉) + L·o =
12036630804624214148766676 ≈ 2^83.32` (`pmTree_le_levels`; `0.06` bit above the tree's exact
value). -/
theorem pmLevels_28_4 :
    pmLevels (pmNodePrice pmMac pmOvh pmRows_28_4 pmCols_28_4) 36 pmOrder_28_4 +
        pmLeafPrice pmMac pmRows_28_4 * pmOrder_28_4 =
      12036630804624214148766676 := by
  decide +kernel

/-- **Per lane and over `64` lanes at `(28, 4)`**: one lane's PM-basis (the fuel's fold,
`64·415 + 100`, and the tree) between `2^83.25` and `2^83.26`; `64` lanes `13` times below
`2^93` (a margin above `log₂ 13 ≈ 3.70` bits; exactly `≈ 3.745`). -/
theorem pmBasis_lanes_28_4 :
    2 ^ 83 * 1193 < 1000 * (64 * pmCols_28_4 + 100 + 11539379281308906874275088) ∧
      1000 * (64 * pmCols_28_4 + 100 + 11539379281308906874275088) < 2 ^ 83 * 1194 ∧
      13 * (64 * (64 * pmCols_28_4 + 100 + 11539379281308906874275088)) < 2 ^ 93 := by
  decide +kernel

end

end LeanVM.Cost.Bounds.PMBasis
