module

public import LeanVM.Cost.Bounds.PMBasis.LaneDefs
public import LeanVM.Cost.Bounds.PMBasis.Values

/-!
# The lane decoder on the new solver at `(28, 4)`: the numbers, by kernel evaluation

`LaneDefs.lean`'s model at `(28, 4)` (`k = 2^22`, `n = 2^26`, `A = 16792398`, `m = 415`,
`W = 6968845169`, `ℓ = 1661`), at the measured prices and at those with their margin:

| | measured | margin (`5/4`) |
|---|---|---|
| PM-basis (`pmBasisPrice`) | `≈ 2^82.944` | `≈ 2^83.268` |
| GS data (`gsDataPrice`) | `≈ 2^74.21` | `≈ 2^74.53` |
| interpolation (`interpPMPrice`) | `≈ 2^82.947` | `≈ 2^83.272` |
| a lane's run (`gsRunBoundPM`; Roth–Ruckenstein `≈ 2^87.98`) | `≈ 2^88.024` | `≈ 2^88.034` |
| **the decoder, `64` lanes (`decoderBoundPM 28 4 0 0`)** | **`≈ 2^94.024`** | **`≈ 2^94.034`** |

against `≈ 2^117.67` today (`decoderBound 28 4 0 0`, Mulders–Storjohann's interpolation).
Roth–Ruckenstein's search (proved, `rrBound_28_4`) is now `95%` of each lane; the
interpolation `3%`.
-/

namespace LeanVM.Cost.Bounds.PMBasis

open LeanVM.Parameters LeanVM.Extraction CompPoly CompPoly.GuruswamiSudan
open LeanVM.Cost.Bounds.Decoder

public section

/-- The PM-basis inside the certified solve at `(28, 4)`, measured prices: `≈ 2^82.944`. -/
theorem pmBasisPrice_28_4_measured :
    pmBasisPrice measuredPrices 2077 415 34819023731 = 9303084148594118146469154 := by
  decide +kernel

/-- **The interpolation at `(28, 4)`, measured prices**: `≈ 2^82.947`. -/
theorem interpPMPrice_28_4_measured :
    interpPMPrice measuredPrices (2 ^ 26) (gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp =
      9324991030033325270634505 := by
  decide +kernel

/-- **The interpolation at `(28, 4)`, the prices with their margin**: `≈ 2^83.272`. -/
theorem interpPMPrice_28_4 :
    interpPMPrice marginPrices (2 ^ 26) (gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp =
      11676002225385735708534088 := by
  decide +kernel

/-- **A lane at `(28, 4)`, measured prices**: `≈ 2^88.024` (Roth–Ruckenstein `≈ 2^87.98`). -/
theorem decoderLaneBoundPM_28_4_measured :
    decoderLaneBoundPM measuredPrices 22 4 16792398 12 = 314573919866599537871596590 := by
  decide +kernel

/-- **The decoder at `(28, 4)`, `64` lanes, measured prices**:
`20132730948208792406439714522 ≈ 2^94.024`. -/
theorem decoderBoundPM_28_4_measured :
    decoderBoundPM measuredPrices 28 4 0 0 = 20132730948208792406439714522 := by
  decide +kernel

/-- **The decoder at `(28, 4)`, `64` lanes, the prices with their margin**:
`20283195664711346674465287834 ≈ 2^94.034`. -/
theorem decoderBoundPM_28_4 :
    decoderBoundPM marginPrices 28 4 0 0 = 20283195664711346674465287834 := by
  decide +kernel

/-- Both between `2^94` and `2^94·1.025` (`≈ 2^94.036`). -/
theorem decoderBoundPM_28_4_range :
    2 ^ 94 < 20132730948208792406439714522 ∧
      20283195664711346674465287834 * 1000 < 2 ^ 94 * 1025 := by
  decide +kernel

end

end LeanVM.Cost.Bounds.PMBasis
