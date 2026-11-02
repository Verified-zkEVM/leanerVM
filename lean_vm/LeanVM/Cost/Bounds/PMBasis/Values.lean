module

public import LeanVM.Cost.Bounds.PMBasis.Defs

/-!
# The prices the decoder's bound is proved at

`marginPrices`: the per-operation prices of `Bounds/PMBasis/Defs.lean`'s model at which the
approximant-basis decoder's bound is proved (`decoderBoundPM`, `Bounds/PMBasis/LaneDefs.lean`;
`decodeStacksPMC_cost_worst`, `Bounds/PMLane/Decode.lean`). A definition alone, so that the shape
checks (`Bounds/PMLane/Shapes.lean`) import only what they evaluate.
-/

namespace LeanVM.Cost.Bounds.PMBasis

public section

/-- **The decoder's prices**: `80` per pointwise multiply-add (`evalDot`); `129`/`87` per element
and stage of the forward/inverse NTT; `1134`/`1401` per `j·2^j` of the conversions to/from the
novel basis (for `j ≤ 36`; with the stages, the transforms' proved prices `fwdNeed`/`invNeed` at
`j = 36` less `ovh` per point); the order-one leaf `16600·r³ + 100000·r²` (above its proved price
`PMCore.leafBound`); `395` per schoolbook coefficient product; `600` per coefficient moved (at
least `fwdNeed 0 = 504`). The transforms' and products' proved prices fit them
(`FFTPricesOK marginPrices`, `PMSolve.fftPricesOK_margin`). -/
@[expose] def marginPrices : PMPrices :=
  { mac := 80, fwd := 129, inv := 87, toNovel := 1134, fromNovel := 1401, leafCube := 16600,
    leafSquare := 100000, coeff := 395, ovh := 600 }

end

end LeanVM.Cost.Bounds.PMBasis
