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

/-- **The decoder's prices**: `382` per pointwise multiply-add (`evalDot`); `650`/`517` per element
and stage of the forward/inverse NTT; `4100`/`5490` per `j·2^j` of the conversions to/from the
novel basis (for `j ≤ 36`); the order-one leaf `16600·r³ + 100000·r²` (above its proved price
`PMCore.leafBound`, `≈ 16550·r³` at `r = 2077`); `395` per schoolbook coefficient product; `600`
per coefficient moved. The transforms' and products' proved prices fit them
(`FFTPricesOK marginPrices`, `PMSolve.fftPricesOK_margin`). -/
@[expose] def marginPrices : PMPrices :=
  { mac := 382, fwd := 650, inv := 517, toNovel := 4100, fromNovel := 5490, leafCube := 16600,
    leafSquare := 100000, coeff := 395, ovh := 600 }

end

end LeanVM.Cost.Bounds.PMBasis
