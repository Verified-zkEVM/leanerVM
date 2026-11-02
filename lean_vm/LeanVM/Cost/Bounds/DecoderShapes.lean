module

public import LeanVM.Cost.Bounds.Decoder.ShapeDefs

/-!
# Bounds: Roth–Ruckenstein's search at the worst shape

At `(28, 4)`, the worst admissible shape, Roth–Ruckenstein's search per lane, `rrBound_28_4`
(`≈ 2^87.98`), evaluated. **A documentation value**: no end proof uses it (the decoder's bound
at every admissible shape, Roth–Ruckenstein's term included, is decided in
`Bounds/PMLane/Shapes.lean`); it records the share of the search that the docs cite
(`Bounds/PMBasis/LaneValues.lean`).

The check evaluates only the extractor's parameter search and the bounds' definitions
(`Bounds/Decoder/ShapeDefs.lean`), none of their proofs: an edit of a proof does not rebuild it
(`Bounds/DecoderShapesFirewall.lean`).
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Parameters CompPoly CompPoly.GuruswamiSudan LeanVM.Extraction

public section

/-- **Roth–Ruckenstein's search at `(28, 4)`** (`k = 2^22`, `W = 6968845169`, `ℓ = 1661`): at most
`305248793717338995471780915 ≈ 2^87.98` per lane (`prefixesNFC_cost`: `1 + k·ℓ ≈ 2^32.7` nodes, the
substitution by the butterfly `≈ 2^55.2` per node, the roots `≈ 2^49.9`). -/
theorem rrBound_28_4 :
    rrBound ((gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp.weightedDegreeBound + 1)
        (interpolationYCap (gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp + 2) (2 ^ 22)
        (interpolationYCap (gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp) =
      305248793717338995471780915 := by
  decide +kernel

end

end LeanVM.Cost.Bounds.Decoder
