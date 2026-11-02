module

public import LeanVM.Cost.Bounds.PMBasis.LaneDefs
public import LeanVM.Cost.Bounds.PMBasis.Values

/-!
# Bounds: the decoder on the new solver at every admissible shape, as definitions

`DecoderShapeOkPM μ R`: what the new decoder's bound needs at a shape (the lanes word-sized,
`DecoderLaneSizes`, as for the extractor's decoder) and its value, at the model's prices with
their margin (`marginPrices`), at most the one at `(28, 4)`, which
`Bounds/PMLane/Shapes.lean` decides at each of the `56` admissible shapes. Definitions only, so
that the checks import no proof (`Bounds/PMLane/ShapesFirewall.lean`).
-/

namespace LeanVM.Cost.Bounds.PMLane

open LeanVM.Parameters LeanVM.Extraction LeanVM.Cost.Bounds.Decoder LeanVM.Cost.Bounds.PMBasis

public section

/-- **The new decoder's worst price beyond the word's**: `decoderBoundPM` at `(28, 4)`, the
model's prices with their margin. -/
@[expose] def pmDecoderWorstPrice : ℕ := decoderBoundPM marginPrices 28 4 0 0

/-- What the new decoder's bound needs at a shape, and its value at most the worst. -/
@[expose] def DecoderShapeOkPM (μ R : ℕ) : Prop :=
  DecoderLaneSizes (μ - Whir.initialFold) R (johnsonThreshold μ R) ∧
    decoderBoundPM marginPrices μ R 0 0 ≤ pmDecoderWorstPrice

instance (μ R : ℕ) : Decidable (DecoderShapeOkPM μ R) := by
  unfold DecoderShapeOkPM; infer_instance

end

end LeanVM.Cost.Bounds.PMLane
