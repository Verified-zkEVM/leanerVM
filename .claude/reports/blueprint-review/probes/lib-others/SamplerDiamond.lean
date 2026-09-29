import LeanerVM.Parameters.Field
import VCVio.OracleComp.Constructions.SampleableType

/-!
Probe `SamplerDiamond`: without `LeanerVM.Protocol.Field`, instance search already finds a
sampler on `K`, because `K` unfolds to `BitVec 64` and Mathlib enumerates `BitVec n` as a
`FinEnum`. It is a different term from leanerVM's `instSampleableTypeK`. Both are lawful, so
they have the same distribution.
-/

open LeanerVM.Parameters OracleComp
open scoped ENNReal

#synth SampleableType K
#synth SampleableType (BitVec 64)
#synth FinEnum K

-- the library's sampler on `K` is uniform too (uniformity is a law of the class)
example (x : K) : Pr[= x | $ᵗ K] = (Fintype.card K : ℝ≥0∞)⁻¹ := probOutput_uniformSample K x

-- any two samplers on the same finite type give every element the same probability
theorem sampler_unique {α : Type} [Fintype α] (s t : SampleableType α) (x : α) :
    Pr[= x | @uniformSample α s] = Pr[= x | @uniformSample α t] := by
  rw [@probOutput_uniformSample α s, @probOutput_uniformSample α t]

#print axioms sampler_unique

-- no sampler is found on `E` without leanerVM's instance: `Ext` is not reducible
#synth SampleableType E
