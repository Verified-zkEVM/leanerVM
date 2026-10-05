/-
  LeanerVM.Protocol.ToArkLib.PowerBatching

  The collision probability of a fixed family under a fresh uniform challenge.
  Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToCompPoly.PowerBatching
public import LeanerVM.Protocol.ToVCVio.UniformSample

/-!
# Uniform power-batching bound

The root count for zero-based power batching gives a probability bound in the native
`OracleComp` event carrier used by ArkLib. The actual and target values are fixed outside
the uniform sample. A protocol consumer must establish that its challenge is sampled this
way after fixing those values; this is not a knowledge-soundness or transcript theorem.
-/

namespace LeanerVM.Protocol

open OracleComp
open scoped NNReal ENNReal

public section

/-- A fixed false family passes a fresh uniform power batch with probability at most
`(J - 1) / |F|`. The subtraction is in `ℕ`, so the singleton bound is zero. -/
theorem probEvent_uniform_false_batch_le {F : Type} [Field F] [Fintype F]
    [DecidableEq F] [SampleableType F] {J : ℕ}
    (a v : Fin J → F) (h : ∃ j, a j ≠ v j) :
    Pr{let ρ ← $ᵗ F}[powerBatch a ρ = powerBatch v ρ] ≤
      (((J - 1 : ℕ) / Fintype.card F : ℝ≥0) : ℝ≥0∞) := by
  have bound := (SampleableType.prEvent_uniformSample_le_div_iff
    (p := fun ρ ↦ powerBatch a ρ = powerBatch v ρ)).mpr (card_false_batch_le a v h)
  rwa [ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
    ENNReal.coe_natCast]

end
end LeanerVM.Protocol
