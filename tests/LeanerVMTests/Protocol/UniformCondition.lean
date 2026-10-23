import LeanerVM.Protocol.ToVCVio.UniformCondition

/-!
# Conditioning a uniform sample: tests

The second entry of a uniform pair in `Fin 2 × Fin 3` is `0` with probability `1/3`, read off
the second entry alone. The integral form at `Fin 3 × (Fin 2 → Fin 3)`, conditioning on the
tuple's first entry: that entry equals the pair's first coordinate with probability `1/3`, the
expectation over the entry of the probability, `1/3` whatever the entry, that the coordinate is
it.
-/

namespace LeanerVMTests.Protocol.UniformCondition

open LeanerVM.Protocol OracleComp MeasureTheory
open scoped ENNReal

-- The second entry of a uniform pair is uniform.
example : Pr{let z ← $ᵗ (Fin 2 × Fin 3)}[z.2 = 0] = 3⁻¹ := by
  rw [prEvent_uniformSample_snd (· = 0), SampleableType.prEvent_uniformSample_eq_singleton,
    Fintype.card_fin]
  norm_num

-- Conditioning on the tuple's first entry.
example : Pr{let z ← $ᵗ (Fin 3 × (Fin 2 → Fin 3))}[z.2 0 = z.1] = 3⁻¹ := by
  rw [prEvent_uniformSample_prod_finCons_eq_lintegral]
  simp only [Fin.cons_zero]
  have hx : ∀ x : Fin 3, Pr{let z ← $ᵗ (Fin 3 × (Fin 1 → Fin 3))}[x = z.1] = 3⁻¹ + 0 := by
    intro x
    rw [add_zero, SampleableType.prEvent_uniformSample_fst (fun c ↦ x = c),
      prEvent_congr _ _ (· = x) fun _ ↦ eq_comm, SampleableType.prEvent_uniformSample_eq_singleton,
      Fintype.card_fin]
    norm_num
  simp only [hx]
  rw [lintegral_id_evalDist_map_const_add _ (OracleComp.prEvent_true_eq_one _) _ fun _ ↦ 0,
    lintegral_id_evalDist_map_zero, add_zero]

end LeanerVMTests.Protocol.UniformCondition
