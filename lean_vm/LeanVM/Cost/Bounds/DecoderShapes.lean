module

public import LeanVM.Cost.Bounds.Decoder.Decode

/-!
# Bounds: the decoder at every admissible shape

`decodeStacksDistinctC_cost` (`Bounds/Decoder/Decode.lean`) holds at a shape whose lanes are
word-sized (`DecoderLaneSizes`). Here, at each of the `56` admissible shapes (`15 ≤ μ ≤ 28`,
`1 ≤ R ≤ 4`), one `decide +kernel` each (a single `decide` over all shapes at once outgrows the
memory): the lanes are word-sized and the decoder's bound beyond the word's prices is at most the
one at `(28, 4)` (`decoderWorstPrice ≈ 2^117.67`):

* **`decoderShape_ok`**: `DecoderLaneSizes` and `decoderBound μ R 0 0 ≤ decoderWorstPrice` at every
  admissible `(μ, R)`;
* **`decodeStacksDistinctC_cost_worst`**: at every admissible shape, at most
  `(BW + 10·Lw)·2^26 + decoderWorstPrice`.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Extractor LeanVM.Parameters LeanVM.Extraction

public section

/-- What the decoder's bound needs at a shape, and its value at most the worst. -/
@[expose] def DecoderShapeOk (μ R : ℕ) : Prop :=
  DecoderLaneSizes (μ - Whir.initialFold) R (johnsonThreshold μ R) ∧
    decoderBound μ R 0 0 ≤ decoderWorstPrice

instance (μ R : ℕ) : Decidable (DecoderShapeOk μ R) := by
  unfold DecoderShapeOk; infer_instance
theorem decoderShapeOk_15_1 : DecoderShapeOk 15 1 := by decide +kernel
theorem decoderShapeOk_15_2 : DecoderShapeOk 15 2 := by decide +kernel
theorem decoderShapeOk_15_3 : DecoderShapeOk 15 3 := by decide +kernel
theorem decoderShapeOk_15_4 : DecoderShapeOk 15 4 := by decide +kernel
theorem decoderShapeOk_16_1 : DecoderShapeOk 16 1 := by decide +kernel
theorem decoderShapeOk_16_2 : DecoderShapeOk 16 2 := by decide +kernel
theorem decoderShapeOk_16_3 : DecoderShapeOk 16 3 := by decide +kernel
theorem decoderShapeOk_16_4 : DecoderShapeOk 16 4 := by decide +kernel
theorem decoderShapeOk_17_1 : DecoderShapeOk 17 1 := by decide +kernel
theorem decoderShapeOk_17_2 : DecoderShapeOk 17 2 := by decide +kernel
theorem decoderShapeOk_17_3 : DecoderShapeOk 17 3 := by decide +kernel
theorem decoderShapeOk_17_4 : DecoderShapeOk 17 4 := by decide +kernel
theorem decoderShapeOk_18_1 : DecoderShapeOk 18 1 := by decide +kernel
theorem decoderShapeOk_18_2 : DecoderShapeOk 18 2 := by decide +kernel
theorem decoderShapeOk_18_3 : DecoderShapeOk 18 3 := by decide +kernel
theorem decoderShapeOk_18_4 : DecoderShapeOk 18 4 := by decide +kernel
theorem decoderShapeOk_19_1 : DecoderShapeOk 19 1 := by decide +kernel
theorem decoderShapeOk_19_2 : DecoderShapeOk 19 2 := by decide +kernel
theorem decoderShapeOk_19_3 : DecoderShapeOk 19 3 := by decide +kernel
theorem decoderShapeOk_19_4 : DecoderShapeOk 19 4 := by decide +kernel
theorem decoderShapeOk_20_1 : DecoderShapeOk 20 1 := by decide +kernel
theorem decoderShapeOk_20_2 : DecoderShapeOk 20 2 := by decide +kernel
theorem decoderShapeOk_20_3 : DecoderShapeOk 20 3 := by decide +kernel
theorem decoderShapeOk_20_4 : DecoderShapeOk 20 4 := by decide +kernel
theorem decoderShapeOk_21_1 : DecoderShapeOk 21 1 := by decide +kernel
theorem decoderShapeOk_21_2 : DecoderShapeOk 21 2 := by decide +kernel
theorem decoderShapeOk_21_3 : DecoderShapeOk 21 3 := by decide +kernel
theorem decoderShapeOk_21_4 : DecoderShapeOk 21 4 := by decide +kernel
theorem decoderShapeOk_22_1 : DecoderShapeOk 22 1 := by decide +kernel
theorem decoderShapeOk_22_2 : DecoderShapeOk 22 2 := by decide +kernel
theorem decoderShapeOk_22_3 : DecoderShapeOk 22 3 := by decide +kernel
theorem decoderShapeOk_22_4 : DecoderShapeOk 22 4 := by decide +kernel
theorem decoderShapeOk_23_1 : DecoderShapeOk 23 1 := by decide +kernel
theorem decoderShapeOk_23_2 : DecoderShapeOk 23 2 := by decide +kernel
theorem decoderShapeOk_23_3 : DecoderShapeOk 23 3 := by decide +kernel
theorem decoderShapeOk_23_4 : DecoderShapeOk 23 4 := by decide +kernel
theorem decoderShapeOk_24_1 : DecoderShapeOk 24 1 := by decide +kernel
theorem decoderShapeOk_24_2 : DecoderShapeOk 24 2 := by decide +kernel
theorem decoderShapeOk_24_3 : DecoderShapeOk 24 3 := by decide +kernel
theorem decoderShapeOk_24_4 : DecoderShapeOk 24 4 := by decide +kernel
theorem decoderShapeOk_25_1 : DecoderShapeOk 25 1 := by decide +kernel
theorem decoderShapeOk_25_2 : DecoderShapeOk 25 2 := by decide +kernel
theorem decoderShapeOk_25_3 : DecoderShapeOk 25 3 := by decide +kernel
theorem decoderShapeOk_25_4 : DecoderShapeOk 25 4 := by decide +kernel
theorem decoderShapeOk_26_1 : DecoderShapeOk 26 1 := by decide +kernel
theorem decoderShapeOk_26_2 : DecoderShapeOk 26 2 := by decide +kernel
theorem decoderShapeOk_26_3 : DecoderShapeOk 26 3 := by decide +kernel
theorem decoderShapeOk_26_4 : DecoderShapeOk 26 4 := by decide +kernel
theorem decoderShapeOk_27_1 : DecoderShapeOk 27 1 := by decide +kernel
theorem decoderShapeOk_27_2 : DecoderShapeOk 27 2 := by decide +kernel
theorem decoderShapeOk_27_3 : DecoderShapeOk 27 3 := by decide +kernel
theorem decoderShapeOk_27_4 : DecoderShapeOk 27 4 := by decide +kernel
theorem decoderShapeOk_28_1 : DecoderShapeOk 28 1 := by decide +kernel
theorem decoderShapeOk_28_2 : DecoderShapeOk 28 2 := by decide +kernel
theorem decoderShapeOk_28_3 : DecoderShapeOk 28 3 := by decide +kernel
theorem decoderShapeOk_28_4 : DecoderShapeOk 28 4 := by decide +kernel

/-- **The decoder's hypotheses at every admissible shape.** -/
theorem decoderShape_ok {μ R : ℕ} (h : Whir.Admissible μ R) : DecoderShapeOk μ R := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Whir.minLogStack, Whir.maxLogStack, Whir.minLogInvRate, Whir.maxLogInvRate] at h1 h2 h3 h4
  have hR : R = 1 ∨ R = 2 ∨ R = 3 ∨ R = 4 := by omega
  rcases (show μ = 15 ∨ μ = 16 ∨ μ = 17 ∨ μ = 18 ∨ μ = 19 ∨ μ = 20 ∨ μ = 21 ∨ μ = 22 ∨ μ = 23 ∨ μ = 24 ∨ μ = 25 ∨ μ = 26 ∨ μ = 27 ∨ μ = 28 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hR with rfl | rfl | rfl | rfl
  · exact decoderShapeOk_15_1
  · exact decoderShapeOk_15_2
  · exact decoderShapeOk_15_3
  · exact decoderShapeOk_15_4
  · exact decoderShapeOk_16_1
  · exact decoderShapeOk_16_2
  · exact decoderShapeOk_16_3
  · exact decoderShapeOk_16_4
  · exact decoderShapeOk_17_1
  · exact decoderShapeOk_17_2
  · exact decoderShapeOk_17_3
  · exact decoderShapeOk_17_4
  · exact decoderShapeOk_18_1
  · exact decoderShapeOk_18_2
  · exact decoderShapeOk_18_3
  · exact decoderShapeOk_18_4
  · exact decoderShapeOk_19_1
  · exact decoderShapeOk_19_2
  · exact decoderShapeOk_19_3
  · exact decoderShapeOk_19_4
  · exact decoderShapeOk_20_1
  · exact decoderShapeOk_20_2
  · exact decoderShapeOk_20_3
  · exact decoderShapeOk_20_4
  · exact decoderShapeOk_21_1
  · exact decoderShapeOk_21_2
  · exact decoderShapeOk_21_3
  · exact decoderShapeOk_21_4
  · exact decoderShapeOk_22_1
  · exact decoderShapeOk_22_2
  · exact decoderShapeOk_22_3
  · exact decoderShapeOk_22_4
  · exact decoderShapeOk_23_1
  · exact decoderShapeOk_23_2
  · exact decoderShapeOk_23_3
  · exact decoderShapeOk_23_4
  · exact decoderShapeOk_24_1
  · exact decoderShapeOk_24_2
  · exact decoderShapeOk_24_3
  · exact decoderShapeOk_24_4
  · exact decoderShapeOk_25_1
  · exact decoderShapeOk_25_2
  · exact decoderShapeOk_25_3
  · exact decoderShapeOk_25_4
  · exact decoderShapeOk_26_1
  · exact decoderShapeOk_26_2
  · exact decoderShapeOk_26_3
  · exact decoderShapeOk_26_4
  · exact decoderShapeOk_27_1
  · exact decoderShapeOk_27_2
  · exact decoderShapeOk_27_3
  · exact decoderShapeOk_27_4
  · exact decoderShapeOk_28_1
  · exact decoderShapeOk_28_2
  · exact decoderShapeOk_28_3
  · exact decoderShapeOk_28_4

/-- **The decoder at every admissible shape**: at most `(BW + 10·Lw)·2^26 + decoderWorstPrice`. -/
theorem decodeStacksDistinctC_cost_worst (P : Program) (hP : Includes P decodeStacksDistinctC.costDeps)
    {μ R : ℕ} (hadm : Whir.Admissible μ R)
    (W : ℕ → List K) (WVal : Val) (hW : ∀ a, RunsApp P WVal [enc a] (enc (W a))) {BW Lw : ℕ}
    (hBW : ∀ v : ℕ, v < 2 ^ 64 → appCost P WVal [enc v] ≤ BW) (hLw : ∀ v, (W v).length ≤ Lw) :
    machineCost P decodeStacksDistinctC.costIdx [enc μ, enc R, WVal] ≤
      (BW + 10 * Lw) * 2 ^ 26 + decoderWorstPrice := by
  obtain ⟨hsz, hle⟩ := decoderShape_ok hadm
  have h := decodeStacksDistinctC_cost P hP μ R hadm hsz W WVal hW hBW hLw
  rw [decoderBound_eq] at h
  have hadm' := hadm
  obtain ⟨-, h2, -, h4⟩ := hadm'
  simp only [Whir.maxLogStack, Whir.maxLogInvRate] at h2 h4
  have hp : 2 ^ (μ - Whir.initialFold + R) ≤ 2 ^ 26 :=
    Nat.pow_le_pow_right (by norm_num) (by simp only [Whir.initialFold]; omega)
  have := Nat.mul_le_mul_left (BW + 10 * Lw) hp
  omega

end

end LeanVM.Cost.Bounds.Decoder
