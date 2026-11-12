/-
  LeanerVMTests.Protocol.UniformSample

  The uniform laws of pushed-forward samples on small instances: tuples of a parity, low binary
  digits, and digits read in chunks.
-/

module

public import LeanerVM.Protocol.ToVCVio.UniformSample

/-!
# Uniform pushforward controls

The parity of a uniform `Fin 4` is the first half of the bijection `x ↦ (x % 2, x / 2)`, so two
independent samples have uniform parities: a given pair with probability `1/4`. One sample used
twice is not two samples: its two parities never differ, so the pair `(0, 1)` has probability
`0`.

The two low binary digits of a uniform `Fin 8` are uniform; the low digit of a uniform `Fin 3`,
where `2 ∤ 3`, is not: it is `0` with probability `2/3`. Three binary digits read in chunks of two
off two uniform `Fin 4`, low digit first, are uniform: a given triple with probability `1/8`.
-/

namespace LeanerVMTests.Protocol.UniformSample

open LeanerVM.Protocol OracleComp
open scoped ENNReal

@[expose] public section

/-! ## Tuples -/

/-- The parity of a number below `4`. -/
def parity (x : Fin 4) : Fin 2 := ⟨x % 2, Nat.mod_lt _ (by decide)⟩

/-- The half of a number below `4`. -/
def half (x : Fin 4) : Fin 2 := ⟨x / 2, by omega⟩

theorem parity_half_bijective : Function.Bijective fun x ↦ (parity x, half x) := by decide

-- Two independent parities are a given pair with probability `1/4`.
example : Pr{let d ← $ᵗ (Fin 2 → Fin 4)}[(fun i ↦ parity (d i)) = ![0, 1]] = 4⁻¹ := by
  refine (prEvent_uniformSample_pi_of_bijective parity_half_bijective 2 (· = ![0, 1])).trans ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fun, Fintype.card_fin]
  norm_num

-- One sample used twice: its parities never differ.
example : Pr{let x ← $ᵗ Fin 4}[(fun _ : Fin 2 ↦ parity x) = ![0, 1]] = 0 :=
  (SampleableType.prEvent_uniformSample_eq_zero_iff _).mpr fun x h ↦ by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact absurd (h0.symm.trans h1) (by decide)

/-! ## Digits -/

-- The two low binary digits of a uniform `Fin 8` are a given pair with probability `1/4`.
example :
    Pr{let x ← $ᵗ Fin 8}[(fun i : Fin 2 ↦ (⟨x / 2 ^ (i : ℕ) % 2, Nat.mod_lt _ (by decide)⟩ :
      Fin 2)) = ![1, 0]] = 4⁻¹ := by
  refine (prEvent_uniformSample_digits (a := 2) (k := 2) (N := 8) (by norm_num)
    (· = ![1, 0])).trans ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fun, Fintype.card_fin]
  norm_num

-- Without `2 ∣ 3`, the low digit of a uniform `Fin 3` is `0` with probability `2/3`, not `1/2`.
example :
    Pr{let x ← $ᵗ Fin 3}[(x : ℕ) % 2 = 0] = (2 : ℕ) / (Fintype.card (Fin 3) : ℝ≥0∞) :=
  (SampleableType.prEvent_uniformSample_eq_div_iff fun x : Fin 3 ↦ (x : ℕ) % 2 = 0).mpr
    (by decide)

/-! ## Digits in chunks -/

/-- Three binary digits off two numbers below `4`, two to a number, low digit first. -/
def chunksOf (x : Fin 2 → Fin 4) : Fin 3 → Fin 2 := fun q ↦
  ⟨(x ⟨q / 2, by omega⟩ : ℕ) / 2 ^ ((q : ℕ) % 2) % 2, Nat.mod_lt _ (by decide)⟩

-- `1 = 01₂` gives the digits `1, 0`, then `2 = 10₂` gives `0`.
example : chunksOf ![1, 2] = ![1, 0, 0] := by decide

-- The three digits are a given triple with probability `1/8`.
example : Pr{let x ← $ᵗ (Fin 2 → Fin 4)}[chunksOf x = ![0, 1, 1]] = 8⁻¹ := by
  refine (prEvent_uniformSample_digitChunks (a := 2) (k := 2) (N := 4) (m := 2) (t := 3)
    (by norm_num) (by norm_num) (· = ![0, 1, 1])).trans ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fun, Fintype.card_fin]
  norm_num

end

end LeanerVMTests.Protocol.UniformSample
