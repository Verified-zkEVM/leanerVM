import LeanerVM.Protocol.Field
import LeanerVM.Protocol.ToVCVio.UniformSample

/-!
Probe `CountingBounds`: the two counting bounds of `ToVCVio/UniformSample.lean` are correct
and not vacuous. On `Fin 4`, an event with exactly one witness has probability exactly `1/4`
(so the bound `1/|α|` is attained), and an event with two witnesses has probability `1/2`,
which exceeds `1/4` (so the hypothesis of the second bound is load-bearing).
-/

open LeanerVM.Protocol OracleComp
open scoped NNReal ENNReal

-- one witness: probability exactly 1/4
theorem one_witness : Pr[fun x : Fin 4 ↦ x = 2 | $ᵗ (Fin 4)] = 1 / 4 := by
  rw [probEvent_uniformSample]
  have h : (Finset.univ.filter fun x : Fin 4 ↦ x = 2).card = 1 := by decide
  rw [h]
  simp

-- the second bound, instantiated, gives `≤ 1/4`: it is attained
theorem one_witness_bound :
    Pr[fun x : Fin 4 ↦ x = 2 | $ᵗ (Fin 4)] ≤ ((1 / Fintype.card (Fin 4) : ℝ≥0) : ℝ≥0∞) :=
  probEvent_uniformSample_le_of_subsingleton (fun x : Fin 4 ↦ x = 2)
    (fun a b ha hb ↦ ha.trans hb.symm)

-- the right-hand side of the bound is the number 1/4
theorem rhs_eq : ((1 / Fintype.card (Fin 4) : ℝ≥0) : ℝ≥0∞) = 1 / 4 := by
  rw [Fintype.card_fin]
  rw [ENNReal.coe_div (by norm_num)]
  simp

-- two witnesses: probability exactly 1/2, which is not `≤ 1/4`
theorem two_witnesses : Pr[fun x : Fin 4 ↦ x = 1 ∨ x = 2 | $ᵗ (Fin 4)] = 1 / 2 := by
  rw [probEvent_uniformSample]
  have h : (Finset.univ.filter fun x : Fin 4 ↦ x = 1 ∨ x = 2).card = 2 := by decide
  rw [h]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, one_div]

theorem two_witnesses_exceed :
    ¬ Pr[fun x : Fin 4 ↦ x = 1 ∨ x = 2 | $ᵗ (Fin 4)] ≤ 1 / 4 := by
  rw [two_witnesses, not_le]
  rw [one_div, one_div]
  exact ENNReal.inv_lt_inv.mpr (by norm_num)

-- the first bound with `k = 2` on the same event
theorem two_witnesses_bound :
    Pr[fun x : Fin 4 ↦ x = 1 ∨ x = 2 | $ᵗ (Fin 4)]
      ≤ (((2 : ℕ) / Fintype.card (Fin 4) : ℝ≥0) : ℝ≥0∞) :=
  probEvent_uniformSample_le_of_card_le (fun x : Fin 4 ↦ x = 1 ∨ x = 2) (k := 2) (by decide)

-- over the challenge field: a single bad challenge has probability exactly `1 / 2^192`
open LeanerVM.Parameters in
theorem one_bad_challenge (c : E) :
    Pr[fun x : E ↦ x = c | $ᵗ E] = ((2 ^ 192 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, card_E]

open LeanerVM.Parameters in
theorem one_bad_challenge_bound (c : E) :
    Pr[fun x : E ↦ x = c | $ᵗ E] ≤ ((1 / Fintype.card E : ℝ≥0) : ℝ≥0∞) :=
  probEvent_uniformSample_le_of_subsingleton (fun x : E ↦ x = c)
    (fun a b ha hb ↦ ha.trans hb.symm)

#print axioms one_witness
#print axioms one_witness_bound
#print axioms rhs_eq
#print axioms two_witnesses
#print axioms two_witnesses_exceed
#print axioms two_witnesses_bound
#print axioms one_bad_challenge
#print axioms one_bad_challenge_bound
