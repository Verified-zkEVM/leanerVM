import VCVio.OracleComp.EvalDist.Sum
import ToMathlib.Probability.TailSums
import VCVio.ProgramLogic.Relational.Basic
import XmssSecurity.Proof.EvalDistEq

/-!
# Expected counts through couplings

The mean of a natural-valued observable is the sum of its tail probabilities, so a coupling whose
relation orders two observables orders their means (`tsum_le_of_relTriple`).
-/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

/-- The mean of a natural-valued observable is the sum of its tail probabilities. -/
theorem tsum_prEvent_mul_natCast_eq_tsum_lt {α : Type} (mx : ProbComp α) (f : α → ℕ) :
    ∑' x, Pr{let y ← mx}[y = x] * (f x : ℝ≥0∞) = ∑' t : ℕ, Pr{let y ← mx}[t < f y] := by
  let : MeasurableSpace α := ⊤
  rw [← OracleComp.lintegral_evalDist_eq_tsum,
    MeasureTheory.lintegral_coe_nat_eq_tsum (measurable_from_top) 𝒟[mx]]
  exact tsum_congr fun t => (prEvent_eq_evalDist_of_discrete mx (fun y => t < f y)).symm

/-- A coupling ordering two natural-valued observables orders their means. -/
theorem tsum_le_of_relTriple {α β : Type} {oa : ProbComp α} {ob : ProbComp β}
    {relation : α → β → Prop} (h : RelTriple oa ob relation) (f : α → ℕ) (g : β → ℕ)
    (hfg : ∀ a b, relation a b → g b ≤ f a) :
    ∑' b, Pr{let y ← ob}[y = b] * (g b : ℝ≥0∞) ≤ ∑' a, Pr{let y ← oa}[y = a] * (f a : ℝ≥0∞) := by
  rw [tsum_prEvent_mul_natCast_eq_tsum_lt, tsum_prEvent_mul_natCast_eq_tsum_lt]
  exact ENNReal.tsum_le_tsum fun t =>
    prEvent_le_of_relTriple (relTriple_symm h) fun b a hrel hlt => lt_of_lt_of_le hlt (hfg a b hrel)

/-- Means of an observable agree under equality in distribution. -/
theorem tsum_prEvent_mul_congr {α : Type} {mx my : ProbComp α} (h : mx =ᵈ my) (f : α → ℝ≥0∞) :
    ∑' x, Pr{let y ← mx}[y = x] * f x = ∑' x, Pr{let y ← my}[y = x] * f x :=
  tsum_congr fun x => by rw [h.prEvent_eq (· = x)]

/-- Solve `h ≤ a + c h` for a probability `h` and `c ≤ 3/4`: `h ≤ a + 4 c a`. -/
theorem le_add_four_mul_of_le_add_mul {h a c : ℝ≥0∞} (hh : h ≤ 1) (hc : c ≤ 3 / 4)
    (hle : h ≤ a + c * h) : h ≤ a + 4 * c * a := by
  by_cases ha : a = ⊤
  · simp [ha]
  have h34 : (3 / 4 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top h34 hc
  have hhtop : h ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hh
  have h4 : h ≤ 4 * a := by
    rw [← ENNReal.toReal_le_toReal hhtop (by finiteness)]
    have hreal := (ENNReal.toReal_le_toReal hhtop (by finiteness)).mpr hle
    rw [ENNReal.toReal_add ha (by finiteness), ENNReal.toReal_mul] at hreal
    have hcreal : c.toReal ≤ 3 / 4 := by
      have := (ENNReal.toReal_le_toReal hctop h34).mpr hc
      simpa using this
    rw [ENNReal.toReal_mul]
    simp only [ENNReal.toReal_ofNat]
    have hnonneg := ENNReal.toReal_nonneg (a := h)
    nlinarith
  calc
    h ≤ a + c * h := hle
    _ ≤ a + c * (4 * a) := by gcongr
    _ = a + 4 * c * a := by ring

end XmssSecurity
