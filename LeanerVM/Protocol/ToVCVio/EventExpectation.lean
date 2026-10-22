/-
  LeanerVM.Protocol.ToVCVio.EventExpectation

  Events and constants in the expectation of a scalar observation. Candidate for VCVio.
-/

module

public import LeanerVM.Protocol.ToVCVio.ScalarExpectation
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Events and constants in scalar expectations

Two laws of the expectation `∫⁻ r, r ∂𝒟[f <$> mx]`, for any lawful measure semantics: the
probability of an event is the expectation of its indicator, and a constant comes out of the
expectation over a computation that does not fail.
-/

namespace LeanerVM.Protocol

open MeasureTheory
open scoped ENNReal

public section

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α : Type}

/-- An event's probability is the expectation of its indicator. -/
theorem prEvent_eq_lintegral_id_evalDist_map_ite (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← mx}[p x] = ∫⁻ r, r ∂𝒟[(fun x ↦ if p x then 1 else 0) <$> mx] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, lintegral_id_evalDist_map,
    ← lintegral_indicator_one MeasurableSet.of_discrete]
  exact lintegral_congr fun x ↦ by by_cases hx : p x <;> simp [hx]

/-- Over a computation that does not fail, a constant comes out of an expectation. -/
theorem lintegral_id_evalDist_map_const_add (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (a : ℝ≥0∞) (f : α → ℝ≥0∞) :
    ∫⁻ r, r ∂𝒟[(fun x ↦ a + f x) <$> mx] = a + ∫⁻ r, r ∂𝒟[f <$> mx] := by
  rw [lintegral_id_evalDist_map_add mx (fun _ ↦ a) f]
  congr 1
  let : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map, lintegral_const, ← prEvent_true_eq_evalDist_apply_univ, hmx,
    mul_one]

end

end LeanerVM.Protocol
