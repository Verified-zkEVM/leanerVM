/-
  LeanerVM.Protocol.ToVCVio.EventExpectation

  Events and constants in the expectation of a scalar observation, and an event after a draw.
  Candidate for VCVio.
-/

module

public import LeanerVM.Protocol.ToVCVio.ScalarExpectation
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Events and constants in scalar expectations

Laws of the expectation `∫⁻ r, r ∂𝒟[f <$> mx]`, for any lawful measure semantics: the
probability of an event is the expectation of its indicator, a constant comes out of the
expectation over a computation that does not fail, and the expectation is monotone in an
observation bounded on the support (`lintegral_id_evalDist_map_mono_of_mem_support`), and the
expectation of a finite sum is the sum of the expectations
(`lintegral_id_evalDist_map_finset_sum`).

An event after a draw: its probability is the expectation over the draw of its probability after
each output (`prEvent_bind_eq_lintegral_id_evalDist_map`), and at most the probability of an
event of the draw plus the largest probability after an output outside it
(`prEvent_bind_le_add_iSup`).
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
  exact lintegral_congr fun x ↦ by simp [Set.indicator_apply]

/-- Over a computation that does not fail, a constant comes out of an expectation. -/
theorem lintegral_id_evalDist_map_const_add (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (a : ℝ≥0∞) (f : α → ℝ≥0∞) :
    ∫⁻ r, r ∂𝒟[(fun x ↦ a + f x) <$> mx] = a + ∫⁻ r, r ∂𝒟[f <$> mx] := by
  rw [lintegral_id_evalDist_map_add mx (fun _ ↦ a) f]
  congr 1
  let : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map, lintegral_const, ← prEvent_true_eq_evalDist_apply_univ, hmx,
    mul_one]

/-- The expectation of a finite sum of scalar observations is the sum of their expectations. -/
theorem lintegral_id_evalDist_map_finset_sum {ι : Type} (S : Finset ι) (mx : m α)
    (f : ι → α → ℝ≥0∞) :
    ∫⁻ r, r ∂𝒟[(fun x ↦ ∑ i ∈ S, f i x) <$> mx] = ∑ i ∈ S, ∫⁻ r, r ∂𝒟[f i <$> mx] := by
  let : MeasurableSpace α := ⊤
  simp only [lintegral_id_evalDist_map]
  exact lintegral_finsetSum S fun _ _ ↦ Measurable.of_discrete

/-- An event after a draw has as probability the expectation, over the draw, of its probability
after each output. -/
theorem prEvent_bind_eq_lintegral_id_evalDist_map {β : Type} (mx : m α) (f : α → m β)
    (q : β → Prop) :
    Pr{let y ← mx >>= f}[q y] = ∫⁻ r, r ∂𝒟[(fun a ↦ Pr{let y ← f a}[q y]) <$> mx] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, lintegral_id_evalDist_map]

section Support

variable [MonadAttach m] [WeaklyLawfulMonadAttach m]

/-- An observation at most another at every output in the support has at most its
expectation. -/
theorem lintegral_id_evalDist_map_mono_of_mem_support (mx : m α) {f g : α → ℝ≥0∞}
    (hfg : ∀ x ∈ support mx, f x ≤ g x) :
    ∫⁻ r, r ∂𝒟[f <$> mx] ≤ ∫⁻ r, r ∂𝒟[g <$> mx] := by
  let : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
  exact lintegral_mono_ae (evalDist.ae_of_forall_mem_support mx _ MeasurableSet.of_discrete hfg)

/-- **An event after a draw.** The event `q` after `mx >>= f` has probability at most that of
`p` under `mx` plus the largest probability of `q` under `f a`, over the outputs `a` of `mx`
outside `p`. -/
theorem prEvent_bind_le_add_iSup {β : Type} (mx : m α) (f : α → m β) (p : α → Prop)
    (q : β → Prop) :
    Pr{let y ← mx >>= f}[q y] ≤
      Pr{let a ← mx}[p a] + ⨆ a ∈ support mx, ⨆ (_ : ¬ p a), Pr{let y ← f a}[q y] :=
  prEvent_bind_le_prEvent_add_of_support mx f p q fun a ha hp ↦
    le_iSup₂_of_le a ha (le_iSup_of_le hp le_rfl)

end Support

end

end LeanerVM.Protocol
