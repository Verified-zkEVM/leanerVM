/-
  LeanerVM.Protocol.ToVCVio.ScalarExpectation

  Below this header, a verbatim copy of the declarations VCVio pull request 817 (`9146f78c`) adds
  to `VCVio/EvalDist/Defs/Measure/Core.lean` (its section "Expectations of a scalar observation")
  and to `VCVio/EvalDist/Monad/Measure.lean` (its section "Expectations bounded on the support"),
  which the VCVio pin does not contain. Deleted when the pin contains them; its importers then
  import those two modules.

  Copyright (c) 2026 Devon Tuma. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Defs.Measure.Core
public import VCVio.EvalDist.Monad.Measure

/-!
# Expectations of a scalar observation

The laws of the expectation `∫⁻ r, r ∂𝒟[f <$> mx]` of a scalar observation `f`: its integral
form, bounds, monotonicity, additivity, the zero observation, and the tower law for a bind.
-/

public section

open MeasureTheory

universe u v

/-!
## Expectations of a scalar observation

For `f : α → ℝ≥0∞`, `∫⁻ r, r ∂𝒟[f <$> mx]` is the expectation of `f` under the successful-output
measure `𝒟[mx]`. It is not normalised by the success mass `𝒟[mx] Set.univ`: failure contributes
zero, so for a constant observation `c` it is `c * 𝒟[mx] Set.univ`. Only `ℝ≥0∞` needs a
measurable space in this form, so the laws below place none on `α`, except
`lintegral_id_evalDist_map`, which identifies the expectation with `∫⁻ x, f x ∂𝒟[mx]` at a
discrete measurable space on `α`.
-/

/-- The expectation of a scalar observation is its integral against the computation's
successful-output measure, at any discrete measurable space on the output type. -/
theorem lintegral_id_evalDist_map {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (mx : m α) (f : α → ENNReal) :
    ∫⁻ r, r ∂𝒟[f <$> mx] = ∫⁻ x, f x ∂𝒟[mx] :=
  lintegral_evalDist_map mx .of_discrete measurable_id

/-- A pointwise bound on a scalar observation bounds its expectation. -/
theorem lintegral_id_evalDist_map_le_of_le {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α)
    {f : α → ENNReal} {c : ENNReal} (hf : ∀ x, f x ≤ c) : ∫⁻ r, r ∂𝒟[f <$> mx] ≤ c := by
  let _ : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map]
  calc ∫⁻ x, f x ∂𝒟[mx] ≤ ∫⁻ _, c ∂𝒟[mx] := lintegral_mono hf
    _ = c * 𝒟[mx] Set.univ := lintegral_const c
    _ ≤ c := mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx)

/-- The expectation of a scalar observation is monotone in the observation. -/
theorem lintegral_id_evalDist_map_mono {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α)
    {f g : α → ENNReal} (hfg : ∀ x, f x ≤ g x) :
    ∫⁻ r, r ∂𝒟[f <$> mx] ≤ ∫⁻ r, r ∂𝒟[g <$> mx] := by
  let _ : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
  exact lintegral_mono hfg

/-- The expectation of a sum of scalar observations is the sum of their expectations. -/
theorem lintegral_id_evalDist_map_add {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α)
    (f g : α → ENNReal) :
    ∫⁻ r, r ∂𝒟[(fun x ↦ f x + g x) <$> mx] =
      (∫⁻ r, r ∂𝒟[f <$> mx]) + ∫⁻ r, r ∂𝒟[g <$> mx] := by
  let _ : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map, lintegral_id_evalDist_map,
    lintegral_add_left Measurable.of_discrete]

/-- The constant-zero observation has expectation zero. -/
@[simp]
theorem lintegral_id_evalDist_map_zero {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α) :
    ∫⁻ r, r ∂𝒟[(fun _ ↦ (0 : ENNReal)) <$> mx] = 0 :=
  le_zero_iff.mp (lintegral_id_evalDist_map_le_of_le mx fun _ ↦ le_rfl)

/-- The expectation of a scalar observation of a bind is the expectation, under the head's
measure, of the observation's expectation under the continuation. -/
theorem lintegral_id_evalDist_map_bind {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type} (mx : m α)
    (g : α → m β) (f : β → ENNReal) :
    ∫⁻ r, r ∂𝒟[f <$> (mx >>= g)] = ∫⁻ r, r ∂𝒟[(fun x ↦ ∫⁻ r, r ∂𝒟[f <$> g x]) <$> mx] := by
  let _ : MeasurableSpace α := ⊤
  let _ : MeasurableSpace β := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map,
    lintegral_evalDist_bind_of_discrete mx g (g := f) Measurable.of_discrete]
  simp only [lintegral_id_evalDist_map]

/-! ## Expectations bounded on the support -/

/-- A bound on a scalar observation at every output in the support bounds its expectation. -/
theorem lintegral_id_evalDist_map_le_of_le_of_mem_support {m : Type → Type v} [Monad m]
    [LawfulMonad m] [MonadAttach m] [WeaklyLawfulMonadAttach m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α : Type} (mx : m α) {f : α → ENNReal} {c : ENNReal}
    (hf : ∀ x ∈ support mx, f x ≤ c) : ∫⁻ r, r ∂𝒟[f <$> mx] ≤ c := by
  let _ : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map]
  calc ∫⁻ x, f x ∂𝒟[mx] ≤ ∫⁻ _, c ∂𝒟[mx] :=
        lintegral_mono_ae (evalDist.ae_of_forall_mem_support mx _ MeasurableSet.of_discrete hf)
    _ = c * 𝒟[mx] Set.univ := lintegral_const c
    _ ≤ c := mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx)
