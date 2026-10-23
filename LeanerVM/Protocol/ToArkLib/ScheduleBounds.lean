/-
  LeanerVM.Protocol.ToArkLib.ScheduleBounds

  Per-challenge bounds on the errors of schedules side by side, and marks that single out some
  challenges of a schedule for a bound of their own. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Schedule

/-!
# Per-challenge bounds on schedule errors

The errors of `LeanerVM.Protocol.ToArkLib.Schedule` are summed by their own lemmas; a random-oracle
argument charges them one challenge at a time instead, and needs every challenge's error below a
budget. Some challenges carry another budget than the rest (a challenge drawn after a proof of
work, for instance). `markAppend` marks the challenges of two schedules side by side, as
`errAppend` assigns their errors, and `errAppend_le_mark` bounds every challenge's error by the
budget its mark selects, from the two schedules' bounds. `errAppend_le_const` is the unmarked
case, and the schedules of `Schedule` meet a constant bound on each challenge: `sayError_le`,
`drawsError_le`,
`roundsError_le`, `stepError_le`, `stepsError_le`, `oddError_le`, `gkrError_le`.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

/-! ## Marks side by side -/

/-- Marks on the challenges of two schedules in sequence: each challenge keeps the mark its
schedule gave it, as `errAppend` keeps its error. -/
def markAppend {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    (b₁ : pSpec₁.ChallengeIdx → Bool) (b₂ : pSpec₂.ChallengeIdx → Bool) :
    (pSpec₁ ++ₚ pSpec₂).ChallengeIdx → Bool :=
  Sum.elim b₁ b₂ ∘ ChallengeIdx.sumEquiv.symm

/-- **Bounds by mark, side by side.** If every challenge of each schedule has its error below the
budget `B` its mark selects, so does every challenge of the two in sequence. -/
theorem errAppend_le_mark {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    (B : Bool → ℝ≥0) {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    {b₁ : pSpec₁.ChallengeIdx → Bool} {b₂ : pSpec₂.ChallengeIdx → Bool}
    (h₁ : ∀ i, ε₁ i ≤ B (b₁ i)) (h₂ : ∀ i, ε₂ i ≤ B (b₂ i)) (i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx) :
    errAppend ε₁ ε₂ i ≤ B (markAppend b₁ b₂ i) := by
  simp only [errAppend, markAppend, Function.comp_apply]
  cases ChallengeIdx.sumEquiv.symm i with
  | inl j => exact h₁ j
  | inr j => exact h₂ j

/-- A constant bound on every challenge's error, side by side. -/
theorem errAppend_le_const {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {c : ℝ≥0} {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : ∀ i, ε₁ i ≤ c) (h₂ : ∀ i, ε₂ i ≤ c) (i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx) :
    errAppend ε₁ ε₂ i ≤ c :=
  errAppend_le_mark (fun _ ↦ c) (b₁ := fun _ ↦ false) (b₂ := fun _ ↦ false) h₁ h₂ i

/-! ## The schedules' errors, challenge by challenge -/

/-- A message has no challenge: any bound holds. -/
theorem sayError_le (M : Type) (c : ℝ≥0) : ∀ i, sayError M i ≤ c := fun i ↦ (IsEmpty.false i).elim

variable (C : Type)

/-- Every challenge of `k` draws has the error `e`. -/
theorem drawsError_le (e : ℝ≥0) : (k : ℕ) → ∀ i, drawsError C e k i ≤ e
  | 0 => fun i ↦ Fin.elim0 i.1
  | k + 1 => errAppend_le_const (drawsError_le e k) fun _ ↦ le_rfl

/-- Every round's challenge has the error `e`. -/
theorem roundsError_le (d : ℕ) (e : ℝ≥0) : (m : ℕ) → ∀ i, roundsError C d e m i ≤ e
  | 0 => fun i ↦ Fin.elim0 i.1
  | m + 1 => errAppend_le_const
      (errAppend_le_const (sayError_le _ e) fun _ ↦ le_rfl) (roundsError_le d e m)

/-- A layer's challenges: the combiner's error, the rounds' `2 ^ ρ · u`, the combination
challenges' `u`, all below `c`. -/
theorem stepError_le [SampleableType C] (nside ρ m : ℕ) {combiner u c : ℝ≥0} (hc : combiner ≤ c)
    (hr : ((2 ^ ρ : ℕ) : ℝ≥0) * u ≤ c) (hu : u ≤ c) :
    ∀ i, stepError C nside ρ m combiner u i ≤ c :=
  errAppend_le_const (errAppend_le_const (errAppend_le_const (fun _ ↦ hc)
    fun i ↦ (roundsError_le C _ _ m i).trans hr) (sayError_le _ c))
    fun i ↦ (drawsError_le C u ρ i).trans hu

/-- The layers of radix four: every challenge below `c`, when `(nside − 1) · u`, `4 · u` and
`u` are. -/
theorem stepsError_le [SampleableType C] (nside : ℕ) {u c : ℝ≥0}
    (hc : ((nside - 1 : ℕ) : ℝ≥0) * u ≤ c)
    (hr : ((2 ^ 2 : ℕ) : ℝ≥0) * u ≤ c) (hu : u ≤ c) :
    (k m : ℕ) → ∀ i, stepsError C nside u k m i ≤ c
  | 0, _ => fun i ↦ Fin.elim0 i.1
  | k + 1, m => errAppend_le_const (stepError_le C nside 2 m hc hr hu)
      (stepsError_le nside hc hr hu k (m + 2))

/-- The binary layer: every challenge below `c`, when `(nside − 1) · u`, `2 · u` and `u` are. -/
theorem oddError_le [SampleableType C] (nside : ℕ) {u c : ℝ≥0}
    (hc : ((nside - 1 : ℕ) : ℝ≥0) * u ≤ c)
    (hr : ((2 ^ 1 : ℕ) : ℝ≥0) * u ≤ c) (hu : u ≤ c) : (r : ℕ) → ∀ i, oddError C nside u r i ≤ c
  | 0 => fun i ↦ Fin.elim0 i.1
  | _ + 1 => stepError_le C nside 1 0 hc hr hu

/-- **The grand-product argument, challenge by challenge**: every challenge's error is at most
`max (nside − 1) 4 · u`. -/
theorem gkrError_le [SampleableType C] (u : ℝ≥0) (nside μ : ℕ) :
    ∀ i, gkrError C u nside μ i ≤ ((max (nside - 1) 4 : ℕ) : ℝ≥0) * u := by
  have hc : ((nside - 1 : ℕ) : ℝ≥0) * u ≤ ((max (nside - 1) 4 : ℕ) : ℝ≥0) * u :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_max_left _ _)) zero_le
  have h4 : ((2 ^ 2 : ℕ) : ℝ≥0) * u ≤ ((max (nside - 1) 4 : ℕ) : ℝ≥0) * u :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_max_right _ _)) zero_le
  have h2 : ((2 ^ 1 : ℕ) : ℝ≥0) * u ≤ ((max (nside - 1) 4 : ℕ) : ℝ≥0) * u :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by norm_num)) zero_le).trans h4
  have hu : u ≤ ((max (nside - 1) 4 : ℕ) : ℝ≥0) * u :=
    le_mul_of_one_le_left zero_le (by exact_mod_cast (show 1 ≤ max (nside - 1) 4 by omega))
  exact errAppend_le_const (errAppend_le_const (oddError_le C nside hc h2 hu _)
    (stepsError_le C nside hc h4 hu _ _)) fun _ ↦ zero_le

end
end LeanerVM.Protocol
