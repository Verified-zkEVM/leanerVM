module

public import Mathlib.Tactic

/-!
# Bounds: Karatsuba's product and the schoolbook product, as definitions

The bounds `Cost/Bounds/PMFFT/Karatsuba.lean` proves of the compiled `karatsuba` (the schedule's
middle branch of `fftMulContext`'s product, `FFT.fftSchedule`: both factors of `33` to `4096`
coefficients) and of the schoolbook branch (a factor of at most `32` coefficients, the fold over
the small one), apart from their proofs so that their values evaluate alone.
-/

namespace LeanVM.Cost.Bounds.PMFFT

public section

/-- A schoolbook product of factors of at most `32` coefficients. -/
@[expose] def karaBase : ℕ := 1040000

/-- **Karatsuba's product on factors of at most `n` coefficients**: the schoolbook product at most
`32`, else three products of half the size and the splits, sums and shifts, linear in `n`. -/
@[expose] def karaBound (n : ℕ) : ℕ :=
  if h : n ≤ 32 then karaBase else 3 * karaBound ((n + 1) / 2) + 2000 * n + 5000
decreasing_by omega

/-- **The schoolbook branch** (a factor of at most `32` coefficients, the other of at most `n`):
`906·32` per coefficient of the other factor, and the small factor's own terms. -/
@[expose] def schoolMulBound (n : ℕ) : ℕ := 29015 * n + 103000

theorem karaBound_eq (n : ℕ) :
    karaBound n = if n ≤ 32 then karaBase else 3 * karaBound ((n + 1) / 2) + 2000 * n + 5000 := by
  rw [karaBound]
  split <;> simp_all

theorem karaBase_le_karaBound (n : ℕ) : karaBase ≤ karaBound n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [karaBound_eq]
    split
    · exact le_rfl
    · have := ih ((n + 1) / 2) (by omega)
      omega

/-- **`karaBound` is monotone.** -/
theorem karaBound_mono : ∀ {m n : ℕ}, m ≤ n → karaBound m ≤ karaBound n := by
  intro m n
  induction n using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    intro hmn
    rw [karaBound_eq m, karaBound_eq n]
    by_cases hn : n ≤ 32
    · simp [show m ≤ 32 by omega, hn]
    · simp only [hn, ↓reduceIte]
      by_cases hm : m ≤ 32
      · simp only [hm, ↓reduceIte]
        have := karaBase_le_karaBound ((n + 1) / 2)
        omega
      · simp only [hm, ↓reduceIte]
        have := ih ((n + 1) / 2) (by omega) (show (m + 1) / 2 ≤ (n + 1) / 2 by omega)
        omega

/-- **Karatsuba's product below the transform** (`4096` coefficients each, the schedule's
`mid`): `2543497000 ≈ 2^31.24`. -/
theorem karaBound_4096 : karaBound 4096 = 2543497000 := by
  simp only [karaBound_eq (4096 : ℕ), karaBound_eq (2048 : ℕ), karaBound_eq (1024 : ℕ),
    karaBound_eq (512 : ℕ), karaBound_eq (256 : ℕ), karaBound_eq (128 : ℕ), karaBound_eq (64 : ℕ),
    karaBound_eq (32 : ℕ), karaBase]
  norm_num

end

end LeanVM.Cost.Bounds.PMFFT
