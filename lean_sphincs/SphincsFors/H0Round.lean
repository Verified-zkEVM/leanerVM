import Mathlib

/-! **Dyadic rounding and exponential bounds** of the rational certificates (`H0SplitCert.lean`):
round down and up to a multiple of `2^-P`, iterated squaring rounded up, and the exponential's
upper bound `(1 - u / 2^s)^(-2^s)` and lower bound by partial sums. Apart from `H0SplitCert.lean`,
so that the kernel-checked tables, which evaluate them, do not depend on the bounds' proofs. -/

namespace SphincsFors.Security.H0

set_option exponentiation.threshold 512

/-- Round down to a multiple of `2^-P`. -/
def rdown (x : ℚ) (P : ℕ) : ℚ := ((⌊x * 2 ^ P⌋ : ℤ) : ℚ) / 2 ^ P

/-- Round up to a multiple of `2^-P`. -/
def rup (x : ℚ) (P : ℕ) : ℚ := ((⌈x * 2 ^ P⌉ : ℤ) : ℚ) / 2 ^ P

/-- Iterated squaring, rounded up: an upper bound for `x^(2^s)`. -/
def sqUp (P : ℕ) : ℕ → ℚ → ℚ
  | 0, x => x
  | s + 1, x => sqUp P s (rup (x * x) P)

/-- Upper bound for `e^u`: `(1 - u / 2^s)^(-2^s)`, rounded up. -/
def expUp (u : ℚ) (s P : ℕ) : ℚ := sqUp P s (rup (1 / (1 - u / 2 ^ s)) P)

/-- Partial sums of the exponential series with rounded-down terms. -/
def expLowGo (u : ℚ) (P : ℕ) : ℕ → ℕ → ℚ → ℚ → ℚ
  | 0, _, t, acc => acc + t
  | r + 1, j, t, acc => expLowGo u P r (j + 1) (rdown (t * u / (j + 1)) P) (acc + t)

/-- Lower bound for `e^u` from `J + 1` terms of the series. -/
def expLow (u : ℚ) (J P : ℕ) : ℚ := expLowGo u P J 0 1 0

/-- A lower bound for `e`. -/
def eLowQ : ℚ := 27182818283 / 10 ^ 10

theorem le_rup (x : ℚ) (P : ℕ) : x ≤ rup x P := by
  unfold rup
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

end SphincsFors.Security.H0
