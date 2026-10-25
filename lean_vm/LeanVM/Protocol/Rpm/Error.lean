/-
  LeanVM.Protocol.Rpm.Error

  The cost of building Keccak-256 and Keccak-f[1600] from one random permutation, `q² / 2^508`
  for `q` permutation calls (`rpmError`), and its linear form `q · 2^-379` for `q ≤ 2^129`, which
  the end statements state.
-/

import Statement.LeanVm
import Common.Linear

/-!
# The random-permutation transfer's error

The proofs move each theorem from two independent random functions to one random permutation
with `Common.keccak256_transfer2`, at a cost of `q² / 2^508` for `q` permutation calls
(`rpmError`). Under the cap `q ≤ 2^129` this is at most `q · 2^-379` (`rpmError_le_linear`), the
term the end statements of `Statement/` state; the caps hold for an adversary of at most `2^128`
queries with the verifier's calls (`le_two_pow_129_of_verifier`), and for the honest prover and
the verifier at a fuel of at most `2^64` (`completenessPermCalls_le`).
-/

namespace LeanVM

open scoped ENNReal

/-- The transfer's error for an experiment of `q` permutation calls: `q² / 2^508`, the cost of
building Keccak-256 and Keccak-f[1600] from one random permutation rather than taking them
independent random functions (`Common.keccak256_transfer2`). -/
noncomputable def rpmError (q : ℕ) : ℝ≥0∞ := (q ^ 2 : ℝ≥0∞) / 2 ^ 508

/-- **The transfer's error, linear under a cap**: `q² / 2^508 ≤ q · 2^-379` for `q ≤ 2^129`. -/
theorem rpmError_le_linear {q : ℕ} (hq : q ≤ 2 ^ 129) :
    rpmError q ≤ (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 379 :=
  Common.sq_div_le_mul_inv_pow (k := 129) 379 hq

/-- The verifier's permutation calls, `12008 · 2^32`, are at most `2^128`. -/
theorem verifierPermCalls_le : verifierPermCalls ≤ 2 ^ 128 := by
  show verifierQueries * 2 ^ 32 ≤ 2 ^ 128
  rw [show verifierQueries = 12008 from rfl]
  norm_num

/-- Two counts of at most `2^128` add to at most `2^129`. -/
theorem add_le_two_pow_129 {a b : ℕ} (ha : a ≤ 2 ^ 128) (hb : b ≤ 2 ^ 128) : a + b ≤ 2 ^ 129 :=
  calc a + b ≤ 2 ^ 128 + 2 ^ 128 := Nat.add_le_add ha hb
    _ = 2 ^ 129 := by norm_num

/-- An adversary's `Q ≤ 2^128` queries and the verifier's calls are at most `2^129`. -/
theorem le_two_pow_129_of_verifier {Q : ℕ} (hQ : Q ≤ 2 ^ 128) :
    Q + verifierPermCalls ≤ 2 ^ 129 :=
  add_le_two_pow_129 hQ verifierPermCalls_le

/-- The honest prover's and the verifier's permutation calls at a fuel of at most `2^64` are at
most `2^113`, so at most `2^129`. -/
theorem completenessPermCalls_le {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    completenessPermCalls fuel ≤ 2 ^ 129 := by
  unfold completenessPermCalls
  calc (12012 + 48017 * (2 ^ 27 + 2 * fuel + 2)) * 2 ^ 32
      ≤ (12012 + 48017 * (2 ^ 27 + 2 * 2 ^ 64 + 2)) * 2 ^ 32 := by gcongr
    _ ≤ 2 ^ 129 := by norm_num

end LeanVM
