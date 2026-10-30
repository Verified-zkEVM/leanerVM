import LeanXmss.StatementRpm
import XmssSecurity.Proof.Bridge.Security
import Common.Linear
import Common.PiOnly

/-!
# leanXMSS in the random-permutation model

The ROM theorem (`Bridge.leanXmss_security`, 127 bits) moved to the random-permutation model by
`Common.SufCma.rpm_bound`: the leanXMSS game is the generic SUF-CMA game of
`Common.Signature` (`experiment_eq_romExperiment`), and an RPM adversary with the signing
oracle, its permutation queries answered by the indifferentiability simulator, is a ROM
adversary whose experiment makes at most as many hash calls as the RPM game makes calls of `H`,
`π` and `π⁻¹`.
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace XmssSecurity

/- A weight bound of a concrete game must not be unfolded: it recurses through the whole game. -/
attribute [local irreducible] IsWeightBound

/-- The leanXMSS ROM experiment is the generic one. -/
theorem experiment_eq_romExperiment
    (main : LeanXmss.PublicKey →
      OracleComp (LeanXmss.OracleWorld + LeanXmss.SigningSpec) LeanXmss.Forgery) :
    LeanXmss.Security.experiment ⟨main⟩ = romExperiment LeanXmss.Rpm.scheme main := by
  have h : LeanXmss.Security.countedOracle = countedImpl := by
    unfold LeanXmss.Security.countedOracle countedImpl
    congr 1
  unfold LeanXmss.Security.experiment romExperiment
  rw [h]
  rfl

/-- The ROM theorem in the form of `Common.SufCma.rpm_bound`. -/
theorem romBound : ∀ q, 1 ≤ q →
    ∀ main : LeanXmss.PublicKey →
      OracleComp (LeanXmss.OracleWorld + LeanXmss.SigningSpec) LeanXmss.Forgery,
      (∀ r ∈ support (romExperiment LeanXmss.Rpm.scheme main), r.2 ≤ q) →
        Pr{let r ← romExperiment LeanXmss.Rpm.scheme main}[r.1 = true] ≤
          q / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  intro q hq main hb
  rw [← experiment_eq_romExperiment] at hb ⊢
  exact Bridge.leanXmss_security q hq ⟨main⟩ hb

/-- **leanXMSS in the random-permutation model, refined**: an adversary whose game makes at most
`q ≥ 1` calls of `H`, `π` and `π⁻¹` and at most `Q` permutation calls on every path forges with
probability at most `q / 2^127 + Q² / 2^509`. -/
theorem leanXmss_rpm_security_calls (q Q : ℕ) (hq1 : 1 ≤ q) (adversary : LeanXmss.Rpm.Adversary)
    (hq : LeanXmss.Rpm.HasCallBound adversary q)
    (hQ : LeanXmss.Rpm.HasPermutationBound adversary Q) :
    LeanXmss.Rpm.forgeAdvantage adversary ≤
      q / ((2 ^ 127 : ℕ) : ℝ≥0∞) + (Q ^ 2 : ℝ≥0∞) / 2 ^ 509 := by
  exact rpm_bound LeanXmss.Rpm.scheme 127
    romBound adversary.main q Q hq1 hq hQ

/-- **leanXMSS against adversaries that also query Keccak-256**: an adversary whose game makes at
most `Q ≥ 1` permutation calls on every path forges with probability at most `(Q + 1) · 2^-127`:
`Q / 2^127 + Q² / 2^509` (`rpm_bound_perm`), at most `(Q + 1) · 2^-127` for `Q ≤ 2^128`
(`Common.bits_add_sq_le`); past `2^128` the bound is at least one. -/
theorem leanXmss_rpm_securityH : RpmSecureH LeanXmss.Rpm.scheme 127 := by
  intro Q hQ main hbound
  rcases le_or_gt Q (2 ^ 128) with hcap | hcap
  · exact (rpm_bound_perm LeanXmss.Rpm.scheme 127 romBound main Q hQ hbound).trans
      (Common.bits_add_sq_le hcap (by norm_num))
  · exact Common.le_succ_mul_inv_two_pow_of_lt (prEvent_le_one _) (by norm_num) hcap

/-- **leanXMSS in the random-permutation model**: the statement's adversary queries `π` and `π⁻¹`
alone, and its game is the game above with each hash call expanded into its permutation calls
(`Common.SufCma.rpmSecure_of_rpmSecureH`). -/
theorem leanXmss_rpm_security : LeanXmss.Rpm.LeanXmssRpmSecurityStatement :=
  rpmSecure_of_rpmSecureH leanXmss_rpm_securityH

end XmssSecurity
