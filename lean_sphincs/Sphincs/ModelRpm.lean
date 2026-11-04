import FORS.Statement
import Common.Signature
import Common.PiOnly
import Common.Linear
import Sphincs.Model

/-!
# The model's theorem in the random-permutation model

`FORS.h26_layered` is the random-oracle theorem of the model at the deployed configuration: 127
bits, `q / 2^127` for `q` hash calls. The model's game is the generic SUF-CMA game of `common`
(`experiment_eq`), so `Common.SufCma.rpm_bound` moves it to the random-permutation model:
`Q / 2^127 + Q² / 2^509` for `Q` permutation calls (the sponge's indifferentiability,
`Q² / 2^509`), which is at most `(Q + 1) · 2^-127` for `Q ≤ 2^128` (`Common.bits_add_sq_le`), and
past `2^128` the bound exceeds one. So the model is strongly unforgeable at 127 bits against
adversaries that also query Keccak-256, and so against the statement's, which query `π` and `π⁻¹`
alone (`Common.SufCma.rpmSecure_of_rpmSecureH`): `modelScheme_stronglyUnforgeable`, from
`FORS.h26_layered` in `Sphincs/Security.lean`.
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace Sphincs.Model

attribute [local instance] params

/- A weight bound of a concrete game must not be unfolded: it recurses through the whole game. -/
attribute [local irreducible] QueryCostAtMost

/-- The model in the generic SUF-CMA game: the seed, key generation, the deterministic signer, the
verifier, and the winning condition (`FORS.SigningTranscript`). -/
noncomputable def modelScheme :
    SchemeWithHash FORS.MasterSeed FORS.PublicKey FORS.Seeded.SecretKey FORS.Message
      (Option FORS.Signature) FORS.Forgery where
  sample := FORS.sampleMasterSeed
  keygen := FORS.Seeded.keygen
  sign sk message := FORS.Seeded.sign (m := OracleComp FORS.HashSpec) sk message
  verify pk forgery :=
    FORS.Concrete.verify (m := OracleComp FORS.HashSpec) pk forgery.message forgery.signature
  win log forgery :=
    decide (FORS.SigningTranscript.Valid log ∧ ¬FORS.SigningTranscript.Contains log forgery)

/-- The model's ROM experiment is the generic one. -/
theorem experiment_eq
    (main : FORS.PublicKey → OracleComp (World + (FORS.Message →ₒ Option FORS.Signature))
      FORS.Forgery) :
    FORS.Security.experiment ⟨main⟩ = romExperiment modelScheme main := by
  have h : FORS.Security.countedOracle = countedImpl := by
    unfold FORS.Security.countedOracle countedImpl
    congr 1
  unfold FORS.Security.experiment romExperiment
  rw [h]
  rfl

/-- From `bits ≤ 128` bits in the random-oracle model to `bits` bits in the random-permutation
model, against adversaries that also query Keccak-256. -/
theorem modelScheme_rpmSecureH {bits : ℕ} (h : FORS.SecurityBits params bits) (hb : bits ≤ 128) :
    RpmSecureH modelScheme bits := by
  have hrom : ∀ q, 1 ≤ q →
      ∀ main : FORS.PublicKey → OracleComp (World + (FORS.Message →ₒ Option FORS.Signature))
        FORS.Forgery,
        (∀ r ∈ support (romExperiment modelScheme main), r.2 ≤ q) →
          Pr{let r ← romExperiment modelScheme main}[r.1 = true] ≤
            q / ((2 ^ bits : ℕ) : ℝ≥0∞) := by
    intro q hq main hb'
    have hbound : FORS.Security.HasHashQueryBound ⟨main⟩ q := by
      unfold FORS.Security.HasHashQueryBound
      rw [experiment_eq]
      exact hb'
    have hwin := h q hq ⟨main⟩ hbound
    unfold FORS.Security.forgeAdvantage at hwin
    rw [experiment_eq] at hwin
    exact hwin
  intro Q hQ main hbound
  rcases le_or_gt Q (2 ^ 128) with hcap | hcap
  · exact (rpm_bound modelScheme bits hrom main Q Q hQ
      (QueryCostAtMost.mono_weight hbound oracleCalls_le_permCalls) hbound).trans
      (Common.bits_add_sq_le hcap (hb.trans (by norm_num)))
  · exact Common.le_succ_mul_inv_two_pow_of_lt (prEvent_le_one _) hb hcap

/-- **The model in the random-permutation model**: 127 bits of SUF-CMA security, from its 127
bits in the random-oracle model. -/
theorem modelScheme_stronglyUnforgeable (h : FORS.SecurityBits params 127) :
    StronglyUnforgeableWithHash modelScheme 127 :=
  rpmSecure_of_rpmSecureH (modelScheme_rpmSecureH h (by norm_num))

end Sphincs.Model
