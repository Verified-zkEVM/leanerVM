import FORS.Statement
import Common.Signature
import Common.PiOnly
import Common.Linear
import Sphincs.ModelSigner
import Common.SeedKey

/-!
# The model's theorem in the random-permutation model

`FORS.h26_layered` is the random-oracle theorem of the model at the deployed configuration: 127
bits, `q / 2^127` for `q` hash calls. The model's game is the generic SUF-CMA game of `common`
(`experiment_eq`), so `Common.SufCma.rpm_bound` moves it to the random-permutation model:
`Q / 2^127 + Q² / 2^509` for `Q` permutation calls (the sponge's indifferentiability,
`Q² / 2^509`), which is at most `(Q + 1) · 2^-127` for `Q ≤ 2^128` (`Common.bits_add_sq_le`), and
past `2^128` the bound exceeds one. The statement's secret key is the seed `S0`, from which the
signer derives the scheme seed and the parameter again; a random-oracle bound passes to that form of
the model (`seedKeyed`, `Common.SufCma.SeedKeyed.romBound`). So the model is strongly unforgeable
at 127 bits against
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

/-- The model's ROM bound at `bits` bits, in the form of `Common.SufCma.rpm_bound`. -/
theorem modelScheme_romBound {bits : ℕ} (h : FORS.SecurityBits params bits) :
    RomBound modelScheme bits := by
  refine romBound_of_support _ _ fun q hq main hb' ↦ ?_
  have hbound : FORS.Security.HasHashQueryBound ⟨main⟩ q := by
    unfold FORS.Security.HasHashQueryBound
    rw [experiment_eq]
    exact hb'
  have hwin := h q hq ⟨main⟩ hbound
  unfold FORS.Security.forgeAdvantage at hwin
  rw [experiment_eq] at hwin
  exact hwin

section

attribute [local irreducible] FORS.Seeded.treeRoot FORS.Seeded.sign

theorem keygenRest_key (derived : FORS.MasterSeed × FORS.PublicParameter) :
    ∀ keys ∈ support (keygenRest derived), ∃ root, keys.2 = ⟨derived.1, derived.2, root⟩ := by
  intro keys hkeys
  unfold keygenRest at hkeys
  rw [mem_support_bind_iff] at hkeys
  obtain ⟨root, -, hroot⟩ := hkeys
  rw [support_pure, Set.mem_singleton_iff] at hroot
  exact ⟨root, by rw [hroot]⟩

theorem modelScheme_sign (derived : FORS.MasterSeed × FORS.PublicParameter) (root : FORS.Digest) :
    modelScheme.sign ⟨derived.1, derived.2, root⟩ =
      fun message ↦ FORS.Seeded.sign (m := OracleComp FORS.HashSpec) ⟨derived.1, derived.2, 0⟩ message :=
  funext fun message ↦ sign_root derived.1 derived.2 root message

end

attribute [local irreducible] FORS.Seeded.treeRoot FORS.Seeded.sign keygenRest deriveSeeded
  FORS.Seeded.keygen

/-- The model with the crate's secret key, the seed `S0`: key generation derives the scheme seed
and the parameter first, and the signer derives them again (`Common.SufCma.SeedKeyed`). -/
noncomputable def seedKeyed : SeedKeyed modelScheme (FORS.MasterSeed × FORS.PublicParameter) where
  derive := deriveSeeded
  rest _ := keygenRest
  signWith derived message :=
    FORS.Seeded.sign (m := OracleComp FORS.HashSpec) ⟨derived.1, derived.2, 0⟩ message
  keygen_eq := keygen_eq
  sign_eq _ derived keys hkeys := by
    obtain ⟨root, hroot⟩ := keygenRest_key derived keys hkeys
    rw [hroot]
    exact modelScheme_sign derived root

/-- The model with the seed as the key. -/
noncomputable abbrev modelSchemeFromSeed :
    SchemeWithHash FORS.MasterSeed FORS.PublicKey FORS.MasterSeed FORS.Message
      (Option FORS.Signature) FORS.Forgery :=
  seedKeyed.scheme

/-- From `bits ≤ 128` bits in the random-oracle model to `bits` bits in the random-permutation
model, for the model with the seed as the key, against adversaries that also query Keccak-256. -/
theorem modelScheme_rpmSecureH {bits : ℕ} (h : FORS.SecurityBits params bits) (hb : bits ≤ 128) :
    RpmSecureH modelSchemeFromSeed bits := by
  have hrom := seedKeyed.romBound (modelScheme_romBound h)
  intro Q hQ main hbound
  rcases le_or_gt Q (2 ^ 128) with hcap | hcap
  · exact (rpm_bound modelSchemeFromSeed bits hrom main Q Q hQ
      (QueryCostAtMost.mono_weight hbound oracleCalls_le_permCalls) hbound).trans
      (Common.bits_add_sq_le hcap (hb.trans (by norm_num)))
  · exact Common.le_succ_mul_inv_two_pow_of_lt (prEvent_le_one _) hb hcap

/-- **The model in the random-permutation model**, the seed as the key: 127 bits of SUF-CMA
security, from its 127 bits in the random-oracle model. -/
theorem modelScheme_stronglyUnforgeable (h : FORS.SecurityBits params 127) :
    StronglyUnforgeableWithHash modelSchemeFromSeed 127 :=
  rpmSecure_of_rpmSecureH (modelScheme_rpmSecureH h (by norm_num))

end Sphincs.Model
