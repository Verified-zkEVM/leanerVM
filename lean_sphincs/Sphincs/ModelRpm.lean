import FORS.Statement
import FORS.CrateStatic
import Common.Signature
import Common.PiOnly
import Common.Linear
import Common.StaticSwap
import Sphincs.Model
import Sphincs.Queries

/-!
# From the model's theorem to the crate's signer, in the random-permutation model

`FORS.h26_layered` is the random-oracle theorem of upstream's model at the deployed configuration:
127 bits, `q / 2^127` for `q` hash calls, for the model's key generation and signer
(`FORS.Seeded.keygen`, `FORS.Seeded.sign`: a landing call, sibling subtrees, the verifier's
recomputation of each layer's root). The model's game is the generic SUF-CMA game of `common`
(`experiment_eq`).

The statement's key generation and signer are the crate's (`sign_with`: the key expanded again,
the top tree rebuilt, every tree built level by level), not the model's call for call; their copy in
the model's hash monad is `FORS.Crate.keygen` / `FORS.Crate.sign` (`crateScheme`, the seed as the
secret key). On every answer function the crate's copy gives the model's public key and
signatures with at least the model's hash calls (`FORS.Crate.eval_keygen`, `eval_sign`,
`hashCalls_keygen`, `hashCalls_sign`), and both query only inputs of at most 2084 bytes
(`Sphincs.Queries`): `Common.SufCma.StaticSwap.romBound` moves the model's bound to the crate's
copy (`crateScheme_romBound`). `Common.SufCma.rpm_bound` then moves it to the random-permutation
model: `Q / 2^127 + Q² / 2^509` for `Q` permutation calls (the sponge's indifferentiability), at
most `(Q + 1) · 2^-127` for `Q ≤ 2^128` (`Common.bits_add_sq_le`); past `2^128` the bound exceeds
one. So the crate's copy is strongly unforgeable at 127 bits against adversaries that also query
Keccak-256, and so against the statement's, which query `π` and `π⁻¹` alone
(`Common.SufCma.rpmSecure_of_rpmSecureH`): `crateScheme_stronglyUnforgeable`.
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace Sphincs.Model

attribute [local instance] params

/- A weight bound of a concrete game must not be unfolded: it recurses through the whole game. -/
attribute [local irreducible] QueryCostAtMost

/-- Upstream's model in the generic SUF-CMA game: the seed, key generation, the deterministic
signer, the verifier, and the winning condition (`FORS.SigningTranscript`). -/
noncomputable def modelScheme :
    SchemeWithHash FORS.MasterSeed FORS.PublicKey FORS.Seeded.SecretKey FORS.Message
      (Option FORS.Signature) FORS.Forgery where
  sample := FORS.sampleMasterSeed
  keygen := FORS.Seeded.keygen
  sign sk message := (FORS.Seeded.sign sk message : OracleComp FORS.HashSpec _)
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

/-- The model's ROM bound at `bits` bits, on every adversary whose experiment makes at most `q`
hash calls on every outcome. -/
theorem modelScheme_bound {bits : ℕ} (h : FORS.SecurityBits params bits) (q : ℕ) (hq : 1 ≤ q)
    (main : FORS.PublicKey → OracleComp (World + (FORS.Message →ₒ Option FORS.Signature))
      FORS.Forgery)
    (hcost : ∀ r ∈ support (romExperiment modelScheme main), r.2 ≤ q) :
    Pr{let r ← romExperiment modelScheme main}[r.1 = true] ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞) := by
  have hbound : FORS.Security.HasHashQueryBound ⟨main⟩ q := by
    unfold FORS.Security.HasHashQueryBound
    rw [experiment_eq]
    exact hcost
  have hwin := h q hq ⟨main⟩ hbound
  unfold FORS.Security.forgeAdvantage at hwin
  rw [experiment_eq] at hwin
  exact hwin

/-- The crate's key generation and signer in the generic SUF-CMA game, the seed `SK.seed` as the
secret key (`FORS.Crate.keygen`, `FORS.Crate.sign`); the model's verifier and winning condition. -/
noncomputable def crateScheme :
    SchemeWithHash FORS.MasterSeed FORS.PublicKey FORS.MasterSeed FORS.Message
      (Option FORS.Signature) FORS.Forgery where
  sample := FORS.sampleMasterSeed
  keygen seed := (FORS.Crate.keygen seed : OracleComp FORS.HashSpec _)
  sign seed message := (FORS.Crate.sign seed message : OracleComp FORS.HashSpec _)
  verify := modelScheme.verify
  win := modelScheme.win

/-- **The crate's signer for the model's**: the same public key and signatures on every answer
function, with at least the model's hash calls (`FORS/CrateStatic.lean`). -/
noncomputable def staticSwap : StaticSwap modelScheme crateScheme where
  keep := id
  sample_eq := rfl
  verify_eq := rfl
  win_eq := rfl
  keygen_eval f seed := by
    simp only [modelScheme, crateScheme, id]
    exact FORS.Crate.eval_keygen f seed
  keygen_calls f seed := by
    simp only [modelScheme, crateScheme]
    exact FORS.Crate.hashCalls_keygen f seed
  sign_eval f seed message := by
    simp only [modelScheme, crateScheme, id]
    exact FORS.Crate.eval_sign f seed message
  sign_calls f seed message := by
    simp only [modelScheme, crateScheme, id]
    exact FORS.Crate.hashCalls_sign f seed message

/-- The crate's ROM bound at `bits` bits, from the model's. -/
theorem crateScheme_romBound {bits : ℕ} (h : FORS.SecurityBits params bits) :
    RomBound crateScheme bits :=
  StaticSwap.romBound staticSwap Queries.Honest Queries.queriesIn_seededKeygen
    Queries.queriesIn_crateKeygen Queries.queriesIn_seededSign Queries.queriesIn_crateSign
    (modelScheme_bound h)

/-- From `bits ≤ 128` bits in the random-oracle model to `bits` bits in the random-permutation
model, for the crate's signer, against adversaries that also query Keccak-256. -/
theorem crateScheme_rpmSecureH {bits : ℕ} (h : FORS.SecurityBits params bits) (hb : bits ≤ 128) :
    RpmSecureH crateScheme bits := by
  have hrom := crateScheme_romBound h
  intro Q hQ main hbound
  rcases le_or_gt Q (2 ^ 128) with hcap | hcap
  · exact (rpm_bound crateScheme bits hrom main Q Q hQ
      (QueryCostAtMost.mono_weight hbound oracleCalls_le_permCalls) hbound).trans
      (Common.bits_add_sq_le hcap (hb.trans (by norm_num)))
  · exact Common.le_succ_mul_inv_two_pow_of_lt (prEvent_le_one _) hb hcap

/-- **The crate's signer in the random-permutation model**: 127 bits of SUF-CMA security, from the
model's 127 bits in the random-oracle model. -/
theorem crateScheme_stronglyUnforgeable (h : FORS.SecurityBits params 127) :
    StronglyUnforgeableWithHash crateScheme 127 :=
  rpmSecure_of_rpmSecureH (crateScheme_rpmSecureH h (by norm_num))

end Sphincs.Model
