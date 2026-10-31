module

public import XmssSecurity.Proof.EvalDistEq
public import XmssSecurity.Proof.Seeded.KeyDerivation

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option backward.isDefEq.respectTransparency false

theorem randomizerHashInput_injective {p₁ p₂ : PublicParameter} {s₁ s₂ : MasterSeed}
    {e₁ e₂ : LeafIndex} {m₁ m₂ : Message}
    (h : randomizerHashInput p₁ s₁ e₁ m₁ = randomizerHashInput p₂ s₂ e₂ m₂) :
    p₁ = p₂ ∧ s₁ = s₂ ∧ e₁ = e₂ ∧ m₁ = m₂ := by
  unfold randomizerHashInput at h
  obtain ⟨hprefix, hm⟩ := List.append_inj' h (by simp [length_bytesLE])
  obtain ⟨hprefix, hs⟩ := List.append_inj' hprefix (by simp [length_bytesLE])
  obtain ⟨hp, htweak⟩ := List.append_inj' hprefix (by simp)
  have hf := fieldBytes_injective htweak
  have he : e₁ = e₂ := by
    apply Fin.ext
    have h := congrArg BitVec.toNat (congrArg TweakFields.lo hf)
    simpa [tweakFields, LeafIndex, lifetime, BitVec.toNat_ofNat, Nat.mod_eq_of_lt e₁.isLt,
      Nat.mod_eq_of_lt e₂.isLt] using h
  exact ⟨bytesLE_injective 16 hp, bytesLE_injective 32 hs, he, bytesLE_injective 32 hm⟩

/-- Every seed-derived input puts the complete seed in bytes 32 through 63. -/
def DerivationSeedHit (input : HashInput) (seed : MasterSeed) : Prop :=
  (input.drop 32).take 32 = bytesLE 32 seed

theorem derivationSeedHit_unique {input : HashInput} {left right : MasterSeed}
    (hl : DerivationSeedHit input left) (hr : DerivationSeedHit input right) : left = right :=
  bytesLE_injective 32 (hl.symm.trans hr)

theorem probEvent_derivationSeedHit_le (input : HashInput) :
    Pr{let x ← sampleMasterSeed}[(DerivationSeedHit input) x] ≤ 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  by_cases hexists : ∃ seed, DerivationSeedHit input seed
  · obtain ⟨seed, hseed⟩ := hexists
    have hevent : DerivationSeedHit input = fun other => other = seed := by
      funext other
      exact propext ⟨fun h => derivationSeedHit_unique h hseed, fun h => h ▸ hseed⟩
    rw [hevent]
    simp [sampleMasterSeed, MasterSeed, SampleableType.prEvent_uniformSample_eq_singleton]
  · have hempty : DerivationSeedHit input = fun _ => False := by
      funext seed
      exact propext ⟨fun h => hexists ⟨seed, h⟩, False.elim⟩
    simp [hempty]

end XmssSecurity
