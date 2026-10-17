import XmssSecurity.Proof.Deterministic.Inputs

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

abbrev SeedHit := DerivationSeedHit

theorem probEvent_seedHit_le (input : HashInput) :
    Pr{let x ← sampleMasterSeed}[(SeedHit input) x] ≤ 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
  probEvent_derivationSeedHit_le input

def SeedHitLog (inputs : List HashInput) (seed : MasterSeed) : Prop :=
  ∃ input ∈ inputs, SeedHit input seed

/-- A list chosen independently of the seed contributes at most one 256-bit guess per input. -/
theorem probEvent_seedHitLog_le (inputs : List HashInput) :
    Pr{let x ← sampleMasterSeed}[(SeedHitLog inputs) x] ≤ inputs.length / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  induction inputs with
  | nil =>
      rw [prEvent_eq_zero_of_forall_not _ _ fun _ h => by simp [SeedHitLog] at h]
      simp

  | cons input inputs ih =>
      have hevent : SeedHitLog (input :: inputs) = fun seed =>
          SeedHit input seed ∨ SeedHitLog inputs seed := by
        funext seed
        simp [SeedHitLog]
      rw [hevent]
      calc
        _ ≤ Pr{let x ← sampleMasterSeed}[(SeedHit input) x] + Pr{let x ← sampleMasterSeed}[(SeedHitLog inputs) x] :=
          prEvent_or_le _ _ _
        _ ≤ 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) + inputs.length / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
          add_le_add (probEvent_seedHit_le input) ih
        _ = _ := by simp [List.length_cons, Nat.cast_add, ENNReal.add_div, add_comm]

end XmssSecurity
