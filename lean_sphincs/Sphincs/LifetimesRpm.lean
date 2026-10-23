import Sphincs.StatementRpm
import Sphincs.Lifetimes

/-!
**The forest lifetimes in the random-permutation model.** The ROM theorems of `Lifetimes.lean`
(127 bits at each subtree height) moved to the RPM by `LeanRpm.SufCma.rpm_bound`: the
leanSPHINCS game is the generic SUF-CMA game of `LeanRpm.Signature` (`experimentDet_eq`), and an
RPM adversary with the signing oracle, its permutation queries answered by the
indifferentiability simulator, is a ROM adversary whose experiment makes at most as many hash
calls as the RPM game makes calls of `H`, `π` and `π⁻¹`.
-/

open OracleComp OracleSpec ENNReal LeanRpm LeanRpm.SufCma

namespace Sphincs.Lifetimes

/- A weight bound of a concrete game must not be unfolded: it recurses through the whole game. -/
attribute [local irreducible] IsWeightBound

section

variable [Params]

/-- The leanSPHINCS ROM experiment is the generic one. -/
theorem experimentDet_eq
    (main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery) :
    Security.Det.experimentDet ⟨main⟩ = romExperiment Rpm.scheme main := by
  have h : Security.countedOracle = countedImpl (D := HashOutput) := by
    unfold Security.countedOracle countedImpl
    congr 1
    funext t
    rcases t with n | m <;> rfl
  unfold Security.Det.experimentDet romExperiment
  rw [h]
  rfl

/-- **From the ROM to the RPM, refined**: `bits` classical bits for the deterministic signer give
the bound `q / 2^bits + Q² / 2^509` in the random-permutation model. -/
theorem rpmBitsCalls_of_det {bits : Nat} (h : Security.Det.HasClassicalSecurityBitsDet bits) :
    Rpm.HasRpmSecurityBitsCalls bits := by
  have hrom : ∀ q, 1 ≤ q →
      ∀ main : PublicKey → OracleComp (World HashOutput + SigningSpec) Forgery,
        (∀ r ∈ support (romExperiment Rpm.scheme main), r.2 ≤ q) →
          Pr{let r ← romExperiment Rpm.scheme main}[r.1 = true] ≤
            q / ((2 ^ bits : ℕ) : ℝ≥0∞) := by
    intro q hq main hb
    rw [← experimentDet_eq] at hb ⊢
    exact h q hq ⟨main⟩ hb
  intro q Q hq1 adversary hq hQ
  exact rpm_bound (digestBitVec : KDigest ≃ HashOutput) Rpm.scheme bits hrom adversary.main q Q
    hq1 hq hQ

/-- **From the ROM to the RPM**: `bits` classical bits for the deterministic signer give the
bound `Q / 2^bits + Q² / 2^509` in the random-permutation model. -/
theorem rpmBits_of_det {bits : Nat} (h : Security.Det.HasClassicalSecurityBitsDet bits) :
    Rpm.HasRpmSecurityBits bits :=
  fun Q hQ adversary hbound ↦ rpmBitsCalls_of_det h Q Q hQ adversary
    (IsWeightBound.mono_weight hbound oracleCalls_le_permCalls) hbound

end

/-- **The forest lifetimes in the random-permutation model**: at each proved subtree height
(`b` = 26, 20, 14, 13, 12, 10, 8), an adversary whose game makes at most `Q ≥ 1` permutation
calls forges with probability at most `Q / 2^127 + Q² / 2^509`. -/
theorem requestedSecurityRpm :
    @Rpm.HasRpmSecurityBits full 127 ∧
    @Rpm.HasRpmSecurityBits pruned20 127 ∧
    @Rpm.HasRpmSecurityBits pruned14 127 ∧
    @Rpm.HasRpmSecurityBits pruned13 127 ∧
    @Rpm.HasRpmSecurityBits pruned12 127 ∧
    @Rpm.HasRpmSecurityBits pruned10 127 ∧
    @Rpm.HasRpmSecurityBits pruned8 127 :=
  ⟨@rpmBits_of_det full 127 full_bits, @rpmBits_of_det pruned20 127 pruned20_bits, @rpmBits_of_det pruned14 127 pruned14_bits,
    @rpmBits_of_det pruned13 127 pruned13_bits, @rpmBits_of_det pruned12 127 pruned12_bits, @rpmBits_of_det pruned10 127 pruned10_bits,
    @rpmBits_of_det pruned8 127 pruned8_bits⟩

/-- **The forest lifetimes in the random-permutation model, refined**: at each proved subtree
height, an adversary whose game makes at most `q ≥ 1` calls of `H`, `π` and `π⁻¹` and at most `Q`
permutation calls forges with probability at most `q / 2^127 + Q² / 2^509`. -/
theorem requestedSecurityRpmCalls :
    @Rpm.HasRpmSecurityBitsCalls full 127 ∧
    @Rpm.HasRpmSecurityBitsCalls pruned20 127 ∧
    @Rpm.HasRpmSecurityBitsCalls pruned14 127 ∧
    @Rpm.HasRpmSecurityBitsCalls pruned13 127 ∧
    @Rpm.HasRpmSecurityBitsCalls pruned12 127 ∧
    @Rpm.HasRpmSecurityBitsCalls pruned10 127 ∧
    @Rpm.HasRpmSecurityBitsCalls pruned8 127 :=
  ⟨@rpmBitsCalls_of_det full 127 full_bits, @rpmBitsCalls_of_det pruned20 127 pruned20_bits,
    @rpmBitsCalls_of_det pruned14 127 pruned14_bits, @rpmBitsCalls_of_det pruned13 127 pruned13_bits,
    @rpmBitsCalls_of_det pruned12 127 pruned12_bits, @rpmBitsCalls_of_det pruned10 127 pruned10_bits,
    @rpmBitsCalls_of_det pruned8 127 pruned8_bits⟩

end Sphincs.Lifetimes
