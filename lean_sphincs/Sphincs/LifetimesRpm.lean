import Sphincs.StatementRpm
import Sphincs.OneLayer
import Sphincs.Lifetimes
import Common.Linear

/-!
**The forest lifetimes in the random-permutation model.** The ROM theorems of `Lifetimes.lean`
(127 bits at each subtree height) moved to the RPM by `Common.SufCma.rpm_bound`: the
leanSPHINCS game is the generic SUF-CMA game of `Common.Signature` (`experimentDet_eq`), and an
RPM adversary with the signing oracle, its permutation queries answered by the
indifferentiability simulator, is a ROM adversary whose experiment makes at most as many hash
calls as the RPM game makes calls of `H`, `π` and `π⁻¹`.
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace SphincsLayered.Lifetimes

/- A weight bound of a concrete game must not be unfolded: it recurses through the whole game. -/
attribute [local irreducible] QueryCostAtMost

section

variable [Params]

/-- The leanSPHINCS ROM experiment is the generic one. -/
theorem experimentDet_eq
    (main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery) :
    Security.Det.experimentDet ⟨main⟩ = romExperiment Rpm.scheme main := by
  have h : Security.countedOracle = countedImpl := by
    unfold Security.countedOracle countedImpl
    congr 1
  unfold Security.Det.experimentDet romExperiment
  rw [h]
  rfl

/-- **From the ROM to the RPM, refined**: `bits` classical bits for the deterministic signer give
the bound `q / 2^bits + Q² / 2^509` in the random-permutation model. -/
theorem rpmBitsCalls_of_det {bits : Nat} (h : Security.Det.HasClassicalSecurityBitsDet bits) :
    Rpm.HasRpmSecurityBitsCalls bits := by
  have hrom : ∀ q, 1 ≤ q →
      ∀ main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery,
        (∀ r ∈ support (romExperiment Rpm.scheme main), r.2 ≤ q) →
          Pr{let r ← romExperiment Rpm.scheme main}[r.1 = true] ≤
            q / ((2 ^ bits : ℕ) : ℝ≥0∞) := by
    intro q hq main hb
    rw [← experimentDet_eq] at hb ⊢
    exact h q hq ⟨main⟩ hb
  intro q Q hq1 adversary hq hQ
  exact rpm_bound Rpm.scheme bits hrom adversary.main q Q
    hq1 hq hQ

/-- **From the ROM to the RPM**: `bits ≤ 253` classical bits for the deterministic signer give the
bound `(Q + 1) · 2^-bits` in the random-permutation model, for `Q ≤ 2^128`: the refined bound
`Q / 2^bits + Q² / 2^509` is at most that under the cap (`Common.bits_add_sq_le`). -/
theorem rpmBits_of_det {bits : Nat} (h : Security.Det.HasClassicalSecurityBitsDet bits)
    (hb : bits ≤ 253) : Rpm.HasRpmSecurityBits bits :=
  fun Q hQ hcap adversary hbound ↦ (rpmBitsCalls_of_det h Q Q hQ adversary
    (QueryCostAtMost.mono_weight hbound oracleCalls_le_permCalls) hbound).trans
    (Common.bits_add_sq_le hcap hb)

end

/-- **The forest lifetimes in the random-permutation model**: at each proved subtree height
(`b` = 26, 20, 14, 13, 12, 10, 8), an adversary whose game makes at most `Q` permutation calls,
`Q ≥ 1`, forges with probability at most `(Q + 1) · 2^-127`. -/
theorem requestedSecurityRpm : RequestedSecurityRpm :=
  ⟨@Rpm.rpmSecure_of_bits full 127 (@rpmBits_of_det full 127 full_bits (by norm_num)) (by norm_num),
    @Rpm.rpmSecure_of_bits pruned20 127 (@rpmBits_of_det pruned20 127 pruned20_bits (by norm_num)) (by norm_num),
    @Rpm.rpmSecure_of_bits pruned14 127 (@rpmBits_of_det pruned14 127 pruned14_bits (by norm_num)) (by norm_num),
    @Rpm.rpmSecure_of_bits pruned13 127 (@rpmBits_of_det pruned13 127 pruned13_bits (by norm_num)) (by norm_num),
    @Rpm.rpmSecure_of_bits pruned12 127 (@rpmBits_of_det pruned12 127 pruned12_bits (by norm_num)) (by norm_num),
    @Rpm.rpmSecure_of_bits pruned10 127 (@rpmBits_of_det pruned10 127 pruned10_bits (by norm_num)) (by norm_num),
    @Rpm.rpmSecure_of_bits pruned8 127 (@rpmBits_of_det pruned8 127 pruned8_bits (by norm_num)) (by norm_num)⟩

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

end SphincsLayered.Lifetimes

/-- **The end theorem**: the statement's leanSPHINCS, its one tree written without layers, at every
proved lifetime, an adversary whose game makes at most `Q` permutation calls, `1 ≤ Q ≤ 2^128`,
forges with probability at most `(Q + 1) · 2^-127`: the layered presentation's theorem above,
through the bijection of the signatures (`Sphincs.OneLayer.requestedSecurityRpm_iff`). -/
theorem Sphincs.Lifetimes.requestedSecurityRpm : Sphincs.Lifetimes.LeanSphincsStronglyUnforgeable :=
  Sphincs.OneLayer.requestedSecurityRpm_iff.mpr SphincsLayered.Lifetimes.requestedSecurityRpm
