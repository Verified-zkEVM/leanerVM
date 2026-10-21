/-
  LeanVM.Guest.Count.MainS

  `Main.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.Count.Main
public import LeanVM.Guest.Count.StaticS
public import LeanVM.Guest.Count.OsStaticS
public import LeanVM.Guest.Count.RatioS
public import LeanVM.Guest.B1.Main.WeightLoopS
public import LeanVM.Guest.B2C.CntWeightB

/-!
# `Main.lean` under any `BLAKE2S` semantics

Each definition and lemma of `Main.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.B1.Main (MainWeightHyps MainWeightHypsS)

@[expose] public section

variable {S : BlakeSem}

variable (S) in
/-- **The weights of `main`'s callees** at `op`'s instructions, `verify_lean_xmss`'s arms counted
separately (`B2C.ωArm B1.Sig.xmssArmC`). -/
noncomputable def kcWtS (op : Opcode) : MainWeightHypsS S B2C.fs (B2C.ωArm B1.Sig.xmssArmC op) where
  Bexp := kcExp op
  exp := by rw [ωArm_xmssArmC]; exact kcExpS_weightLe op
  Kl0 := kcL0 op
  l0 := by rw [ωArm_xmssArmC]; exact kcL0S_loop op
  Kl1 := kcL1 op
  l1 := by rw [ωArm_xmssArmC]; exact kcL1S_loop op
  Kl2 := kcL2 op
  l2 := by rw [ωArm_xmssArmC]; exact kcL2S_loop op
  Kl3 := kcL3 op
  l3 := by rw [ωArm_xmssArmC]; exact kcL3S_loop op
  Kl4 := kcL4 op
  l4 := by rw [ωArm_xmssArmC]; exact kcL4S_loop op
  Kl100 := kcL100 op
  l100 := by rw [ωArm_xmssArmC]; exact kcL100S_loop op
  Bdl := kcDl op
  dl := by rw [ωArm_xmssArmC]; exact kcDlS_weightLe op
  Bcov := kcCov op
  cov := by rw [ωArm_xmssArmC]; exact kcCovS_weightLe op
  cAgg := kcAggC op
  dAgg := kcAggD op
  agg := by rw [ωArm_xmssArmC]; exact kcAggS_le op
  Bsd := kcSd op
  sd := by rw [ωArm_xmssArmC]; exact kcSdS_weightLe op
  αcl := krClA op
  cl := by rw [ωArm_xmssArmC]; exact krClS_weight op
  αccl := krCclA op
  ccl := by rw [ωArm_xmssArmC]; exact krCclS_weight op
  vsc := ⟨kcoGpw op, kcoL2a op, kcoL2b op, kcoAc op, kcoPl op, kcoOs op⟩
  vsOk := by
    rw [ωArm_xmssArmC]
    exact ⟨kcoGpwS_weightLe op, kcoL2aS_weightLe op, kcoL2bS_weightLe op, kcoAcS_weightLe op, kcoPlS_weightLe op,
      fun μ r _ _ _ _ => kcoOsS_weightLe op (μ - 22 + 7 * (r - 1)) (by omega)⟩

end
end LeanVM.Guest.Count
