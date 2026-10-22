/-
  LeanVM.E2E.Complete.Rom.RootBudgetB

  T6-prob's two-level inhabitant: `open_stacked`'s bound at its configurations 14–27
  (rates 3 and 4), by kernel evaluation one configuration at a time.
-/

module

public import LeanVM.E2E.Complete.Rom.RootBudgetA

/-!
# `open_stacked`'s configurations 14–27 (rates 3 and 4)

`calleesHyps_b2c.Bop` is the largest of `open_stacked`'s 28 configurations' bounds (`osBop`). Its
kernel evaluation in one piece exceeds 30 GB; one configuration takes about 20 s and 9 GB, so
they are evaluated one at a time, in two modules of 14 (`RootBudget.lean` combines them).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B2C

@[expose] public section

/-- `open_stacked`'s configuration `14` (stack log `22`, rate `3`) is within `2^20` words. -/
theorem osCfgBound_le_rb14 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg14
      (VerifySub.openName 22 3) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `15` (stack log `23`, rate `3`) is within `2^20` words. -/
theorem osCfgBound_le_rb15 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg15
      (VerifySub.openName 23 3) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `16` (stack log `24`, rate `3`) is within `2^20` words. -/
theorem osCfgBound_le_rb16 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg16
      (VerifySub.openName 24 3) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `17` (stack log `25`, rate `3`) is within `2^20` words. -/
theorem osCfgBound_le_rb17 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg17
      (VerifySub.openName 25 3) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `18` (stack log `26`, rate `3`) is within `2^20` words. -/
theorem osCfgBound_le_rb18 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg18
      (VerifySub.openName 26 3) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `19` (stack log `27`, rate `3`) is within `2^20` words. -/
theorem osCfgBound_le_rb19 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg19
      (VerifySub.openName 27 3) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `20` (stack log `28`, rate `3`) is within `2^20` words. -/
theorem osCfgBound_le_rb20 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg20
      (VerifySub.openName 28 3) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `21` (stack log `22`, rate `4`) is within `2^20` words. -/
theorem osCfgBound_le_rb21 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg21
      (VerifySub.openName 22 4) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `22` (stack log `23`, rate `4`) is within `2^20` words. -/
theorem osCfgBound_le_rb22 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg22
      (VerifySub.openName 23 4) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `23` (stack log `24`, rate `4`) is within `2^20` words. -/
theorem osCfgBound_le_rb23 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg23
      (VerifySub.openName 24 4) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `24` (stack log `25`, rate `4`) is within `2^20` words. -/
theorem osCfgBound_le_rb24 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg24
      (VerifySub.openName 25 4) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `25` (stack log `26`, rate `4`) is within `2^20` words. -/
theorem osCfgBound_le_rb25 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg25
      (VerifySub.openName 26 4) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `26` (stack log `27`, rate `4`) is within `2^20` words. -/
theorem osCfgBound_le_rb26 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg26
      (VerifySub.openName 27 4) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `27` (stack log `28`, rate `4`) is within `2^20` words. -/
theorem osCfgBound_le_rb27 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg27
      (VerifySub.openName 28 4) ≤ 2 ^ 20 := by
  decide +kernel

end
end LeanVM.E2E.Complete
