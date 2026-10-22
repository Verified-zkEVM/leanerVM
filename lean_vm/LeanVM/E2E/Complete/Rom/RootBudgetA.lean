/-
  LeanVM.E2E.Complete.Rom.RootBudgetA

  T6-prob's two-level inhabitant: `open_stacked`'s bound at its configurations 0–13
  (rates 1 and 2), by kernel evaluation one configuration at a time.
-/

module

public import LeanVM.Guest.EndCompleteFinal

/-!
# `open_stacked`'s configurations 0–13 (rates 1 and 2)

`calleesHyps_b2c.Bop` is the largest of `open_stacked`'s 28 configurations' bounds (`osBop`). Its
kernel evaluation in one piece exceeds 30 GB; one configuration takes about 20 s and 9 GB, so
they are evaluated one at a time, in two modules of 14 (`RootBudget.lean` combines them).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B2C

@[expose] public section

/-- `open_stacked`'s configuration `0` (stack log `22`, rate `1`) is within `2^20` words. -/
theorem osCfgBound_le_rb0 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg0
      (VerifySub.openName 22 1) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `1` (stack log `23`, rate `1`) is within `2^20` words. -/
theorem osCfgBound_le_rb1 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg1
      (VerifySub.openName 23 1) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `2` (stack log `24`, rate `1`) is within `2^20` words. -/
theorem osCfgBound_le_rb2 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg2
      (VerifySub.openName 24 1) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `3` (stack log `25`, rate `1`) is within `2^20` words. -/
theorem osCfgBound_le_rb3 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg3
      (VerifySub.openName 25 1) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `4` (stack log `26`, rate `1`) is within `2^20` words. -/
theorem osCfgBound_le_rb4 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg4
      (VerifySub.openName 26 1) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `5` (stack log `27`, rate `1`) is within `2^20` words. -/
theorem osCfgBound_le_rb5 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg5
      (VerifySub.openName 27 1) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `6` (stack log `28`, rate `1`) is within `2^20` words. -/
theorem osCfgBound_le_rb6 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg6
      (VerifySub.openName 28 1) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `7` (stack log `22`, rate `2`) is within `2^20` words. -/
theorem osCfgBound_le_rb7 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg7
      (VerifySub.openName 22 2) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `8` (stack log `23`, rate `2`) is within `2^20` words. -/
theorem osCfgBound_le_rb8 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg8
      (VerifySub.openName 23 2) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `9` (stack log `24`, rate `2`) is within `2^20` words. -/
theorem osCfgBound_le_rb9 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg9
      (VerifySub.openName 24 2) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `10` (stack log `25`, rate `2`) is within `2^20` words. -/
theorem osCfgBound_le_rb10 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg10
      (VerifySub.openName 25 2) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `11` (stack log `26`, rate `2`) is within `2^20` words. -/
theorem osCfgBound_le_rb11 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg11
      (VerifySub.openName 26 2) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `12` (stack log `27`, rate `2`) is within `2^20` words. -/
theorem osCfgBound_le_rb12 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg12
      (VerifySub.openName 27 2) ≤ 2 ^ 20 := by
  decide +kernel

/-- `open_stacked`'s configuration `13` (stack log `28`, rate `2`) is within `2^20` words. -/
theorem osCfgBound_le_rb13 :
    osCfgBound fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs) osCfg13
      (VerifySub.openName 28 2) ≤ 2 ^ 20 := by
  decide +kernel

end
end LeanVM.E2E.Complete
