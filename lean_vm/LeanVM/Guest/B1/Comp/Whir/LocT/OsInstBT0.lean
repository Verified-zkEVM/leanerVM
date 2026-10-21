/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBT0

  `open_stacked`'s instances' queries by trees decoding to their openings, their caps' names, the
  root's read cells (`Loc/OsInstB0.lean` with the decoding)
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBaseT
public import LeanVM.Guest.B1.Comp.Whir.LocT.QueriesAtSpecT0
public import LeanVM.Guest.B1.Comp.Whir.LocT.QueriesAtSpecT1
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsInstB0

/-!
# `open_stacked`'s instances with the decoding (`Loc/OsInstB0.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

set_option maxRecDepth 100000 in
theorem osKidsAtBT_0C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg0 (osBdC CM fs hm hp osCfg0) := fun i hi => by
  have : i < 4 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L17_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f430) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L16_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f432) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L15_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f434) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L14_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f435) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_0 : OsCapNames osCfg0 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_0 : CellsOk "open_stacked__L0" (osLvsReads osCfg0 0 osCfg0.levels (osHead osCfg0).2) :=
  cellsOk_of (j := 178) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_1C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg1 (osBdC CM fs hm hp osCfg1) := fun i hi => by
  have : i < 4 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L18_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f436) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L17_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f437) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L16_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f438) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L15_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f434) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_1 : OsCapNames osCfg1 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_1 : CellsOk "open_stacked__L1" (osLvsReads osCfg1 0 osCfg1.levels (osHead osCfg1).2) :=
  cellsOk_of (j := 179) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_2C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg2 (osBdC CM fs hm hp osCfg2) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L19_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f439) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f440) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L17_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f441) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L16_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f438) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L15_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f434) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_2 : OsCapNames osCfg2 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_2 : CellsOk "open_stacked__L2" (osLvsReads osCfg2 0 osCfg2.levels (osHead osCfg2).2) :=
  cellsOk_of (j := 180) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_3C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg3 (osBdC CM fs hm hp osCfg3) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L20_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f442) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f443) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f444) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L17_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f441) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L16_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f438) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_3 : OsCapNames osCfg3 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_3 : CellsOk "open_stacked__L3" (osLvsReads osCfg3 0 osCfg3.levels (osHead osCfg3).2) :=
  cellsOk_of (j := 181) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_4C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg4 (osBdC CM fs hm hp osCfg4) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L21_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f445) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f446) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f447) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f444) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L17_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f441) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_4 : OsCapNames osCfg4 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_4 : CellsOk "open_stacked__L4" (osLvsReads osCfg4 0 osCfg4.levels (osHead osCfg4).2) :=
  cellsOk_of (j := 182) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_5C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg5 (osBdC CM fs hm hp osCfg5) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L22_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f448) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L21_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f449) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f450) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f447) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f444) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_5 : OsCapNames osCfg5 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_5 : CellsOk "open_stacked__L5" (osLvsReads osCfg5 0 osCfg5.levels (osHead osCfg5).2) :=
  cellsOk_of (j := 183) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_6C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg6 (osBdC CM fs hm hp osCfg6) := fun i hi => by
  have : i < 6 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L23_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f451) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L22_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f452) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L21_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f453) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f450) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f447) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f455) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_6 : OsCapNames osCfg6 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_6 : CellsOk "open_stacked__L6" (osLvsReads osCfg6 0 osCfg6.levels (osHead osCfg6).2) :=
  cellsOk_of (j := 184) (by decide +kernel) (by decide +kernel)

end
end LeanVM.Guest.B1
