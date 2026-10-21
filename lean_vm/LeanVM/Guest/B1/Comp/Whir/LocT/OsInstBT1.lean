/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBT1

  `open_stacked`'s instances' queries by trees decoding to their openings, their caps' names, the
  root's read cells (`Loc/OsInstB1.lean` with the decoding)
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBaseT
public import LeanVM.Guest.B1.Comp.Whir.LocT.QueriesAtSpecT0
public import LeanVM.Guest.B1.Comp.Whir.LocT.QueriesAtSpecT1
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsInstB1

/-!
# `open_stacked`'s instances with the decoding (`Loc/OsInstB1.lean`)
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
theorem osKidsAtBT_7C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg7 (osBdC CM fs hm hp osCfg7) := fun i hi => by
  have : i < 4 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L18_L7C (Ht := Ht) (CM := CM) fs cert κ hq.f457) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L17_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f437) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L16_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f438) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L15_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f434) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_7 : OsCapNames osCfg7 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_7 : CellsOk "open_stacked__L7" (osLvsReads osCfg7 0 osCfg7.levels (osHead osCfg7).2) :=
  cellsOk_of (j := 185) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_8C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg8 (osBdC CM fs hm hp osCfg8) := fun i hi => by
  have : i < 4 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L19_L7C (Ht := Ht) (CM := CM) fs cert κ hq.f458) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f440) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L17_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f441) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L16_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f438) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_8 : OsCapNames osCfg8 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_8 : CellsOk "open_stacked__L8" (osLvsReads osCfg8 0 osCfg8.levels (osHead osCfg8).2) :=
  cellsOk_of (j := 186) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_9C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg9 (osBdC CM fs hm hp osCfg9) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L20_L7C (Ht := Ht) (CM := CM) fs cert κ hq.f459) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f443) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f444) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L17_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f441) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L16_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f460) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_9 : OsCapNames osCfg9 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_9 : CellsOk "open_stacked__L9" (osLvsReads osCfg9 0 osCfg9.levels (osHead osCfg9).2) :=
  cellsOk_of (j := 187) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_10C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg10 (osBdC CM fs hm hp osCfg10) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L21_L7C (Ht := Ht) (CM := CM) fs cert κ hq.f461) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f446) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f447) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f444) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L17_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f462) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_10 : OsCapNames osCfg10 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_10 : CellsOk "open_stacked__L10" (osLvsReads osCfg10 0 osCfg10.levels (osHead osCfg10).2) :=
  cellsOk_of (j := 188) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_11C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg11 (osBdC CM fs hm hp osCfg11) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L22_L7C (Ht := Ht) (CM := CM) fs cert κ hq.f463) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L21_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f449) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f450) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f447) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f455) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_11 : OsCapNames osCfg11 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_11 : CellsOk "open_stacked__L11" (osLvsReads osCfg11 0 osCfg11.levels (osHead osCfg11).2) :=
  cellsOk_of (j := 189) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_12C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg12 (osBdC CM fs hm hp osCfg12) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L23_L7C (Ht := Ht) (CM := CM) fs cert κ hq.f464) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L22_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f452) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L21_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f453) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f450) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f465) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_12 : OsCapNames osCfg12 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_12 : CellsOk "open_stacked__L12" (osLvsReads osCfg12 0 osCfg12.levels (osHead osCfg12).2) :=
  cellsOk_of (j := 190) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_13C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg13 (osBdC CM fs hm hp osCfg13) := fun i hi => by
  have : i < 6 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L24_L7C (Ht := Ht) (CM := CM) fs cert κ hq.f466) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L23_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f467) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L22_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f468) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L21_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f453) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f469) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f465) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_13 : OsCapNames osCfg13 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_13 : CellsOk "open_stacked__L13" (osLvsReads osCfg13 0 osCfg13.levels (osHead osCfg13).2) :=
  cellsOk_of (j := 191) (by decide +kernel) (by decide +kernel)

end
end LeanVM.Guest.B1
