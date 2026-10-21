/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBT2

  `open_stacked`'s instances' queries by trees decoding to their openings, their caps' names, the
  root's read cells (`Loc/OsInstB2.lean` with the decoding)
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBaseT
public import LeanVM.Guest.B1.Comp.Whir.LocT.QueriesAtSpecT0
public import LeanVM.Guest.B1.Comp.Whir.LocT.QueriesAtSpecT1
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsInstB2

/-!
# `open_stacked`'s instances with the decoding (`Loc/OsInstB2.lean`)
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
theorem osKidsAtBT_14C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg14 (osBdC CM fs hm hp osCfg14) := fun i hi => by
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
theorem osCapNames_14 : OsCapNames osCfg14 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_14 : CellsOk "open_stacked__L14" (osLvsReads osCfg14 0 osCfg14.levels (osHead osCfg14).2) :=
  cellsOk_of (j := 192) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_15C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg15 (osBdC CM fs hm hp osCfg15) := fun i hi => by
  have : i < 4 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L20_L7C (Ht := Ht) (CM := CM) fs cert κ hq.f459) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f443) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f444) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L17_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f441) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_15 : OsCapNames osCfg15 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_15 : CellsOk "open_stacked__L15" (osLvsReads osCfg15 0 osCfg15.levels (osHead osCfg15).2) :=
  cellsOk_of (j := 193) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_16C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg16 (osBdC CM fs hm hp osCfg16) := fun i hi => by
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
theorem osCapNames_16 : OsCapNames osCfg16 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_16 : CellsOk "open_stacked__L16" (osLvsReads osCfg16 0 osCfg16.levels (osHead osCfg16).2) :=
  cellsOk_of (j := 194) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_17C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg17 (osBdC CM fs hm hp osCfg17) := fun i hi => by
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
theorem osCapNames_17 : OsCapNames osCfg17 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_17 : CellsOk "open_stacked__L17" (osLvsReads osCfg17 0 osCfg17.levels (osHead osCfg17).2) :=
  cellsOk_of (j := 195) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_18C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg18 (osBdC CM fs hm hp osCfg18) := fun i hi => by
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
theorem osCapNames_18 : OsCapNames osCfg18 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_18 : CellsOk "open_stacked__L18" (osLvsReads osCfg18 0 osCfg18.levels (osHead osCfg18).2) :=
  cellsOk_of (j := 196) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_19C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg19 (osBdC CM fs hm hp osCfg19) := fun i hi => by
  have : i < 5 := hi
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

set_option maxRecDepth 100000 in
theorem osCapNames_19 : OsCapNames osCfg19 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_19 : CellsOk "open_stacked__L19" (osLvsReads osCfg19 0 osCfg19.levels (osHead osCfg19).2) :=
  cellsOk_of (j := 197) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_20C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg20 (osBdC CM fs hm hp osCfg20) := fun i hi => by
  have : i < 6 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L25_L7C (Ht := Ht) (CM := CM) fs cert κ hq.f470) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L24_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f471) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L23_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f472) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L22_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f468) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L21_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f473) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f469) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_20 : OsCapNames osCfg20 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_20 : CellsOk "open_stacked__L20" (osLvsReads osCfg20 0 osCfg20.levels (osHead osCfg20).2) :=
  cellsOk_of (j := 198) (by decide +kernel) (by decide +kernel)

end
end LeanVM.Guest.B1
