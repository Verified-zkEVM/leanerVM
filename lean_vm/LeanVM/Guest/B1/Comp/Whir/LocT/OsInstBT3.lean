/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBT3

  `open_stacked`'s instances' queries by trees decoding to their openings, their caps' names, the
  root's read cells (`Loc/OsInstB3.lean` with the decoding)
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBaseT
public import LeanVM.Guest.B1.Comp.Whir.LocT.QueriesAtSpecT0
public import LeanVM.Guest.B1.Comp.Whir.LocT.QueriesAtSpecT1
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsInstB3

/-!
# `open_stacked`'s instances with the decoding (`Loc/OsInstB3.lean`)
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
theorem osKidsAtBT_21C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg21 (osBdC CM fs hm hp osCfg21) := fun i hi => by
  have : i < 4 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L20_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f474) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f447) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f444) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L17_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f441) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_21 : OsCapNames osCfg21 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_21 : CellsOk "open_stacked__L21" (osLvsReads osCfg21 0 osCfg21.levels (osHead osCfg21).2) :=
  cellsOk_of (j := 199) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_22C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg22 (osBdC CM fs hm hp osCfg22) := fun i hi => by
  have : i < 4 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L21_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f475) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f450) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f447) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f444) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_22 : OsCapNames osCfg22 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_22 : CellsOk "open_stacked__L22" (osLvsReads osCfg22 0 osCfg22.levels (osHead osCfg22).2) :=
  cellsOk_of (j := 200) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_23C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg23 (osBdC CM fs hm hp osCfg23) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L22_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f476) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L21_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f453) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f450) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f447) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L18_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f455) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_23 : OsCapNames osCfg23 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_23 : CellsOk "open_stacked__L23" (osLvsReads osCfg23 0 osCfg23.levels (osHead osCfg23).2) :=
  cellsOk_of (j := 201) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_24C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg24 (osBdC CM fs hm hp osCfg24) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L23_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f477) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L22_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f468) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L21_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f453) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f450) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L19_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f465) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_24 : OsCapNames osCfg24 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_24 : CellsOk "open_stacked__L24" (osLvsReads osCfg24 0 osCfg24.levels (osHead osCfg24).2) :=
  cellsOk_of (j := 202) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_25C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg25 (osBdC CM fs hm hp osCfg25) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L24_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f478) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L23_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f472) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L22_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f468) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L21_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f453) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L20_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f469) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_25 : OsCapNames osCfg25 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_25 : CellsOk "open_stacked__L25" (osLvsReads osCfg25 0 osCfg25.levels (osHead osCfg25).2) :=
  cellsOk_of (j := 203) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_26C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg26 (osBdC CM fs hm hp osCfg26) := fun i hi => by
  have : i < 5 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L25_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f479) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L24_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f480) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L23_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f472) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L22_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f468) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L21_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f473) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_26 : OsCapNames osCfg26 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_26 : CellsOk "open_stacked__L26" (osLvsReads osCfg26 0 osCfg26.levels (osHead osCfg26).2) :=
  cellsOk_of (j := 204) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtBT_27C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBCT CM Ht fs cert κ osCfg27 (osBdC CM fs hm hp osCfg27) := fun i hi => by
  have : i < 6 := hi
  interval_cases i
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L1_L64_L8_L26_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f481) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L25_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f482) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L24_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f480) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L23_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f472) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L22_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f483) (by decide +kernel)
  · exact osLvKidsAtBT_mkC (Ht := Ht) (CM := CM) (hm := hm) (hp := hp) hi
      (oq_completeAtBT_L0_L16_L6_L21_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f473) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osCapNames_27 : OsCapNames osCfg27 := by unfold OsCapNames; decide +kernel

set_option maxRecDepth 100000 in
theorem osRootCells_27 : CellsOk "open_stacked__L27" (osLvsReads osCfg27 0 osCfg27.levels (osHead osCfg27).2) :=
  cellsOk_of (j := 205) (by decide +kernel) (by decide +kernel)

end
end LeanVM.Guest.B1
