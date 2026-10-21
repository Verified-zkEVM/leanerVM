/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsInstB0

  `open_stacked`'s instances' callees, bounded, over a completeness model (`Whir/OsInstB0.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsInstB0
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsInstBaseB
public import LeanVM.Guest.B1.Comp.Whir.Loc.QueriesAtSpec0
public import LeanVM.Guest.B1.Comp.Whir.Loc.QueriesAtSpec1
public import LeanVM.Guest.B1.Comp.Whir.Loc.CapAt

/-!
# `open_stacked`'s instances' callees, bounded, over a completeness model (`Whir/OsInstB0.lean`)
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
theorem osKidsAtB_0C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBC CM Ht fs cert κ osCfg0 (osBdC CM fs hm hp osCfg0) where
  fold := osKB_foldC (CM := CM) hm hp _
  canonical := osKB_canonicalC (CM := CM) hm hp _
  ood := osKB_oodC (CM := CM) hm hp _
  grind := osKB_grindC (CM := CM) hm hp _
  finalMsg := osKB_finalMsg16C (CM := CM) hm hp _
  foldFinal := osKB_foldFinal4C (CM := CM) hm hp _
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights6C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L8C (CM := CM) fs cert κ)
        (oq_completeAtB_L1_L64_L8_L17_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f430) (by decide +kernel)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_0_0 rfl os_sq_body_0_0
        (by show coreProgram.loop "__loop102" = true; rw [Program.loop_of_find? os_sq_find_0_0]; decide +kernel)
        os_res_find_0_0 rfl os_res_body_0_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L6C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L16_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f432) (by decide +kernel)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_0_1 rfl os_sq_body_0_1
        (by show coreProgram.loop "__loop103" = true; rw [Program.loop_of_find? os_sq_find_0_1]; decide +kernel)
        os_res_find_0_1 rfl os_res_body_0_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L15_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f434) (by decide +kernel)
        (h1.decode (15, "decode_query_bits__L15") (by decide)) (by decide +kernel) os_sq_find_0_2 rfl os_sq_body_0_2
        (by show coreProgram.loop "__loop104" = true; rw [Program.loop_of_find? os_sq_find_0_2]; decide +kernel)
        os_res_find_0_2 rfl os_res_body_0_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L14_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f435) (by decide +kernel)
        (h1.decode (14, "decode_query_bits__L14") (by decide)) (by decide +kernel) os_sq_find_0_3 rfl os_sq_body_0_3
        (by show coreProgram.loop "__loop105" = true; rw [Program.loop_of_find? os_sq_find_0_3]; decide +kernel)
        os_res_find_0_3 rfl os_res_body_0_3
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_1C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBC CM Ht fs cert κ osCfg1 (osBdC CM fs hm hp osCfg1) where
  fold := osKB_foldC (CM := CM) hm hp _
  canonical := osKB_canonicalC (CM := CM) hm hp _
  ood := osKB_oodC (CM := CM) hm hp _
  grind := osKB_grindC (CM := CM) hm hp _
  finalMsg := osKB_finalMsg32C (CM := CM) hm hp _
  foldFinal := osKB_foldFinal5C (CM := CM) hm hp _
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights6C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L8C (CM := CM) fs cert κ)
        (oq_completeAtB_L1_L64_L8_L18_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f436) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_1_0 rfl os_sq_body_1_0
        (by show coreProgram.loop "__loop110" = true; rw [Program.loop_of_find? os_sq_find_1_0]; decide +kernel)
        os_res_find_1_0 rfl os_res_body_1_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L6C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L17_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f437) (by decide +kernel)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_1_1 rfl os_sq_body_1_1
        (by show coreProgram.loop "__loop111" = true; rw [Program.loop_of_find? os_sq_find_1_1]; decide +kernel)
        os_res_find_1_1 rfl os_res_body_1_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L16_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f438) (by decide +kernel)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_1_2 rfl os_sq_body_1_2
        (by show coreProgram.loop "__loop112" = true; rw [Program.loop_of_find? os_sq_find_1_2]; decide +kernel)
        os_res_find_1_2 rfl os_res_body_1_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L15_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f434) (by decide +kernel)
        (h1.decode (15, "decode_query_bits__L15") (by decide)) (by decide +kernel) os_sq_find_1_3 rfl os_sq_body_1_3
        (by show coreProgram.loop "__loop113" = true; rw [Program.loop_of_find? os_sq_find_1_3]; decide +kernel)
        os_res_find_1_3 rfl os_res_body_1_3
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_2C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBC CM Ht fs cert κ osCfg2 (osBdC CM fs hm hp osCfg2) where
  fold := osKB_foldC (CM := CM) hm hp _
  canonical := osKB_canonicalC (CM := CM) hm hp _
  ood := osKB_oodC (CM := CM) hm hp _
  grind := osKB_grindC (CM := CM) hm hp _
  finalMsg := osKB_finalMsg4C (CM := CM) hm hp _
  foldFinal := osKB_foldFinal2C (CM := CM) hm hp _
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights6C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L8C (CM := CM) fs cert κ)
        (oq_completeAtB_L1_L64_L8_L19_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f439) (by decide +kernel)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_2_0 rfl os_sq_body_2_0
        (by show coreProgram.loop "__loop118" = true; rw [Program.loop_of_find? os_sq_find_2_0]; decide +kernel)
        os_res_find_2_0 rfl os_res_body_2_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L6C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L18_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f440) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_2_1 rfl os_sq_body_2_1
        (by show coreProgram.loop "__loop119" = true; rw [Program.loop_of_find? os_sq_find_2_1]; decide +kernel)
        os_res_find_2_1 rfl os_res_body_2_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L17_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f441) (by decide +kernel)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_2_2 rfl os_sq_body_2_2
        (by show coreProgram.loop "__loop120" = true; rw [Program.loop_of_find? os_sq_find_2_2]; decide +kernel)
        os_res_find_2_2 rfl os_res_body_2_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L16_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f438) (by decide +kernel)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_2_3 rfl os_sq_body_2_3
        (by show coreProgram.loop "__loop121" = true; rw [Program.loop_of_find? os_sq_find_2_3]; decide +kernel)
        os_res_find_2_3 rfl os_res_body_2_3
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L15_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f434) (by decide +kernel)
        (h1.decode (15, "decode_query_bits__L15") (by decide)) (by decide +kernel) os_sq_find_2_4 rfl os_sq_body_2_4
        (by show coreProgram.loop "__loop122" = true; rw [Program.loop_of_find? os_sq_find_2_4]; decide +kernel)
        os_res_find_2_4 rfl os_res_body_2_4
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_3C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBC CM Ht fs cert κ osCfg3 (osBdC CM fs hm hp osCfg3) where
  fold := osKB_foldC (CM := CM) hm hp _
  canonical := osKB_canonicalC (CM := CM) hm hp _
  ood := osKB_oodC (CM := CM) hm hp _
  grind := osKB_grindC (CM := CM) hm hp _
  finalMsg := osKB_finalMsg8C (CM := CM) hm hp _
  foldFinal := osKB_foldFinal3C (CM := CM) hm hp _
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights6C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L8C (CM := CM) fs cert κ)
        (oq_completeAtB_L1_L64_L8_L20_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f442) (by decide +kernel)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_3_0 rfl os_sq_body_3_0
        (by show coreProgram.loop "__loop128" = true; rw [Program.loop_of_find? os_sq_find_3_0]; decide +kernel)
        os_res_find_3_0 rfl os_res_body_3_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L6C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L19_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f443) (by decide +kernel)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_3_1 rfl os_sq_body_3_1
        (by show coreProgram.loop "__loop129" = true; rw [Program.loop_of_find? os_sq_find_3_1]; decide +kernel)
        os_res_find_3_1 rfl os_res_body_3_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L18_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f444) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_3_2 rfl os_sq_body_3_2
        (by show coreProgram.loop "__loop130" = true; rw [Program.loop_of_find? os_sq_find_3_2]; decide +kernel)
        os_res_find_3_2 rfl os_res_body_3_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L17_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f441) (by decide +kernel)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_3_3 rfl os_sq_body_3_3
        (by show coreProgram.loop "__loop131" = true; rw [Program.loop_of_find? os_sq_find_3_3]; decide +kernel)
        os_res_find_3_3 rfl os_res_body_3_3
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L16_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f438) (by decide +kernel)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_3_4 rfl os_sq_body_3_4
        (by show coreProgram.loop "__loop132" = true; rw [Program.loop_of_find? os_sq_find_3_4]; decide +kernel)
        os_res_find_3_4 rfl os_res_body_3_4
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_4C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBC CM Ht fs cert κ osCfg4 (osBdC CM fs hm hp osCfg4) where
  fold := osKB_foldC (CM := CM) hm hp _
  canonical := osKB_canonicalC (CM := CM) hm hp _
  ood := osKB_oodC (CM := CM) hm hp _
  grind := osKB_grindC (CM := CM) hm hp _
  finalMsg := osKB_finalMsg16C (CM := CM) hm hp _
  foldFinal := osKB_foldFinal4C (CM := CM) hm hp _
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights6C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L8C (CM := CM) fs cert κ)
        (oq_completeAtB_L1_L64_L8_L21_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f445) (by decide +kernel)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_4_0 rfl os_sq_body_4_0
        (by show coreProgram.loop "__loop138" = true; rw [Program.loop_of_find? os_sq_find_4_0]; decide +kernel)
        os_res_find_4_0 rfl os_res_body_4_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L6C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L20_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f446) (by decide +kernel)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_4_1 rfl os_sq_body_4_1
        (by show coreProgram.loop "__loop139" = true; rw [Program.loop_of_find? os_sq_find_4_1]; decide +kernel)
        os_res_find_4_1 rfl os_res_body_4_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L19_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f447) (by decide +kernel)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_4_2 rfl os_sq_body_4_2
        (by show coreProgram.loop "__loop140" = true; rw [Program.loop_of_find? os_sq_find_4_2]; decide +kernel)
        os_res_find_4_2 rfl os_res_body_4_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L18_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f444) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_4_3 rfl os_sq_body_4_3
        (by show coreProgram.loop "__loop141" = true; rw [Program.loop_of_find? os_sq_find_4_3]; decide +kernel)
        os_res_find_4_3 rfl os_res_body_4_3
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L17_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f441) (by decide +kernel)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_4_4 rfl os_sq_body_4_4
        (by show coreProgram.loop "__loop142" = true; rw [Program.loop_of_find? os_sq_find_4_4]; decide +kernel)
        os_res_find_4_4 rfl os_res_body_4_4
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_5C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBC CM Ht fs cert κ osCfg5 (osBdC CM fs hm hp osCfg5) where
  fold := osKB_foldC (CM := CM) hm hp _
  canonical := osKB_canonicalC (CM := CM) hm hp _
  ood := osKB_oodC (CM := CM) hm hp _
  grind := osKB_grindC (CM := CM) hm hp _
  finalMsg := osKB_finalMsg32C (CM := CM) hm hp _
  foldFinal := osKB_foldFinal5C (CM := CM) hm hp _
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights6C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L8C (CM := CM) fs cert κ)
        (oq_completeAtB_L1_L64_L8_L22_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f448) (by decide +kernel)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_5_0 rfl os_sq_body_5_0
        (by show coreProgram.loop "__loop148" = true; rw [Program.loop_of_find? os_sq_find_5_0]; decide +kernel)
        os_res_find_5_0 rfl os_res_body_5_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L6C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L21_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f449) (by decide +kernel)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_5_1 rfl os_sq_body_5_1
        (by show coreProgram.loop "__loop149" = true; rw [Program.loop_of_find? os_sq_find_5_1]; decide +kernel)
        os_res_find_5_1 rfl os_res_body_5_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L20_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f450) (by decide +kernel)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_5_2 rfl os_sq_body_5_2
        (by show coreProgram.loop "__loop150" = true; rw [Program.loop_of_find? os_sq_find_5_2]; decide +kernel)
        os_res_find_5_2 rfl os_res_body_5_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L19_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f447) (by decide +kernel)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_5_3 rfl os_sq_body_5_3
        (by show coreProgram.loop "__loop151" = true; rw [Program.loop_of_find? os_sq_find_5_3]; decide +kernel)
        os_res_find_5_3 rfl os_res_body_5_3
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L18_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f444) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_5_4 rfl os_sq_body_5_4
        (by show coreProgram.loop "__loop152" = true; rw [Program.loop_of_find? os_sq_find_5_4]; decide +kernel)
        os_res_find_5_4 rfl os_res_body_5_4
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_6C (h1 : OsCalleesAtBC CM fs cert κ) (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizesC CM fs) : OsKidsAtBC CM Ht fs cert κ osCfg6 (osBdC CM fs hm hp osCfg6) where
  fold := osKB_foldC (CM := CM) hm hp _
  canonical := osKB_canonicalC (CM := CM) hm hp _
  ood := osKB_oodC (CM := CM) hm hp _
  grind := osKB_grindC (CM := CM) hm hp _
  finalMsg := osKB_finalMsg4C (CM := CM) hm hp _
  foldFinal := osKB_foldFinal2C (CM := CM) hm hp _
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights6C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L8C (CM := CM) fs cert κ)
        (oq_completeAtB_L1_L64_L8_L23_L8C (Ht := Ht) (CM := CM) fs cert κ hq.f451) (by decide +kernel)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_6_0 rfl os_sq_body_6_0
        (by show coreProgram.loop "__loop158" = true; rw [Program.loop_of_find? os_sq_find_6_0]; decide +kernel)
        os_res_find_6_0 rfl os_res_body_6_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L6C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L22_L6C (Ht := Ht) (CM := CM) fs cert κ hq.f452) (by decide +kernel)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_6_1 rfl os_sq_body_6_1
        (by show coreProgram.loop "__loop159" = true; rw [Program.loop_of_find? os_sq_find_6_1]; decide +kernel)
        os_res_find_6_1 rfl os_res_body_6_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L21_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f453) (by decide +kernel)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_6_2 rfl os_sq_body_6_2
        (by show coreProgram.loop "__loop160" = true; rw [Program.loop_of_find? os_sq_find_6_2]; decide +kernel)
        os_res_find_6_2 rfl os_res_body_6_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L20_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f450) (by decide +kernel)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_6_3 rfl os_sq_body_6_3
        (by show coreProgram.loop "__loop161" = true; rw [Program.loop_of_find? os_sq_find_6_3]; decide +kernel)
        os_res_find_6_3 rfl os_res_body_6_3
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L5C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L19_L5C (Ht := Ht) (CM := CM) fs cert κ hq.f447) (by decide +kernel)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_6_4 rfl os_sq_body_6_4
        (by show coreProgram.loop "__loop162" = true; rw [Program.loop_of_find? os_sq_find_6_4]; decide +kernel)
        os_res_find_6_4 rfl os_res_body_6_4
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mkC (Ht := Ht) (CM := CM) hi (osKB_rowWeights4C (CM := CM) hm hp _) (by decide +kernel) (vmc_completeAtB_L4C (CM := CM) fs cert κ)
        (oq_completeAtB_L0_L16_L6_L18_L4C (Ht := Ht) (CM := CM) fs cert κ hq.f455) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_6_5 rfl os_sq_body_6_5
        (by show coreProgram.loop "__loop163" = true; rw [Program.loop_of_find? os_sq_find_6_5]; decide +kernel)
        os_res_find_6_5 rfl os_res_body_6_5
        (by decide +kernel) (by decide +kernel)

end
end LeanVM.Guest.B1
