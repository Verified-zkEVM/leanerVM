/-
  LeanVM.Guest.B1.Opening.QueriesW3

  A quarter of `opening_queries`' specializations, sound with their queries named.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody3
public import LeanVM.Guest.B1.Opening.QueriesMainW

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7` is sound with its queries named. -/
theorem oqSpecW_542 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L19_L7" "__loop383" ⟨1, 64, 12, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 521) (by decide +kernel) rfl) rfl oqBody_542
    (Program.find?_of_indexOf? (j := 839) (by decide +kernel) rfl) rfl oqBody_860

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8` is sound with its queries named. -/
theorem oqSpecW_468 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L20_L8" "__loop369" ⟨1, 64, 12, 8⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 447) (by decide +kernel) rfl) rfl oqBody_468
    (Program.find?_of_indexOf? (j := 822) (by decide +kernel) rfl) rfl oqBody_843

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L6` is sound with its queries named. -/
theorem oqSpecW_710 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L22_L6" "__loop407" ⟨1, 64, 16, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 16, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 689) (by decide +kernel) rfl) rfl oqBody_710
    (Program.find?_of_indexOf? (j := 865) (by decide +kernel) rfl) rfl oqBody_886

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6` is sound with its queries named. -/
theorem oqSpecW_732 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L24_L6" "__loop409" ⟨1, 64, 18, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 711) (by decide +kernel) rfl) rfl oqBody_732
    (Program.find?_of_indexOf? (j := 867) (by decide +kernel) rfl) rfl oqBody_888

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7` is sound with its queries named. -/
theorem oqSpecW_614 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L19_L7" "__loop395" ⟨1, 64, 12, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 593) (by decide +kernel) rfl) rfl oqBody_614
    (Program.find?_of_indexOf? (j := 852) (by decide +kernel) rfl) rfl oqBody_873

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L8` is sound with its queries named. -/
theorem oqSpecW_501 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L22_L8" "__loop375" ⟨1, 64, 14, 8⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 14, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 480) (by decide +kernel) rfl) rfl oqBody_501
    (Program.find?_of_indexOf? (j := 830) (by decide +kernel) rfl) rfl oqBody_851

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7` is sound with its queries named. -/
theorem oqSpecW_676 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L25_L7" "__loop401" ⟨1, 64, 18, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 655) (by decide +kernel) rfl) rfl oqBody_676
    (Program.find?_of_indexOf? (j := 859) (by decide +kernel) rfl) rfl oqBody_880

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L5` is sound with its queries named. -/
theorem oqSpecW_439 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L16_L5" "__loop365" ⟨0, 16, 11, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 11, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 418) (by decide +kernel) rfl) rfl oqBody_439
    (Program.find?_of_indexOf? (j := 816) (by decide +kernel) rfl) rfl oqBody_837

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L6` is sound with its queries named. -/
theorem oqSpecW_436 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L17_L6" "__loop364" ⟨0, 16, 11, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 11, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 415) (by decide +kernel) rfl) rfl oqBody_436
    (Program.find?_of_indexOf? (j := 815) (by decide +kernel) rfl) rfl oqBody_836

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L4` is sound with its queries named. -/
theorem oqSpecW_591 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L19_L4" "__loop390" ⟨0, 16, 15, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 15, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 570) (by decide +kernel) rfl) rfl oqBody_591
    (Program.find?_of_indexOf? (j := 846) (by decide +kernel) rfl) rfl oqBody_867

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L5` is sound with its queries named. -/
theorem oqSpecW_505 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L20_L5" "__loop377" ⟨0, 16, 15, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 15, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 484) (by decide +kernel) rfl) rfl oqBody_505
    (Program.find?_of_indexOf? (j := 832) (by decide +kernel) rfl) rfl oqBody_853

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L6` is sound with its queries named. -/
theorem oqSpecW_503 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L21_L6" "__loop376" ⟨0, 16, 15, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 15, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 482) (by decide +kernel) rfl) rfl oqBody_503
    (Program.find?_of_indexOf? (j := 831) (by decide +kernel) rfl) rfl oqBody_852

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5` is sound with its queries named. -/
theorem oqSpecW_680 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L23_L5" "__loop403" ⟨0, 16, 18, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 659) (by decide +kernel) rfl) rfl oqBody_680
    (Program.find?_of_indexOf? (j := 861) (by decide +kernel) rfl) rfl oqBody_882

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L5` is sound with its queries named. -/
theorem oqSpecW_757 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L25_L5" "__loop413" ⟨0, 16, 20, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 20, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 736) (by decide +kernel) rfl) rfl oqBody_757
    (Program.find?_of_indexOf? (j := 872) (by decide +kernel) rfl) rfl oqBody_893

end
end LeanVM.Guest.B1
