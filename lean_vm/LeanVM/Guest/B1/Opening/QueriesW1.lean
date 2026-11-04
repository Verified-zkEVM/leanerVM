/-
  LeanVM.Guest.B1.Opening.QueriesW1

  A quarter of `opening_queries`' specializations, sound with their queries named.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody1
public import LeanVM.Guest.B1.Opening.QueriesMainW

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L7` is sound with its queries named. -/
theorem oqSpecW_533 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L18_L7" "__loop391" ⟨1, 64, 11, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 11, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 555) (by decide +kernel) rfl) rfl oqBody_533
    (Program.find?_of_indexOf? (j := 893) (by decide +kernel) rfl) rfl oqBody_859

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L6` is sound with its queries named. -/
theorem oqSpecW_692 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L20_L6" "__loop414" ⟨1, 64, 14, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 14, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 714) (by decide +kernel) rfl) rfl oqBody_692
    (Program.find?_of_indexOf? (j := 932) (by decide +kernel) rfl) rfl oqBody_884

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L7` is sound with its queries named. -/
theorem oqSpecW_563 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L21_L7" "__loop395" ⟨1, 64, 14, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 14, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 585) (by decide +kernel) rfl) rfl oqBody_563
    (Program.find?_of_indexOf? (j := 901) (by decide +kernel) rfl) rfl oqBody_863

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L6` is sound with its queries named. -/
theorem oqSpecW_721 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L23_L6" "__loop417" ⟨1, 64, 17, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 17, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 743) (by decide +kernel) rfl) rfl oqBody_721
    (Program.find?_of_indexOf? (j := 935) (by decide +kernel) rfl) rfl oqBody_887

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L6` is sound with its queries named. -/
theorem oqSpecW_743 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L25_L6" "__loop419" ⟨1, 64, 19, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 19, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 765) (by decide +kernel) rfl) rfl oqBody_743
    (Program.find?_of_indexOf? (j := 938) (by decide +kernel) rfl) rfl oqBody_889

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L7` is sound with its queries named. -/
theorem oqSpecW_632 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L21_L7" "__loop406" ⟨1, 64, 14, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 14, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 654) (by decide +kernel) rfl) rfl oqBody_632
    (Program.find?_of_indexOf? (j := 920) (by decide +kernel) rfl) rfl oqBody_875

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L8` is sound with its queries named. -/
theorem oqSpecW_515 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L23_L8" "__loop387" ⟨1, 64, 15, 8⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 15, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 537) (by decide +kernel) rfl) rfl oqBody_515
    (Program.find?_of_indexOf? (j := 885) (by decide +kernel) rfl) rfl oqBody_855

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L5` is sound with its queries named. -/
theorem oqSpecW_422 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L15_L5" "__loop370" ⟨0, 16, 10, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 10, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 444) (by decide +kernel) rfl) rfl oqBody_422
    (Program.find?_of_indexOf? (j := 851) (by decide +kernel) rfl) rfl oqBody_831

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L4` is sound with its queries named. -/
theorem oqSpecW_568 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L17_L4" "__loop396" ⟨0, 16, 13, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 13, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 590) (by decide +kernel) rfl) rfl oqBody_568
    (Program.find?_of_indexOf? (j := 903) (by decide +kernel) rfl) rfl oqBody_864

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L5` is sound with its queries named. -/
theorem oqSpecW_474 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L18_L5" "__loop380" ⟨0, 16, 13, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 13, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 496) (by decide +kernel) rfl) rfl oqBody_474
    (Program.find?_of_indexOf? (j := 871) (by decide +kernel) rfl) rfl oqBody_845

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L6` is sound with its queries named. -/
theorem oqSpecW_471 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L19_L6" "__loop379" ⟨0, 16, 13, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 13, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 493) (by decide +kernel) rfl) rfl oqBody_471
    (Program.find?_of_indexOf? (j := 869) (by decide +kernel) rfl) rfl oqBody_844

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L4` is sound with its queries named. -/
theorem oqSpecW_683 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L21_L4" "__loop413" ⟨0, 16, 17, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 17, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 705) (by decide +kernel) rfl) rfl oqBody_683
    (Program.find?_of_indexOf? (j := 931) (by decide +kernel) rfl) rfl oqBody_883

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L5` is sound with its queries named. -/
theorem oqSpecW_602 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L22_L5" "__loop402" ⟨0, 16, 17, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 17, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 624) (by decide +kernel) rfl) rfl oqBody_602
    (Program.find?_of_indexOf? (j := 915) (by decide +kernel) rfl) rfl oqBody_871

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L5` is sound with its queries named. -/
theorem oqSpecW_745 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L24_L5" "__loop420" ⟨0, 16, 19, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 19, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 767) (by decide +kernel) rfl) rfl oqBody_745
    (Program.find?_of_indexOf? (j := 940) (by decide +kernel) rfl) rfl oqBody_890

end
end LeanVM.Guest.B1
