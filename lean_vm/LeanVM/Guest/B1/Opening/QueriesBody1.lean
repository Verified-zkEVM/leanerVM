/-
  LeanVM.Guest.B1.Opening.QueriesBody1

  The bodies of a quarter of `opening_queries`' specializations and of their loop helpers are the
  templates (kernel evaluation), and so they are their meaning.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete6

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem oqBody_533 : Data.core512.body = oqMainT ⟨1, 64, 11, 7⟩ 0 "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_859 : Data.core838.body = oqLoop1T ⟨1, 64, 11, 7⟩ 0 "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L7` is its meaning. -/
theorem oqSpec_533 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L18_L7" 0 1 64 18 7 :=
  oqMain1_iff (s := ⟨1, 64, 11, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 512) (by decide +kernel) rfl) rfl oqBody_533
    (Program.find?_of_indexOf? (j := 838) (by decide +kernel) rfl) rfl oqBody_859

set_option maxRecDepth 100000 in
theorem oqBody_692 : Data.core671.body = oqMainT ⟨1, 64, 14, 6⟩ 0 "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_884 : Data.core863.body = oqLoop1T ⟨1, 64, 14, 6⟩ 0 "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L6` is its meaning. -/
theorem oqSpec_692 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L20_L6" 0 1 64 20 6 :=
  oqMain1_iff (s := ⟨1, 64, 14, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 671) (by decide +kernel) rfl) rfl oqBody_692
    (Program.find?_of_indexOf? (j := 863) (by decide +kernel) rfl) rfl oqBody_884

set_option maxRecDepth 100000 in
theorem oqBody_563 : Data.core542.body = oqMainT ⟨1, 64, 14, 7⟩ 0 "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_863 : Data.core842.body = oqLoop1T ⟨1, 64, 14, 7⟩ 0 "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L7` is its meaning. -/
theorem oqSpec_563 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L21_L7" 0 1 64 21 7 :=
  oqMain1_iff (s := ⟨1, 64, 14, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 542) (by decide +kernel) rfl) rfl oqBody_563
    (Program.find?_of_indexOf? (j := 842) (by decide +kernel) rfl) rfl oqBody_863

set_option maxRecDepth 100000 in
theorem oqBody_721 : Data.core700.body = oqMainT ⟨1, 64, 17, 6⟩ 0 "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_887 : Data.core866.body = oqLoop1T ⟨1, 64, 17, 6⟩ 0 "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L6` is its meaning. -/
theorem oqSpec_721 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L23_L6" 0 1 64 23 6 :=
  oqMain1_iff (s := ⟨1, 64, 17, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 700) (by decide +kernel) rfl) rfl oqBody_721
    (Program.find?_of_indexOf? (j := 866) (by decide +kernel) rfl) rfl oqBody_887

set_option maxRecDepth 100000 in
theorem oqBody_743 : Data.core722.body = oqMainT ⟨1, 64, 19, 6⟩ 0 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_889 : Data.core868.body = oqLoop1T ⟨1, 64, 19, 6⟩ 0 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L6` is its meaning. -/
theorem oqSpec_743 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L25_L6" 0 1 64 25 6 :=
  oqMain1_iff (s := ⟨1, 64, 19, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 722) (by decide +kernel) rfl) rfl oqBody_743
    (Program.find?_of_indexOf? (j := 868) (by decide +kernel) rfl) rfl oqBody_889

set_option maxRecDepth 100000 in
theorem oqBody_632 : Data.core611.body = oqMainT ⟨1, 64, 14, 7⟩ 1 "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_875 : Data.core854.body = oqLoop1T ⟨1, 64, 14, 7⟩ 1 "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L7` is its meaning. -/
theorem oqSpec_632 :
    opening_queries_Spec "opening_queries__L1_L1_L64_L32_L21_L7" 1 1 64 21 7 :=
  oqMain1_iff (s := ⟨1, 64, 14, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 611) (by decide +kernel) rfl) rfl oqBody_632
    (Program.find?_of_indexOf? (j := 854) (by decide +kernel) rfl) rfl oqBody_875

set_option maxRecDepth 100000 in
theorem oqBody_515 : Data.core494.body = oqMainT ⟨1, 64, 15, 8⟩ 1 "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_855 : Data.core834.body = oqLoop1T ⟨1, 64, 15, 8⟩ 1 "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L8` is its meaning. -/
theorem oqSpec_515 :
    opening_queries_Spec "opening_queries__L1_L1_L64_L32_L23_L8" 1 1 64 23 8 :=
  oqMain1_iff (s := ⟨1, 64, 15, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 494) (by decide +kernel) rfl) rfl oqBody_515
    (Program.find?_of_indexOf? (j := 834) (by decide +kernel) rfl) rfl oqBody_855

set_option maxRecDepth 100000 in
theorem oqBody_422 : Data.core401.body = oqMainT ⟨0, 16, 10, 5⟩ 0 "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_831 : Data.core810.body = oqLoop0T ⟨0, 16, 10, 5⟩ "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L5` is its meaning. -/
theorem oqSpec_422 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L15_L5" 0 0 16 15 5 :=
  oqMain0_iff (s := ⟨0, 16, 10, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 401) (by decide +kernel) rfl) rfl oqBody_422
    (Program.find?_of_indexOf? (j := 810) (by decide +kernel) rfl) rfl oqBody_831

set_option maxRecDepth 100000 in
theorem oqBody_568 : Data.core547.body = oqMainT ⟨0, 16, 13, 4⟩ 0 "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_864 : Data.core843.body = oqLoop0T ⟨0, 16, 13, 4⟩ "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L4` is its meaning. -/
theorem oqSpec_568 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L17_L4" 0 0 16 17 4 :=
  oqMain0_iff (s := ⟨0, 16, 13, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 547) (by decide +kernel) rfl) rfl oqBody_568
    (Program.find?_of_indexOf? (j := 843) (by decide +kernel) rfl) rfl oqBody_864

set_option maxRecDepth 100000 in
theorem oqBody_474 : Data.core453.body = oqMainT ⟨0, 16, 13, 5⟩ 0 "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_845 : Data.core824.body = oqLoop0T ⟨0, 16, 13, 5⟩ "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L5` is its meaning. -/
theorem oqSpec_474 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L18_L5" 0 0 16 18 5 :=
  oqMain0_iff (s := ⟨0, 16, 13, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 453) (by decide +kernel) rfl) rfl oqBody_474
    (Program.find?_of_indexOf? (j := 824) (by decide +kernel) rfl) rfl oqBody_845

set_option maxRecDepth 100000 in
theorem oqBody_471 : Data.core450.body = oqMainT ⟨0, 16, 13, 6⟩ 0 "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_844 : Data.core823.body = oqLoop0T ⟨0, 16, 13, 6⟩ "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L6` is its meaning. -/
theorem oqSpec_471 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L19_L6" 0 0 16 19 6 :=
  oqMain0_iff (s := ⟨0, 16, 13, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 450) (by decide +kernel) rfl) rfl oqBody_471
    (Program.find?_of_indexOf? (j := 823) (by decide +kernel) rfl) rfl oqBody_844

set_option maxRecDepth 100000 in
theorem oqBody_683 : Data.core662.body = oqMainT ⟨0, 16, 17, 4⟩ 0 "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_883 : Data.core862.body = oqLoop0T ⟨0, 16, 17, 4⟩ "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L4` is its meaning. -/
theorem oqSpec_683 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L21_L4" 0 0 16 21 4 :=
  oqMain0_iff (s := ⟨0, 16, 17, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 662) (by decide +kernel) rfl) rfl oqBody_683
    (Program.find?_of_indexOf? (j := 862) (by decide +kernel) rfl) rfl oqBody_883

set_option maxRecDepth 100000 in
theorem oqBody_602 : Data.core581.body = oqMainT ⟨0, 16, 17, 5⟩ 0 "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_871 : Data.core850.body = oqLoop0T ⟨0, 16, 17, 5⟩ "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L5` is its meaning. -/
theorem oqSpec_602 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L22_L5" 0 0 16 22 5 :=
  oqMain0_iff (s := ⟨0, 16, 17, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 581) (by decide +kernel) rfl) rfl oqBody_602
    (Program.find?_of_indexOf? (j := 850) (by decide +kernel) rfl) rfl oqBody_871

set_option maxRecDepth 100000 in
theorem oqBody_745 : Data.core724.body = oqMainT ⟨0, 16, 19, 5⟩ 0 "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_890 : Data.core869.body = oqLoop0T ⟨0, 16, 19, 5⟩ "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L5` is its meaning. -/
theorem oqSpec_745 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L24_L5" 0 0 16 24 5 :=
  oqMain0_iff (s := ⟨0, 16, 19, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 724) (by decide +kernel) rfl) rfl oqBody_745
    (Program.find?_of_indexOf? (j := 869) (by decide +kernel) rfl) rfl oqBody_890

end
end LeanVM.Guest.B1
