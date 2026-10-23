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
theorem oqBody_533 : Data.core533.body = oqMainT ⟨1, 64, 11, 7⟩ 0 "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_859 : Data.core859.body = oqLoop1T ⟨1, 64, 11, 7⟩ 0 "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L7` is its meaning. -/
theorem oqSpec_533 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L18_L7" 0 1 64 18 7 :=
  oqMain1_iff (s := ⟨1, 64, 11, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 533) (by decide +kernel) rfl) rfl oqBody_533
    (Program.find?_of_indexOf? (j := 859) (by decide +kernel) rfl) rfl oqBody_859

set_option maxRecDepth 100000 in
theorem oqBody_692 : Data.core692.body = oqMainT ⟨1, 64, 14, 6⟩ 0 "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_884 : Data.core884.body = oqLoop1T ⟨1, 64, 14, 6⟩ 0 "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L6` is its meaning. -/
theorem oqSpec_692 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L20_L6" 0 1 64 20 6 :=
  oqMain1_iff (s := ⟨1, 64, 14, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 692) (by decide +kernel) rfl) rfl oqBody_692
    (Program.find?_of_indexOf? (j := 884) (by decide +kernel) rfl) rfl oqBody_884

set_option maxRecDepth 100000 in
theorem oqBody_563 : Data.core563.body = oqMainT ⟨1, 64, 14, 7⟩ 0 "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_863 : Data.core863.body = oqLoop1T ⟨1, 64, 14, 7⟩ 0 "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L7` is its meaning. -/
theorem oqSpec_563 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L21_L7" 0 1 64 21 7 :=
  oqMain1_iff (s := ⟨1, 64, 14, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 563) (by decide +kernel) rfl) rfl oqBody_563
    (Program.find?_of_indexOf? (j := 863) (by decide +kernel) rfl) rfl oqBody_863

set_option maxRecDepth 100000 in
theorem oqBody_721 : Data.core721.body = oqMainT ⟨1, 64, 17, 6⟩ 0 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_887 : Data.core887.body = oqLoop1T ⟨1, 64, 17, 6⟩ 0 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L6` is its meaning. -/
theorem oqSpec_721 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L23_L6" 0 1 64 23 6 :=
  oqMain1_iff (s := ⟨1, 64, 17, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 721) (by decide +kernel) rfl) rfl oqBody_721
    (Program.find?_of_indexOf? (j := 887) (by decide +kernel) rfl) rfl oqBody_887

set_option maxRecDepth 100000 in
theorem oqBody_743 : Data.core743.body = oqMainT ⟨1, 64, 19, 6⟩ 0 "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_889 : Data.core889.body = oqLoop1T ⟨1, 64, 19, 6⟩ 0 "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L6` is its meaning. -/
theorem oqSpec_743 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L25_L6" 0 1 64 25 6 :=
  oqMain1_iff (s := ⟨1, 64, 19, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 743) (by decide +kernel) rfl) rfl oqBody_743
    (Program.find?_of_indexOf? (j := 889) (by decide +kernel) rfl) rfl oqBody_889

set_option maxRecDepth 100000 in
theorem oqBody_632 : Data.core632.body = oqMainT ⟨1, 64, 14, 7⟩ 1 "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_875 : Data.core875.body = oqLoop1T ⟨1, 64, 14, 7⟩ 1 "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L7` is its meaning. -/
theorem oqSpec_632 :
    opening_queries_Spec "opening_queries__L1_L1_L64_L32_L21_L7" 1 1 64 21 7 :=
  oqMain1_iff (s := ⟨1, 64, 14, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 632) (by decide +kernel) rfl) rfl oqBody_632
    (Program.find?_of_indexOf? (j := 875) (by decide +kernel) rfl) rfl oqBody_875

set_option maxRecDepth 100000 in
theorem oqBody_515 : Data.core515.body = oqMainT ⟨1, 64, 15, 8⟩ 1 "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_855 : Data.core855.body = oqLoop1T ⟨1, 64, 15, 8⟩ 1 "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L8` is its meaning. -/
theorem oqSpec_515 :
    opening_queries_Spec "opening_queries__L1_L1_L64_L32_L23_L8" 1 1 64 23 8 :=
  oqMain1_iff (s := ⟨1, 64, 15, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 515) (by decide +kernel) rfl) rfl oqBody_515
    (Program.find?_of_indexOf? (j := 855) (by decide +kernel) rfl) rfl oqBody_855

set_option maxRecDepth 100000 in
theorem oqBody_422 : Data.core422.body = oqMainT ⟨0, 16, 10, 5⟩ 0 "__loop363" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_831 : Data.core831.body = oqLoop0T ⟨0, 16, 10, 5⟩ "__loop363" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L5` is its meaning. -/
theorem oqSpec_422 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L15_L5" 0 0 16 15 5 :=
  oqMain0_iff (s := ⟨0, 16, 10, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 422) (by decide +kernel) rfl) rfl oqBody_422
    (Program.find?_of_indexOf? (j := 831) (by decide +kernel) rfl) rfl oqBody_831

set_option maxRecDepth 100000 in
theorem oqBody_568 : Data.core568.body = oqMainT ⟨0, 16, 13, 4⟩ 0 "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_864 : Data.core864.body = oqLoop0T ⟨0, 16, 13, 4⟩ "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L4` is its meaning. -/
theorem oqSpec_568 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L17_L4" 0 0 16 17 4 :=
  oqMain0_iff (s := ⟨0, 16, 13, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 568) (by decide +kernel) rfl) rfl oqBody_568
    (Program.find?_of_indexOf? (j := 864) (by decide +kernel) rfl) rfl oqBody_864

set_option maxRecDepth 100000 in
theorem oqBody_474 : Data.core474.body = oqMainT ⟨0, 16, 13, 5⟩ 0 "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_845 : Data.core845.body = oqLoop0T ⟨0, 16, 13, 5⟩ "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L5` is its meaning. -/
theorem oqSpec_474 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L18_L5" 0 0 16 18 5 :=
  oqMain0_iff (s := ⟨0, 16, 13, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 474) (by decide +kernel) rfl) rfl oqBody_474
    (Program.find?_of_indexOf? (j := 845) (by decide +kernel) rfl) rfl oqBody_845

set_option maxRecDepth 100000 in
theorem oqBody_471 : Data.core471.body = oqMainT ⟨0, 16, 13, 6⟩ 0 "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_844 : Data.core844.body = oqLoop0T ⟨0, 16, 13, 6⟩ "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L6` is its meaning. -/
theorem oqSpec_471 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L19_L6" 0 0 16 19 6 :=
  oqMain0_iff (s := ⟨0, 16, 13, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 471) (by decide +kernel) rfl) rfl oqBody_471
    (Program.find?_of_indexOf? (j := 844) (by decide +kernel) rfl) rfl oqBody_844

set_option maxRecDepth 100000 in
theorem oqBody_683 : Data.core683.body = oqMainT ⟨0, 16, 17, 4⟩ 0 "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_883 : Data.core883.body = oqLoop0T ⟨0, 16, 17, 4⟩ "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L4` is its meaning. -/
theorem oqSpec_683 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L21_L4" 0 0 16 21 4 :=
  oqMain0_iff (s := ⟨0, 16, 17, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 683) (by decide +kernel) rfl) rfl oqBody_683
    (Program.find?_of_indexOf? (j := 883) (by decide +kernel) rfl) rfl oqBody_883

set_option maxRecDepth 100000 in
theorem oqBody_602 : Data.core602.body = oqMainT ⟨0, 16, 17, 5⟩ 0 "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_871 : Data.core871.body = oqLoop0T ⟨0, 16, 17, 5⟩ "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L5` is its meaning. -/
theorem oqSpec_602 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L22_L5" 0 0 16 22 5 :=
  oqMain0_iff (s := ⟨0, 16, 17, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 602) (by decide +kernel) rfl) rfl oqBody_602
    (Program.find?_of_indexOf? (j := 871) (by decide +kernel) rfl) rfl oqBody_871

set_option maxRecDepth 100000 in
theorem oqBody_745 : Data.core745.body = oqMainT ⟨0, 16, 19, 5⟩ 0 "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_890 : Data.core890.body = oqLoop0T ⟨0, 16, 19, 5⟩ "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L5` is its meaning. -/
theorem oqSpec_745 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L24_L5" 0 0 16 24 5 :=
  oqMain0_iff (s := ⟨0, 16, 19, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 745) (by decide +kernel) rfl) rfl oqBody_745
    (Program.find?_of_indexOf? (j := 890) (by decide +kernel) rfl) rfl oqBody_890

end
end LeanVM.Guest.B1
