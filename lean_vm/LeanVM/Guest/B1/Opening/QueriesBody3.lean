/-
  LeanVM.Guest.B1.Opening.QueriesBody3

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
theorem oqBody_542 : Data.core521.body = oqMainT ⟨1, 64, 12, 7⟩ 0 "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_860 : Data.core839.body = oqLoop1T ⟨1, 64, 12, 7⟩ 0 "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7` is its meaning. -/
theorem oqSpec_542 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L19_L7" 0 1 64 19 7 :=
  oqMain1_iff (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 521) (by decide +kernel) rfl) rfl oqBody_542
    (Program.find?_of_indexOf? (j := 839) (by decide +kernel) rfl) rfl oqBody_860

set_option maxRecDepth 100000 in
theorem oqBody_468 : Data.core447.body = oqMainT ⟨1, 64, 12, 8⟩ 0 "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_843 : Data.core822.body = oqLoop1T ⟨1, 64, 12, 8⟩ 0 "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8` is its meaning. -/
theorem oqSpec_468 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L20_L8" 0 1 64 20 8 :=
  oqMain1_iff (s := ⟨1, 64, 12, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 447) (by decide +kernel) rfl) rfl oqBody_468
    (Program.find?_of_indexOf? (j := 822) (by decide +kernel) rfl) rfl oqBody_843

set_option maxRecDepth 100000 in
theorem oqBody_710 : Data.core689.body = oqMainT ⟨1, 64, 16, 6⟩ 0 "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_886 : Data.core865.body = oqLoop1T ⟨1, 64, 16, 6⟩ 0 "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L6` is its meaning. -/
theorem oqSpec_710 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L22_L6" 0 1 64 22 6 :=
  oqMain1_iff (s := ⟨1, 64, 16, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 689) (by decide +kernel) rfl) rfl oqBody_710
    (Program.find?_of_indexOf? (j := 865) (by decide +kernel) rfl) rfl oqBody_886

set_option maxRecDepth 100000 in
theorem oqBody_732 : Data.core711.body = oqMainT ⟨1, 64, 18, 6⟩ 0 "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_888 : Data.core867.body = oqLoop1T ⟨1, 64, 18, 6⟩ 0 "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6` is its meaning. -/
theorem oqSpec_732 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L24_L6" 0 1 64 24 6 :=
  oqMain1_iff (s := ⟨1, 64, 18, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 711) (by decide +kernel) rfl) rfl oqBody_732
    (Program.find?_of_indexOf? (j := 867) (by decide +kernel) rfl) rfl oqBody_888

set_option maxRecDepth 100000 in
theorem oqBody_614 : Data.core593.body = oqMainT ⟨1, 64, 12, 7⟩ 1 "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_873 : Data.core852.body = oqLoop1T ⟨1, 64, 12, 7⟩ 1 "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7` is its meaning. -/
theorem oqSpec_614 :
    opening_queries_Spec "opening_queries__L1_L1_L64_L32_L19_L7" 1 1 64 19 7 :=
  oqMain1_iff (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 593) (by decide +kernel) rfl) rfl oqBody_614
    (Program.find?_of_indexOf? (j := 852) (by decide +kernel) rfl) rfl oqBody_873

set_option maxRecDepth 100000 in
theorem oqBody_501 : Data.core480.body = oqMainT ⟨1, 64, 14, 8⟩ 1 "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_851 : Data.core830.body = oqLoop1T ⟨1, 64, 14, 8⟩ 1 "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L8` is its meaning. -/
theorem oqSpec_501 :
    opening_queries_Spec "opening_queries__L1_L1_L64_L32_L22_L8" 1 1 64 22 8 :=
  oqMain1_iff (s := ⟨1, 64, 14, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 480) (by decide +kernel) rfl) rfl oqBody_501
    (Program.find?_of_indexOf? (j := 830) (by decide +kernel) rfl) rfl oqBody_851

set_option maxRecDepth 100000 in
theorem oqBody_676 : Data.core655.body = oqMainT ⟨1, 64, 18, 7⟩ 1 "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_880 : Data.core859.body = oqLoop1T ⟨1, 64, 18, 7⟩ 1 "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7` is its meaning. -/
theorem oqSpec_676 :
    opening_queries_Spec "opening_queries__L1_L1_L64_L32_L25_L7" 1 1 64 25 7 :=
  oqMain1_iff (s := ⟨1, 64, 18, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 655) (by decide +kernel) rfl) rfl oqBody_676
    (Program.find?_of_indexOf? (j := 859) (by decide +kernel) rfl) rfl oqBody_880

set_option maxRecDepth 100000 in
theorem oqBody_439 : Data.core418.body = oqMainT ⟨0, 16, 11, 5⟩ 0 "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_837 : Data.core816.body = oqLoop0T ⟨0, 16, 11, 5⟩ "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L5` is its meaning. -/
theorem oqSpec_439 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L16_L5" 0 0 16 16 5 :=
  oqMain0_iff (s := ⟨0, 16, 11, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 418) (by decide +kernel) rfl) rfl oqBody_439
    (Program.find?_of_indexOf? (j := 816) (by decide +kernel) rfl) rfl oqBody_837

set_option maxRecDepth 100000 in
theorem oqBody_436 : Data.core415.body = oqMainT ⟨0, 16, 11, 6⟩ 0 "__loop364" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_836 : Data.core815.body = oqLoop0T ⟨0, 16, 11, 6⟩ "__loop364" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L6` is its meaning. -/
theorem oqSpec_436 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L17_L6" 0 0 16 17 6 :=
  oqMain0_iff (s := ⟨0, 16, 11, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 415) (by decide +kernel) rfl) rfl oqBody_436
    (Program.find?_of_indexOf? (j := 815) (by decide +kernel) rfl) rfl oqBody_836

set_option maxRecDepth 100000 in
theorem oqBody_591 : Data.core570.body = oqMainT ⟨0, 16, 15, 4⟩ 0 "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_867 : Data.core846.body = oqLoop0T ⟨0, 16, 15, 4⟩ "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L4` is its meaning. -/
theorem oqSpec_591 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L19_L4" 0 0 16 19 4 :=
  oqMain0_iff (s := ⟨0, 16, 15, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 570) (by decide +kernel) rfl) rfl oqBody_591
    (Program.find?_of_indexOf? (j := 846) (by decide +kernel) rfl) rfl oqBody_867

set_option maxRecDepth 100000 in
theorem oqBody_505 : Data.core484.body = oqMainT ⟨0, 16, 15, 5⟩ 0 "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_853 : Data.core832.body = oqLoop0T ⟨0, 16, 15, 5⟩ "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L5` is its meaning. -/
theorem oqSpec_505 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L20_L5" 0 0 16 20 5 :=
  oqMain0_iff (s := ⟨0, 16, 15, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 484) (by decide +kernel) rfl) rfl oqBody_505
    (Program.find?_of_indexOf? (j := 832) (by decide +kernel) rfl) rfl oqBody_853

set_option maxRecDepth 100000 in
theorem oqBody_503 : Data.core482.body = oqMainT ⟨0, 16, 15, 6⟩ 0 "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_852 : Data.core831.body = oqLoop0T ⟨0, 16, 15, 6⟩ "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L6` is its meaning. -/
theorem oqSpec_503 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L21_L6" 0 0 16 21 6 :=
  oqMain0_iff (s := ⟨0, 16, 15, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 482) (by decide +kernel) rfl) rfl oqBody_503
    (Program.find?_of_indexOf? (j := 831) (by decide +kernel) rfl) rfl oqBody_852

set_option maxRecDepth 100000 in
theorem oqBody_680 : Data.core659.body = oqMainT ⟨0, 16, 18, 5⟩ 0 "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_882 : Data.core861.body = oqLoop0T ⟨0, 16, 18, 5⟩ "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5` is its meaning. -/
theorem oqSpec_680 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L23_L5" 0 0 16 23 5 :=
  oqMain0_iff (s := ⟨0, 16, 18, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 659) (by decide +kernel) rfl) rfl oqBody_680
    (Program.find?_of_indexOf? (j := 861) (by decide +kernel) rfl) rfl oqBody_882

set_option maxRecDepth 100000 in
theorem oqBody_757 : Data.core736.body = oqMainT ⟨0, 16, 20, 5⟩ 0 "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_893 : Data.core872.body = oqLoop0T ⟨0, 16, 20, 5⟩ "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L5` is its meaning. -/
theorem oqSpec_757 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L25_L5" 0 0 16 25 5 :=
  oqMain0_iff (s := ⟨0, 16, 20, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 736) (by decide +kernel) rfl) rfl oqBody_757
    (Program.find?_of_indexOf? (j := 872) (by decide +kernel) rfl) rfl oqBody_893

end
end LeanVM.Guest.B1
