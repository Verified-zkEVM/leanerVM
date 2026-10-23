/-
  LeanVM.Guest.B1.Opening.QueriesBody0

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
theorem oqBody_413 : Data.core413.body = oqMainT ⟨1, 64, 9, 8⟩ 0 "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_827 : Data.core827.body = oqLoop1T ⟨1, 64, 9, 8⟩ 0 "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L17_L8` is its meaning. -/
theorem oqSpec_413 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L17_L8" 0 1 64 17 8 :=
  oqMain1_iff (s := ⟨1, 64, 9, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 413) (by decide +kernel) rfl) rfl oqBody_413
    (Program.find?_of_indexOf? (j := 827) (by decide +kernel) rfl) rfl oqBody_827

set_option maxRecDepth 100000 in
theorem oqBody_449 : Data.core449.body = oqMainT ⟨1, 64, 11, 8⟩ 0 "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_839 : Data.core839.body = oqLoop1T ⟨1, 64, 11, 8⟩ 0 "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L8` is its meaning. -/
theorem oqSpec_449 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L19_L8" 0 1 64 19 8 :=
  oqMain1_iff (s := ⟨1, 64, 11, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 449) (by decide +kernel) rfl) rfl oqBody_449
    (Program.find?_of_indexOf? (j := 839) (by decide +kernel) rfl) rfl oqBody_839

set_option maxRecDepth 100000 in
theorem oqBody_701 : Data.core701.body = oqMainT ⟨1, 64, 15, 6⟩ 0 "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_885 : Data.core885.body = oqLoop1T ⟨1, 64, 15, 6⟩ 0 "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L6` is its meaning. -/
theorem oqSpec_701 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L21_L6" 0 1 64 21 6 :=
  oqMain1_iff (s := ⟨1, 64, 15, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 701) (by decide +kernel) rfl) rfl oqBody_701
    (Program.find?_of_indexOf? (j := 885) (by decide +kernel) rfl) rfl oqBody_885

set_option maxRecDepth 100000 in
theorem oqBody_575 : Data.core575.body = oqMainT ⟨1, 64, 15, 7⟩ 0 "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_865 : Data.core865.body = oqLoop1T ⟨1, 64, 15, 7⟩ 0 "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L7` is its meaning. -/
theorem oqSpec_575 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L22_L7" 0 1 64 22 7 :=
  oqMain1_iff (s := ⟨1, 64, 15, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 575) (by decide +kernel) rfl) rfl oqBody_575
    (Program.find?_of_indexOf? (j := 865) (by decide +kernel) rfl) rfl oqBody_865

set_option maxRecDepth 100000 in
theorem oqBody_598 : Data.core598.body = oqMainT ⟨1, 64, 17, 7⟩ 0 "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_869 : Data.core869.body = oqLoop1T ⟨1, 64, 17, 7⟩ 0 "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L7` is its meaning. -/
theorem oqSpec_598 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L24_L7" 0 1 64 24 7 :=
  oqMain1_iff (s := ⟨1, 64, 17, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 598) (by decide +kernel) rfl) rfl oqBody_598
    (Program.find?_of_indexOf? (j := 869) (by decide +kernel) rfl) rfl oqBody_869

set_option maxRecDepth 100000 in
theorem oqBody_623 : Data.core623.body = oqMainT ⟨1, 64, 13, 7⟩ 1 "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_874 : Data.core874.body = oqLoop1T ⟨1, 64, 13, 7⟩ 1 "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L7` is its meaning. -/
theorem oqSpec_623 :
    opening_queries_Spec "opening_queries__L1_L1_L64_L32_L20_L7" 1 1 64 20 7 :=
  oqMain1_iff (s := ⟨1, 64, 13, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 623) (by decide +kernel) rfl) rfl oqBody_623
    (Program.find?_of_indexOf? (j := 874) (by decide +kernel) rfl) rfl oqBody_874

set_option maxRecDepth 100000 in
theorem oqBody_654 : Data.core654.body = oqMainT ⟨1, 64, 16, 7⟩ 1 "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_877 : Data.core877.body = oqLoop1T ⟨1, 64, 16, 7⟩ 1 "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L7` is its meaning. -/
theorem oqSpec_654 :
    opening_queries_Spec "opening_queries__L1_L1_L64_L32_L23_L7" 1 1 64 23 7 :=
  oqMain1_iff (s := ⟨1, 64, 16, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 654) (by decide +kernel) rfl) rfl oqBody_654
    (Program.find?_of_indexOf? (j := 877) (by decide +kernel) rfl) rfl oqBody_877

set_option maxRecDepth 100000 in
theorem oqBody_425 : Data.core425.body = oqMainT ⟨0, 16, 9, 5⟩ 0 "__loop364" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_833 : Data.core833.body = oqLoop0T ⟨0, 16, 9, 5⟩ "__loop364" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L5` is its meaning. -/
theorem oqSpec_425 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L14_L5" 0 0 16 14 5 :=
  oqMain0_iff (s := ⟨0, 16, 9, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 425) (by decide +kernel) rfl) rfl oqBody_425
    (Program.find?_of_indexOf? (j := 833) (by decide +kernel) rfl) rfl oqBody_833

set_option maxRecDepth 100000 in
theorem oqBody_418 : Data.core418.body = oqMainT ⟨0, 16, 10, 6⟩ 0 "__loop362" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_829 : Data.core829.body = oqLoop0T ⟨0, 16, 10, 6⟩ "__loop362" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L6` is its meaning. -/
theorem oqSpec_418 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L16_L6" 0 0 16 16 6 :=
  oqMain0_iff (s := ⟨0, 16, 10, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 418) (by decide +kernel) rfl) rfl oqBody_418
    (Program.find?_of_indexOf? (j := 829) (by decide +kernel) rfl) rfl oqBody_829

set_option maxRecDepth 100000 in
theorem oqBody_524 : Data.core524.body = oqMainT ⟨0, 16, 14, 4⟩ 0 "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_858 : Data.core858.body = oqLoop0T ⟨0, 16, 14, 4⟩ "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L4` is its meaning. -/
theorem oqSpec_524 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L18_L4" 0 0 16 18 4 :=
  oqMain0_iff (s := ⟨0, 16, 14, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 524) (by decide +kernel) rfl) rfl oqBody_524
    (Program.find?_of_indexOf? (j := 858) (by decide +kernel) rfl) rfl oqBody_858

set_option maxRecDepth 100000 in
theorem oqBody_491 : Data.core491.body = oqMainT ⟨0, 16, 14, 5⟩ 0 "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_849 : Data.core849.body = oqLoop0T ⟨0, 16, 14, 5⟩ "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L5` is its meaning. -/
theorem oqSpec_491 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L19_L5" 0 0 16 19 5 :=
  oqMain0_iff (s := ⟨0, 16, 14, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 491) (by decide +kernel) rfl) rfl oqBody_491
    (Program.find?_of_indexOf? (j := 849) (by decide +kernel) rfl) rfl oqBody_849

set_option maxRecDepth 100000 in
theorem oqBody_489 : Data.core489.body = oqMainT ⟨0, 16, 14, 6⟩ 0 "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_848 : Data.core848.body = oqLoop0T ⟨0, 16, 14, 6⟩ "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L6` is its meaning. -/
theorem oqSpec_489 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L20_L6" 0 0 16 20 6 :=
  oqMain0_iff (s := ⟨0, 16, 14, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 489) (by decide +kernel) rfl) rfl oqBody_489
    (Program.find?_of_indexOf? (j := 848) (by decide +kernel) rfl) rfl oqBody_848

set_option maxRecDepth 100000 in
theorem oqBody_761 : Data.core761.body = oqMainT ⟨0, 16, 18, 4⟩ 0 "__loop416" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_894 : Data.core894.body = oqLoop0T ⟨0, 16, 18, 4⟩ "__loop416" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4` is its meaning. -/
theorem oqSpec_761 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L22_L4" 0 0 16 22 4 :=
  oqMain0_iff (s := ⟨0, 16, 18, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 761) (by decide +kernel) rfl) rfl oqBody_761
    (Program.find?_of_indexOf? (j := 894) (by decide +kernel) rfl) rfl oqBody_894

set_option maxRecDepth 100000 in
theorem oqBody_600 : Data.core600.body = oqMainT ⟨0, 16, 17, 6⟩ 0 "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_870 : Data.core870.body = oqLoop0T ⟨0, 16, 17, 6⟩ "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L6` is its meaning. -/
theorem oqSpec_600 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L23_L6" 0 0 16 23 6 :=
  oqMain0_iff (s := ⟨0, 16, 17, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 600) (by decide +kernel) rfl) rfl oqBody_600
    (Program.find?_of_indexOf? (j := 870) (by decide +kernel) rfl) rfl oqBody_870

end
end LeanVM.Guest.B1
