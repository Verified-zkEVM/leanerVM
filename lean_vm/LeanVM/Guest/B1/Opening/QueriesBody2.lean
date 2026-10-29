/-
  LeanVM.Guest.B1.Opening.QueriesBody2

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
theorem oqBody_433 : Data.core412.body = oqMainT ⟨1, 64, 10, 8⟩ 0 "__loop363" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_835 : Data.core814.body = oqLoop1T ⟨1, 64, 10, 8⟩ 0 "__loop363" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L8` is its meaning. -/
theorem oqSpec_433 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L18_L8" 0 1 64 18 8 :=
  oqMain1_iff (s := ⟨1, 64, 10, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 412) (by decide +kernel) rfl) rfl oqBody_433
    (Program.find?_of_indexOf? (j := 814) (by decide +kernel) rfl) rfl oqBody_835

set_option maxRecDepth 100000 in
theorem oqBody_551 : Data.core530.body = oqMainT ⟨1, 64, 13, 7⟩ 0 "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_861 : Data.core840.body = oqLoop1T ⟨1, 64, 13, 7⟩ 0 "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L7` is its meaning. -/
theorem oqSpec_551 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L20_L7" 0 1 64 20 7 :=
  oqMain1_iff (s := ⟨1, 64, 13, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 530) (by decide +kernel) rfl) rfl oqBody_551
    (Program.find?_of_indexOf? (j := 840) (by decide +kernel) rfl) rfl oqBody_861

set_option maxRecDepth 100000 in
theorem oqBody_487 : Data.core466.body = oqMainT ⟨1, 64, 13, 8⟩ 0 "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_847 : Data.core826.body = oqLoop1T ⟨1, 64, 13, 8⟩ 0 "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L8` is its meaning. -/
theorem oqSpec_487 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L21_L8" 0 1 64 21 8 :=
  oqMain1_iff (s := ⟨1, 64, 13, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 466) (by decide +kernel) rfl) rfl oqBody_487
    (Program.find?_of_indexOf? (j := 826) (by decide +kernel) rfl) rfl oqBody_847

set_option maxRecDepth 100000 in
theorem oqBody_586 : Data.core565.body = oqMainT ⟨1, 64, 16, 7⟩ 0 "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_866 : Data.core845.body = oqLoop1T ⟨1, 64, 16, 7⟩ 0 "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L7` is its meaning. -/
theorem oqSpec_586 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L23_L7" 0 1 64 23 7 :=
  oqMain1_iff (s := ⟨1, 64, 16, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 565) (by decide +kernel) rfl) rfl oqBody_586
    (Program.find?_of_indexOf? (j := 845) (by decide +kernel) rfl) rfl oqBody_866

set_option maxRecDepth 100000 in
theorem oqBody_755 : Data.core734.body = oqMainT ⟨1, 64, 20, 6⟩ 0 "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_892 : Data.core871.body = oqLoop1T ⟨1, 64, 20, 6⟩ 0 "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L6` is its meaning. -/
theorem oqSpec_755 :
    opening_queries_Spec "opening_queries__L0_L1_L64_L32_L26_L6" 0 1 64 26 6 :=
  oqMain1_iff (s := ⟨1, 64, 20, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 734) (by decide +kernel) rfl) rfl oqBody_755
    (Program.find?_of_indexOf? (j := 871) (by decide +kernel) rfl) rfl oqBody_892

set_option maxRecDepth 100000 in
theorem oqBody_643 : Data.core622.body = oqMainT ⟨1, 64, 15, 7⟩ 1 "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_876 : Data.core855.body = oqLoop1T ⟨1, 64, 15, 7⟩ 1 "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L7` is its meaning. -/
theorem oqSpec_643 :
    opening_queries_Spec "opening_queries__L1_L1_L64_L32_L22_L7" 1 1 64 22 7 :=
  oqMain1_iff (s := ⟨1, 64, 15, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 622) (by decide +kernel) rfl) rfl oqBody_643
    (Program.find?_of_indexOf? (j := 855) (by decide +kernel) rfl) rfl oqBody_876

set_option maxRecDepth 100000 in
theorem oqBody_665 : Data.core644.body = oqMainT ⟨1, 64, 17, 7⟩ 1 "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_878 : Data.core857.body = oqLoop1T ⟨1, 64, 17, 7⟩ 1 "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L7` is its meaning. -/
theorem oqSpec_665 :
    opening_queries_Spec "opening_queries__L1_L1_L64_L32_L24_L7" 1 1 64 24 7 :=
  oqMain1_iff (s := ⟨1, 64, 17, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 644) (by decide +kernel) rfl) rfl oqBody_665
    (Program.find?_of_indexOf? (j := 857) (by decide +kernel) rfl) rfl oqBody_878

set_option maxRecDepth 100000 in
theorem oqBody_556 : Data.core535.body = oqMainT ⟨0, 16, 12, 4⟩ 0 "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_862 : Data.core841.body = oqLoop0T ⟨0, 16, 12, 4⟩ "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L4` is its meaning. -/
theorem oqSpec_556 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L16_L4" 0 0 16 16 4 :=
  oqMain0_iff (s := ⟨0, 16, 12, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 535) (by decide +kernel) rfl) rfl oqBody_556
    (Program.find?_of_indexOf? (j := 841) (by decide +kernel) rfl) rfl oqBody_862

set_option maxRecDepth 100000 in
theorem oqBody_455 : Data.core434.body = oqMainT ⟨0, 16, 12, 5⟩ 0 "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_841 : Data.core820.body = oqLoop0T ⟨0, 16, 12, 5⟩ "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5` is its meaning. -/
theorem oqSpec_455 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L17_L5" 0 0 16 17 5 :=
  oqMain0_iff (s := ⟨0, 16, 12, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 434) (by decide +kernel) rfl) rfl oqBody_455
    (Program.find?_of_indexOf? (j := 820) (by decide +kernel) rfl) rfl oqBody_841

set_option maxRecDepth 100000 in
theorem oqBody_452 : Data.core431.body = oqMainT ⟨0, 16, 12, 6⟩ 0 "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_840 : Data.core819.body = oqLoop0T ⟨0, 16, 12, 6⟩ "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6` is its meaning. -/
theorem oqSpec_452 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L18_L6" 0 0 16 18 6 :=
  oqMain0_iff (s := ⟨0, 16, 12, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 431) (by decide +kernel) rfl) rfl oqBody_452
    (Program.find?_of_indexOf? (j := 819) (by decide +kernel) rfl) rfl oqBody_840

set_option maxRecDepth 100000 in
theorem oqBody_605 : Data.core584.body = oqMainT ⟨0, 16, 16, 4⟩ 0 "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_872 : Data.core851.body = oqLoop0T ⟨0, 16, 16, 4⟩ "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L4` is its meaning. -/
theorem oqSpec_605 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L20_L4" 0 0 16 20 4 :=
  oqMain0_iff (s := ⟨0, 16, 16, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 584) (by decide +kernel) rfl) rfl oqBody_605
    (Program.find?_of_indexOf? (j := 851) (by decide +kernel) rfl) rfl oqBody_872

set_option maxRecDepth 100000 in
theorem oqBody_519 : Data.core498.body = oqMainT ⟨0, 16, 16, 5⟩ 0 "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_857 : Data.core836.body = oqLoop0T ⟨0, 16, 16, 5⟩ "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L5` is its meaning. -/
theorem oqSpec_519 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L21_L5" 0 0 16 21 5 :=
  oqMain0_iff (s := ⟨0, 16, 16, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 498) (by decide +kernel) rfl) rfl oqBody_519
    (Program.find?_of_indexOf? (j := 836) (by decide +kernel) rfl) rfl oqBody_857

set_option maxRecDepth 100000 in
theorem oqBody_517 : Data.core496.body = oqMainT ⟨0, 16, 16, 6⟩ 0 "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_856 : Data.core835.body = oqLoop0T ⟨0, 16, 16, 6⟩ "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L6` is its meaning. -/
theorem oqSpec_517 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L22_L6" 0 0 16 22 6 :=
  oqMain0_iff (s := ⟨0, 16, 16, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 496) (by decide +kernel) rfl) rfl oqBody_517
    (Program.find?_of_indexOf? (j := 835) (by decide +kernel) rfl) rfl oqBody_856

set_option maxRecDepth 100000 in
theorem oqBody_678 : Data.core657.body = oqMainT ⟨0, 16, 18, 6⟩ 0 "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_881 : Data.core860.body = oqLoop0T ⟨0, 16, 18, 6⟩ "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6` is its meaning. -/
theorem oqSpec_678 :
    opening_queries_Spec "opening_queries__L0_L0_L16_L24_L24_L6" 0 0 16 24 6 :=
  oqMain0_iff (s := ⟨0, 16, 18, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 657) (by decide +kernel) rfl) rfl oqBody_678
    (Program.find?_of_indexOf? (j := 860) (by decide +kernel) rfl) rfl oqBody_881

end
end LeanVM.Guest.B1
