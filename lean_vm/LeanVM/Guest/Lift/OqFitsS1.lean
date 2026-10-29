/-
  LeanVM.Guest.Lift.OqFitsS1

  A quarter of `opening_queries`' specializations: their frames fit their runs (`OqFits`), after
  `QueriesPlacedS1`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody1
public import LeanVM.Guest.Lift.OqFits

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L7`'s frames fit its runs. -/
theorem oqF_533 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L1_L64_L32_L18_L7" "__loop382" ⟨1, 64, 11, 7⟩ 0 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 11, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 0 ≤ 1)
    (Program.find?_of_indexOf? (j := 512) (by decide +kernel) rfl) rfl oqBody_533
    (Program.find?_of_indexOf? (j := 838) (by decide +kernel) rfl) rfl oqBody_859

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L6`'s frames fit its runs. -/
theorem oqF_692 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L1_L64_L32_L20_L6" "__loop405" ⟨1, 64, 14, 6⟩ 0 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 14, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 0 ≤ 1)
    (Program.find?_of_indexOf? (j := 671) (by decide +kernel) rfl) rfl oqBody_692
    (Program.find?_of_indexOf? (j := 863) (by decide +kernel) rfl) rfl oqBody_884

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L7`'s frames fit its runs. -/
theorem oqF_563 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L1_L64_L32_L21_L7" "__loop386" ⟨1, 64, 14, 7⟩ 0 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 14, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 0 ≤ 1)
    (Program.find?_of_indexOf? (j := 542) (by decide +kernel) rfl) rfl oqBody_563
    (Program.find?_of_indexOf? (j := 842) (by decide +kernel) rfl) rfl oqBody_863

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L6`'s frames fit its runs. -/
theorem oqF_721 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L1_L64_L32_L23_L6" "__loop408" ⟨1, 64, 17, 6⟩ 0 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 17, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 0 ≤ 1)
    (Program.find?_of_indexOf? (j := 700) (by decide +kernel) rfl) rfl oqBody_721
    (Program.find?_of_indexOf? (j := 866) (by decide +kernel) rfl) rfl oqBody_887

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L6`'s frames fit its runs. -/
theorem oqF_743 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L1_L64_L32_L25_L6" "__loop410" ⟨1, 64, 19, 6⟩ 0 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 19, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 0 ≤ 1)
    (Program.find?_of_indexOf? (j := 722) (by decide +kernel) rfl) rfl oqBody_743
    (Program.find?_of_indexOf? (j := 868) (by decide +kernel) rfl) rfl oqBody_889

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L7`'s frames fit its runs. -/
theorem oqF_632 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L1_L1_L64_L32_L21_L7" "__loop397" ⟨1, 64, 14, 7⟩ 1 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 14, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 1 ≤ 1)
    (Program.find?_of_indexOf? (j := 611) (by decide +kernel) rfl) rfl oqBody_632
    (Program.find?_of_indexOf? (j := 854) (by decide +kernel) rfl) rfl oqBody_875

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L8`'s frames fit its runs. -/
theorem oqF_515 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L1_L1_L64_L32_L23_L8" "__loop378" ⟨1, 64, 15, 8⟩ 1 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 15, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 1 ≤ 1)
    (Program.find?_of_indexOf? (j := 494) (by decide +kernel) rfl) rfl oqBody_515
    (Program.find?_of_indexOf? (j := 834) (by decide +kernel) rfl) rfl oqBody_855

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L5`'s frames fit its runs. -/
theorem oqF_422 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L15_L5" "__loop361" ⟨0, 16, 10, 5⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 10, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 401) (by decide +kernel) rfl) rfl oqBody_422
    (Program.find?_of_indexOf? (j := 810) (by decide +kernel) rfl) rfl oqBody_831

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L4`'s frames fit its runs. -/
theorem oqF_568 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L17_L4" "__loop387" ⟨0, 16, 13, 4⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 13, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 547) (by decide +kernel) rfl) rfl oqBody_568
    (Program.find?_of_indexOf? (j := 843) (by decide +kernel) rfl) rfl oqBody_864

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L5`'s frames fit its runs. -/
theorem oqF_474 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L18_L5" "__loop371" ⟨0, 16, 13, 5⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 13, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 453) (by decide +kernel) rfl) rfl oqBody_474
    (Program.find?_of_indexOf? (j := 824) (by decide +kernel) rfl) rfl oqBody_845

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L6`'s frames fit its runs. -/
theorem oqF_471 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L19_L6" "__loop370" ⟨0, 16, 13, 6⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 13, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 450) (by decide +kernel) rfl) rfl oqBody_471
    (Program.find?_of_indexOf? (j := 823) (by decide +kernel) rfl) rfl oqBody_844

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L4`'s frames fit its runs. -/
theorem oqF_683 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L21_L4" "__loop404" ⟨0, 16, 17, 4⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 17, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 662) (by decide +kernel) rfl) rfl oqBody_683
    (Program.find?_of_indexOf? (j := 862) (by decide +kernel) rfl) rfl oqBody_883

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L5`'s frames fit its runs. -/
theorem oqF_602 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L22_L5" "__loop393" ⟨0, 16, 17, 5⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 17, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 581) (by decide +kernel) rfl) rfl oqBody_602
    (Program.find?_of_indexOf? (j := 850) (by decide +kernel) rfl) rfl oqBody_871

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L5`'s frames fit its runs. -/
theorem oqF_745 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L24_L5" "__loop411" ⟨0, 16, 19, 5⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 19, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 724) (by decide +kernel) rfl) rfl oqBody_745
    (Program.find?_of_indexOf? (j := 869) (by decide +kernel) rfl) rfl oqBody_890

end
end LeanVM.Guest.B1
