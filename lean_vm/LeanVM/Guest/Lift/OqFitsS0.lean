/-
  LeanVM.Guest.Lift.OqFitsS0

  A quarter of `opening_queries`' specializations: their frames fit their runs (`OqFits`), after
  `QueriesPlacedS0`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody0
public import LeanVM.Guest.Lift.OqFits

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L17_L8`'s frames fit its runs. -/
theorem oqF_413 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L1_L64_L32_L17_L8" "__loop359" ⟨1, 64, 9, 8⟩ 0 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 9, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 0 ≤ 1)
    (Program.find?_of_indexOf? (j := 392) (by decide +kernel) rfl) rfl oqBody_413
    (Program.find?_of_indexOf? (j := 806) (by decide +kernel) rfl) rfl oqBody_827

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L8`'s frames fit its runs. -/
theorem oqF_449 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L1_L64_L32_L19_L8" "__loop366" ⟨1, 64, 11, 8⟩ 0 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 11, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 0 ≤ 1)
    (Program.find?_of_indexOf? (j := 428) (by decide +kernel) rfl) rfl oqBody_449
    (Program.find?_of_indexOf? (j := 818) (by decide +kernel) rfl) rfl oqBody_839

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L6`'s frames fit its runs. -/
theorem oqF_701 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L1_L64_L32_L21_L6" "__loop406" ⟨1, 64, 15, 6⟩ 0 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 15, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 0 ≤ 1)
    (Program.find?_of_indexOf? (j := 680) (by decide +kernel) rfl) rfl oqBody_701
    (Program.find?_of_indexOf? (j := 864) (by decide +kernel) rfl) rfl oqBody_885

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L7`'s frames fit its runs. -/
theorem oqF_575 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L1_L64_L32_L22_L7" "__loop388" ⟨1, 64, 15, 7⟩ 0 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 15, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 0 ≤ 1)
    (Program.find?_of_indexOf? (j := 554) (by decide +kernel) rfl) rfl oqBody_575
    (Program.find?_of_indexOf? (j := 844) (by decide +kernel) rfl) rfl oqBody_865

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L7`'s frames fit its runs. -/
theorem oqF_598 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L1_L64_L32_L24_L7" "__loop391" ⟨1, 64, 17, 7⟩ 0 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 17, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 0 ≤ 1)
    (Program.find?_of_indexOf? (j := 577) (by decide +kernel) rfl) rfl oqBody_598
    (Program.find?_of_indexOf? (j := 848) (by decide +kernel) rfl) rfl oqBody_869

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L7`'s frames fit its runs. -/
theorem oqF_623 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L1_L1_L64_L32_L20_L7" "__loop396" ⟨1, 64, 13, 7⟩ 1 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 13, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 1 ≤ 1)
    (Program.find?_of_indexOf? (j := 602) (by decide +kernel) rfl) rfl oqBody_623
    (Program.find?_of_indexOf? (j := 853) (by decide +kernel) rfl) rfl oqBody_874

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L7`'s frames fit its runs. -/
theorem oqF_654 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L1_L1_L64_L32_L23_L7" "__loop399" ⟨1, 64, 16, 7⟩ 1 :=
  oqFits1_of hfit hap (s := ⟨1, 64, 16, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide : 1 ≤ 1)
    (Program.find?_of_indexOf? (j := 633) (by decide +kernel) rfl) rfl oqBody_654
    (Program.find?_of_indexOf? (j := 856) (by decide +kernel) rfl) rfl oqBody_877

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L5`'s frames fit its runs. -/
theorem oqF_425 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L14_L5" "__loop362" ⟨0, 16, 9, 5⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 9, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 404) (by decide +kernel) rfl) rfl oqBody_425
    (Program.find?_of_indexOf? (j := 812) (by decide +kernel) rfl) rfl oqBody_833

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L6`'s frames fit its runs. -/
theorem oqF_418 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L16_L6" "__loop360" ⟨0, 16, 10, 6⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 10, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 397) (by decide +kernel) rfl) rfl oqBody_418
    (Program.find?_of_indexOf? (j := 808) (by decide +kernel) rfl) rfl oqBody_829

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L4`'s frames fit its runs. -/
theorem oqF_524 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L18_L4" "__loop381" ⟨0, 16, 14, 4⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 14, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 503) (by decide +kernel) rfl) rfl oqBody_524
    (Program.find?_of_indexOf? (j := 837) (by decide +kernel) rfl) rfl oqBody_858

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L5`'s frames fit its runs. -/
theorem oqF_491 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L19_L5" "__loop374" ⟨0, 16, 14, 5⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 14, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 470) (by decide +kernel) rfl) rfl oqBody_491
    (Program.find?_of_indexOf? (j := 828) (by decide +kernel) rfl) rfl oqBody_849

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L6`'s frames fit its runs. -/
theorem oqF_489 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L20_L6" "__loop373" ⟨0, 16, 14, 6⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 14, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 468) (by decide +kernel) rfl) rfl oqBody_489
    (Program.find?_of_indexOf? (j := 827) (by decide +kernel) rfl) rfl oqBody_848

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4`'s frames fit its runs. -/
theorem oqF_761 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L22_L4" "__loop414" ⟨0, 16, 18, 4⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 18, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 740) (by decide +kernel) rfl) rfl oqBody_761
    (Program.find?_of_indexOf? (j := 873) (by decide +kernel) rfl) rfl oqBody_894

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L6`'s frames fit its runs. -/
theorem oqF_600 (fs : String → ℕ) (cert : String → V → ℕ)
    (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) :
    OqFits fs cert "opening_queries__L0_L0_L16_L24_L23_L6" "__loop392" ⟨0, 16, 17, 6⟩ 0 :=
  oqFits0_of hfit hap (s := ⟨0, 16, 17, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 579) (by decide +kernel) rfl) rfl oqBody_600
    (Program.find?_of_indexOf? (j := 849) (by decide +kernel) rfl) rfl oqBody_870

end
end LeanVM.Guest.B1
