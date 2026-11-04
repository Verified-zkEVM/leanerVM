/-
  LeanVM.Guest.WalkOqOk3

  The certificates of a quarter of `opening_queries`' specializations and loops (those whose
  templates `B1/Opening/QueriesBody3.lean` checks) hand on the walk's obligations in the forms
  `WalkKnownDefs` checks, by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkKnownDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

theorem walkOk_459 : mainOkS 459 0 ⟨0, 16, 11, 6⟩ = true := by decide +kernel

theorem walkOk_462 : mainOkS 462 0 ⟨0, 16, 11, 5⟩ = true := by decide +kernel

theorem walkOk_491 : mainOkS 491 0 ⟨1, 64, 12, 8⟩ = true := by decide +kernel

theorem walkOk_524 : mainOkS 524 1 ⟨1, 64, 14, 8⟩ = true := by decide +kernel

theorem walkOk_526 : mainOkS 526 0 ⟨0, 16, 15, 6⟩ = true := by decide +kernel

theorem walkOk_528 : mainOkS 528 0 ⟨0, 16, 15, 5⟩ = true := by decide +kernel

theorem walkOk_565 : mainOkS 565 0 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

theorem walkOk_614 : mainOkS 614 0 ⟨0, 16, 15, 4⟩ = true := by decide +kernel

theorem walkOk_637 : mainOkS 637 1 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

theorem walkOk_699 : mainOkS 699 1 ⟨1, 64, 18, 7⟩ = true := by decide +kernel

theorem walkOk_703 : mainOkS 703 0 ⟨0, 16, 18, 5⟩ = true := by decide +kernel

theorem walkOk_733 : mainOkS 733 0 ⟨1, 64, 16, 6⟩ = true := by decide +kernel

theorem walkOk_755 : mainOkS 755 0 ⟨1, 64, 18, 6⟩ = true := by decide +kernel

theorem walkOk_780 : mainOkS 780 0 ⟨0, 16, 20, 5⟩ = true := by decide +kernel

theorem walkOk_858 : loop0Ok 858 0 ⟨0, 16, 11, 6⟩ = true := by decide +kernel

theorem walkOk_860 : loop0Ok 860 0 ⟨0, 16, 11, 5⟩ = true := by decide +kernel

theorem walkOk_868 : loop1Ok 868 0 ⟨1, 64, 12, 8⟩ = true := by decide +kernel

theorem walkOk_880 : loop1Ok 880 1 ⟨1, 64, 14, 8⟩ = true := by decide +kernel

theorem walkOk_882 : loop0Ok 882 0 ⟨0, 16, 15, 6⟩ = true := by decide +kernel

theorem walkOk_884 : loop0Ok 884 0 ⟨0, 16, 15, 5⟩ = true := by decide +kernel

theorem walkOk_896 : loop1Ok 896 0 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

theorem walkOk_910 : loop0Ok 910 0 ⟨0, 16, 15, 4⟩ = true := by decide +kernel

theorem walkOk_919 : loop1Ok 919 1 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

theorem walkOk_926 : loop1Ok 926 1 ⟨1, 64, 18, 7⟩ = true := by decide +kernel

theorem walkOk_930 : loop0Ok 930 0 ⟨0, 16, 18, 5⟩ = true := by decide +kernel

theorem walkOk_935 : loop1Ok 935 0 ⟨1, 64, 16, 6⟩ = true := by decide +kernel

theorem walkOk_937 : loop1Ok 937 0 ⟨1, 64, 18, 6⟩ = true := by decide +kernel

theorem walkOk_945 : loop0Ok 945 0 ⟨0, 16, 20, 5⟩ = true := by decide +kernel

end
end LeanVM.Guest.End
