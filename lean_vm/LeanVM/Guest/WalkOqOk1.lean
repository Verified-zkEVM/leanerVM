/-
  LeanVM.Guest.WalkOqOk1

  The certificates of a quarter of `opening_queries`' specializations and loops (those whose
  templates `B1/Opening/QueriesBody1.lean` checks) hand on the walk's obligations in the forms
  `WalkKnownDefs` checks, by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkKnownDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

theorem walkOk_445 : mainOkS 445 0 ⟨0, 16, 10, 5⟩ = true := by decide +kernel

theorem walkOk_494 : mainOkS 494 0 ⟨0, 16, 13, 6⟩ = true := by decide +kernel

theorem walkOk_497 : mainOkS 497 0 ⟨0, 16, 13, 5⟩ = true := by decide +kernel

theorem walkOk_538 : mainOkS 538 1 ⟨1, 64, 15, 8⟩ = true := by decide +kernel

theorem walkOk_556 : mainOkS 556 0 ⟨1, 64, 11, 7⟩ = true := by decide +kernel

theorem walkOk_586 : mainOkS 586 0 ⟨1, 64, 14, 7⟩ = true := by decide +kernel

theorem walkOk_591 : mainOkS 591 0 ⟨0, 16, 13, 4⟩ = true := by decide +kernel

theorem walkOk_625 : mainOkS 625 0 ⟨0, 16, 17, 5⟩ = true := by decide +kernel

theorem walkOk_655 : mainOkS 655 1 ⟨1, 64, 14, 7⟩ = true := by decide +kernel

theorem walkOk_706 : mainOkS 706 0 ⟨0, 16, 17, 4⟩ = true := by decide +kernel

theorem walkOk_715 : mainOkS 715 0 ⟨1, 64, 14, 6⟩ = true := by decide +kernel

theorem walkOk_744 : mainOkS 744 0 ⟨1, 64, 17, 6⟩ = true := by decide +kernel

theorem walkOk_766 : mainOkS 766 0 ⟨1, 64, 19, 6⟩ = true := by decide +kernel

theorem walkOk_768 : mainOkS 768 0 ⟨0, 16, 19, 5⟩ = true := by decide +kernel

theorem walkOk_852 : loop0Ok 852 0 ⟨0, 16, 10, 5⟩ = true := by decide +kernel

theorem walkOk_870 : loop0Ok 870 0 ⟨0, 16, 13, 6⟩ = true := by decide +kernel

theorem walkOk_872 : loop0Ok 872 0 ⟨0, 16, 13, 5⟩ = true := by decide +kernel

theorem walkOk_886 : loop1Ok 886 1 ⟨1, 64, 15, 8⟩ = true := by decide +kernel

theorem walkOk_894 : loop1Ok 894 0 ⟨1, 64, 11, 7⟩ = true := by decide +kernel

theorem walkOk_902 : loop1Ok 902 0 ⟨1, 64, 14, 7⟩ = true := by decide +kernel

theorem walkOk_904 : loop0Ok 904 0 ⟨0, 16, 13, 4⟩ = true := by decide +kernel

theorem walkOk_916 : loop0Ok 916 0 ⟨0, 16, 17, 5⟩ = true := by decide +kernel

theorem walkOk_921 : loop1Ok 921 1 ⟨1, 64, 14, 7⟩ = true := by decide +kernel

theorem walkOk_932 : loop0Ok 932 0 ⟨0, 16, 17, 4⟩ = true := by decide +kernel

theorem walkOk_933 : loop1Ok 933 0 ⟨1, 64, 14, 6⟩ = true := by decide +kernel

theorem walkOk_936 : loop1Ok 936 0 ⟨1, 64, 17, 6⟩ = true := by decide +kernel

theorem walkOk_939 : loop1Ok 939 0 ⟨1, 64, 19, 6⟩ = true := by decide +kernel

theorem walkOk_941 : loop0Ok 941 0 ⟨0, 16, 19, 5⟩ = true := by decide +kernel

end
end LeanVM.Guest.End
