/-
  LeanVM.Guest.WalkOqOk2

  The certificates of a quarter of `opening_queries`' specializations and loops (those whose
  templates `B1/Opening/QueriesBody2.lean` checks) hand on the walk's obligations in the forms
  `WalkKnownDefs` checks, by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkKnownDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

theorem walkOk_456 : mainOkS 456 0 ⟨1, 64, 10, 8⟩ = true := by decide +kernel

theorem walkOk_475 : mainOkS 475 0 ⟨0, 16, 12, 6⟩ = true := by decide +kernel

theorem walkOk_478 : mainOkS 478 0 ⟨0, 16, 12, 5⟩ = true := by decide +kernel

theorem walkOk_510 : mainOkS 510 0 ⟨1, 64, 13, 8⟩ = true := by decide +kernel

theorem walkOk_540 : mainOkS 540 0 ⟨0, 16, 16, 6⟩ = true := by decide +kernel

theorem walkOk_542 : mainOkS 542 0 ⟨0, 16, 16, 5⟩ = true := by decide +kernel

theorem walkOk_574 : mainOkS 574 0 ⟨1, 64, 13, 7⟩ = true := by decide +kernel

theorem walkOk_579 : mainOkS 579 0 ⟨0, 16, 12, 4⟩ = true := by decide +kernel

theorem walkOk_609 : mainOkS 609 0 ⟨1, 64, 16, 7⟩ = true := by decide +kernel

theorem walkOk_628 : mainOkS 628 0 ⟨0, 16, 16, 4⟩ = true := by decide +kernel

theorem walkOk_666 : mainOkS 666 1 ⟨1, 64, 15, 7⟩ = true := by decide +kernel

theorem walkOk_688 : mainOkS 688 1 ⟨1, 64, 17, 7⟩ = true := by decide +kernel

theorem walkOk_701 : mainOkS 701 0 ⟨0, 16, 18, 6⟩ = true := by decide +kernel

theorem walkOk_778 : mainOkS 778 0 ⟨1, 64, 20, 6⟩ = true := by decide +kernel

theorem walkOk_856 : loop1Ok 856 0 ⟨1, 64, 10, 8⟩ = true := by decide +kernel

theorem walkOk_864 : loop0Ok 864 0 ⟨0, 16, 12, 6⟩ = true := by decide +kernel

theorem walkOk_866 : loop0Ok 866 0 ⟨0, 16, 12, 5⟩ = true := by decide +kernel

theorem walkOk_874 : loop1Ok 874 0 ⟨1, 64, 13, 8⟩ = true := by decide +kernel

theorem walkOk_888 : loop0Ok 888 0 ⟨0, 16, 16, 6⟩ = true := by decide +kernel

theorem walkOk_890 : loop0Ok 890 0 ⟨0, 16, 16, 5⟩ = true := by decide +kernel

theorem walkOk_898 : loop1Ok 898 0 ⟨1, 64, 13, 7⟩ = true := by decide +kernel

theorem walkOk_900 : loop0Ok 900 0 ⟨0, 16, 12, 4⟩ = true := by decide +kernel

theorem walkOk_908 : loop1Ok 908 0 ⟨1, 64, 16, 7⟩ = true := by decide +kernel

theorem walkOk_918 : loop0Ok 918 0 ⟨0, 16, 16, 4⟩ = true := by decide +kernel

theorem walkOk_922 : loop1Ok 922 1 ⟨1, 64, 15, 7⟩ = true := by decide +kernel

theorem walkOk_924 : loop1Ok 924 1 ⟨1, 64, 17, 7⟩ = true := by decide +kernel

theorem walkOk_928 : loop0Ok 928 0 ⟨0, 16, 18, 6⟩ = true := by decide +kernel

theorem walkOk_943 : loop1Ok 943 0 ⟨1, 64, 20, 6⟩ = true := by decide +kernel

end
end LeanVM.Guest.End
