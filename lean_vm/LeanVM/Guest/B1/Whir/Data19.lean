/-
  LeanVM.Guest.B1.Whir.Data19

  `open_stacked__L19` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 19

`osData_19 : OsData 19`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_19_0 : stmtsEqb ((Data.core314.body.drop 0).take 1100)
    (((osBody (osCfg 19)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_19_1 : stmtsEqb ((Data.core314.body.drop 1100).take 1100)
    (((osBody (osCfg 19)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_19_2 : stmtsEqb ((Data.core314.body.drop 2200).take 1100)
    (((osBody (osCfg 19)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_19 : OsData 19 := by
  have hl : (osCfg 19).levels.length = 5 := by decide +kernel
  have hb : Data.core314.body.drop 0 = (osBody (osCfg 19)).drop 0 :=
    run_step 1100 0 os_run_19_0 <|
    run_step 1100 1100 os_run_19_1 <|
    run_step 1100 2200 os_run_19_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core314, Program.find?_of_indexOf? (j := 314) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core664, Program.find?_of_indexOf? (j := 664) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core670, Program.find?_of_indexOf? (j := 670) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core666, Program.find?_of_indexOf? (j := 666) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core671, Program.find?_of_indexOf? (j := 671) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core667, Program.find?_of_indexOf? (j := 667) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core672, Program.find?_of_indexOf? (j := 672) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core668, Program.find?_of_indexOf? (j := 668) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core673, Program.find?_of_indexOf? (j := 673) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core669, Program.find?_of_indexOf? (j := 669) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core674, Program.find?_of_indexOf? (j := 674) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
