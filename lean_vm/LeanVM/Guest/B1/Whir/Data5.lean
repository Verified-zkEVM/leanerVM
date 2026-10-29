/-
  LeanVM.Guest.B1.Whir.Data5

  `open_stacked__L5` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 5

`osData_5 : OsData 5`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_5_0 : stmtsEqb ((Data.core297.body.drop 0).take 1100)
    (((osBody (osCfg 5)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_5_1 : stmtsEqb ((Data.core297.body.drop 1100).take 1100)
    (((osBody (osCfg 5)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_5_2 : stmtsEqb ((Data.core297.body.drop 2200).take 1100)
    (((osBody (osCfg 5)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_5 : OsData 5 := by
  have hl : (osCfg 5).levels.length = 5 := by decide +kernel
  have hb : Data.core297.body.drop 0 = (osBody (osCfg 5)).drop 0 :=
    run_step 1100 0 os_run_5_0 <|
    run_step 1100 1100 os_run_5_1 <|
    run_step 1100 2200 os_run_5_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core297, Program.find?_of_indexOf? (j := 297) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core479, Program.find?_of_indexOf? (j := 479) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core487, Program.find?_of_indexOf? (j := 487) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core481, Program.find?_of_indexOf? (j := 481) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core488, Program.find?_of_indexOf? (j := 488) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core483, Program.find?_of_indexOf? (j := 483) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core489, Program.find?_of_indexOf? (j := 489) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core485, Program.find?_of_indexOf? (j := 485) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core490, Program.find?_of_indexOf? (j := 490) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core486, Program.find?_of_indexOf? (j := 486) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core491, Program.find?_of_indexOf? (j := 491) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
