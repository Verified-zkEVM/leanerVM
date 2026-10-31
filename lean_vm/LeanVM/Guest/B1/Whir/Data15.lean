/-
  LeanVM.Guest.B1.Whir.Data15

  `open_stacked__L15` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 15

`osData_15 : OsData 15`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_15_0 : stmtsEqb ((Data.core307.body.drop 0).take 1100)
    (((osBody (osCfg 15)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_15_1 : stmtsEqb ((Data.core307.body.drop 1100).take 1100)
    (((osBody (osCfg 15)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osData_15 : OsData 15 := by
  have hl : (osCfg 15).levels.length = 4 := by decide +kernel
  have hb : Data.core307.body.drop 0 = (osBody (osCfg 15)).drop 0 :=
    run_step 1100 0 os_run_15_0 <|
    run_step 1100 1100 os_run_15_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core307, Program.find?_of_indexOf? (j := 307) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core601, Program.find?_of_indexOf? (j := 601) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core606, Program.find?_of_indexOf? (j := 606) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core603, Program.find?_of_indexOf? (j := 603) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core607, Program.find?_of_indexOf? (j := 607) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core604, Program.find?_of_indexOf? (j := 604) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core608, Program.find?_of_indexOf? (j := 608) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core605, Program.find?_of_indexOf? (j := 605) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core609, Program.find?_of_indexOf? (j := 609) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
