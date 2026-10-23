/-
  LeanVM.Guest.B1.Whir.Data9

  `open_stacked__L9` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 9

`osData_9 : OsData 9`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_9_0 : stmtsEqb ((Data.core304.body.drop 0).take 1100)
    (((osBody (osCfg 9)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_9_1 : stmtsEqb ((Data.core304.body.drop 1100).take 1100)
    (((osBody (osCfg 9)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_9_2 : stmtsEqb ((Data.core304.body.drop 2200).take 1100)
    (((osBody (osCfg 9)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_9 : OsData 9 := by
  have hl : (osCfg 9).levels.length = 5 := by decide +kernel
  have hb : Data.core304.body.drop 0 = (osBody (osCfg 9)).drop 0 :=
    run_step 1100 0 os_run_9_0 <|
    run_step 1100 1100 os_run_9_1 <|
    run_step 1100 2200 os_run_9_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core304, Program.find?_of_indexOf? (j := 304) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core550, Program.find?_of_indexOf? (j := 550) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core557, Program.find?_of_indexOf? (j := 557) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core552, Program.find?_of_indexOf? (j := 552) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core558, Program.find?_of_indexOf? (j := 558) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core553, Program.find?_of_indexOf? (j := 553) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core559, Program.find?_of_indexOf? (j := 559) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core554, Program.find?_of_indexOf? (j := 554) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core560, Program.find?_of_indexOf? (j := 560) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core555, Program.find?_of_indexOf? (j := 555) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core561, Program.find?_of_indexOf? (j := 561) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
