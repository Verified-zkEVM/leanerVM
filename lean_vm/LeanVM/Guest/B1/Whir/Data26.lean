/-
  LeanVM.Guest.B1.Whir.Data26

  `open_stacked__L26` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 26

`osData_26 : OsData 26`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_26_0 : stmtsEqb ((Data.core321.body.drop 0).take 1100)
    (((osBody (osCfg 26)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_26_1 : stmtsEqb ((Data.core321.body.drop 1100).take 1100)
    (((osBody (osCfg 26)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_26_2 : stmtsEqb ((Data.core321.body.drop 2200).take 1100)
    (((osBody (osCfg 26)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_26 : OsData 26 := by
  have hl : (osCfg 26).levels.length = 5 := by decide +kernel
  have hb : Data.core321.body.drop 0 = (osBody (osCfg 26)).drop 0 :=
    run_step 1100 0 os_run_26_0 <|
    run_step 1100 1100 os_run_26_1 <|
    run_step 1100 2200 os_run_26_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core321, Program.find?_of_indexOf? (j := 321) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core742, Program.find?_of_indexOf? (j := 742) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core749, Program.find?_of_indexOf? (j := 749) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core744, Program.find?_of_indexOf? (j := 744) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core750, Program.find?_of_indexOf? (j := 750) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core746, Program.find?_of_indexOf? (j := 746) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core751, Program.find?_of_indexOf? (j := 751) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core747, Program.find?_of_indexOf? (j := 747) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core752, Program.find?_of_indexOf? (j := 752) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core748, Program.find?_of_indexOf? (j := 748) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core753, Program.find?_of_indexOf? (j := 753) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
