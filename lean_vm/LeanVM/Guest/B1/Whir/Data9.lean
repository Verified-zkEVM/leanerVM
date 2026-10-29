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
theorem os_run_9_0 : stmtsEqb ((Data.core301.body.drop 0).take 1100)
    (((osBody (osCfg 9)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_9_1 : stmtsEqb ((Data.core301.body.drop 1100).take 1100)
    (((osBody (osCfg 9)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_9_2 : stmtsEqb ((Data.core301.body.drop 2200).take 1100)
    (((osBody (osCfg 9)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_9 : OsData 9 := by
  have hl : (osCfg 9).levels.length = 5 := by decide +kernel
  have hb : Data.core301.body.drop 0 = (osBody (osCfg 9)).drop 0 :=
    run_step 1100 0 os_run_9_0 <|
    run_step 1100 1100 os_run_9_1 <|
    run_step 1100 2200 os_run_9_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core301, Program.find?_of_indexOf? (j := 301) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core529, Program.find?_of_indexOf? (j := 529) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core536, Program.find?_of_indexOf? (j := 536) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core531, Program.find?_of_indexOf? (j := 531) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core537, Program.find?_of_indexOf? (j := 537) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core532, Program.find?_of_indexOf? (j := 532) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core538, Program.find?_of_indexOf? (j := 538) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core533, Program.find?_of_indexOf? (j := 533) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core539, Program.find?_of_indexOf? (j := 539) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core534, Program.find?_of_indexOf? (j := 534) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core540, Program.find?_of_indexOf? (j := 540) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
