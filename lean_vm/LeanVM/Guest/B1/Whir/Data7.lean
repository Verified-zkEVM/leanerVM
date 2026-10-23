/-
  LeanVM.Guest.B1.Whir.Data7

  `open_stacked__L7` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 7

`osData_7 : OsData 7`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_7_0 : stmtsEqb ((Data.core302.body.drop 0).take 1100)
    (((osBody (osCfg 7)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_7_1 : stmtsEqb ((Data.core302.body.drop 1100).take 1100)
    (((osBody (osCfg 7)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_7 : OsData 7 := by
  have hl : (osCfg 7).levels.length = 4 := by decide +kernel
  have hb : Data.core302.body.drop 0 = (osBody (osCfg 7)).drop 0 :=
    run_step 1100 0 os_run_7_0 <|
    run_step 1100 1100 os_run_7_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core302, Program.find?_of_indexOf? (j := 302) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core531, Program.find?_of_indexOf? (j := 531) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core537, Program.find?_of_indexOf? (j := 537) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core534, Program.find?_of_indexOf? (j := 534) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core538, Program.find?_of_indexOf? (j := 538) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core535, Program.find?_of_indexOf? (j := 535) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core539, Program.find?_of_indexOf? (j := 539) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core536, Program.find?_of_indexOf? (j := 536) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core540, Program.find?_of_indexOf? (j := 540) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
