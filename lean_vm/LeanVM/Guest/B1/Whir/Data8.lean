/-
  LeanVM.Guest.B1.Whir.Data8

  `open_stacked__L8` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 8

`osData_8 : OsData 8`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_8_0 : stmtsEqb ((Data.core302.body.drop 0).take 1100)
    (((osBody (osCfg 8)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_8_1 : stmtsEqb ((Data.core302.body.drop 1100).take 1100)
    (((osBody (osCfg 8)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osData_8 : OsData 8 := by
  have hl : (osCfg 8).levels.length = 4 := by decide +kernel
  have hb : Data.core302.body.drop 0 = (osBody (osCfg 8)).drop 0 :=
    run_step 1100 0 os_run_8_0 <|
    run_step 1100 1100 os_run_8_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core302, Program.find?_of_indexOf? (j := 300) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core531, Program.find?_of_indexOf? (j := 520) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core536, Program.find?_of_indexOf? (j := 525) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core533, Program.find?_of_indexOf? (j := 522) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core537, Program.find?_of_indexOf? (j := 526) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core534, Program.find?_of_indexOf? (j := 523) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core538, Program.find?_of_indexOf? (j := 527) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core535, Program.find?_of_indexOf? (j := 524) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core539, Program.find?_of_indexOf? (j := 528) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
