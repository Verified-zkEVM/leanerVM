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
theorem os_run_8_0 : stmtsEqb ((Data.core303.body.drop 0).take 1100)
    (((osBody (osCfg 8)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_8_1 : stmtsEqb ((Data.core303.body.drop 1100).take 1100)
    (((osBody (osCfg 8)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_8_0 : FnIs ((osCfg 8).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 8 0) ((osCfg 8).sqLoop 0)) ∧
    FnIs ((osCfg 8).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 8) 0 (osLv 8 0) ((osCfg 8).resLoop 0)) :=
  ⟨⟨Data.core532, Program.find?_of_indexOf? (j := 532) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core537, Program.find?_of_indexOf? (j := 537) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_8_1 : FnIs ((osCfg 8).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 8 1) ((osCfg 8).sqLoop 1)) ∧
    FnIs ((osCfg 8).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 8) 1 (osLv 8 1) ((osCfg 8).resLoop 1)) :=
  ⟨⟨Data.core534, Program.find?_of_indexOf? (j := 534) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core538, Program.find?_of_indexOf? (j := 538) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_8_2 : FnIs ((osCfg 8).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 8 2) ((osCfg 8).sqLoop 2)) ∧
    FnIs ((osCfg 8).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 8) 2 (osLv 8 2) ((osCfg 8).resLoop 2)) :=
  ⟨⟨Data.core535, Program.find?_of_indexOf? (j := 535) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core539, Program.find?_of_indexOf? (j := 539) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_8_3 : FnIs ((osCfg 8).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 8 3) ((osCfg 8).sqLoop 3)) ∧
    FnIs ((osCfg 8).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 8) 3 (osLv 8 3) ((osCfg 8).resLoop 3)) :=
  ⟨⟨Data.core536, Program.find?_of_indexOf? (j := 536) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core540, Program.find?_of_indexOf? (j := 540) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_8 : OsData 8 := by
  have hl : (osCfg 8).levels.length = 4 := by decide +kernel
  have hb : Data.core303.body.drop 0 = (osBody (osCfg 8)).drop 0 :=
    run_step 1100 0 os_run_8_0 <|
    run_step 1100 1100 os_run_8_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core303, Program.find?_of_indexOf? (j := 303) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_8_0
  · exact osLv_8_1
  · exact osLv_8_2
  · exact osLv_8_3

end
end LeanVM.Guest.B1.Whir
