/-
  LeanVM.Guest.B1.Whir.Data4

  `open_stacked__L4` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 4

`osData_4 : OsData 4`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_4_0 : stmtsEqb ((Data.core299.body.drop 0).take 1100)
    (((osBody (osCfg 4)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_4_1 : stmtsEqb ((Data.core299.body.drop 1100).take 1100)
    (((osBody (osCfg 4)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_4_2 : stmtsEqb ((Data.core299.body.drop 2200).take 1100)
    (((osBody (osCfg 4)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_4_0 : FnIs ((osCfg 4).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 4 0) ((osCfg 4).sqLoop 0)) ∧
    FnIs ((osCfg 4).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 4) 0 (osLv 4 0) ((osCfg 4).resLoop 0)) :=
  ⟨⟨Data.core477, Program.find?_of_indexOf? (j := 477) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core485, Program.find?_of_indexOf? (j := 485) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_4_1 : FnIs ((osCfg 4).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 4 1) ((osCfg 4).sqLoop 1)) ∧
    FnIs ((osCfg 4).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 4) 1 (osLv 4 1) ((osCfg 4).resLoop 1)) :=
  ⟨⟨Data.core479, Program.find?_of_indexOf? (j := 479) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core486, Program.find?_of_indexOf? (j := 486) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_4_2 : FnIs ((osCfg 4).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 4 2) ((osCfg 4).sqLoop 2)) ∧
    FnIs ((osCfg 4).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 4) 2 (osLv 4 2) ((osCfg 4).resLoop 2)) :=
  ⟨⟨Data.core481, Program.find?_of_indexOf? (j := 481) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core487, Program.find?_of_indexOf? (j := 487) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_4_3 : FnIs ((osCfg 4).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 4 3) ((osCfg 4).sqLoop 3)) ∧
    FnIs ((osCfg 4).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 4) 3 (osLv 4 3) ((osCfg 4).resLoop 3)) :=
  ⟨⟨Data.core483, Program.find?_of_indexOf? (j := 483) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core488, Program.find?_of_indexOf? (j := 488) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_4_4 : FnIs ((osCfg 4).sqLoop 4) (osParams 5)
      (sqLoopBody (osLv 4 4) ((osCfg 4).sqLoop 4)) ∧
    FnIs ((osCfg 4).resLoop 4) (osParams 6)
      (resLoopBody (osCfg 4) 4 (osLv 4 4) ((osCfg 4).resLoop 4)) :=
  ⟨⟨Data.core484, Program.find?_of_indexOf? (j := 484) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core489, Program.find?_of_indexOf? (j := 489) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_4 : OsData 4 := by
  have hl : (osCfg 4).levels.length = 5 := by decide +kernel
  have hb : Data.core299.body.drop 0 = (osBody (osCfg 4)).drop 0 :=
    run_step 1100 0 os_run_4_0 <|
    run_step 1100 1100 os_run_4_1 <|
    run_step 1100 2200 os_run_4_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core299, Program.find?_of_indexOf? (j := 299) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_4_0
  · exact osLv_4_1
  · exact osLv_4_2
  · exact osLv_4_3
  · exact osLv_4_4

end
end LeanVM.Guest.B1.Whir
