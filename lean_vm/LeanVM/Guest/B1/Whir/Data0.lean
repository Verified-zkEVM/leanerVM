/-
  LeanVM.Guest.B1.Whir.Data0

  `open_stacked__L0` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 0

`osData_0 : OsData 0`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_0_0 : stmtsEqb ((Data.core295.body.drop 0).take 1100)
    (((osBody (osCfg 0)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_0_1 : stmtsEqb ((Data.core295.body.drop 1100).take 1100)
    (((osBody (osCfg 0)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_0_2 : stmtsEqb ((Data.core295.body.drop 2200).take 1100)
    (((osBody (osCfg 0)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_0_0 : FnIs ((osCfg 0).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 0 0) ((osCfg 0).sqLoop 0)) ∧
    FnIs ((osCfg 0).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 0) 0 (osLv 0 0) ((osCfg 0).resLoop 0)) :=
  ⟨⟨Data.core401, Program.find?_of_indexOf? (j := 401) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core418, Program.find?_of_indexOf? (j := 418) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_0_1 : FnIs ((osCfg 0).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 0 1) ((osCfg 0).sqLoop 1)) ∧
    FnIs ((osCfg 0).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 0) 1 (osLv 0 1) ((osCfg 0).resLoop 1)) :=
  ⟨⟨Data.core406, Program.find?_of_indexOf? (j := 406) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core419, Program.find?_of_indexOf? (j := 419) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_0_2 : FnIs ((osCfg 0).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 0 2) ((osCfg 0).sqLoop 2)) ∧
    FnIs ((osCfg 0).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 0) 2 (osLv 0 2) ((osCfg 0).resLoop 2)) :=
  ⟨⟨Data.core411, Program.find?_of_indexOf? (j := 411) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core420, Program.find?_of_indexOf? (j := 420) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_0_3 : FnIs ((osCfg 0).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 0 3) ((osCfg 0).sqLoop 3)) ∧
    FnIs ((osCfg 0).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 0) 3 (osLv 0 3) ((osCfg 0).resLoop 3)) :=
  ⟨⟨Data.core415, Program.find?_of_indexOf? (j := 415) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core421, Program.find?_of_indexOf? (j := 421) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_0 : OsData 0 := by
  have hl : (osCfg 0).levels.length = 4 := by decide +kernel
  have hb : Data.core295.body.drop 0 = (osBody (osCfg 0)).drop 0 :=
    run_step 1100 0 os_run_0_0 <|
    run_step 1100 1100 os_run_0_1 <|
    run_step 1100 2200 os_run_0_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core295, Program.find?_of_indexOf? (j := 295) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_0_0
  · exact osLv_0_1
  · exact osLv_0_2
  · exact osLv_0_3

end
end LeanVM.Guest.B1.Whir
