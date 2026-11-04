/-
  LeanVM.Guest.B1.Whir.Data3

  `open_stacked__L3` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 3

`osData_3 : OsData 3`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_3_0 : stmtsEqb ((Data.core298.body.drop 0).take 1100)
    (((osBody (osCfg 3)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_3_1 : stmtsEqb ((Data.core298.body.drop 1100).take 1100)
    (((osBody (osCfg 3)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_3_2 : stmtsEqb ((Data.core298.body.drop 2200).take 1100)
    (((osBody (osCfg 3)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_3_0 : FnIs ((osCfg 3).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 3 0) ((osCfg 3).sqLoop 0)) ∧
    FnIs ((osCfg 3).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 3) 0 (osLv 3 0) ((osCfg 3).resLoop 0)) :=
  ⟨⟨Data.core458, Program.find?_of_indexOf? (j := 458) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core471, Program.find?_of_indexOf? (j := 471) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_3_1 : FnIs ((osCfg 3).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 3 1) ((osCfg 3).sqLoop 1)) ∧
    FnIs ((osCfg 3).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 3) 1 (osLv 3 1) ((osCfg 3).resLoop 1)) :=
  ⟨⟨Data.core461, Program.find?_of_indexOf? (j := 461) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core472, Program.find?_of_indexOf? (j := 472) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_3_2 : FnIs ((osCfg 3).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 3 2) ((osCfg 3).sqLoop 2)) ∧
    FnIs ((osCfg 3).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 3) 2 (osLv 3 2) ((osCfg 3).resLoop 2)) :=
  ⟨⟨Data.core464, Program.find?_of_indexOf? (j := 464) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core473, Program.find?_of_indexOf? (j := 473) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_3_3 : FnIs ((osCfg 3).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 3 3) ((osCfg 3).sqLoop 3)) ∧
    FnIs ((osCfg 3).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 3) 3 (osLv 3 3) ((osCfg 3).resLoop 3)) :=
  ⟨⟨Data.core467, Program.find?_of_indexOf? (j := 467) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core474, Program.find?_of_indexOf? (j := 474) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_3_4 : FnIs ((osCfg 3).sqLoop 4) (osParams 5)
      (sqLoopBody (osLv 3 4) ((osCfg 3).sqLoop 4)) ∧
    FnIs ((osCfg 3).resLoop 4) (osParams 6)
      (resLoopBody (osCfg 3) 4 (osLv 3 4) ((osCfg 3).resLoop 4)) :=
  ⟨⟨Data.core469, Program.find?_of_indexOf? (j := 469) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core475, Program.find?_of_indexOf? (j := 475) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_3 : OsData 3 := by
  have hl : (osCfg 3).levels.length = 5 := by decide +kernel
  have hb : Data.core298.body.drop 0 = (osBody (osCfg 3)).drop 0 :=
    run_step 1100 0 os_run_3_0 <|
    run_step 1100 1100 os_run_3_1 <|
    run_step 1100 2200 os_run_3_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core298, Program.find?_of_indexOf? (j := 298) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_3_0
  · exact osLv_3_1
  · exact osLv_3_2
  · exact osLv_3_3
  · exact osLv_3_4

end
end LeanVM.Guest.B1.Whir
