/-
  LeanVM.Guest.B1.Whir.Data18

  `open_stacked__L18` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 18

`osData_18 : OsData 18`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_18_0 : stmtsEqb ((Data.core312.body.drop 0).take 1100)
    (((osBody (osCfg 18)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_18_1 : stmtsEqb ((Data.core312.body.drop 1100).take 1100)
    (((osBody (osCfg 18)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_18_2 : stmtsEqb ((Data.core312.body.drop 2200).take 1100)
    (((osBody (osCfg 18)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_18_0 : FnIs ((osCfg 18).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 18 0) ((osCfg 18).sqLoop 0)) ∧
    FnIs ((osCfg 18).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 18) 0 (osLv 18 0) ((osCfg 18).resLoop 0)) :=
  ⟨⟨Data.core643, Program.find?_of_indexOf? (j := 643) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core649, Program.find?_of_indexOf? (j := 649) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_18_1 : FnIs ((osCfg 18).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 18 1) ((osCfg 18).sqLoop 1)) ∧
    FnIs ((osCfg 18).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 18) 1 (osLv 18 1) ((osCfg 18).resLoop 1)) :=
  ⟨⟨Data.core645, Program.find?_of_indexOf? (j := 645) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core650, Program.find?_of_indexOf? (j := 650) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_18_2 : FnIs ((osCfg 18).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 18 2) ((osCfg 18).sqLoop 2)) ∧
    FnIs ((osCfg 18).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 18) 2 (osLv 18 2) ((osCfg 18).resLoop 2)) :=
  ⟨⟨Data.core646, Program.find?_of_indexOf? (j := 646) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core651, Program.find?_of_indexOf? (j := 651) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_18_3 : FnIs ((osCfg 18).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 18 3) ((osCfg 18).sqLoop 3)) ∧
    FnIs ((osCfg 18).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 18) 3 (osLv 18 3) ((osCfg 18).resLoop 3)) :=
  ⟨⟨Data.core647, Program.find?_of_indexOf? (j := 647) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core652, Program.find?_of_indexOf? (j := 652) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_18_4 : FnIs ((osCfg 18).sqLoop 4) (osParams 5)
      (sqLoopBody (osLv 18 4) ((osCfg 18).sqLoop 4)) ∧
    FnIs ((osCfg 18).resLoop 4) (osParams 6)
      (resLoopBody (osCfg 18) 4 (osLv 18 4) ((osCfg 18).resLoop 4)) :=
  ⟨⟨Data.core648, Program.find?_of_indexOf? (j := 648) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core653, Program.find?_of_indexOf? (j := 653) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_18 : OsData 18 := by
  have hl : (osCfg 18).levels.length = 5 := by decide +kernel
  have hb : Data.core312.body.drop 0 = (osBody (osCfg 18)).drop 0 :=
    run_step 1100 0 os_run_18_0 <|
    run_step 1100 1100 os_run_18_1 <|
    run_step 1100 2200 os_run_18_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core312, Program.find?_of_indexOf? (j := 312) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_18_0
  · exact osLv_18_1
  · exact osLv_18_2
  · exact osLv_18_3
  · exact osLv_18_4

end
end LeanVM.Guest.B1.Whir
