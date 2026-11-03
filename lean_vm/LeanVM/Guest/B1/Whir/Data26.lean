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
theorem os_run_26_0 : stmtsEqb ((Data.core320.body.drop 0).take 1100)
    (((osBody (osCfg 26)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_26_1 : stmtsEqb ((Data.core320.body.drop 1100).take 1100)
    (((osBody (osCfg 26)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_26_2 : stmtsEqb ((Data.core320.body.drop 2200).take 1100)
    (((osBody (osCfg 26)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_26_0 : FnIs ((osCfg 26).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 26 0) ((osCfg 26).sqLoop 0)) ∧
    FnIs ((osCfg 26).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 26) 0 (osLv 26 0) ((osCfg 26).resLoop 0)) :=
  ⟨⟨Data.core732, Program.find?_of_indexOf? (j := 732) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core739, Program.find?_of_indexOf? (j := 739) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_26_1 : FnIs ((osCfg 26).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 26 1) ((osCfg 26).sqLoop 1)) ∧
    FnIs ((osCfg 26).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 26) 1 (osLv 26 1) ((osCfg 26).resLoop 1)) :=
  ⟨⟨Data.core734, Program.find?_of_indexOf? (j := 734) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core740, Program.find?_of_indexOf? (j := 740) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_26_2 : FnIs ((osCfg 26).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 26 2) ((osCfg 26).sqLoop 2)) ∧
    FnIs ((osCfg 26).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 26) 2 (osLv 26 2) ((osCfg 26).resLoop 2)) :=
  ⟨⟨Data.core736, Program.find?_of_indexOf? (j := 736) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core741, Program.find?_of_indexOf? (j := 741) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_26_3 : FnIs ((osCfg 26).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 26 3) ((osCfg 26).sqLoop 3)) ∧
    FnIs ((osCfg 26).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 26) 3 (osLv 26 3) ((osCfg 26).resLoop 3)) :=
  ⟨⟨Data.core737, Program.find?_of_indexOf? (j := 737) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core742, Program.find?_of_indexOf? (j := 742) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_26_4 : FnIs ((osCfg 26).sqLoop 4) (osParams 5)
      (sqLoopBody (osLv 26 4) ((osCfg 26).sqLoop 4)) ∧
    FnIs ((osCfg 26).resLoop 4) (osParams 6)
      (resLoopBody (osCfg 26) 4 (osLv 26 4) ((osCfg 26).resLoop 4)) :=
  ⟨⟨Data.core738, Program.find?_of_indexOf? (j := 738) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core743, Program.find?_of_indexOf? (j := 743) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_26 : OsData 26 := by
  have hl : (osCfg 26).levels.length = 5 := by decide +kernel
  have hb : Data.core320.body.drop 0 = (osBody (osCfg 26)).drop 0 :=
    run_step 1100 0 os_run_26_0 <|
    run_step 1100 1100 os_run_26_1 <|
    run_step 1100 2200 os_run_26_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core320, Program.find?_of_indexOf? (j := 320) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_26_0
  · exact osLv_26_1
  · exact osLv_26_2
  · exact osLv_26_3
  · exact osLv_26_4

end
end LeanVM.Guest.B1.Whir
