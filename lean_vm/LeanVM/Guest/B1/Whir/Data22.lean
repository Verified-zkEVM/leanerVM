/-
  LeanVM.Guest.B1.Whir.Data22

  `open_stacked__L22` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 22

`osData_22 : OsData 22`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_22_0 : stmtsEqb ((Data.core316.body.drop 0).take 1100)
    (((osBody (osCfg 22)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_22_1 : stmtsEqb ((Data.core316.body.drop 1100).take 1100)
    (((osBody (osCfg 22)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_22_0 : FnIs ((osCfg 22).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 22 0) ((osCfg 22).sqLoop 0)) ∧
    FnIs ((osCfg 22).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 22) 0 (osLv 22 0) ((osCfg 22).resLoop 0)) :=
  ⟨⟨Data.core690, Program.find?_of_indexOf? (j := 690) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core695, Program.find?_of_indexOf? (j := 695) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_22_1 : FnIs ((osCfg 22).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 22 1) ((osCfg 22).sqLoop 1)) ∧
    FnIs ((osCfg 22).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 22) 1 (osLv 22 1) ((osCfg 22).resLoop 1)) :=
  ⟨⟨Data.core692, Program.find?_of_indexOf? (j := 692) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core696, Program.find?_of_indexOf? (j := 696) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_22_2 : FnIs ((osCfg 22).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 22 2) ((osCfg 22).sqLoop 2)) ∧
    FnIs ((osCfg 22).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 22) 2 (osLv 22 2) ((osCfg 22).resLoop 2)) :=
  ⟨⟨Data.core693, Program.find?_of_indexOf? (j := 693) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core697, Program.find?_of_indexOf? (j := 697) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_22_3 : FnIs ((osCfg 22).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 22 3) ((osCfg 22).sqLoop 3)) ∧
    FnIs ((osCfg 22).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 22) 3 (osLv 22 3) ((osCfg 22).resLoop 3)) :=
  ⟨⟨Data.core694, Program.find?_of_indexOf? (j := 694) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core698, Program.find?_of_indexOf? (j := 698) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_22 : OsData 22 := by
  have hl : (osCfg 22).levels.length = 4 := by decide +kernel
  have hb : Data.core316.body.drop 0 = (osBody (osCfg 22)).drop 0 :=
    run_step 1100 0 os_run_22_0 <|
    run_step 1100 1100 os_run_22_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core316, Program.find?_of_indexOf? (j := 316) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_22_0
  · exact osLv_22_1
  · exact osLv_22_2
  · exact osLv_22_3

end
end LeanVM.Guest.B1.Whir
