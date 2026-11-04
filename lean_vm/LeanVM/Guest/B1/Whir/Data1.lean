/-
  LeanVM.Guest.B1.Whir.Data1

  `open_stacked__L1` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 1

`osData_1 : OsData 1`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_1_0 : stmtsEqb ((Data.core296.body.drop 0).take 1100)
    (((osBody (osCfg 1)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_1_1 : stmtsEqb ((Data.core296.body.drop 1100).take 1100)
    (((osBody (osCfg 1)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_1_2 : stmtsEqb ((Data.core296.body.drop 2200).take 1100)
    (((osBody (osCfg 1)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_1_0 : FnIs ((osCfg 1).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 1 0) ((osCfg 1).sqLoop 0)) ∧
    FnIs ((osCfg 1).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 1) 0 (osLv 1 0) ((osCfg 1).resLoop 0)) :=
  ⟨⟨Data.core423, Program.find?_of_indexOf? (j := 422) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core434, Program.find?_of_indexOf? (j := 433) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_1_1 : FnIs ((osCfg 1).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 1 1) ((osCfg 1).sqLoop 1)) ∧
    FnIs ((osCfg 1).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 1) 1 (osLv 1 1) ((osCfg 1).resLoop 1)) :=
  ⟨⟨Data.core426, Program.find?_of_indexOf? (j := 425) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core435, Program.find?_of_indexOf? (j := 434) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_1_2 : FnIs ((osCfg 1).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 1 2) ((osCfg 1).sqLoop 2)) ∧
    FnIs ((osCfg 1).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 1) 2 (osLv 1 2) ((osCfg 1).resLoop 2)) :=
  ⟨⟨Data.core429, Program.find?_of_indexOf? (j := 428) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core436, Program.find?_of_indexOf? (j := 435) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_1_3 : FnIs ((osCfg 1).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 1 3) ((osCfg 1).sqLoop 3)) ∧
    FnIs ((osCfg 1).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 1) 3 (osLv 1 3) ((osCfg 1).resLoop 3)) :=
  ⟨⟨Data.core432, Program.find?_of_indexOf? (j := 431) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core437, Program.find?_of_indexOf? (j := 436) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_1 : OsData 1 := by
  have hl : (osCfg 1).levels.length = 4 := by decide +kernel
  have hb : Data.core296.body.drop 0 = (osBody (osCfg 1)).drop 0 :=
    run_step 1100 0 os_run_1_0 <|
    run_step 1100 1100 os_run_1_1 <|
    run_step 1100 2200 os_run_1_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core296, Program.find?_of_indexOf? (j := 295) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_1_0
  · exact osLv_1_1
  · exact osLv_1_2
  · exact osLv_1_3

end
end LeanVM.Guest.B1.Whir
