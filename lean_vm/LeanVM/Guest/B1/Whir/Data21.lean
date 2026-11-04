/-
  LeanVM.Guest.B1.Whir.Data21

  `open_stacked__L21` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 21

`osData_21 : OsData 21`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_21_0 : stmtsEqb ((Data.core316.body.drop 0).take 1100)
    (((osBody (osCfg 21)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_21_1 : stmtsEqb ((Data.core316.body.drop 1100).take 1100)
    (((osBody (osCfg 21)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_21_0 : FnIs ((osCfg 21).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 21 0) ((osCfg 21).sqLoop 0)) ∧
    FnIs ((osCfg 21).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 21) 0 (osLv 21 0) ((osCfg 21).resLoop 0)) :=
  ⟨⟨Data.core682, Program.find?_of_indexOf? (j := 682) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core687, Program.find?_of_indexOf? (j := 687) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_21_1 : FnIs ((osCfg 21).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 21 1) ((osCfg 21).sqLoop 1)) ∧
    FnIs ((osCfg 21).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 21) 1 (osLv 21 1) ((osCfg 21).resLoop 1)) :=
  ⟨⟨Data.core684, Program.find?_of_indexOf? (j := 684) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core688, Program.find?_of_indexOf? (j := 688) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_21_2 : FnIs ((osCfg 21).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 21 2) ((osCfg 21).sqLoop 2)) ∧
    FnIs ((osCfg 21).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 21) 2 (osLv 21 2) ((osCfg 21).resLoop 2)) :=
  ⟨⟨Data.core685, Program.find?_of_indexOf? (j := 685) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core689, Program.find?_of_indexOf? (j := 689) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_21_3 : FnIs ((osCfg 21).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 21 3) ((osCfg 21).sqLoop 3)) ∧
    FnIs ((osCfg 21).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 21) 3 (osLv 21 3) ((osCfg 21).resLoop 3)) :=
  ⟨⟨Data.core686, Program.find?_of_indexOf? (j := 686) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core690, Program.find?_of_indexOf? (j := 690) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_21 : OsData 21 := by
  have hl : (osCfg 21).levels.length = 4 := by decide +kernel
  have hb : Data.core316.body.drop 0 = (osBody (osCfg 21)).drop 0 :=
    run_step 1100 0 os_run_21_0 <|
    run_step 1100 1100 os_run_21_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core316, Program.find?_of_indexOf? (j := 316) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_21_0
  · exact osLv_21_1
  · exact osLv_21_2
  · exact osLv_21_3

end
end LeanVM.Guest.B1.Whir
