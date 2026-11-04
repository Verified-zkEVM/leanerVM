/-
  LeanVM.Guest.B1.Whir.Data14

  `open_stacked__L14` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 14

`osData_14 : OsData 14`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_14_0 : stmtsEqb ((Data.core309.body.drop 0).take 1100)
    (((osBody (osCfg 14)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_14_1 : stmtsEqb ((Data.core309.body.drop 1100).take 1100)
    (((osBody (osCfg 14)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_14_0 : FnIs ((osCfg 14).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 14 0) ((osCfg 14).sqLoop 0)) ∧
    FnIs ((osCfg 14).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 14) 0 (osLv 14 0) ((osCfg 14).resLoop 0)) :=
  ⟨⟨Data.core604, Program.find?_of_indexOf? (j := 604) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core609, Program.find?_of_indexOf? (j := 609) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_14_1 : FnIs ((osCfg 14).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 14 1) ((osCfg 14).sqLoop 1)) ∧
    FnIs ((osCfg 14).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 14) 1 (osLv 14 1) ((osCfg 14).resLoop 1)) :=
  ⟨⟨Data.core606, Program.find?_of_indexOf? (j := 606) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core610, Program.find?_of_indexOf? (j := 610) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_14_2 : FnIs ((osCfg 14).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 14 2) ((osCfg 14).sqLoop 2)) ∧
    FnIs ((osCfg 14).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 14) 2 (osLv 14 2) ((osCfg 14).resLoop 2)) :=
  ⟨⟨Data.core607, Program.find?_of_indexOf? (j := 607) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core611, Program.find?_of_indexOf? (j := 611) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_14_3 : FnIs ((osCfg 14).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 14 3) ((osCfg 14).sqLoop 3)) ∧
    FnIs ((osCfg 14).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 14) 3 (osLv 14 3) ((osCfg 14).resLoop 3)) :=
  ⟨⟨Data.core608, Program.find?_of_indexOf? (j := 608) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core612, Program.find?_of_indexOf? (j := 612) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_14 : OsData 14 := by
  have hl : (osCfg 14).levels.length = 4 := by decide +kernel
  have hb : Data.core309.body.drop 0 = (osBody (osCfg 14)).drop 0 :=
    run_step 1100 0 os_run_14_0 <|
    run_step 1100 1100 os_run_14_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core309, Program.find?_of_indexOf? (j := 309) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_14_0
  · exact osLv_14_1
  · exact osLv_14_2
  · exact osLv_14_3

end
end LeanVM.Guest.B1.Whir
