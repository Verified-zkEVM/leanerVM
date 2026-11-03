/-
  LeanVM.Guest.B1.Whir.Data13

  `open_stacked__L13` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 13

`osData_13 : OsData 13`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_13_0 : stmtsEqb ((Data.core307.body.drop 0).take 1100)
    (((osBody (osCfg 13)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_13_1 : stmtsEqb ((Data.core307.body.drop 1100).take 1100)
    (((osBody (osCfg 13)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_13_2 : stmtsEqb ((Data.core307.body.drop 2200).take 1100)
    (((osBody (osCfg 13)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_13_0 : FnIs ((osCfg 13).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 13 0) ((osCfg 13).sqLoop 0)) ∧
    FnIs ((osCfg 13).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 13) 0 (osLv 13 0) ((osCfg 13).resLoop 0)) :=
  ⟨⟨Data.core587, Program.find?_of_indexOf? (j := 587) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core597, Program.find?_of_indexOf? (j := 597) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_13_1 : FnIs ((osCfg 13).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 13 1) ((osCfg 13).sqLoop 1)) ∧
    FnIs ((osCfg 13).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 13) 1 (osLv 13 1) ((osCfg 13).resLoop 1)) :=
  ⟨⟨Data.core589, Program.find?_of_indexOf? (j := 589) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core598, Program.find?_of_indexOf? (j := 598) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_13_2 : FnIs ((osCfg 13).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 13 2) ((osCfg 13).sqLoop 2)) ∧
    FnIs ((osCfg 13).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 13) 2 (osLv 13 2) ((osCfg 13).resLoop 2)) :=
  ⟨⟨Data.core591, Program.find?_of_indexOf? (j := 591) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core599, Program.find?_of_indexOf? (j := 599) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_13_3 : FnIs ((osCfg 13).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 13 3) ((osCfg 13).sqLoop 3)) ∧
    FnIs ((osCfg 13).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 13) 3 (osLv 13 3) ((osCfg 13).resLoop 3)) :=
  ⟨⟨Data.core593, Program.find?_of_indexOf? (j := 593) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core600, Program.find?_of_indexOf? (j := 600) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_13_4 : FnIs ((osCfg 13).sqLoop 4) (osParams 5)
      (sqLoopBody (osLv 13 4) ((osCfg 13).sqLoop 4)) ∧
    FnIs ((osCfg 13).resLoop 4) (osParams 6)
      (resLoopBody (osCfg 13) 4 (osLv 13 4) ((osCfg 13).resLoop 4)) :=
  ⟨⟨Data.core594, Program.find?_of_indexOf? (j := 594) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core601, Program.find?_of_indexOf? (j := 601) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_13_5 : FnIs ((osCfg 13).sqLoop 5) (osParams 5)
      (sqLoopBody (osLv 13 5) ((osCfg 13).sqLoop 5)) ∧
    FnIs ((osCfg 13).resLoop 5) (osParams 6)
      (resLoopBody (osCfg 13) 5 (osLv 13 5) ((osCfg 13).resLoop 5)) :=
  ⟨⟨Data.core596, Program.find?_of_indexOf? (j := 596) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core602, Program.find?_of_indexOf? (j := 602) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_13 : OsData 13 := by
  have hl : (osCfg 13).levels.length = 6 := by decide +kernel
  have hb : Data.core307.body.drop 0 = (osBody (osCfg 13)).drop 0 :=
    run_step 1100 0 os_run_13_0 <|
    run_step 1100 1100 os_run_13_1 <|
    run_step 1100 2200 os_run_13_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core307, Program.find?_of_indexOf? (j := 307) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_13_0
  · exact osLv_13_1
  · exact osLv_13_2
  · exact osLv_13_3
  · exact osLv_13_4
  · exact osLv_13_5

end
end LeanVM.Guest.B1.Whir
