/-
  LeanVM.Guest.B1.Whir.Data11

  `open_stacked__L11` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 11

`osData_11 : OsData 11`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_11_0 : stmtsEqb ((Data.core306.body.drop 0).take 1100)
    (((osBody (osCfg 11)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_11_1 : stmtsEqb ((Data.core306.body.drop 1100).take 1100)
    (((osBody (osCfg 11)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_11_2 : stmtsEqb ((Data.core306.body.drop 2200).take 1100)
    (((osBody (osCfg 11)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_11_0 : FnIs ((osCfg 11).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 11 0) ((osCfg 11).sqLoop 0)) ∧
    FnIs ((osCfg 11).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 11) 0 (osLv 11 0) ((osCfg 11).resLoop 0)) :=
  ⟨⟨Data.core565, Program.find?_of_indexOf? (j := 565) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core571, Program.find?_of_indexOf? (j := 571) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_11_1 : FnIs ((osCfg 11).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 11 1) ((osCfg 11).sqLoop 1)) ∧
    FnIs ((osCfg 11).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 11) 1 (osLv 11 1) ((osCfg 11).resLoop 1)) :=
  ⟨⟨Data.core567, Program.find?_of_indexOf? (j := 567) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core572, Program.find?_of_indexOf? (j := 572) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_11_2 : FnIs ((osCfg 11).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 11 2) ((osCfg 11).sqLoop 2)) ∧
    FnIs ((osCfg 11).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 11) 2 (osLv 11 2) ((osCfg 11).resLoop 2)) :=
  ⟨⟨Data.core568, Program.find?_of_indexOf? (j := 568) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core573, Program.find?_of_indexOf? (j := 573) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_11_3 : FnIs ((osCfg 11).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 11 3) ((osCfg 11).sqLoop 3)) ∧
    FnIs ((osCfg 11).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 11) 3 (osLv 11 3) ((osCfg 11).resLoop 3)) :=
  ⟨⟨Data.core569, Program.find?_of_indexOf? (j := 569) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core574, Program.find?_of_indexOf? (j := 574) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_11_4 : FnIs ((osCfg 11).sqLoop 4) (osParams 5)
      (sqLoopBody (osLv 11 4) ((osCfg 11).sqLoop 4)) ∧
    FnIs ((osCfg 11).resLoop 4) (osParams 6)
      (resLoopBody (osCfg 11) 4 (osLv 11 4) ((osCfg 11).resLoop 4)) :=
  ⟨⟨Data.core570, Program.find?_of_indexOf? (j := 570) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core575, Program.find?_of_indexOf? (j := 575) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_11 : OsData 11 := by
  have hl : (osCfg 11).levels.length = 5 := by decide +kernel
  have hb : Data.core306.body.drop 0 = (osBody (osCfg 11)).drop 0 :=
    run_step 1100 0 os_run_11_0 <|
    run_step 1100 1100 os_run_11_1 <|
    run_step 1100 2200 os_run_11_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core306, Program.find?_of_indexOf? (j := 306) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_11_0
  · exact osLv_11_1
  · exact osLv_11_2
  · exact osLv_11_3
  · exact osLv_11_4

end
end LeanVM.Guest.B1.Whir
