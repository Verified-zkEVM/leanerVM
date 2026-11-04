/-
  LeanVM.Guest.B1.Whir.Data24

  `open_stacked__L24` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 24

`osData_24 : OsData 24`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_24_0 : stmtsEqb ((Data.core318.body.drop 0).take 1100)
    (((osBody (osCfg 24)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_24_1 : stmtsEqb ((Data.core318.body.drop 1100).take 1100)
    (((osBody (osCfg 24)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_24_2 : stmtsEqb ((Data.core318.body.drop 2200).take 1100)
    (((osBody (osCfg 24)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_24_0 : FnIs ((osCfg 24).sqLoop 0) (osParams 5)
      (sqLoopBody (osLv 24 0) ((osCfg 24).sqLoop 0)) ∧
    FnIs ((osCfg 24).resLoop 0) (osParams 6)
      (resLoopBody (osCfg 24) 0 (osLv 24 0) ((osCfg 24).resLoop 0)) :=
  ⟨⟨Data.core710, Program.find?_of_indexOf? (j := 710) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core716, Program.find?_of_indexOf? (j := 716) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_24_1 : FnIs ((osCfg 24).sqLoop 1) (osParams 5)
      (sqLoopBody (osLv 24 1) ((osCfg 24).sqLoop 1)) ∧
    FnIs ((osCfg 24).resLoop 1) (osParams 6)
      (resLoopBody (osCfg 24) 1 (osLv 24 1) ((osCfg 24).resLoop 1)) :=
  ⟨⟨Data.core712, Program.find?_of_indexOf? (j := 712) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core717, Program.find?_of_indexOf? (j := 717) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_24_2 : FnIs ((osCfg 24).sqLoop 2) (osParams 5)
      (sqLoopBody (osLv 24 2) ((osCfg 24).sqLoop 2)) ∧
    FnIs ((osCfg 24).resLoop 2) (osParams 6)
      (resLoopBody (osCfg 24) 2 (osLv 24 2) ((osCfg 24).resLoop 2)) :=
  ⟨⟨Data.core713, Program.find?_of_indexOf? (j := 713) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core718, Program.find?_of_indexOf? (j := 718) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_24_3 : FnIs ((osCfg 24).sqLoop 3) (osParams 5)
      (sqLoopBody (osLv 24 3) ((osCfg 24).sqLoop 3)) ∧
    FnIs ((osCfg 24).resLoop 3) (osParams 6)
      (resLoopBody (osCfg 24) 3 (osLv 24 3) ((osCfg 24).resLoop 3)) :=
  ⟨⟨Data.core714, Program.find?_of_indexOf? (j := 714) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core719, Program.find?_of_indexOf? (j := 719) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_24_4 : FnIs ((osCfg 24).sqLoop 4) (osParams 5)
      (sqLoopBody (osLv 24 4) ((osCfg 24).sqLoop 4)) ∧
    FnIs ((osCfg 24).resLoop 4) (osParams 6)
      (resLoopBody (osCfg 24) 4 (osLv 24 4) ((osCfg 24).resLoop 4)) :=
  ⟨⟨Data.core715, Program.find?_of_indexOf? (j := 715) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core720, Program.find?_of_indexOf? (j := 720) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_24 : OsData 24 := by
  have hl : (osCfg 24).levels.length = 5 := by decide +kernel
  have hb : Data.core318.body.drop 0 = (osBody (osCfg 24)).drop 0 :=
    run_step 1100 0 os_run_24_0 <|
    run_step 1100 1100 os_run_24_1 <|
    run_step 1100 2200 os_run_24_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core318, Program.find?_of_indexOf? (j := 318) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_24_0
  · exact osLv_24_1
  · exact osLv_24_2
  · exact osLv_24_3
  · exact osLv_24_4

end
end LeanVM.Guest.B1.Whir
