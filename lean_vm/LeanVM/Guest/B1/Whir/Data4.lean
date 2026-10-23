/-
  LeanVM.Guest.B1.Whir.Data4

  `open_stacked__L4` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 4

`osData_4 : OsData 4`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_4_0 : stmtsEqb ((Data.core299.body.drop 0).take 1100)
    (((osBody (osCfg 4)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_4_1 : stmtsEqb ((Data.core299.body.drop 1100).take 1100)
    (((osBody (osCfg 4)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_4_2 : stmtsEqb ((Data.core299.body.drop 2200).take 1100)
    (((osBody (osCfg 4)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_4 : OsData 4 := by
  have hl : (osCfg 4).levels.length = 5 := by decide +kernel
  have hb : Data.core299.body.drop 0 = (osBody (osCfg 4)).drop 0 :=
    run_step 1100 0 os_run_4_0 <|
    run_step 1100 1100 os_run_4_1 <|
    run_step 1100 2200 os_run_4_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core299, Program.find?_of_indexOf? (j := 299) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core486, Program.find?_of_indexOf? (j := 486) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core494, Program.find?_of_indexOf? (j := 494) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core488, Program.find?_of_indexOf? (j := 488) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core495, Program.find?_of_indexOf? (j := 495) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core490, Program.find?_of_indexOf? (j := 490) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core496, Program.find?_of_indexOf? (j := 496) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core492, Program.find?_of_indexOf? (j := 492) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core497, Program.find?_of_indexOf? (j := 497) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core493, Program.find?_of_indexOf? (j := 493) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core498, Program.find?_of_indexOf? (j := 498) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
