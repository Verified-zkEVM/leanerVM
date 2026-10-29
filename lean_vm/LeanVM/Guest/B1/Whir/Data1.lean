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
theorem os_run_1_0 : stmtsEqb ((Data.core293.body.drop 0).take 1100)
    (((osBody (osCfg 1)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_1_1 : stmtsEqb ((Data.core293.body.drop 1100).take 1100)
    (((osBody (osCfg 1)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_1_2 : stmtsEqb ((Data.core293.body.drop 2200).take 1100)
    (((osBody (osCfg 1)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_1 : OsData 1 := by
  have hl : (osCfg 1).levels.length = 4 := by decide +kernel
  have hb : Data.core293.body.drop 0 = (osBody (osCfg 1)).drop 0 :=
    run_step 1100 0 os_run_1_0 <|
    run_step 1100 1100 os_run_1_1 <|
    run_step 1100 2200 os_run_1_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core293, Program.find?_of_indexOf? (j := 293) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core411, Program.find?_of_indexOf? (j := 411) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core422, Program.find?_of_indexOf? (j := 422) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core414, Program.find?_of_indexOf? (j := 414) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core423, Program.find?_of_indexOf? (j := 423) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core417, Program.find?_of_indexOf? (j := 417) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core424, Program.find?_of_indexOf? (j := 424) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core420, Program.find?_of_indexOf? (j := 420) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core425, Program.find?_of_indexOf? (j := 425) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
