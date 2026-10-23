/-
  LeanVM.Guest.B1.Whir.Data16

  `open_stacked__L16` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 16

`osData_16 : OsData 16`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_16_0 : stmtsEqb ((Data.core311.body.drop 0).take 1100)
    (((osBody (osCfg 16)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_16_1 : stmtsEqb ((Data.core311.body.drop 1100).take 1100)
    (((osBody (osCfg 16)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_16_2 : stmtsEqb ((Data.core311.body.drop 2200).take 1100)
    (((osBody (osCfg 16)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_16 : OsData 16 := by
  have hl : (osCfg 16).levels.length = 5 := by decide +kernel
  have hb : Data.core311.body.drop 0 = (osBody (osCfg 16)).drop 0 :=
    run_step 1100 0 os_run_16_0 <|
    run_step 1100 1100 os_run_16_1 <|
    run_step 1100 2200 os_run_16_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core311, Program.find?_of_indexOf? (j := 311) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core631, Program.find?_of_indexOf? (j := 631) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core637, Program.find?_of_indexOf? (j := 637) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core633, Program.find?_of_indexOf? (j := 633) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core638, Program.find?_of_indexOf? (j := 638) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core634, Program.find?_of_indexOf? (j := 634) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core639, Program.find?_of_indexOf? (j := 639) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core635, Program.find?_of_indexOf? (j := 635) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core640, Program.find?_of_indexOf? (j := 640) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core636, Program.find?_of_indexOf? (j := 636) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core641, Program.find?_of_indexOf? (j := 641) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
