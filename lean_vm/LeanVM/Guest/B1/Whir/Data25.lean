/-
  LeanVM.Guest.B1.Whir.Data25

  `open_stacked__L25` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 25

`osData_25 : OsData 25`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_25_0 : stmtsEqb ((Data.core320.body.drop 0).take 1100)
    (((osBody (osCfg 25)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_25_1 : stmtsEqb ((Data.core320.body.drop 1100).take 1100)
    (((osBody (osCfg 25)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_25_2 : stmtsEqb ((Data.core320.body.drop 2200).take 1100)
    (((osBody (osCfg 25)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_25 : OsData 25 := by
  have hl : (osCfg 25).levels.length = 5 := by decide +kernel
  have hb : Data.core320.body.drop 0 = (osBody (osCfg 25)).drop 0 :=
    run_step 1100 0 os_run_25_0 <|
    run_step 1100 1100 os_run_25_1 <|
    run_step 1100 2200 os_run_25_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core320, Program.find?_of_indexOf? (j := 320) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core731, Program.find?_of_indexOf? (j := 731) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core737, Program.find?_of_indexOf? (j := 737) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core733, Program.find?_of_indexOf? (j := 733) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core738, Program.find?_of_indexOf? (j := 738) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core734, Program.find?_of_indexOf? (j := 734) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core739, Program.find?_of_indexOf? (j := 739) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core735, Program.find?_of_indexOf? (j := 735) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core740, Program.find?_of_indexOf? (j := 740) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core736, Program.find?_of_indexOf? (j := 736) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core741, Program.find?_of_indexOf? (j := 741) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
