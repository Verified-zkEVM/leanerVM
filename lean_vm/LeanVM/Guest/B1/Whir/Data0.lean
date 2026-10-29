/-
  LeanVM.Guest.B1.Whir.Data0

  `open_stacked__L0` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 0

`osData_0 : OsData 0`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_0_0 : stmtsEqb ((Data.core292.body.drop 0).take 1100)
    (((osBody (osCfg 0)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_0_1 : stmtsEqb ((Data.core292.body.drop 1100).take 1100)
    (((osBody (osCfg 0)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_0_2 : stmtsEqb ((Data.core292.body.drop 2200).take 1100)
    (((osBody (osCfg 0)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_0 : OsData 0 := by
  have hl : (osCfg 0).levels.length = 4 := by decide +kernel
  have hb : Data.core292.body.drop 0 = (osBody (osCfg 0)).drop 0 :=
    run_step 1100 0 os_run_0_0 <|
    run_step 1100 1100 os_run_0_1 <|
    run_step 1100 2200 os_run_0_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core292, Program.find?_of_indexOf? (j := 292) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core389, Program.find?_of_indexOf? (j := 389) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core406, Program.find?_of_indexOf? (j := 406) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core394, Program.find?_of_indexOf? (j := 394) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core407, Program.find?_of_indexOf? (j := 407) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core399, Program.find?_of_indexOf? (j := 399) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core408, Program.find?_of_indexOf? (j := 408) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core403, Program.find?_of_indexOf? (j := 403) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core409, Program.find?_of_indexOf? (j := 409) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
