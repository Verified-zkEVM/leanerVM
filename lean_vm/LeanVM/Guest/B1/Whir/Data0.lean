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
theorem os_run_0_0 : stmtsEqb ((Data.core295.body.drop 0).take 1100)
    (((osBody (osCfg 0)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_0_1 : stmtsEqb ((Data.core295.body.drop 1100).take 1100)
    (((osBody (osCfg 0)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_0_2 : stmtsEqb ((Data.core295.body.drop 2200).take 1100)
    (((osBody (osCfg 0)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_0 : OsData 0 := by
  have hl : (osCfg 0).levels.length = 4 := by decide +kernel
  have hb : Data.core295.body.drop 0 = (osBody (osCfg 0)).drop 0 :=
    run_step 1100 0 os_run_0_0 <|
    run_step 1100 1100 os_run_0_1 <|
    run_step 1100 2200 os_run_0_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core295, Program.find?_of_indexOf? (j := 295) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core410, Program.find?_of_indexOf? (j := 410) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core427, Program.find?_of_indexOf? (j := 427) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core415, Program.find?_of_indexOf? (j := 415) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core428, Program.find?_of_indexOf? (j := 428) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core420, Program.find?_of_indexOf? (j := 420) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core429, Program.find?_of_indexOf? (j := 429) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core424, Program.find?_of_indexOf? (j := 424) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core430, Program.find?_of_indexOf? (j := 430) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
