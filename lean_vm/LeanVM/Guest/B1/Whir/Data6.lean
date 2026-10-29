/-
  LeanVM.Guest.B1.Whir.Data6

  `open_stacked__L6` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 6

`osData_6 : OsData 6`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_6_0 : stmtsEqb ((Data.core298.body.drop 0).take 1100)
    (((osBody (osCfg 6)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_6_1 : stmtsEqb ((Data.core298.body.drop 1100).take 1100)
    (((osBody (osCfg 6)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_6_2 : stmtsEqb ((Data.core298.body.drop 2200).take 1100)
    (((osBody (osCfg 6)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_6_3 : stmtsEqb ((Data.core298.body.drop 3300).take 1100)
    (((osBody (osCfg 6)).drop 3300).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_6 : OsData 6 := by
  have hl : (osCfg 6).levels.length = 6 := by decide +kernel
  have hb : Data.core298.body.drop 0 = (osBody (osCfg 6)).drop 0 :=
    run_step 1100 0 os_run_6_0 <|
    run_step 1100 1100 os_run_6_1 <|
    run_step 1100 2200 os_run_6_2 <|
    run_step 1100 3300 os_run_6_3 <|
    drop_end (o := 4400) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core298, Program.find?_of_indexOf? (j := 298) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core493, Program.find?_of_indexOf? (j := 493) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core504, Program.find?_of_indexOf? (j := 504) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core495, Program.find?_of_indexOf? (j := 495) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core505, Program.find?_of_indexOf? (j := 505) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core497, Program.find?_of_indexOf? (j := 497) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core506, Program.find?_of_indexOf? (j := 506) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core499, Program.find?_of_indexOf? (j := 499) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core507, Program.find?_of_indexOf? (j := 507) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core500, Program.find?_of_indexOf? (j := 500) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core508, Program.find?_of_indexOf? (j := 508) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core501, Program.find?_of_indexOf? (j := 501) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core509, Program.find?_of_indexOf? (j := 509) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
