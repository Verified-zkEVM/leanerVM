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
theorem os_run_6_0 : stmtsEqb ((Data.core301.body.drop 0).take 1100)
    (((osBody (osCfg 6)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_6_1 : stmtsEqb ((Data.core301.body.drop 1100).take 1100)
    (((osBody (osCfg 6)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_6_2 : stmtsEqb ((Data.core301.body.drop 2200).take 1100)
    (((osBody (osCfg 6)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_6_3 : stmtsEqb ((Data.core301.body.drop 3300).take 1100)
    (((osBody (osCfg 6)).drop 3300).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_6 : OsData 6 := by
  have hl : (osCfg 6).levels.length = 6 := by decide +kernel
  have hb : Data.core301.body.drop 0 = (osBody (osCfg 6)).drop 0 :=
    run_step 1100 0 os_run_6_0 <|
    run_step 1100 1100 os_run_6_1 <|
    run_step 1100 2200 os_run_6_2 <|
    run_step 1100 3300 os_run_6_3 <|
    drop_end (o := 4400) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core301, Program.find?_of_indexOf? (j := 301) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core514, Program.find?_of_indexOf? (j := 514) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core525, Program.find?_of_indexOf? (j := 525) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core516, Program.find?_of_indexOf? (j := 516) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core526, Program.find?_of_indexOf? (j := 526) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core518, Program.find?_of_indexOf? (j := 518) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core527, Program.find?_of_indexOf? (j := 527) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core520, Program.find?_of_indexOf? (j := 520) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core528, Program.find?_of_indexOf? (j := 528) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core521, Program.find?_of_indexOf? (j := 521) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core529, Program.find?_of_indexOf? (j := 529) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core522, Program.find?_of_indexOf? (j := 522) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core530, Program.find?_of_indexOf? (j := 530) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
