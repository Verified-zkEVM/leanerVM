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
theorem os_run_24_0 : stmtsEqb ((Data.core316.body.drop 0).take 1100)
    (((osBody (osCfg 24)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_24_1 : stmtsEqb ((Data.core316.body.drop 1100).take 1100)
    (((osBody (osCfg 24)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_24_2 : stmtsEqb ((Data.core316.body.drop 2200).take 1100)
    (((osBody (osCfg 24)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_24 : OsData 24 := by
  have hl : (osCfg 24).levels.length = 5 := by decide +kernel
  have hb : Data.core316.body.drop 0 = (osBody (osCfg 24)).drop 0 :=
    run_step 1100 0 os_run_24_0 <|
    run_step 1100 1100 os_run_24_1 <|
    run_step 1100 2200 os_run_24_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core316, Program.find?_of_indexOf? (j := 316) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core699, Program.find?_of_indexOf? (j := 699) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core705, Program.find?_of_indexOf? (j := 705) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core701, Program.find?_of_indexOf? (j := 701) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core706, Program.find?_of_indexOf? (j := 706) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core702, Program.find?_of_indexOf? (j := 702) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core707, Program.find?_of_indexOf? (j := 707) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core703, Program.find?_of_indexOf? (j := 703) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core708, Program.find?_of_indexOf? (j := 708) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core704, Program.find?_of_indexOf? (j := 704) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core709, Program.find?_of_indexOf? (j := 709) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
