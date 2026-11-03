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
theorem os_run_25_0 : stmtsEqb ((Data.core319.body.drop 0).take 1100)
    (((osBody (osCfg 25)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_25_1 : stmtsEqb ((Data.core319.body.drop 1100).take 1100)
    (((osBody (osCfg 25)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_25_2 : stmtsEqb ((Data.core319.body.drop 2200).take 1100)
    (((osBody (osCfg 25)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_25 : OsData 25 := by
  have hl : (osCfg 25).levels.length = 5 := by decide +kernel
  have hb : Data.core319.body.drop 0 = (osBody (osCfg 25)).drop 0 :=
    run_step 1100 0 os_run_25_0 <|
    run_step 1100 1100 os_run_25_1 <|
    run_step 1100 2200 os_run_25_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core319, Program.find?_of_indexOf? (j := 317) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core721, Program.find?_of_indexOf? (j := 710) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core727, Program.find?_of_indexOf? (j := 716) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core723, Program.find?_of_indexOf? (j := 712) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core728, Program.find?_of_indexOf? (j := 717) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core724, Program.find?_of_indexOf? (j := 713) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core729, Program.find?_of_indexOf? (j := 718) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core725, Program.find?_of_indexOf? (j := 714) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core730, Program.find?_of_indexOf? (j := 719) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core726, Program.find?_of_indexOf? (j := 715) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core731, Program.find?_of_indexOf? (j := 720) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
