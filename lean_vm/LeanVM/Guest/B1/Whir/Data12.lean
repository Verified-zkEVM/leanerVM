/-
  LeanVM.Guest.B1.Whir.Data12

  `open_stacked__L12` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 12

`osData_12 : OsData 12`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_12_0 : stmtsEqb ((Data.core307.body.drop 0).take 1100)
    (((osBody (osCfg 12)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_12_1 : stmtsEqb ((Data.core307.body.drop 1100).take 1100)
    (((osBody (osCfg 12)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_12_2 : stmtsEqb ((Data.core307.body.drop 2200).take 1100)
    (((osBody (osCfg 12)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_12 : OsData 12 := by
  have hl : (osCfg 12).levels.length = 5 := by decide +kernel
  have hb : Data.core307.body.drop 0 = (osBody (osCfg 12)).drop 0 :=
    run_step 1100 0 os_run_12_0 <|
    run_step 1100 1100 os_run_12_1 <|
    run_step 1100 2200 os_run_12_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core307, Program.find?_of_indexOf? (j := 307) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core585, Program.find?_of_indexOf? (j := 585) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core592, Program.find?_of_indexOf? (j := 592) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core587, Program.find?_of_indexOf? (j := 587) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core593, Program.find?_of_indexOf? (j := 593) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core588, Program.find?_of_indexOf? (j := 588) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core594, Program.find?_of_indexOf? (j := 594) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core589, Program.find?_of_indexOf? (j := 589) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core595, Program.find?_of_indexOf? (j := 595) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core590, Program.find?_of_indexOf? (j := 590) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core596, Program.find?_of_indexOf? (j := 596) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
