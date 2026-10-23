/-
  LeanVM.Guest.B1.Whir.Data17

  `open_stacked__L17` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 17

`osData_17 : OsData 17`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_17_0 : stmtsEqb ((Data.core312.body.drop 0).take 1100)
    (((osBody (osCfg 17)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_17_1 : stmtsEqb ((Data.core312.body.drop 1100).take 1100)
    (((osBody (osCfg 17)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_17_2 : stmtsEqb ((Data.core312.body.drop 2200).take 1100)
    (((osBody (osCfg 17)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_17 : OsData 17 := by
  have hl : (osCfg 17).levels.length = 5 := by decide +kernel
  have hb : Data.core312.body.drop 0 = (osBody (osCfg 17)).drop 0 :=
    run_step 1100 0 os_run_17_0 <|
    run_step 1100 1100 os_run_17_1 <|
    run_step 1100 2200 os_run_17_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core312, Program.find?_of_indexOf? (j := 312) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core642, Program.find?_of_indexOf? (j := 642) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core648, Program.find?_of_indexOf? (j := 648) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core644, Program.find?_of_indexOf? (j := 644) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core649, Program.find?_of_indexOf? (j := 649) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core645, Program.find?_of_indexOf? (j := 645) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core650, Program.find?_of_indexOf? (j := 650) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core646, Program.find?_of_indexOf? (j := 646) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core651, Program.find?_of_indexOf? (j := 651) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core647, Program.find?_of_indexOf? (j := 647) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core652, Program.find?_of_indexOf? (j := 652) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
