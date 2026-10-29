/-
  LeanVM.Guest.B1.Whir.Data13

  `open_stacked__L13` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 13

`osData_13 : OsData 13`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_13_0 : stmtsEqb ((Data.core305.body.drop 0).take 1100)
    (((osBody (osCfg 13)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_13_1 : stmtsEqb ((Data.core305.body.drop 1100).take 1100)
    (((osBody (osCfg 13)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_13_2 : stmtsEqb ((Data.core305.body.drop 2200).take 1100)
    (((osBody (osCfg 13)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_13 : OsData 13 := by
  have hl : (osCfg 13).levels.length = 6 := by decide +kernel
  have hb : Data.core305.body.drop 0 = (osBody (osCfg 13)).drop 0 :=
    run_step 1100 0 os_run_13_0 <|
    run_step 1100 1100 os_run_13_1 <|
    run_step 1100 2200 os_run_13_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core305, Program.find?_of_indexOf? (j := 305) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core576, Program.find?_of_indexOf? (j := 576) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core586, Program.find?_of_indexOf? (j := 586) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core578, Program.find?_of_indexOf? (j := 578) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core587, Program.find?_of_indexOf? (j := 587) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core580, Program.find?_of_indexOf? (j := 580) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core588, Program.find?_of_indexOf? (j := 588) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core582, Program.find?_of_indexOf? (j := 582) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core589, Program.find?_of_indexOf? (j := 589) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core583, Program.find?_of_indexOf? (j := 583) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core590, Program.find?_of_indexOf? (j := 590) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core585, Program.find?_of_indexOf? (j := 585) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core591, Program.find?_of_indexOf? (j := 591) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
