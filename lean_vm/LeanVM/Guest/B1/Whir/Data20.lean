/-
  LeanVM.Guest.B1.Whir.Data20

  `open_stacked__L20` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 20

`osData_20 : OsData 20`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_20_0 : stmtsEqb ((Data.core312.body.drop 0).take 1100)
    (((osBody (osCfg 20)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_20_1 : stmtsEqb ((Data.core312.body.drop 1100).take 1100)
    (((osBody (osCfg 20)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_20_2 : stmtsEqb ((Data.core312.body.drop 2200).take 1100)
    (((osBody (osCfg 20)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_20 : OsData 20 := by
  have hl : (osCfg 20).levels.length = 6 := by decide +kernel
  have hb : Data.core312.body.drop 0 = (osBody (osCfg 20)).drop 0 :=
    run_step 1100 0 os_run_20_0 <|
    run_step 1100 1100 os_run_20_1 <|
    run_step 1100 2200 os_run_20_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core312, Program.find?_of_indexOf? (j := 312) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core654, Program.find?_of_indexOf? (j := 654) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core664, Program.find?_of_indexOf? (j := 664) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core656, Program.find?_of_indexOf? (j := 656) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core665, Program.find?_of_indexOf? (j := 665) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core658, Program.find?_of_indexOf? (j := 658) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core666, Program.find?_of_indexOf? (j := 666) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core660, Program.find?_of_indexOf? (j := 660) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core667, Program.find?_of_indexOf? (j := 667) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core661, Program.find?_of_indexOf? (j := 661) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core668, Program.find?_of_indexOf? (j := 668) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core663, Program.find?_of_indexOf? (j := 663) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core669, Program.find?_of_indexOf? (j := 669) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
