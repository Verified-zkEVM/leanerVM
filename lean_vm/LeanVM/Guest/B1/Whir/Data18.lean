/-
  LeanVM.Guest.B1.Whir.Data18

  `open_stacked__L18` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 18

`osData_18 : OsData 18`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_18_0 : stmtsEqb ((Data.core313.body.drop 0).take 1100)
    (((osBody (osCfg 18)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_18_1 : stmtsEqb ((Data.core313.body.drop 1100).take 1100)
    (((osBody (osCfg 18)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_18_2 : stmtsEqb ((Data.core313.body.drop 2200).take 1100)
    (((osBody (osCfg 18)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_18 : OsData 18 := by
  have hl : (osCfg 18).levels.length = 5 := by decide +kernel
  have hb : Data.core313.body.drop 0 = (osBody (osCfg 18)).drop 0 :=
    run_step 1100 0 os_run_18_0 <|
    run_step 1100 1100 os_run_18_1 <|
    run_step 1100 2200 os_run_18_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core313, Program.find?_of_indexOf? (j := 313) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core653, Program.find?_of_indexOf? (j := 653) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core659, Program.find?_of_indexOf? (j := 659) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core655, Program.find?_of_indexOf? (j := 655) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core660, Program.find?_of_indexOf? (j := 660) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core656, Program.find?_of_indexOf? (j := 656) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core661, Program.find?_of_indexOf? (j := 661) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core657, Program.find?_of_indexOf? (j := 657) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core662, Program.find?_of_indexOf? (j := 662) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core658, Program.find?_of_indexOf? (j := 658) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core663, Program.find?_of_indexOf? (j := 663) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
