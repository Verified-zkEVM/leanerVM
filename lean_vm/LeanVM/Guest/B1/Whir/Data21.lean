/-
  LeanVM.Guest.B1.Whir.Data21

  `open_stacked__L21` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 21

`osData_21 : OsData 21`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_21_0 : stmtsEqb ((Data.core313.body.drop 0).take 1100)
    (((osBody (osCfg 21)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_21_1 : stmtsEqb ((Data.core313.body.drop 1100).take 1100)
    (((osBody (osCfg 21)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osData_21 : OsData 21 := by
  have hl : (osCfg 21).levels.length = 4 := by decide +kernel
  have hb : Data.core313.body.drop 0 = (osBody (osCfg 21)).drop 0 :=
    run_step 1100 0 os_run_21_0 <|
    run_step 1100 1100 os_run_21_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core313, Program.find?_of_indexOf? (j := 313) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core670, Program.find?_of_indexOf? (j := 670) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core675, Program.find?_of_indexOf? (j := 675) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core672, Program.find?_of_indexOf? (j := 672) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core676, Program.find?_of_indexOf? (j := 676) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core673, Program.find?_of_indexOf? (j := 673) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core677, Program.find?_of_indexOf? (j := 677) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core674, Program.find?_of_indexOf? (j := 674) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core678, Program.find?_of_indexOf? (j := 678) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
