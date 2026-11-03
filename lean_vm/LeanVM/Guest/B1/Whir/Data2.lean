/-
  LeanVM.Guest.B1.Whir.Data2

  `open_stacked__L2` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 2

`osData_2 : OsData 2`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_2_0 : stmtsEqb ((Data.core296.body.drop 0).take 1100)
    (((osBody (osCfg 2)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_2_1 : stmtsEqb ((Data.core296.body.drop 1100).take 1100)
    (((osBody (osCfg 2)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_2_2 : stmtsEqb ((Data.core296.body.drop 2200).take 1100)
    (((osBody (osCfg 2)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osData_2 : OsData 2 := by
  have hl : (osCfg 2).levels.length = 5 := by decide +kernel
  have hb : Data.core296.body.drop 0 = (osBody (osCfg 2)).drop 0 :=
    run_step 1100 0 os_run_2_0 <|
    run_step 1100 1100 os_run_2_1 <|
    run_step 1100 2200 os_run_2_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core296, Program.find?_of_indexOf? (j := 294) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core438, Program.find?_of_indexOf? (j := 427) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core451, Program.find?_of_indexOf? (j := 440) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core441, Program.find?_of_indexOf? (j := 430) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core452, Program.find?_of_indexOf? (j := 441) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core444, Program.find?_of_indexOf? (j := 433) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core453, Program.find?_of_indexOf? (j := 442) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core447, Program.find?_of_indexOf? (j := 436) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core454, Program.find?_of_indexOf? (j := 443) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core449, Program.find?_of_indexOf? (j := 438) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core455, Program.find?_of_indexOf? (j := 444) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
