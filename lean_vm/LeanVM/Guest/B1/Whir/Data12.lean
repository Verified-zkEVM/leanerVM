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
theorem os_run_12_0 : stmtsEqb ((Data.core304.body.drop 0).take 1100)
    (((osBody (osCfg 12)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_12_1 : stmtsEqb ((Data.core304.body.drop 1100).take 1100)
    (((osBody (osCfg 12)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_12_2 : stmtsEqb ((Data.core304.body.drop 2200).take 1100)
    (((osBody (osCfg 12)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osData_12 : OsData 12 := by
  have hl : (osCfg 12).levels.length = 5 := by decide +kernel
  have hb : Data.core304.body.drop 0 = (osBody (osCfg 12)).drop 0 :=
    run_step 1100 0 os_run_12_0 <|
    run_step 1100 1100 os_run_12_1 <|
    run_step 1100 2200 os_run_12_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core304, Program.find?_of_indexOf? (j := 304) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core564, Program.find?_of_indexOf? (j := 564) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core571, Program.find?_of_indexOf? (j := 571) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core566, Program.find?_of_indexOf? (j := 566) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core572, Program.find?_of_indexOf? (j := 572) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core567, Program.find?_of_indexOf? (j := 567) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core573, Program.find?_of_indexOf? (j := 573) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core568, Program.find?_of_indexOf? (j := 568) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core574, Program.find?_of_indexOf? (j := 574) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core569, Program.find?_of_indexOf? (j := 569) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core575, Program.find?_of_indexOf? (j := 575) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
