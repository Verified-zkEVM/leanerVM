/-
  LeanVM.Guest.B1.Whir.Data16

  `open_stacked__L16` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 16

`osData_16 : OsData 16`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_16_0 : stmtsEqb ((Data.core308.body.drop 0).take 1100)
    (((osBody (osCfg 16)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_16_1 : stmtsEqb ((Data.core308.body.drop 1100).take 1100)
    (((osBody (osCfg 16)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_16_2 : stmtsEqb ((Data.core308.body.drop 2200).take 1100)
    (((osBody (osCfg 16)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osData_16 : OsData 16 := by
  have hl : (osCfg 16).levels.length = 5 := by decide +kernel
  have hb : Data.core308.body.drop 0 = (osBody (osCfg 16)).drop 0 :=
    run_step 1100 0 os_run_16_0 <|
    run_step 1100 1100 os_run_16_1 <|
    run_step 1100 2200 os_run_16_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core308, Program.find?_of_indexOf? (j := 308) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core610, Program.find?_of_indexOf? (j := 610) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core616, Program.find?_of_indexOf? (j := 616) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core612, Program.find?_of_indexOf? (j := 612) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core617, Program.find?_of_indexOf? (j := 617) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core613, Program.find?_of_indexOf? (j := 613) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core618, Program.find?_of_indexOf? (j := 618) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core614, Program.find?_of_indexOf? (j := 614) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core619, Program.find?_of_indexOf? (j := 619) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core615, Program.find?_of_indexOf? (j := 615) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core620, Program.find?_of_indexOf? (j := 620) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
