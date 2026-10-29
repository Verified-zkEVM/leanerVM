/-
  LeanVM.Guest.B1.Whir.Data14

  `open_stacked__L14` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 14

`osData_14 : OsData 14`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_14_0 : stmtsEqb ((Data.core306.body.drop 0).take 1100)
    (((osBody (osCfg 14)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_14_1 : stmtsEqb ((Data.core306.body.drop 1100).take 1100)
    (((osBody (osCfg 14)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_14 : OsData 14 := by
  have hl : (osCfg 14).levels.length = 4 := by decide +kernel
  have hb : Data.core306.body.drop 0 = (osBody (osCfg 14)).drop 0 :=
    run_step 1100 0 os_run_14_0 <|
    run_step 1100 1100 os_run_14_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core306, Program.find?_of_indexOf? (j := 306) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core592, Program.find?_of_indexOf? (j := 592) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core597, Program.find?_of_indexOf? (j := 597) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core594, Program.find?_of_indexOf? (j := 594) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core598, Program.find?_of_indexOf? (j := 598) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core595, Program.find?_of_indexOf? (j := 595) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core599, Program.find?_of_indexOf? (j := 599) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core596, Program.find?_of_indexOf? (j := 596) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core600, Program.find?_of_indexOf? (j := 600) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
