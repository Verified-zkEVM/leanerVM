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
theorem os_run_14_0 : stmtsEqb ((Data.core309.body.drop 0).take 1100)
    (((osBody (osCfg 14)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_14_1 : stmtsEqb ((Data.core309.body.drop 1100).take 1100)
    (((osBody (osCfg 14)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_14 : OsData 14 := by
  have hl : (osCfg 14).levels.length = 4 := by decide +kernel
  have hb : Data.core309.body.drop 0 = (osBody (osCfg 14)).drop 0 :=
    run_step 1100 0 os_run_14_0 <|
    run_step 1100 1100 os_run_14_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core309, Program.find?_of_indexOf? (j := 309) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core613, Program.find?_of_indexOf? (j := 613) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core618, Program.find?_of_indexOf? (j := 618) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core615, Program.find?_of_indexOf? (j := 615) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core619, Program.find?_of_indexOf? (j := 619) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core616, Program.find?_of_indexOf? (j := 616) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core620, Program.find?_of_indexOf? (j := 620) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core617, Program.find?_of_indexOf? (j := 617) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core621, Program.find?_of_indexOf? (j := 621) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
