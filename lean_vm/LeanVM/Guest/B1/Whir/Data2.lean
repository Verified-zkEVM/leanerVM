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
theorem os_run_2_0 : stmtsEqb ((Data.core297.body.drop 0).take 1100)
    (((osBody (osCfg 2)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_2_1 : stmtsEqb ((Data.core297.body.drop 1100).take 1100)
    (((osBody (osCfg 2)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_2_2 : stmtsEqb ((Data.core297.body.drop 2200).take 1100)
    (((osBody (osCfg 2)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_2 : OsData 2 := by
  have hl : (osCfg 2).levels.length = 5 := by decide +kernel
  have hb : Data.core297.body.drop 0 = (osBody (osCfg 2)).drop 0 :=
    run_step 1100 0 os_run_2_0 <|
    run_step 1100 1100 os_run_2_1 <|
    run_step 1100 2200 os_run_2_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core297, Program.find?_of_indexOf? (j := 297) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core448, Program.find?_of_indexOf? (j := 448) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core461, Program.find?_of_indexOf? (j := 461) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core451, Program.find?_of_indexOf? (j := 451) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core462, Program.find?_of_indexOf? (j := 462) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core454, Program.find?_of_indexOf? (j := 454) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core463, Program.find?_of_indexOf? (j := 463) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core457, Program.find?_of_indexOf? (j := 457) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core464, Program.find?_of_indexOf? (j := 464) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core459, Program.find?_of_indexOf? (j := 459) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core465, Program.find?_of_indexOf? (j := 465) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
