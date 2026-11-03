/-
  LeanVM.Guest.B1.Whir.Data3

  `open_stacked__L3` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 3

`osData_3 : OsData 3`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_3_0 : stmtsEqb ((Data.core297.body.drop 0).take 1100)
    (((osBody (osCfg 3)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_3_1 : stmtsEqb ((Data.core297.body.drop 1100).take 1100)
    (((osBody (osCfg 3)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_3_2 : stmtsEqb ((Data.core297.body.drop 2200).take 1100)
    (((osBody (osCfg 3)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osData_3 : OsData 3 := by
  have hl : (osCfg 3).levels.length = 5 := by decide +kernel
  have hb : Data.core297.body.drop 0 = (osBody (osCfg 3)).drop 0 :=
    run_step 1100 0 os_run_3_0 <|
    run_step 1100 1100 os_run_3_1 <|
    run_step 1100 2200 os_run_3_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core297, Program.find?_of_indexOf? (j := 297) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core457, Program.find?_of_indexOf? (j := 457) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core470, Program.find?_of_indexOf? (j := 470) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core460, Program.find?_of_indexOf? (j := 460) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core471, Program.find?_of_indexOf? (j := 471) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core463, Program.find?_of_indexOf? (j := 463) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core472, Program.find?_of_indexOf? (j := 472) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core466, Program.find?_of_indexOf? (j := 466) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core473, Program.find?_of_indexOf? (j := 473) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core468, Program.find?_of_indexOf? (j := 468) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core474, Program.find?_of_indexOf? (j := 474) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
