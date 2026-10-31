/-
  LeanVM.Guest.B1.Whir.Data10

  `open_stacked__L10` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 10

`osData_10 : OsData 10`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_10_0 : stmtsEqb ((Data.core302.body.drop 0).take 1100)
    (((osBody (osCfg 10)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_10_1 : stmtsEqb ((Data.core302.body.drop 1100).take 1100)
    (((osBody (osCfg 10)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_10_2 : stmtsEqb ((Data.core302.body.drop 2200).take 1100)
    (((osBody (osCfg 10)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osData_10 : OsData 10 := by
  have hl : (osCfg 10).levels.length = 5 := by decide +kernel
  have hb : Data.core302.body.drop 0 = (osBody (osCfg 10)).drop 0 :=
    run_step 1100 0 os_run_10_0 <|
    run_step 1100 1100 os_run_10_1 <|
    run_step 1100 2200 os_run_10_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core302, Program.find?_of_indexOf? (j := 302) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core541, Program.find?_of_indexOf? (j := 541) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core548, Program.find?_of_indexOf? (j := 548) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core543, Program.find?_of_indexOf? (j := 543) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core549, Program.find?_of_indexOf? (j := 549) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core544, Program.find?_of_indexOf? (j := 544) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core550, Program.find?_of_indexOf? (j := 550) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core545, Program.find?_of_indexOf? (j := 545) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core551, Program.find?_of_indexOf? (j := 551) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core546, Program.find?_of_indexOf? (j := 546) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core552, Program.find?_of_indexOf? (j := 552) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
