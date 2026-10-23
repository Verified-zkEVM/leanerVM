/-
  LeanVM.Guest.B1.Whir.Data20

  `open_stacked__L20` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 20

`osData_20 : OsData 20`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_20_0 : stmtsEqb ((Data.core315.body.drop 0).take 1100)
    (((osBody (osCfg 20)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_20_1 : stmtsEqb ((Data.core315.body.drop 1100).take 1100)
    (((osBody (osCfg 20)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_20_2 : stmtsEqb ((Data.core315.body.drop 2200).take 1100)
    (((osBody (osCfg 20)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_20 : OsData 20 := by
  have hl : (osCfg 20).levels.length = 6 := by decide +kernel
  have hb : Data.core315.body.drop 0 = (osBody (osCfg 20)).drop 0 :=
    run_step 1100 0 os_run_20_0 <|
    run_step 1100 1100 os_run_20_1 <|
    run_step 1100 2200 os_run_20_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core315, Program.find?_of_indexOf? (j := 315) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core675, Program.find?_of_indexOf? (j := 675) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core685, Program.find?_of_indexOf? (j := 685) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core677, Program.find?_of_indexOf? (j := 677) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core686, Program.find?_of_indexOf? (j := 686) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core679, Program.find?_of_indexOf? (j := 679) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core687, Program.find?_of_indexOf? (j := 687) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core681, Program.find?_of_indexOf? (j := 681) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core688, Program.find?_of_indexOf? (j := 688) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core682, Program.find?_of_indexOf? (j := 682) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core689, Program.find?_of_indexOf? (j := 689) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core684, Program.find?_of_indexOf? (j := 684) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core690, Program.find?_of_indexOf? (j := 690) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
