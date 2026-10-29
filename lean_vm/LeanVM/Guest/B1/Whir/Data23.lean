/-
  LeanVM.Guest.B1.Whir.Data23

  `open_stacked__L23` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 23

`osData_23 : OsData 23`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_23_0 : stmtsEqb ((Data.core315.body.drop 0).take 1100)
    (((osBody (osCfg 23)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_23_1 : stmtsEqb ((Data.core315.body.drop 1100).take 1100)
    (((osBody (osCfg 23)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_23_2 : stmtsEqb ((Data.core315.body.drop 2200).take 1100)
    (((osBody (osCfg 23)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_23 : OsData 23 := by
  have hl : (osCfg 23).levels.length = 5 := by decide +kernel
  have hb : Data.core315.body.drop 0 = (osBody (osCfg 23)).drop 0 :=
    run_step 1100 0 os_run_23_0 <|
    run_step 1100 1100 os_run_23_1 <|
    run_step 1100 2200 os_run_23_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core315, Program.find?_of_indexOf? (j := 315) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core688, Program.find?_of_indexOf? (j := 688) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core694, Program.find?_of_indexOf? (j := 694) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core690, Program.find?_of_indexOf? (j := 690) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core695, Program.find?_of_indexOf? (j := 695) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core691, Program.find?_of_indexOf? (j := 691) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core696, Program.find?_of_indexOf? (j := 696) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core692, Program.find?_of_indexOf? (j := 692) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core697, Program.find?_of_indexOf? (j := 697) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core693, Program.find?_of_indexOf? (j := 693) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core698, Program.find?_of_indexOf? (j := 698) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
