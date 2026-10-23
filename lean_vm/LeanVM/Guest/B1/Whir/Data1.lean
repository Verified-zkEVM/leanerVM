/-
  LeanVM.Guest.B1.Whir.Data1

  `open_stacked__L1` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 1

`osData_1 : OsData 1`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_1_0 : stmtsEqb ((Data.core296.body.drop 0).take 1100)
    (((osBody (osCfg 1)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_1_1 : stmtsEqb ((Data.core296.body.drop 1100).take 1100)
    (((osBody (osCfg 1)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_1_2 : stmtsEqb ((Data.core296.body.drop 2200).take 1100)
    (((osBody (osCfg 1)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem osData_1 : OsData 1 := by
  have hl : (osCfg 1).levels.length = 4 := by decide +kernel
  have hb : Data.core296.body.drop 0 = (osBody (osCfg 1)).drop 0 :=
    run_step 1100 0 os_run_1_0 <|
    run_step 1100 1100 os_run_1_1 <|
    run_step 1100 2200 os_run_1_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core296, Program.find?_of_indexOf? (j := 296) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact ⟨⟨Data.core432, Program.find?_of_indexOf? (j := 432) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core443, Program.find?_of_indexOf? (j := 443) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core435, Program.find?_of_indexOf? (j := 435) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core444, Program.find?_of_indexOf? (j := 444) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core438, Program.find?_of_indexOf? (j := 438) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core445, Program.find?_of_indexOf? (j := 445) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩
  · exact ⟨⟨Data.core441, Program.find?_of_indexOf? (j := 441) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
      ⟨Data.core446, Program.find?_of_indexOf? (j := 446) (by decide +kernel) rfl,
      by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

end
end LeanVM.Guest.B1.Whir
