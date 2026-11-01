import LeanVM.Cost.Efficient
import LeanVM.Cost.Samples.MsStep

/-!
# Tests: the entry of the extractor's program, and a program's size by evaluation

* the entry body (`entryBody`) destructures its input, calls its function on the four fields and
  unwraps the optional output, at `9` steps more than the call, here with a stand-in callee;
* a program built from a compiled function's bodies (`msStepK`, one Mulders–Storjohann step) and
  the entry: its bodies held (`includes_ofList`, the indices' distinctness decided) and its size
  bounded by evaluating its bodies' sizes (`size_ofList_le`, decided by the kernel), as the
  extractor's program's will be.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Cost.Samples

/-- A stand-in callee: `some` of its first argument. -/
def standIn : Term := .ctor 1 [.var 0]

/-- The entry calling the stand-in. -/
def entryProgram : Program := Program.ofList [(0, entryBody 1), (1, standIn)]

#guard (run entryProgram 10 (.ctor 0 [.nat 5, .nat 6, .nat 7, .nat 8])).map (·.1) == some (.nat 5)
-- the stand-in's body costs `3` (a variable, a constructor of one field), the entry `9` more
#guard (run entryProgram 10 (.ctor 0 [.nat 5, .nat 6, .nat 7, .nat 8])).map (·.2) == some 12
#guard outputWithin entryProgram (.ctor 0 [.nat 5, .nat 6, .nat 7, .nat 8]) 12 == some (.nat 5)
#guard outputWithin entryProgram (.ctor 0 [.nat 5, .nat 6, .nat 7, .nat 8]) 11 == none

/-- The bodies of one Mulders–Storjohann step, and the entry calling it. -/
def msProgramBodies : List (ℕ × Term) := (0, entryBody 1) :: msStepK.costDeps

theorem msProgram_includes : Includes (Program.ofList msProgramBodies) msStepK.costDeps :=
  (includes_ofList msProgramBodies (by decide +kernel)).mono fun _ hp ↦ List.mem_cons_of_mem _ hp

theorem msProgram_size : (Program.ofList msProgramBodies).size ≤ 2 ^ 10 :=
  (size_ofList_le msProgramBodies).trans (by decide +kernel)

/-- info: 'LeanVMTests.Cost.msProgram_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms msProgram_size

end LeanVMTests.Cost
