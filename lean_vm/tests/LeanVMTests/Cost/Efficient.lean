import LeanVM.Cost.Efficient

/-!
# Tests: the entry of the extractor's program, and a program's size by evaluation

* the entry body (`entryBody`) destructures its input, calls its function on the four fields and
  unwraps the optional output, at `9` steps more than the call, here with a stand-in callee;
* a program built from a compiled function's bodies (`invItohTsujii.c9`, the inverse in `K`, the
  extractor's) and the entry: its size bounded by evaluating its bodies' sizes (`size_ofList_le`,
  decided by the kernel);
* the extractor's program (`extractorProgram`): `698` bodies, the entry's and the compiled
  extractor's, the largest index `710`, its size `13813` (`Cost/ExtractorSize.lean` proves at
  most `14400`, `extractorSizeBound`, by evaluating the program itself);
* the axioms of `extractorOf_extractorProgram`, `extractorOf extractorProgram =
  transcriptExtractor`.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Cost.Extractor

/-- A stand-in callee: `some` of its first argument. -/
def standIn : Term := .ctor 1 [.var 0]

/-- The entry calling the stand-in. -/
def entryProgram : MachineProgram := MachineProgram.ofList [(0, entryBody 1), (1, standIn)]

#guard (run entryProgram 10 (.ctor 0 [.nat 5, .nat 6, .nat 7, .nat 8])).map (·.1) == some (.nat 5)
-- the stand-in's body costs `3` (a variable, a constructor of one field), the entry `9` more
#guard (run entryProgram 10 (.ctor 0 [.nat 5, .nat 6, .nat 7, .nat 8])).map (·.2) == some 12
#guard outputWithin entryProgram (.ctor 0 [.nat 5, .nat 6, .nat 7, .nat 8]) 12 == some (.nat 5)
#guard outputWithin entryProgram (.ctor 0 [.nat 5, .nat 6, .nat 7, .nat 8]) 11 == none

/-- The bodies of the inverse in `K`, and the entry calling it. -/
def invProgramBodies : List (ℕ × Term) :=
  (0, entryBody 1) :: LeanVM.Cost.Auto.BF64.invItohTsujii.c9.costDeps

theorem invProgram_size : (MachineProgram.ofList invProgramBodies).size ≤ 2 ^ 10 :=
  (size_ofList_le invProgramBodies).trans (by decide +kernel)

/-- info: 'LeanVMTests.Cost.invProgram_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms invProgram_size

/-! ## The extractor's program -/

#guard extractorProgramBodies.length == 698
#guard (extractorProgramBodies.map (·.1)).foldr max 0 == 710
#guard extractorProgram.size == 13813
#guard (extractorProgramBodies.map fun p ↦ p.2.size).sum == 13787

/-- info: 'LeanVM.Cost.extractorOf_extractorProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms extractorOf_extractorProgram

end LeanVMTests.Cost
