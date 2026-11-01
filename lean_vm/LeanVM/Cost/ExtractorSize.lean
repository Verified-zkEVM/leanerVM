module

public import LeanVM.Cost.ExtractorProgram
-- the body of a closure compiled under an induction hypothesis (`prefixesNF`'s fold closure,
-- function `202`) is not exposed (`localClosure` adds it with `addAndCompile`): without it the
-- kernel's evaluation of the sizes is stuck
import all LeanVM.Cost.Extractor.GsRun

/-!
# The extractor's program: its indices and its size, by evaluation

A firewall (`AGENTS.md`): the two kernel evaluations over the compiled extractor's `512` bodies,
in a module of their own that imports only the program's definition, so that no edit of a proof
rebuilds them.

* `extractorProgram_indices_increasing`: the bodies' indices are distinct (they increase from the
  entry's `0`: the compiler allocates indices from `1`, and sorts each dependency list);
* **`extractorProgram_size_le_measured`**: the program's size is at most `11515`, the bodies' sizes
  (`10465`) plus two per index (`525` of them, `size_ofList_le`). Its exact size is `10491`
  (`13` indices without a body, a literal `0` each; `LeanVMTests/Cost/Efficient.lean`).
  `LeanVM.extractorSizeBound` (`Statement/CostMachine.lean`) is `2^15`, twice the exact size
  rounded up to a power of two.
-/

namespace LeanVM.Cost

open LeanVM.Cost.Extractor

public section

/-- The bodies' indices increase: the entry's `0`, then the compiled extractor's. -/
theorem extractorProgram_indices_increasing :
    increasingFrom 0 (extractorC.costDeps.map (·.1)) = true := by
  decide +kernel

/-- The bound of `size_ofList_le` on the program's size, evaluated: the bodies' sizes (`10465`)
plus two per index (`525`). -/
theorem extractorProgramBodies_size_bound :
    (extractorProgramBodies.map fun p ↦ p.2.size).sum +
      2 * ((extractorProgramBodies.map (·.1)).foldr max 0 + 1) ≤ 11515 := by
  decide +kernel

/-- **The program's size**, evaluated: at most `11515`. -/
theorem extractorProgram_size_le_measured : extractorProgram.size ≤ 11515 :=
  (size_ofList_le extractorProgramBodies).trans extractorProgramBodies_size_bound

end

end LeanVM.Cost
