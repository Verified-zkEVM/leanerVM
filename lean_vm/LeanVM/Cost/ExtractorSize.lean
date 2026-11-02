module

public import LeanVM.Cost.ExtractorProgram

/-!
# The extractor's program: its indices and its size, by evaluation

A firewall (`AGENTS.md`): the kernel evaluations over the compiled extractor's program, in a
module of their own that imports only the program's definition, so that no edit of a proof
rebuilds them.

* `extractorProgram_indices_increasing`: the bodies' indices are distinct (they increase from the
  entry's `0`: the compiler allocates indices from `1`, and sorts each dependency list);
* **`extractorProgram_size_le_measured`**: the program's size is at most `11000`, evaluated on the
  program itself. Its exact size is `10479` (`LeanVMTests/Cost/Efficient.lean`): the bodies' sizes
  (`10455`: `511` compiled bodies and the entry, each natural literal counted by its limbs) and
  `12` indices without a body, a literal `0` of size `2` each, `524` indices in all. The bound of
  `size_ofList_le`, two per index on top of the bodies' sizes (`11503`), is too loose for
  `LeanVM.extractorSizeBound` (`11000`, `Statement/CostMachine.lean`).
-/

namespace LeanVM.Cost

open LeanVM.Cost.Extractor

public section

/-- The bodies' indices increase: the entry's `0`, then the compiled extractor's. -/
theorem extractorProgram_indices_increasing :
    increasingFrom 0 (extractorC.costDeps.map (·.1)) = true := by
  decide +kernel

-- The kernel builds the program's array: deeper than the default recursion depth.
set_option maxRecDepth 100000 in
/-- **The program's size**, evaluated: at most `11000` (exactly `10479`). -/
theorem extractorProgram_size_le_measured : extractorProgram.size ≤ 11000 := by
  decide +kernel

end

end LeanVM.Cost
