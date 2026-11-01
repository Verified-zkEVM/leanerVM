module

public import LeanVM.Cost.FastLib
public import LeanVM.Protocol.Extraction.Fast.RunVec
public import LeanVM.Protocol.Extraction.Fast.Extract
import all LeanVM.Protocol.Extraction.Fast.RunVec
import all LeanVM.Protocol.Extraction.Fast.AfterRoot
import all LeanVM.Protocol.Extraction.Fast.Extract
import all Statement.Extractor

/-!
# The candidate runner and the fast path, compiled

`candidateRunner prog input layout` (`Fast/RunVec.lean`: the address tables, the final registers
and the step cap built once, then per stack the boundary check `boundaryOfStack`, the memory
vector `memoryVec` and the halting loop `haltLoopVec`, Keccak-f inside the instructions) and
`fastStacksFast` (the fast path: each lane's word read as a codeword, `Fast/Extract.lean`).

The runner does not compile yet: the projection `Placement.index` (in `memoryVec`,
`memoryImageLite`) has no translation rule; reported to the compiler's owner.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast
open LeanVM.Protocol.Compile LeanVM.Semantics LeanVM.Cost.FastLib

public section

cost_enc LeanVM.Extraction.Fast.LayoutLite

/-- A column's stack index, the default placement's `0` where none is placed. -/
def placementIndexLite (layout : LayoutLite) (column : ℕ) : ℕ :=
  match layout.placements.getD column none with
  | some p => p.index
  | none => 0

theorem placement_index_eq (layout : LayoutLite) (column : ℕ) :
    (layout.placement column).index = placementIndexLite layout column := by
  unfold LayoutLite.placement placementIndexLite
  cases layout.placements.getD column none <;> rfl

cost_rewrite placement_index_eq

cost_compile fastStacksFastC := fastStacksFast

/-- The fast path on the committed word as the extractor reads it (`leafAt`). -/
@[expose] def fastStacksOfLeaves (μ R : ℕ) (leaves : Array (List K)) (h w : ℕ) :
    List (Vector K (2 ^ μ)) :=
  fastStacksFast μ R (leafAt leaves h w)

cost_compile fastStacksOfLeavesC := fastStacksOfLeaves

set_option maxHeartbeats 20000000 in
cost_compile candidateRunnerC := candidateRunner

end

end LeanVM.Cost.Extractor
