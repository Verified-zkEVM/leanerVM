import LeanerVM.Semantics.ReadHints
import LeanerVMTests.Semantics.Cycle

/-!
# Address-hint acceptance and coverage

Wrong, incomplete, duplicate, empty and out-of-range hints cannot change acceptance. A
candidate is verified before use, and a cache miss must use the exhaustive fallback.
-/

namespace LeanerVMTests.Semantics.ReadHints

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Checker LeanerVMTests.Semantics.Cycle

#guard addressIndexWithHints 4 (hintIndices 4 [0, 0, 3, 16, 1000]) (gpow 3) =
  some ⟨3, by decide⟩
#guard addressIndexWithHints 4 (hintIndices 4 [0, 3]) (gpow 2) = some ⟨2, by decide⟩
#guard addressIndexWithHints 4 (hintIndices 4 [16, 1000]) (gpow 15) = some ⟨15, by decide⟩
#guard addressIndexWithHints 4 [] 0 = none
#guard addressIndexWithHints 4 (hintIndices 4 [0, 1]) (gpow 16) = none
#guard checkFillerRowsWithHints loopProgram loopImage (hintIndices 1 [1000]) [Regs.initial]

/-- The equivalence also covers completely useless hints, including duplicate entries. -/
example : checkFillerRowsWithHints loopProgram loopImage (hintIndices 1 [1000, 1, 1])
    [Regs.initial] = checkFillerRows loopProgram loopImage [Regs.initial] :=
  checkFillerRowsWithHints_eq (by decide) _ _ _ _

end LeanerVMTests.Semantics.ReadHints
