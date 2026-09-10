module

public import LeanerVM.Protocol.Stacking
public import LeanerVM.Parameters.Field
meta import LeanerVM.Protocol.Stacking
meta import LeanerVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Protocol Layer 1 tests: aligned stacking

Three blocks of heights 4, 2, 1, largest first, stacked on three variables: the offsets and
selectors decided in the kernel, the stack's entries, and the selection identity `stack_eval`
checked numerically for every block with two pad values.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

/-- Blocks of heights 4, 2, 1 with values `[1, 2, 3, 4]`, `[5, 6]`, `[7]`. -/
def blocks : Blocks K where
  n := 3
  size := ![2, 1, 0]
  values := fun b ↦ match b with
    | 0 => (#v[1, 2, 3, 4] : CMlPolynomialEval K 2)
    | 1 => (#v[5, 6] : CMlPolynomialEval K 1)
    | 2 => (#v[7] : CMlPolynomialEval K 0)
  descending := by
    show ∀ a b : Fin 3, a ≤ b → ![2, 1, 0] b ≤ ![2, 1, 0] a
    decide

/-- The blocks fit on three variables. -/
theorem blocks_total_le : blocks.total ≤ 2 ^ 3 := by decide

-- Offsets are prefix sums of the heights; selectors are the offsets shifted by the sizes.
example : blocks.total = 7 := by decide
example : blocks.offset (1 : Fin 3) = 4 := by decide
example : blocks.offset (2 : Fin 3) = 6 := by decide
example : (blocks.selector blocks_total_le (0 : Fin 3)).val = 0 := by decide
example : (blocks.selector blocks_total_le (1 : Fin 3)).val = 2 := by decide
example : (blocks.selector blocks_total_le (2 : Fin 3)).val = 6 := by decide

/-- The stack with pad `0`. -/
def stack0 : CMlPolynomialEval K 3 := blocks.stackAt 3 0

-- The stack lays the blocks out in order and pads the last entry.
#guard stack0 = #v[1, 2, 3, 4, 5, 6, 7, 0]
#guard blocks.stackAt 3 1 = #v[1, 2, 3, 4, 5, 6, 7, 1]

-- `stack_eval` numerically: block 0 at `(9, 11)`, with either pad.
#guard evalMle stack0
    (Vector.cast (by decide) ((#v[9, 11] : Vector K 2) ++ (boolVec (blocks.selector blocks_total_le (0 : Fin 3)) : Vector K _))) =
  evalMle (#v[1, 2, 3, 4] : CMlPolynomialEval K 2) #v[9, 11]
#guard evalMle (blocks.stackAt 3 1)
    (Vector.cast (by decide) ((#v[9, 11] : Vector K 2) ++ (boolVec (blocks.selector blocks_total_le (0 : Fin 3)) : Vector K _))) =
  evalMle (#v[1, 2, 3, 4] : CMlPolynomialEval K 2) #v[9, 11]
-- Block 1 at `13`, block 2 at the empty point.
#guard evalMle stack0
    (Vector.cast (by decide) ((#v[13] : Vector K 1) ++ (boolVec (blocks.selector blocks_total_le (1 : Fin 3)) : Vector K _))) =
  evalMle (#v[5, 6] : CMlPolynomialEval K 1) #v[13]
#guard evalMle stack0
    (Vector.cast (by decide) ((#v[] : Vector K 0) ++ (boolVec (blocks.selector blocks_total_le (2 : Fin 3)) : Vector K _))) =
  7
-- Mutation: block 1's selector with block 0's point shape is a different point and answers
-- differently from block 0.
#guard evalMle stack0
    (Vector.cast (by decide) ((#v[13] : Vector K 1) ++ (boolVec (blocks.selector blocks_total_le (1 : Fin 3)) : Vector K _))) ≠
  evalMle (#v[1, 2, 3, 4] : CMlPolynomialEval K 2) #v[13, 0]

end
end LeanerVMTests.Protocol
