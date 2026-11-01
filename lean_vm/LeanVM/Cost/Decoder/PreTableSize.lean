module

public import LeanVM.Cost.Decoder.PreTable

/-!
# The precondition's test: its size in the decoder's program, by evaluation

As `Cost/ExtractorSize.lean` measures the extractor's program (`MachineValue.size`,
`Term.size`, `Statement/CostMachine.lean`), a module of its own that imports only the compiled
functions:

* **`preTable_size`**: the literal table of the functions' preconditions
  (`Guest.Fast.preTable`, `879` entries, `424` of them not `none`) is a value of size `5129`;
* `preTableC_body_size`: the body that builds it (`preTableC`, its constructors, each natural
  literal a term `Term.val`) has size `6864`, what it adds to the decoder's program (and `2` for
  its index);
* `preTestBodies_size`: the bodies the compiled test adds past the decoder's witness (`preTestAtC`'s
  dependencies from `powBelowAtC` on, `21` of them, `Sym.val` among them) have size `358`;
* `genPowsBodies_size`: the powers table's bodies (`genPowsC`, `squaresFromC`), built once and
  passed to the test, have size `84`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Guest.Fast

public section

/-- **The table's size**: `5129`. -/
theorem preTable_size : (encodeValue preTable).size = 5129 := by
  -- an array's encoding maps `Array.map`, whose body the kernel does not see here: by its list
  show (MachineValue.arr (preTable.map encodeValue)).size = 5129
  rw [MachineValue.size, Array.toList_map]
  decide +kernel

/-- The size of the body that builds the table: `6864`. -/
theorem preTableC_body_size : preTableC.costBody.size = 6864 := by decide +kernel

/-- The sizes of the test's bodies: `358`, `21` bodies. -/
theorem preTestBodies_size :
    ((preTestAtC.costDeps.filter fun p ↦ decide (powBelowAtC.costIdx ≤ p.1)).map
      fun p ↦ p.2.size).sum = 358 ∧
    (preTestAtC.costDeps.filter fun p ↦ decide (powBelowAtC.costIdx ≤ p.1)).length = 21 := by
  decide +kernel

/-- The sizes of the powers table's bodies: `84`, `2` bodies. -/
theorem genPowsBodies_size :
    (genPowsC.costDeps.map fun p ↦ p.2.size).sum = 84 ∧ genPowsC.costDeps.length = 2 := by
  decide +kernel

end

end LeanVM.Cost.Decoder
