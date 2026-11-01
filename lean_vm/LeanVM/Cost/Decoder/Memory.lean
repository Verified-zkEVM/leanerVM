module

public import LeanVM.Cost.Decoder.Witness
public import LeanVM.Guest.Fast.DiscreteLog

/-!
# The guest decoder's compiled chain: the memory's reader and the cursor's length

* **The reader** `Located.readTable memT L a`: the word at address `a`, through the sorted table
  of the memory's `2^κ` addresses (the extractor's `gLogTable`), the memory an array
  (`MemoryImage κ` as data);
* **the cursor's length** (`cursorLenWith discreteLog`, `Guest/Fast/DiscreteLog.lean`): a
  child's proof's stream length off two cells, by the discrete logarithm.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Located LeanVM.Guest.Fast

@[expose] public section

cost_compile readTableC := readTable

/-- The cursor's length by the discrete logarithm. -/
def cursorLength (p q : E) : ℕ := cursorLenWith LeanVM.Extraction.Fast.discreteLog p q

cost_compile limbQuotC := limbQuot
cost_compile cursorLengthC := cursorLength

end

end LeanVM.Cost.Decoder
