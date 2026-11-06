import LeanerVM.Semantics.Blake2sOutput

/-!
# Layer 10 tests: the output cells of a compression

The cell encoding round-trips on concrete words, the compression of the all-zero cells has output
cells, and those cells are not zero: the digest of zero input is a nonzero pair, so the existence
the `BLAKE2S` fill frame relies on is not the trivial one.
-/

namespace LeanerVMTests.Semantics.Blake2sOutput

open LeanerVM.Parameters LeanerVM.Semantics

/-- Four concrete words survive `wordsCell` then `cellWords`. -/
example : (cellWords (wordsCell #v[1, 0xdeadbeef, 0xffffffff, 0x80000000])).toList =
    [1, 0xdeadbeef, 0xffffffff, 0x80000000] := by
  decide +kernel

/-- The general statement, at a vector. -/
example (w : Vector UInt32 4) : cellWords (wordsCell w) = w := cellWords_wordsCell w

/-- A cell holding four words is canonical: its top limb is zero. -/
example (w : Vector UInt32 4) : IsCanonical128 (wordsCell w) := isCanonical128_wordsCell w

/-- The compression of the all-zero cells has output cells. -/
example : ∃ out0 out1 : E, CompressCells ![0, 0, 0, 0] 0 0 out0 out1 0 := compressCells_zero

/-- And they are not the zero cells: the digest of zero input is not zero. -/
example : ¬ CompressCells ![0, 0, 0, 0] 0 0 0 0 0 := by
  decide +kernel

end LeanerVMTests.Semantics.Blake2sOutput
