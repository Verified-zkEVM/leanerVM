/-
  LeanerVM.Semantics.Blake2sOutput

  The output cells of a compression exist: the cell encoding is invertible, so `CompressCells` is
  satisfiable on any canonical inputs.
-/

module

public import LeanerVM.Semantics.Blake2s

/-!
# The output of a compression

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), over Layer 1's cell encoding.
Category A. `CompressCells` says the two output cells hold the compression of the message,
chaining-value and metadata cells. A `BLAKE2S` fill block runs on cells nobody writes, so the
padded image must hold, in its frame, output cells that satisfy it: it needs only that they exist,
never their value. `cellWords_wordsCell` says the words of the cell holding four words are those
four words (Layer 1 has the other direction, `wordsCell_cellWords`), and `compressCells_exists`
builds the two output cells from the words of the compression.

The lemmas are here and not in `LeanerVM.Semantics.Blake2s` so that Layer 1 is untouched.

## Wrong readings excluded

* The output cells are canonical (`isCanonical128_wordsCell`): `CompressCells` requires all nine
  cells to be, the two outputs included (roadmap acceptance test 12).
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-- Joining a low and a high word and splitting the result returns the low word. -/
private theorem lowWord_ofWords (lo hi : UInt32) : lowWord (ofWords lo hi) = lo := by
  unfold lowWord ofWords
  rw [BF64.toBitVec_ofBitVec, BitVec.extractLsb'_append_eq_right]

/-- Joining a low and a high word and splitting the result returns the high word. -/
private theorem highWord_ofWords (lo hi : UInt32) : highWord (ofWords lo hi) = hi := by
  unfold highWord ofWords
  rw [BF64.toBitVec_ofBitVec, BitVec.extractLsb'_append_eq_left]

/-- `wordsCell` is a right inverse of `cellWords`: the words of the cell holding four words are
those four words. -/
theorem cellWords_wordsCell (w : Vector UInt32 4) : cellWords (wordsCell w) = w := by
  simp only [cellWords, wordsCell, limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    lowWord_ofWords, highWord_ofWords]
  ext i hi
  interval_cases i <;> rfl

/-- A cell holding four words is canonical. -/
theorem isCanonical128_wordsCell (w : Vector UInt32 4) : IsCanonical128 (wordsCell w) := by
  show (wordsCell w).limb 2 = 0
  simp only [wordsCell, limb_ofLimbs]
  rfl

/-- Every compression has output cells: on canonical inputs, the two cells holding the words of the
compression satisfy `CompressCells`. -/
theorem compressCells_exists (m : Fin 4 → E) (cv0 cv1 md : E) (hm : ∀ i, IsCanonical128 (m i))
    (hcv0 : IsCanonical128 cv0) (hcv1 : IsCanonical128 cv1) (hmd : IsCanonical128 md) :
    ∃ out0 out1 : E, CompressCells m cv0 cv1 out0 out1 md := by
  set h := compress (cellWords cv0 ++ cellWords cv1) (messageWords m) (unpackMetadata md).1
    (unpackMetadata md).2.1 (unpackMetadata md).2.2 with hh
  refine ⟨wordsCell #v[h[0], h[1], h[2], h[3]], wordsCell #v[h[4], h[5], h[6], h[7]],
    hm, hcv0, hcv1, isCanonical128_wordsCell _, isCanonical128_wordsCell _, hmd, ?_⟩
  rw [cellWords_wordsCell, cellWords_wordsCell]
  ext i hi
  interval_cases i <;> rfl

/-- The compression of the all-zero cells has output cells. -/
theorem compressCells_zero : ∃ out0 out1 : E, CompressCells ![0, 0, 0, 0] 0 0 out0 out1 0 :=
  compressCells_exists _ 0 0 0 (fun i ↦ by fin_cases i <;> exact limb_zero 2) (limb_zero 2)
    (limb_zero 2) (limb_zero 2)

end
end LeanerVM.Semantics
