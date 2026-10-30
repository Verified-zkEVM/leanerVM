import LeanerVM.Arithmetization.Completeness.Witness
import LeanerVMTests.Semantics.PaddedImageRefutation

/-!
# Layer 10 tests: the prover data of the padded witness

`padWitness` is never evaluated: its memory block has `2^κ` rows. Every test here is a statement
about the prover data Clean derives from its tables, generic in the skeletons, through the lemmas
that rewrite and never unfold (`imageOf_padWitness`, `memRows_padWitness_get`). The memory
log-size at most `maxLogMem` is load-bearing twice: a memory block of `2^64` rows is no table of
`u64` row indices, so the block cannot be built, and the data's `imageOf` clamps the log-size, so
a `"mem"` table of `2^33` rows names an image of `2^32` words.
-/

namespace LeanerVMTests.Arithmetization.Completeness.Witness

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Semantics.PaddedImageRefutation

/-- The sentinel counter of a `2^11`-slot program, as a literal term (status finding E8). -/
local notation "d₀" => (gpow 2047 : K)

/-! ## The prover data of the padded witness -/

/-- The image the derived data names is the witness's image, at the least memory log-size. -/
example (S : List Skel) (hS : S.length ≤ UInt64.size) :
    imageOf (padWitness ladderJumpProg badInput (badImage d₀) S (by decide) hS).data =
      ⟨minLogMem, badImage d₀⟩ :=
  imageOf_padWitness

/-- The derived `"mem"` table has the `2^κ` rows of the memory block. -/
example (S : List Skel) (hS : S.length ≤ UInt64.size) :
    (memRows (padWitness ladderJumpProg badInput (badImage d₀) S (by decide) hS).data).size =
      2 ^ minLogMem :=
  memRows_size _ (by decide)

/-- Its row `0` holds the limbs of the image's word at `g^0`, read through `getElem?`. -/
example (S : List Skel) (hS : S.length ≤ UInt64.size) :
    (memRows (padWitness ladderJumpProg badInput (badImage d₀) S (by decide) hS).data)[0]? =
      some #v[(badImage d₀ ⟨0, by decide⟩).limb 0, (badImage d₀ ⟨0, by decide⟩).limb 1,
        (badImage d₀ ⟨0, by decide⟩).limb 2] :=
  memRows_padWitness_get 0 (by decide)

/-! ## The memory cap is load-bearing -/

/-- A memory block of log-size `64` does not agree with its fixed cells: its height `2^64` is
read as the `u64` value `0`, so `padWitness` needs `κ ≤ maxLogMem`. -/
example (img : MemImage 64) (fin : K → ℕ) :
    ¬ (memComponent 64).FixedRowsMatch (memRowsOf img fin) := by
  rintro ⟨h, -⟩
  rw [memRowsOf_length] at h
  exact absurd h (by decide)

/-- A `"mem"` table of `2^33` rows names an image of log-size `maxLogMem`: the bound `κ ≤ maxLogMem`
of `imageOf_padWitness` cannot be dropped. -/
example (data : ProverData K) (h : (memRows data).size = 2 ^ 33) :
    (imageOf data).1 = maxLogMem := by
  show min (Nat.log 2 (memRows data).size) maxLogMem = _
  rw [h, Nat.log_pow (by norm_num)]
  decide

example (data : ProverData K) (h : (memRows data).size = 2 ^ 33) : (imageOf data).1 ≠ 33 := by
  show min (Nat.log 2 (memRows data).size) maxLogMem ≠ 33
  rw [h, Nat.log_pow (by norm_num)]
  decide

end LeanerVMTests.Arithmetization.Completeness.Witness
