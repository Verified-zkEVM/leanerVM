/-
  LeanerVM.Semantics.PaddedImage

  The padded image: the committed image, extended by the frames the fill blocks run in.
-/

module

public import LeanerVM.Semantics.Blake2sOutput
public import LeanerVM.Semantics.PaddedRun

/-!
# The padded image

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category A for the layout, written to what the
interpreter does at `crates/lean_vm/src/cpu/execute.rs:353-411`: one twelve-cell frame per fill
cycle, the closing jump's destination and frame written into it, and the other cells read as zero.

**The layout.** The image of `t` has `2^κ` cells. The padded image has `2^(κ + 1)`: the first `2^κ`
are `t`'s, unchanged, and above them sit the forty-eight frames of the cycles, six tables times
eight sizes, frame `c = 8 * tableIdx t + k` at cell `2^κ + 12 c`. They fit because `12 * 48 = 576`
is at most `2^κ` for every memory log-size the verifier accepts (`κ ≥ 16`). The Rust places its
frames from `max(2^16, next_free)`; any placement above the committed image works, and this one
needs no knowledge of how much of the memory the run used.

**The cells of a frame** (`cpu/filler.rs:73-87`, `lower.rs:482-519`), offsets from the frame base:

* `dest` holds `g^{pc}` for `pc` the block's first slot: the closing jump's destination and, being a
  power of `g`, its nonzero condition. `nextFp` holds `g^{base}`: the frame to go to, this one.
  `ptr` holds `1 = g^0`, the address of memory cell `0`, which the `DEREF` dummy follows.
* The `DEREF` frame's scratch cell holds the word at memory cell `0`, the public input's first
  word: the dummy checks that cell against memory cell `0`.
* The `BLAKE2S` frame's digest pair holds the compression of the all-zero cells (`zeroDigest`,
  chosen, never computed); every other `BLAKE2S` cell is zero.
* Every other cell is zero, the value of a cell nobody writes (`execute.rs:261`).

`padTrace t pcs` is the padded trace; it is a `PaddedFrom` of `t` (`padTrace_from`), so by
`Semantics.PaddedRun` it is valid wherever `t` is.

## Wrong readings excluded

* The frames are above the committed image, never inside it: the committed words are the run's,
  and a frame placed in them would have to agree with whatever the prover chose there.
* Frames of different cycles hold different cells (the `DEREF` scratch cell is the public word,
  the `XOR` scratch cell is zero), which is why each cycle has a frame of its own.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## Indices -/

/-- The index of a table in the ladder. -/
def tableIdx (t : Opcode) : ℕ := fillTables.idxOf t

/-- The size of index `k` in the ladder, and `0` past its end. -/
def sizeAt (k : ℕ) : ℕ := fillSizes.getD k 0

/-- Every table has an index below six. -/
theorem tableIdx_lt (t : Opcode) : tableIdx t < 6 := by
  cases t <;> decide

/-- The table of an index is the table. -/
theorem fillTables_getD_tableIdx (t : Opcode) : fillTables.getD (tableIdx t) .xor = t := by
  cases t <;> decide

/-- The size of an index below eight is a size of the ladder. -/
theorem sizeAt_mem {k : ℕ} (hk : k < 8) : sizeAt k ∈ fillSizes := by
  unfold sizeAt
  interval_cases k <;> simp [fillSizes]

/-! ## The frames -/

/-- The output cells of a compression of the all-zero cells, the pair the `BLAKE2S` dummy writes
(`lower.rs:514-519`). Chosen: it is never computed. -/
noncomputable def zeroDigest : E × E :=
  ⟨Classical.choose compressCells_zero, Classical.choose (Classical.choose_spec compressCells_zero)⟩

/-- The zero input compresses to the digest. -/
theorem zeroDigest_spec :
    CompressCells ![0, 0, 0, 0] 0 0 zeroDigest.1 zeroDigest.2 0 :=
  Classical.choose_spec (Classical.choose_spec compressCells_zero)

/-- The first cell of the frame of the cycles of table `t` whose block starts at slot `pc`, at
cell index `base` (so the frame pointer is `g^base`): the word at offset `o`. `w0` is the word at
memory cell `0`, which the `DEREF` dummy checks. -/
noncomputable def frameCell (w0 : E) (pc base : ℕ) (t : Opcode) (o : ℕ) : E :=
  if o = FillFrame.dest then ofK (gpow pc)
  else if o = FillFrame.nextFp then ofK (gpow base)
  else if o = FillFrame.ptr then ofK 1
  else if o = FillFrame.scratch ∧ t = .deref then w0
  else if o = FillFrame.digest ∧ t = .blake2s then zeroDigest.1
  else if o = FillFrame.digest + 1 ∧ t = .blake2s then zeroDigest.2
  else 0

/-- The cell index of frame `c` for a memory of `2^κ` committed cells. -/
def frameBase (κ c : ℕ) : ℕ := 2 ^ κ + 12 * c

/-- The cell `j` above the committed image, `j = 12 c + o`: offset `o` of frame `c` when `c` is one
of the forty-eight, `0` past them. The block of size `s` of table `t` starts at slot `pcs t s`. -/
noncomputable def padCell (w0 : E) (pcs : Opcode → ℕ → ℕ) (κ j : ℕ) : E :=
  if j / 12 < 48 then
    frameCell w0 (pcs (fillTables.getD (j / 12 / 8) .xor) (sizeAt (j / 12 % 8)))
      (frameBase κ (j / 12)) (fillTables.getD (j / 12 / 8) .xor) (j % 12)
  else 0

/-- The padded image: the committed words below `2^κ`, and above them the forty-eight frames. -/
noncomputable def padImage {κ : ℕ} (img : MemImage κ) (pcs : Opcode → ℕ → ℕ) :
    MemImage (κ + 1) := fun i ↦
  if h : (i : ℕ) < 2 ^ κ then img ⟨i, h⟩
  else padCell (img ⟨0, Nat.two_pow_pos κ⟩) pcs κ ((i : ℕ) - 2 ^ κ)

/-- The trace of the padded image: the same steps, one more doubling of memory. -/
noncomputable def padTrace {prog : Program} (t : Trace prog) (pcs : Opcode → ℕ → ℕ) :
    Trace prog :=
  ⟨t.κ + 1, padImage t.image pcs, t.steps⟩

/-! ## Load-bearing lemmas -/

/-- Below `2^κ` the padded image is the committed image. -/
theorem padImage_below {κ : ℕ} (img : MemImage κ) (pcs : Opcode → ℕ → ℕ) {i : ℕ}
    (hi : i < 2 ^ κ) (hi' : i < 2 ^ (κ + 1)) :
    padImage img pcs ⟨i, hi'⟩ = img ⟨i, hi⟩ := by
  simp only [padImage, hi, ↓reduceDIte]

/-- The padded trace is a padding of the trace. -/
theorem padTrace_from {prog : Program} (t : Trace prog) (pcs : Opcode → ℕ → ℕ) :
    (padTrace t pcs).PaddedFrom t where
  steps_eq := rfl
  κ_le := Nat.le_succ _
  image_ext := fun _ hi hi' ↦ padImage_below t.image pcs hi hi'

/-- The frames fit above the image: the last cell of the last frame is below `2^(κ + 1)`, for a
memory of at least `2^10` cells. -/
theorem frameBase_add_lt {κ : ℕ} (hκ : 10 ≤ κ) {c o : ℕ} (hc : c < 48) (ho : o < 12) :
    frameBase κ c + o < 2 ^ (κ + 1) := by
  have h : 2 ^ 10 ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ
  have h2 : 2 ^ (κ + 1) = 2 * 2 ^ κ := by ring
  unfold frameBase
  omega

/-- Offset `o` of frame `8 * tableIdx t + k` is the frame cell of the cycle `(t, k)`. -/
theorem padCell_frame (w0 : E) (pcs : Opcode → ℕ → ℕ) (κ : ℕ) (t : Opcode) {k o : ℕ}
    (hk : k < 8) (ho : o < 12) :
    padCell w0 pcs κ (12 * (8 * tableIdx t + k) + o) =
      frameCell w0 (pcs t (sizeAt k)) (frameBase κ (8 * tableIdx t + k)) t o := by
  have ht := tableIdx_lt t
  have hdiv : (12 * (8 * tableIdx t + k) + o) / 12 = 8 * tableIdx t + k := by omega
  have hmod : (12 * (8 * tableIdx t + k) + o) % 12 = o := by omega
  have hc : 8 * tableIdx t + k < 48 := by omega
  have h8 : (8 * tableIdx t + k) / 8 = tableIdx t := by omega
  have h8' : (8 * tableIdx t + k) % 8 = k := by omega
  simp only [padCell, hdiv, hmod, hc, ↓reduceIte, h8, h8', fillTables_getD_tableIdx]

/-- The word at offset `o` of the frame of the cycle `(t, k)`, read at its address: the frame cell
the padded image holds there. -/
theorem padImage_read_frame {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ) (t : Opcode) {k o : ℕ} (hk : k < 8) (ho : o < 12) :
    (padImage img pcs).read (gpow (frameBase κ (8 * tableIdx t + k) + o)) =
      some (frameCell (img ⟨0, Nat.two_pow_pos κ⟩) (pcs t (sizeAt k))
        (frameBase κ (8 * tableIdx t + k)) t o) := by
  have ht := tableIdx_lt t
  have hc : 8 * tableIdx t + k < 48 := by omega
  have hi := frameBase_add_lt hκ hc ho
  have hge : ¬ frameBase κ (8 * tableIdx t + k) + o < 2 ^ κ := by
    unfold frameBase; omega
  have hsub : frameBase κ (8 * tableIdx t + k) + o - 2 ^ κ = 12 * (8 * tableIdx t + k) + o := by
    unfold frameBase; omega
  refine (MemImage.read_gpow (by omega) (padImage img pcs) ⟨_, hi⟩).trans (congrArg some ?_)
  simp only [padImage, hge, ↓reduceDIte, hsub]
  exact padCell_frame _ pcs κ t hk ho

end
end LeanerVM.Semantics
