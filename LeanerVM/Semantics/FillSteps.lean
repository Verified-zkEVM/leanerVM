/-
  LeanerVM.Semantics.FillSteps

  The steps of a fill block over the padded image: each dummy executes to the fall-through
  successor, in a frame of its own.
-/

module

public import LeanerVM.Semantics.PaddedImage

/-!
# The dummy steps of a fill block

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category A. Over the padded image, at a frame pointer
`g^base` of one of the forty-eight frames, each of the six dummies (`Semantics.FillBlocks`)
executes to `Regs.next`: the registers advance one slot and the frame is kept. The proof is the
arithmetic of the template: `XOR` and `MUL_NATIVE` read the zero scratch cell three times and
`0 = 0 + 0`, `0 = 0 * 0`; `SET_CONSTANT` sets it to `0`; the `DEREF` dummy follows a pointer `1` to
memory cell `0`, whose word the frame's scratch cell holds; the `JUMP` dummy reads the zero cell as
every operand, so its condition is `0` and it falls through; and the `BLAKE2S` dummy compresses
zero cells into the digest pair the frame holds.

Each arm is first stated abstractly, over any reader: if the cells it reads hold these words, the
instruction executes to the fall-through (`executeWith_*_of_reads`). The six dummy steps are
these lemmas on the frame cells. The abstract statements keep `simp` away from concrete field
elements.

## Wrong readings excluded

* The dummy of one table does not step in the frame of another: the `DEREF` dummy at an `XOR`
  frame finds `0` in its scratch cell and `w0` in memory cell `0`, and fails unless `w0 = 0`
  (`tests/LeanerVMTests/Semantics/FillSteps.lean`).
* A dummy never changes the frame pointer: only the closing jump does.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## The arms, over any reader -/

/-- `XOR` executes to the fall-through when its result cell holds the sum of its operands. -/
theorem executeWith_xor_of_reads {read : K → Option E} {r : Regs K} {oA oB oC : K} {a b c : E}
    (hA : read (r.fp * oA) = some a) (hB : read (r.fp * oB) = some b)
    (hC : read (r.fp * oC) = some c) (h : c = a + b) :
    executeWith read r (.xor oA oB oC) = some r.next := by
  simp [executeWith, hA, hB, hC, h]

/-- `MUL_NATIVE` executes to the fall-through when its result cell holds the product. -/
theorem executeWith_mul_of_reads {read : K → Option E} {r : Regs K} {oA oB oC : K} {a b c : E}
    (hA : read (r.fp * oA) = some a) (hB : read (r.fp * oB) = some b)
    (hC : read (r.fp * oC) = some c) (h : c = a * b) :
    executeWith read r (.mulNative oA oB oC) = some r.next := by
  simp [executeWith, hA, hB, hC, h]

/-- `SET_CONSTANT` executes to the fall-through when its cell holds its immediate. -/
theorem executeWith_set_of_read {read : K → Option E} {r : Regs K} {o : K} {k : E}
    (h : read (r.fp * o) = some k) : executeWith read r (.setConstant o k) = some r.next := by
  simp [executeWith, h]

/-- `DEREF` executes to the fall-through when the pointer is in `K` and the cell it names holds
the source. -/
theorem executeWith_deref_of_reads {read : K → Option E} {r : Regs K} {o1 o2 o3 : K}
    {mode : DerefMode} {p v3 v2 : E} (hp : read (r.fp * o1) = some p) (hK : IsInK p)
    (h3 : read (r.fp * o3) = some v3) (h2 : read (p.limb 0 * o2) = some v2)
    (hv : v2 = derefSource mode r v3) :
    executeWith read r (.deref o1 o2 o3 mode) = some r.next := by
  simp [executeWith, hp, hK, h3, h2, hv]

/-- `JUMP` falls through when its three cells read as zero. -/
theorem executeWith_jump_fall {read : K → Option E} {r : Regs K} {oc od of : K}
    (hc : read (r.fp * oc) = some 0) (hd : read (r.fp * od) = some 0)
    (hf : read (r.fp * of) = some 0) : executeWith read r (.jump oc od of) = some r.next := by
  have h0 : IsInK (0 : E) := ⟨limb_zero 1, limb_zero 2⟩
  simp [executeWith, hc, hd, hf, h0]

/-- `BLAKE2S` executes to the fall-through when its nine cells hold a compression. -/
theorem executeWith_blake2s_of_reads {read : K → Option E} {r : Regs K} {om : Fin 4 → K}
    {ocv oout omd : K} {m0 m1 m2 m3 cv0 cv1 out0 out1 md : E}
    (h0 : read (r.fp * om 0) = some m0) (h1 : read (r.fp * om 1) = some m1)
    (h2 : read (r.fp * om 2) = some m2) (h3 : read (r.fp * om 3) = some m3)
    (hcv0 : read (r.fp * ocv) = some cv0) (hcv1 : read (r.fp * (g * ocv)) = some cv1)
    (hout0 : read (r.fp * oout) = some out0) (hout1 : read (r.fp * (g * oout)) = some out1)
    (hmd : read (r.fp * omd) = some md)
    (h : CompressCells ![m0, m1, m2, m3] cv0 cv1 out0 out1 md) :
    executeWith read r (.blake2s om ocv oout omd) = some r.next := by
  simp [executeWith, h0, h1, h2, h3, hcv0, hcv1, hout0, hout1, hmd, h]

/-! ## The frame cells at their offsets -/

/-- The destination cell holds `g^{pc}`. -/
theorem frameCell_dest (w0 : E) (pc base : ℕ) (t : Opcode) :
    frameCell w0 pc base t FillFrame.dest = ofK (gpow pc) := by
  simp [frameCell, FillFrame.dest]

/-- The cell the closing jump takes its frame from holds `g^{base}`. -/
theorem frameCell_nextFp (w0 : E) (pc base : ℕ) (t : Opcode) :
    frameCell w0 pc base t FillFrame.nextFp = ofK (gpow base) := by
  simp [frameCell, FillFrame.dest, FillFrame.nextFp]

/-- The pointer cell holds `1`. -/
theorem frameCell_ptr (w0 : E) (pc base : ℕ) (t : Opcode) :
    frameCell w0 pc base t FillFrame.ptr = ofK 1 := by
  simp [frameCell, FillFrame.dest, FillFrame.nextFp, FillFrame.ptr]

/-- The cell nothing writes reads as zero. -/
theorem frameCell_zero (w0 : E) (pc base : ℕ) (t : Opcode) :
    frameCell w0 pc base t FillFrame.zero = 0 := by
  simp [frameCell, FillFrame.dest, FillFrame.nextFp, FillFrame.ptr, FillFrame.zero,
    FillFrame.scratch, FillFrame.digest]

/-- The scratch cell of every frame but the `DEREF` one is zero. -/
theorem frameCell_scratch_of_ne (w0 : E) (pc base : ℕ) {t : Opcode} (h : t ≠ .deref) :
    frameCell w0 pc base t FillFrame.scratch = 0 := by
  simp [frameCell, FillFrame.dest, FillFrame.nextFp, FillFrame.ptr, FillFrame.scratch, h]

/-- The `DEREF` frame's scratch cell holds the word at memory cell `0`. -/
theorem frameCell_scratch_deref (w0 : E) (pc base : ℕ) :
    frameCell w0 pc base .deref FillFrame.scratch = w0 := by
  simp [frameCell, FillFrame.dest, FillFrame.nextFp, FillFrame.ptr, FillFrame.scratch]

/-- The cell after the scratch cell, the second chaining-value cell, is zero. -/
theorem frameCell_scratch_succ (w0 : E) (pc base : ℕ) (t : Opcode) :
    frameCell w0 pc base t (FillFrame.scratch + 1) = 0 := by
  simp [frameCell, FillFrame.dest, FillFrame.nextFp, FillFrame.ptr, FillFrame.scratch,
    FillFrame.digest]

/-- The four message cells of the `BLAKE2S` dummy are zero. -/
theorem frameCell_message (w0 : E) (pc base : ℕ) (t : Opcode) {j : ℕ} (hj : j < 4) :
    frameCell w0 pc base t (FillFrame.digest + 2 + j) = 0 := by
  unfold frameCell
  simp only [FillFrame.dest, FillFrame.nextFp, FillFrame.ptr, FillFrame.scratch,
    FillFrame.digest]
  split_ifs <;> first | rfl | omega

/-- The `BLAKE2S` frame's digest pair. -/
theorem frameCell_digest (w0 : E) (pc base : ℕ) :
    frameCell w0 pc base .blake2s FillFrame.digest = zeroDigest.1 ∧
      frameCell w0 pc base .blake2s (FillFrame.digest + 1) = zeroDigest.2 := by
  simp [frameCell, FillFrame.dest, FillFrame.nextFp, FillFrame.ptr, FillFrame.scratch,
    FillFrame.digest]

/-! ## The frame, read from its pointer -/

/-- Reading offset `o` of frame `8 * tableIdx t + k` from its frame pointer `g^base` gives the
frame cell. -/
theorem read_frame_mul {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ) (t : Opcode) {k o : ℕ} (hk : k < 8) (ho : o < 12) :
    (padImage img pcs).read (gpow (frameBase κ (8 * tableIdx t + k)) * gpow o) =
      some (frameCell (img ⟨0, Nat.two_pow_pos κ⟩) (pcs t (sizeAt k))
        (frameBase κ (8 * tableIdx t + k)) t o) := by
  rw [← pow_add]
  exact padImage_read_frame hκ hκ' img pcs t hk ho

/-- The padded image holds the committed image's cell `0` at address `g^0`: the public input's
first word, which the `DEREF` dummy checks. -/
theorem padImage_read_zero {κ : ℕ} (hκ' : κ < 63) (img : MemImage κ) (pcs : Opcode → ℕ → ℕ) :
    (padImage img pcs).read (gpow 0) = some (img ⟨0, Nat.two_pow_pos κ⟩) := by
  have h := MemImage.read_gpow (by omega : κ + 1 < 64) (padImage img pcs)
    ⟨0, by have := Nat.two_pow_pos (κ + 1); omega⟩
  rw [padImage_below img pcs (Nat.two_pow_pos κ)] at h
  exact h

/-! ## The dummy steps -/

/-- **A dummy steps.** In the frame of the cycle `(t, k)`, with frame pointer `g^base`, the dummy
of table `t` at any fetched slot executes to the fall-through: one slot on, the same frame. -/
theorem fill_dummy_step {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ) (t : Opcode) {k : ℕ} (hk : k < 8) {prog : Program} {pc : K}
    (hf : prog.fetch pc = some (fillDummy t)) :
    step prog (padImage img pcs) ⟨pc, gpow (frameBase κ (8 * tableIdx t + k))⟩ =
      some ⟨g * pc, gpow (frameBase κ (8 * tableIdx t + k))⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨pc, gpow (frameBase κ (8 * tableIdx t + k))⟩) hf]
  have R : ∀ o, o < 12 → (padImage img pcs).read (gpow (frameBase κ (8 * tableIdx t + k)) *
      gpow o) = some (frameCell (img ⟨0, Nat.two_pow_pos κ⟩) (pcs t (sizeAt k))
        (frameBase κ (8 * tableIdx t + k)) t o) :=
    fun o ho ↦ read_frame_mul hκ hκ' img pcs t hk ho
  cases t
  · -- `XOR s s -> s`: the scratch cell is zero, and `0 = 0 + 0`.
    have h4 := R FillFrame.scratch (by decide)
    rw [frameCell_scratch_of_ne _ _ _ (by decide)] at h4
    exact executeWith_xor_of_reads h4 h4 h4 (by simp)
  · -- `MUL s s -> s`: `0 = 0 * 0`.
    have h4 := R FillFrame.scratch (by decide)
    rw [frameCell_scratch_of_ne _ _ _ (by decide)] at h4
    exact executeWith_mul_of_reads h4 h4 h4 (by simp)
  · -- `SET s = 0`.
    have h4 := R FillFrame.scratch (by decide)
    rw [frameCell_scratch_of_ne _ _ _ (by decide)] at h4
    exact executeWith_set_of_read h4
  · -- `DEREF`: the pointer `1` names memory cell `0`, which the scratch cell repeats.
    have hp := R FillFrame.ptr (by decide)
    rw [frameCell_ptr] at hp
    have h3 := R FillFrame.scratch (by decide)
    rw [frameCell_scratch_deref] at h3
    have hl : (ofK (1 : K)).limb 0 = 1 := by rw [limb_ofK]; rfl
    have h2 : (padImage img pcs).read ((ofK (1 : K)).limb 0 * gpow 0) =
        some (img ⟨0, Nat.two_pow_pos κ⟩) := by
      rw [hl, one_mul]
      exact padImage_read_zero hκ' img pcs
    exact executeWith_deref_of_reads hp ((isInK_iff _).mpr ⟨1, rfl⟩) h3 h2 rfl
  · -- `JUMP z z z`: the zero cell, so the condition is zero and the jump falls through.
    have h3 := R FillFrame.zero (by decide)
    rw [frameCell_zero] at h3
    exact executeWith_jump_fall h3 h3 h3
  · -- `BLAKE2S`: zero cells compress into the digest pair the frame holds.
    have hz : ∀ j, j < 4 → (padImage img pcs).read (gpow (frameBase κ (8 * tableIdx .blake2s + k)) *
        gpow (FillFrame.digest + 2 + j)) = some 0 := fun j hj ↦ by
      have := R (FillFrame.digest + 2 + j) (by simp [FillFrame.digest]; omega)
      rwa [frameCell_message _ _ _ _ hj] at this
    have hcv0 := R FillFrame.scratch (by decide)
    rw [frameCell_scratch_of_ne _ _ _ (by decide)] at hcv0
    have hcv1 := R (FillFrame.scratch + 1) (by decide)
    rw [frameCell_scratch_succ] at hcv1
    have hd := R FillFrame.digest (by decide)
    have hd1 := R (FillFrame.digest + 1) (by decide)
    rw [(frameCell_digest _ _ _).1] at hd
    rw [(frameCell_digest _ _ _).2] at hd1
    have hmd := R FillFrame.zero (by decide)
    rw [frameCell_zero] at hmd
    have e5 : g * gpow FillFrame.scratch = gpow (FillFrame.scratch + 1) := (gpow_succ _).symm
    have e7 : g * gpow FillFrame.digest = gpow (FillFrame.digest + 1) := (gpow_succ _).symm
    exact executeWith_blake2s_of_reads (hz 0 (by norm_num)) (hz 1 (by norm_num))
      (hz 2 (by norm_num)) (hz 3 (by norm_num)) hcv0 (by rw [e5]; exact hcv1) hd
      (by rw [e7]; exact hd1) hmd zeroDigest_spec

end
end LeanerVM.Semantics
