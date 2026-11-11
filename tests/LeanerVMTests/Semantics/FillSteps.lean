import LeanerVM.Semantics.FillSteps
import LeanerVMTests.Semantics.FillBlocks
import LeanerVMTests.Semantics.Execution

/-!
# Layer 10 tests: the dummy steps of a fill block

The ladder program (`LeanerVMTests.Semantics.FillBlocks`) over the executor's image
(`mul_192bit_word`), padded with the fill frames. For every table the smallest block's dummy steps
in the frame of its own cycle: one slot on, the same frame. The mutation that shows frames are
table-specific: the `DEREF` dummy run in an `XOR` frame is not a step, because the `XOR` frame's
scratch cell is zero while memory cell `0` holds the public input's first word.
-/

namespace LeanerVMTests.Semantics.FillSteps

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Execution LeanerVMTests.Semantics.FillBlocks

/-- The first slot of the block of each size within a table's `263` slots. -/
def blockStart : ℕ → ℕ
  | 128 => 0
  | 64 => 129
  | 32 => 194
  | 16 => 227
  | 8 => 244
  | 4 => 253
  | 2 => 258
  | 1 => 261
  | _ => 0

/-- The starting slots the ladder program has, as `HasFillBlocks` would choose them. -/
def pcsLadder (t : Opcode) (s : ℕ) : ℕ := 1 + 263 * tableIdx t + blockStart s

/-- The table whose blocks start at slot `1 + 263 k` is `tableOf k`, and `tableIdx` inverts it. -/
theorem tableIdx_tableOf {k : ℕ} (hk : k < 6) : tableIdx (tableOf k) = k := by
  interval_cases k <;> rfl

/-- The single dummy of the size-one block of table `tableOf k`, and the frame of its cycle: the
largest index, `k = 7`, holds the size-one cycle. -/
theorem sizeAt_seven : sizeAt 7 = 1 := rfl

/-! ## Every table's dummy steps in its own frame -/

/-- The dummy of the size-one block of each table is fetched at its slot, and steps in the frame of
that table's size-one cycle. -/
theorem ladder_dummy_step (t : Opcode) :
    ∃ pc : K, ladderProg.fetch pc = some (fillDummy t) ∧
      step ladderProg (padImage mulImage pcsLadder)
          ⟨pc, gpow (frameBase minLogMem (8 * tableIdx t + 7))⟩ =
        some ⟨g * pc, gpow (frameBase minLogMem (8 * tableIdx t + 7))⟩ := by
  obtain ⟨k, hk, ht⟩ : ∃ k, k < 6 ∧ tableOf k = t := by
    cases t
    exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩,
      ⟨3, by decide, rfl⟩, ⟨4, by decide, rfl⟩, ⟨5, by decide, rfl⟩]
  have hb := ladder_block t k hk ht 1 261 (by norm_num) (by decide) (by decide)
  have hf := hb.dummies 0 (by norm_num)
  exact ⟨_, hf, fill_dummy_step (by decide) (by decide) mulImage pcsLadder t (by norm_num) hf⟩

/-! ## Frames are table-specific -/

/-- A guard that succeeds holds. -/
theorem guard_of_some {p : Prop} [Decidable p] {u : Unit} (h : (guard p : Option Unit) = some u) :
    p := by
  by_contra hp
  simp [guard, hp] at h

/-- Inverting the `DEREF` arm: an execution reads the pointer, the local cell and the cell the
pointer names, and the last is the source. -/
theorem deref_inv {read : K → Option E} {r r' : Regs K} {o1 o2 o3 : K} {mode : DerefMode}
    (h : executeWith read r (.deref o1 o2 o3 mode) = some r') :
    ∃ p v3 v2 : E, read (r.fp * o1) = some p ∧ read (r.fp * o3) = some v3 ∧
      read (p.limb 0 * o2) = some v2 ∧ v2 = derefSource mode r v3 := by
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, -, -, v3, h3, v2, h2, u, hu, -⟩ := h
  exact ⟨p, v3, v2, hp, h3, h2, guard_of_some hu⟩

/-- The `DEREF` dummy run in the frame of any other table fails when the word at memory cell `0`
is not zero: the pointer cell holds `1`, naming memory cell `0`, but that frame's scratch cell holds
`0`. -/
theorem deref_dummy_fails_elsewhere {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ) {t : Opcode} (ht : t ≠ .deref) {k : ℕ} (hk : k < 8) {prog : Program}
    {pc : K} (hf : prog.fetch pc = some (fillDummy .deref))
    (hw : img ⟨0, Nat.two_pow_pos κ⟩ ≠ 0) :
    step prog (padImage img pcs) ⟨pc, gpow (frameBase κ (8 * tableIdx t + k))⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨pc, gpow (frameBase κ (8 * tableIdx t + k))⟩) hf]
  cases hs : execute (padImage img pcs) ⟨pc, gpow (frameBase κ (8 * tableIdx t + k))⟩
    (fillDummy .deref) with
  | none => rfl
  | some r' =>
    exfalso
    obtain ⟨p, v3, v2, hp, h3, h2, hv⟩ :=
      deref_inv (show executeWith (padImage img pcs).read _ (fillDummy .deref) = some r' from hs)
    have R : ∀ o, o < 12 → (padImage img pcs).read (gpow (frameBase κ (8 * tableIdx t + k)) *
        gpow o) = some (frameCell (img ⟨0, Nat.two_pow_pos κ⟩) (pcs t (sizeAt k))
          (frameBase κ (8 * tableIdx t + k)) t o) :=
      fun o ho ↦ read_frame_mul hκ hκ' img pcs t hk ho
    -- the pointer cell holds `1`
    have hp' := R FillFrame.ptr (by decide)
    rw [frameCell_ptr] at hp'
    obtain rfl : p = ofK 1 := Option.some.inj (hp.symm.trans hp')
    -- the scratch cell holds zero
    have h3' := R FillFrame.scratch (by decide)
    rw [frameCell_scratch_of_ne _ _ _ ht] at h3'
    obtain rfl : v3 = 0 := Option.some.inj (h3.symm.trans h3')
    -- the cell the pointer names is memory cell `0`
    have hl : (ofK (1 : K)).limb 0 = 1 := by rw [limb_ofK]; rfl
    rw [hl, one_mul, padImage_read_zero hκ' img pcs] at h2
    obtain rfl : v2 = img ⟨0, Nat.two_pow_pos κ⟩ := (Option.some.inj h2).symm
    exact hw hv

/-- On the executor's image the word at memory cell `0` is the public input's first word, `1`. -/
theorem mulImage_word0_ne_zero : mulImage ⟨0, Nat.two_pow_pos minLogMem⟩ ≠ 0 := by
  decide +kernel

/-- So the `DEREF` dummy fails in the `XOR` frame. -/
theorem deref_dummy_in_xor_frame :
    ∃ pc : K, ladderProg.fetch pc = some (fillDummy .deref) ∧
      step ladderProg (padImage mulImage pcsLadder)
        ⟨pc, gpow (frameBase minLogMem (8 * tableIdx .xor + 7))⟩ = none := by
  have hb := ladder_block .deref 3 (by norm_num) rfl 1 261 (by norm_num) (by decide) (by decide)
  obtain ⟨pc, hf⟩ : ∃ pc : K, ladderProg.fetch pc = some (fillDummy .deref) :=
    ⟨_, hb.dummies 0 (by norm_num)⟩
  exact ⟨pc, hf, deref_dummy_fails_elsewhere (by decide) (by decide) mulImage pcsLadder
    (by decide) (by norm_num) hf mulImage_word0_ne_zero⟩

end LeanerVMTests.Semantics.FillSteps
