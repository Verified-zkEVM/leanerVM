/-
  LeanerVM.Semantics.FillCycle

  The closing jump of a fill block, and the cycle: a traversal returns to its start, any number of
  times.
-/

module

public import LeanerVM.Semantics.FillSteps

/-!
# The fill-block lemma

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category A. A block is a cycle: its `s` dummies step
one slot at a time in a frame that does not change, and the closing jump reads its destination
`g^{pc}` and its frame `g^{base}` from the frame, so it returns to the block's first slot in the
same frame. Hence `s + 1` steps from the start state return to it (`fill_traversal_run`), and so
do any number of traversals (`fill_cycle_run`). This is the fill-block lemma the blueprint says
completeness needs: the rows a cycle adds to the tables are steps that close on themselves, so
their state tuples cancel on the bus for any number of traversals.

The closing jump is a taken `JUMP`: its condition is the destination cell, a power of `g` and so
nonzero, and the three cells are in `K`. That is why every traversal costs the `JUMP` table a row,
and `Semantics.FillPlan` counts it.

## Wrong readings excluded

* The closing jump is not the last dummy: after `s` steps the state is the closing slot, not the
  start, so a block is a cycle only with its jump (`tests/LeanerVMTests/Semantics/FillCycle.lean`).
* A closing jump run in another cycle's frame does not close its own: that frame names another
  block's first slot.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## Run lemmas -/

/-- One step from a state away from the sentinel is a run of one step. -/
theorem run_one {κ : ℕ} {prog : Program} {L : MemImage κ} {r r' : Regs K}
    (hpc : r.pc ≠ prog.finalPc) (h : step prog L r = some r') : run prog L 1 r = some r' := by
  rw [run_succ_of_ne hpc, h]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rfl

/-- Runs compose. -/
theorem run_trans {κ : ℕ} {prog : Program} {L : MemImage κ} {m n : ℕ} {r r₁ r₂ : Regs K}
    (h1 : run prog L m r = some r₁) (h2 : run prog L n r₁ = some r₂) :
    run prog L (m + n) r = some r₂ := by
  rw [run_add, h1]
  simpa only [Option.bind_eq_bind, Option.bind_some] using h2

/-- A slot below the sentinel is not the sentinel's counter. -/
theorem gpow_ne_finalPc (prog : Program) {n : ℕ} (hn : n + 1 < 2 ^ prog.logSize) :
    gpow n ≠ prog.finalPc := by
  unfold Program.finalPc
  intro heq
  have hL : prog.logSize ≤ 32 := prog.logSize_le
  have h32 : 2 ^ prog.logSize ≤ 4294967296 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hL
    simpa using this
  have hc : (2 : ℕ) ^ 64 - 1 = 18446744073709551615 := by norm_num
  have hm1 : n ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio, hc]; omega
  have hm2 : 2 ^ prog.logSize - 1 ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio, hc]; omega
  have := gpow_injOn hm1 hm2 heq
  omega

/-! ## The closing jump -/

/-- A `JUMP` whose three cells hold words of `K`, the condition nonzero, goes to the destination
in the frame the third cell holds. -/
theorem executeWith_jump_taken {read : K → Option E} {r : Regs K} {oc od of : K} {c d f : K}
    (hc : read (r.fp * oc) = some (ofK c)) (hd : read (r.fp * od) = some (ofK d))
    (hf : read (r.fp * of) = some (ofK f)) (hc0 : c ≠ 0) :
    executeWith read r (.jump oc od of) = some ⟨d, f⟩ := by
  have hin : ∀ a : K, IsInK (ofK a) := fun a ↦ (isInK_iff _).mpr ⟨a, rfl⟩
  have hne : ofK c ≠ 0 := by
    intro h
    have := congrArg (fun z : E ↦ z.limb 0) h
    simp only [limb_ofK, limb_zero] at this
    exact hc0 this
  simp [executeWith, hc, hd, hf, hin, hne, limb_ofK]

/-- The state a cycle starts and ends in: the block's first slot, in the cycle's frame. -/
def cycleStart (κ : ℕ) (pcs : Opcode → ℕ → ℕ) (t : Opcode) (k : ℕ) : Regs K :=
  ⟨gpow (pcs t (sizeAt k)), gpow (frameBase κ (8 * tableIdx t + k))⟩

/-- **The closing jump closes.** In the frame of the cycle `(t, k)`, the closing jump at any
fetched slot goes to the cycle's start: the block's first slot, in the same frame. -/
theorem fill_close_step {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ) (t : Opcode) {k : ℕ} (hk : k < 8) {prog : Program} {pc : K}
    (hf : prog.fetch pc = some fillClose) :
    step prog (padImage img pcs) ⟨pc, gpow (frameBase κ (8 * tableIdx t + k))⟩ =
      some (cycleStart κ pcs t k) := by
  rw [step_of_fetch_eq_some (r := ⟨pc, gpow (frameBase κ (8 * tableIdx t + k))⟩) hf]
  have R : ∀ o, o < 12 → (padImage img pcs).read (gpow (frameBase κ (8 * tableIdx t + k)) *
      gpow o) = some (frameCell (img ⟨0, Nat.two_pow_pos κ⟩) (pcs t (sizeAt k))
        (frameBase κ (8 * tableIdx t + k)) t o) :=
    fun o ho ↦ read_frame_mul hκ hκ' img pcs t hk ho
  have hd := R FillFrame.dest (by decide)
  rw [frameCell_dest] at hd
  have hn := R FillFrame.nextFp (by decide)
  rw [frameCell_nextFp] at hn
  exact executeWith_jump_taken hd hd hn (gpow_ne_zero _)

/-! ## The cycle -/

/-- The `i` dummies of a block, `i ≤ s`, take the start state to the `i`-th slot of the block, in
the same frame. -/
theorem fill_dummies_run {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ) (t : Opcode) {k : ℕ} (hk : k < 8) {prog : Program}
    (hb : IsFillBlock prog t (sizeAt k) (pcs t (sizeAt k))) :
    ∀ i, i ≤ sizeAt k → run prog (padImage img pcs) i (cycleStart κ pcs t k) =
      some ⟨gpow (pcs t (sizeAt k) + i), gpow (frameBase κ (8 * tableIdx t + k))⟩ := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hpc : (⟨gpow (pcs t (sizeAt k) + i), gpow (frameBase κ (8 * tableIdx t + k))⟩ :
        Regs K).pc ≠ prog.finalPc :=
      gpow_ne_finalPc prog (by have := hb.below; omega)
    have hstep := fill_dummy_step hκ hκ' img pcs t hk (hb.dummies i (by omega))
    have h1 := run_trans (ih (by omega)) (run_one hpc hstep)
    rw [← gpow_succ] at h1
    rw [← add_assoc]
    exact h1

/-- **A traversal returns to its start.** From the cycle's start state, the `s` dummies and the
closing jump, `s + 1` steps, return to it. -/
theorem fill_traversal_run {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ) (t : Opcode) {k : ℕ} (hk : k < 8) {prog : Program}
    (hb : IsFillBlock prog t (sizeAt k) (pcs t (sizeAt k))) :
    run prog (padImage img pcs) (sizeAt k + 1) (cycleStart κ pcs t k) =
      some (cycleStart κ pcs t k) := by
  have hpc : (⟨gpow (pcs t (sizeAt k) + sizeAt k), gpow (frameBase κ (8 * tableIdx t + k))⟩ :
      Regs K).pc ≠ prog.finalPc :=
    gpow_ne_finalPc prog (by have := hb.below; omega)
  exact run_trans (fill_dummies_run hκ hκ' img pcs t hk hb (sizeAt k) le_rfl)
    (run_one hpc (fill_close_step hκ hκ' img pcs t hk hb.close))

/-- **The fill-block lemma.** Any number of traversals of a block return to the start: the rows the
cycle adds are steps that close on themselves. -/
theorem fill_cycle_run {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ) (t : Opcode) {k : ℕ} (hk : k < 8) {prog : Program}
    (hb : IsFillBlock prog t (sizeAt k) (pcs t (sizeAt k))) (n : ℕ) :
    run prog (padImage img pcs) (n * (sizeAt k + 1)) (cycleStart κ pcs t k) =
      some (cycleStart κ pcs t k) := by
  induction n with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ n ih =>
    rw [Nat.succ_mul]
    exact run_trans ih (fill_traversal_run hκ hκ' img pcs t hk hb)

end
end LeanerVM.Semantics
