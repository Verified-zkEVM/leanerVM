import LeanerVM.Semantics.FillCycle
import LeanerVMTests.Semantics.FillCycle

/-!
# Layer 10 tests: padding is coupled to the `JUMP` table

Every step but a taken `JUMP` advances the counter by `g`, and `g` has order `2^64 - 1`. So a closed
run shorter than `2^64 - 1` steps, a fill block repeated or any other padding, contains a step that
is not the fall-through, and only a `JUMP` takes one. Every traversal of a fill block therefore adds
a row to the `JUMP` table, whichever table the block fills. That is why `Semantics.FillPlan` counts
the closing jumps (`jumpOwed`) and why a `JUMP` gap of exactly one row is undeliverable
(`JumpFeasible`): the tables are not filled independently.

The theorem is for a walk, then for a run, then for the forty-eight cycles of the ladder program.
-/

namespace LeanerVMTests.Semantics.ClosedWalk

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.Execution LeanerVMTests.Semantics.FillBlocks
open LeanerVMTests.Semantics.FillSteps LeanerVMTests.Semantics.FillCycle

/-- Every instruction but a `JUMP` executes to the fall-through successor, or fails. -/
theorem execute_next_of_ne_jump {κ : ℕ} (L : MemImage κ) (r r' : Regs K) (ins : Instr)
    (hn : ins.opcode ≠ .jump) (h : execute L r ins = some r') : r' = r.next := by
  cases ins with
  | jump oc od of => exact absurd rfl hn
  | _ =>
    simp only [execute, executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    aesop

/-- A step that is not the fall-through successor fetched a `JUMP`. -/
theorem fetch_jump_of_step_ne_next {κ : ℕ} {prog : Program} {L : MemImage κ} {r r' : Regs K}
    (h : step prog L r = some r') (hne : r' ≠ r.next) :
    ∃ oc od of, prog.fetch r.pc = some (.jump oc od of) := by
  unfold step at h
  obtain ⟨ins, hf, hex⟩ := Option.bind_eq_some_iff.mp h
  cases ins with
  | jump oc od of => exact ⟨oc, od, of, hf⟩
  | _ => exact absurd (execute_next_of_ne_jump L r r' _ (by simp [Instr.opcode]) hex) hne

/-- A state that steps has a nonzero counter: it is a power of `g`. -/
theorem pc_ne_zero_of_step {κ : ℕ} {prog : Program} {L : MemImage κ} {r r' : Regs K}
    (h : step prog L r = some r') : r.pc ≠ 0 := by
  unfold step at h
  obtain ⟨ins, hf, -⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨i, hi, -⟩ := (Program.fetch_eq_some_iff prog).mp hf
  rw [hi]
  exact gpow_ne_zero i

/-- **A closed walk contains a taken `JUMP`.** A walk of `n` steps, `0 < n < 2^64 - 1`, that
returns to its first state has a step that fetched a `JUMP`. -/
theorem closed_walk_has_taken_jump {κ : ℕ} {prog : Program} {L : MemImage κ} {n : ℕ}
    (st : ℕ → Regs K) (hstep : ∀ i < n, step prog L (st i) = some (st (i + 1)))
    (hclosed : st n = st 0) (hn0 : 0 < n) (hn : n < 2 ^ 64 - 1) :
    ∃ i < n, ∃ oc od of, prog.fetch (st i).pc = some (.jump oc od of) := by
  by_contra hno
  have hnext : ∀ i < n, st (i + 1) = (st i).next := by
    intro i hi
    by_contra hne
    obtain ⟨oc, od, of, hf⟩ := fetch_jump_of_step_ne_next (hstep i hi) hne
    exact hno ⟨i, hi, oc, od, of, hf⟩
  -- so the counter is `g^k * pc₀`
  have hpc : ∀ k ≤ n, (st k).pc = gpow k * (st 0).pc := by
    intro k
    induction k with
    | zero => intro _; simp [gpow]
    | succ k ih =>
      intro hk
      rw [hnext k (by omega)]
      show g * (st k).pc = gpow (k + 1) * (st 0).pc
      rw [ih (by omega), gpow_succ, mul_assoc]
  have h0 : (st 0).pc ≠ 0 := pc_ne_zero_of_step (hstep 0 hn0)
  have hcl : gpow n * (st 0).pc = (st 0).pc := by
    rw [← hpc n le_rfl, hclosed]
  have hpow : g ^ n = 1 := by
    have : gpow n * (st 0).pc = 1 * (st 0).pc := by rw [hcl, one_mul]
    exact mul_right_cancel₀ h0 this
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  rw [orderOf_g] at hdvd
  have := Nat.le_of_dvd hn0 hdvd
  omega

/-- **A closed run contains a taken `JUMP`.** -/
theorem closed_run_has_taken_jump {κ : ℕ} {prog : Program} {L : MemImage κ} {n : ℕ} {r : Regs K}
    (hrun : run prog L n r = some r) (hn0 : 0 < n) (hn : n < 2 ^ 64 - 1) :
    ∃ i < n, ∃ r₁, run prog L i r = some r₁ ∧ ∃ oc od of,
      prog.fetch r₁.pc = some (.jump oc od of) := by
  let st : ℕ → Regs K := fun i ↦ (run prog L i r).getD r
  have hst : ∀ i ≤ n, run prog L i r = some (st i) := fun i hi ↦ by
    obtain ⟨r₁, h1, -⟩ := run_prefix (m := i) (n := n - i) (by rwa [Nat.add_sub_cancel' hi])
    simp [st, h1]
  have hstep : ∀ i < n, step prog L (st i) = some (st (i + 1)) := fun i hi ↦ by
    have h1 := hst i hi.le
    have h2 := hst (i + 1) hi
    have hpc : (st i).pc ≠ prog.finalPc := by
      obtain ⟨r₁, h, hne⟩ := run_intermediate hrun hi
      rw [h1] at h
      cases h
      exact hne
    rw [run_add i 1, h1] at h2
    simp only [Option.bind_eq_bind, Option.bind_some] at h2
    rw [run_succ_of_ne hpc] at h2
    obtain ⟨r₂, hs, h0⟩ := Option.bind_eq_some_iff.mp h2
    rw [run_zero] at h0
    rw [hs, Option.some.inj h0]
  have hclosed : st n = st 0 := by
    have h := hst n le_rfl
    rw [hrun] at h
    have h0 : st 0 = r := by simp [st]
    rw [h0]
    exact (Option.some.inj h).symm
  obtain ⟨i, hi, oc, od, of, hf⟩ := closed_walk_has_taken_jump (prog := prog) (L := L) st hstep
    hclosed hn0 hn
  exact ⟨i, hi, st i, hst i hi.le, oc, od, of, hf⟩

/-! ## The cycles of the ladder program -/

/-- No block of the ladder has more than `128` dummies. -/
theorem sizeAt_le {k : ℕ} (hk : k < 8) : sizeAt k ≤ 128 := by
  interval_cases k <;> decide

/-- Every traversal of every block of the ladder, over the executor's image, takes a `JUMP` at
some state of the traversal: the closing jump, whichever table the block fills. -/
theorem ladder_traversal_has_jump (t : Opcode) {k : ℕ} (hk : k < 8) :
    ∃ i < sizeAt k + 1, ∃ r₁, run ladderProg (padImage mulImage pcsLadder) i
        (cycleStart minLogMem pcsLadder t k) = some r₁ ∧
      ∃ oc od of, ladderProg.fetch r₁.pc = some (.jump oc od of) :=
  closed_run_has_taken_jump
    (by simpa using ladder_cycle_closed t hk 1) (Nat.succ_pos _)
    (by have := sizeAt_le hk; norm_num; omega)

end LeanerVMTests.Semantics.ClosedWalk
