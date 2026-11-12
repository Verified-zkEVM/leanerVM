import LeanerVM.Semantics.Execution

/-!
# Tests: a valid execution is an ordered trace

`ValidExecution` is stated through the recursive `run`, which tests for the sentinel before
every fetch. Here it is read as a sequence of states instead: a valid execution of `t.steps`
steps is exactly the public boundary and states `r_0 = (1, 1), …, r_steps = (g^(N_prog - 1), 1)`
in which every transition starts away from the sentinel and is one `step` of the program
(`validExecution_iff_trace`). So `run`'s fuel is the exact number of steps, and the run never
passes through the sentinel before its last state.
-/

namespace LeanerVMTests.Semantics.RunTrace

open LeanerVM.Parameters LeanerVM.Semantics

/-- An ordered trace with `n` transitions and `n + 1` states: every transition starts away from
the sentinel and is a step of the program; the last state need not be terminal. -/
def OrderedTrace {κ : ℕ} (prog : Program) (image : MemImage κ) (n : ℕ)
    (states : Fin (n + 1) → Regs K) : Prop :=
  ∀ i : Fin n, (states i.castSucc).pc ≠ prog.finalPc ∧
    step prog image (states i.castSucc) = some (states i.succ)

/-- An ordered trace composes into the run. -/
theorem OrderedTrace.run {κ : ℕ} {prog : Program} {image : MemImage κ} {n : ℕ}
    {states : Fin (n + 1) → Regs K} (h : OrderedTrace prog image n states) :
    run prog image n (states 0) = some (states (Fin.last n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hpc, hstep⟩ := h 0
    simp only [Fin.castSucc_zero] at hpc hstep
    rw [run_succ_of_ne hpc]
    rw [hstep]
    exact ih (states := fun i ↦ states i.succ) fun i ↦ h i.succ

/-- A run succeeds exactly when it has an ordered trace with the same endpoints. -/
theorem run_eq_some_iff_trace {κ : ℕ} (prog : Program) (image : MemImage κ)
    (n : ℕ) (initial final : Regs K) :
    run prog image n initial = some final ↔
      ∃ states : Fin (n + 1) → Regs K,
        states 0 = initial ∧ states (Fin.last n) = final ∧ OrderedTrace prog image n states := by
  constructor
  · intro h
    have hp : ∀ i : Fin (n + 1), ∃ r, run prog image i initial = some r := fun i ↦ by
      obtain ⟨r, hr, _⟩ := run_prefix (m := i) (n := n - i)
        (by rwa [Nat.add_sub_of_le (Nat.lt_succ_iff.mp i.isLt)])
      exact ⟨r, hr⟩
    choose states hs using hp
    refine ⟨states, (Option.some.inj (hs 0)).symm,
      Option.some.inj ((hs (Fin.last n)).symm.trans h), fun i ↦ ?_⟩
    have hnext := hs i.succ
    change run prog image ((i : ℕ) + 1) initial = some (states i.succ) at hnext
    rw [run_add, show (i : ℕ) = (i.castSucc : ℕ) from rfl, hs i.castSucc] at hnext
    change run prog image 1 (states i.castSucc) = some (states i.succ) at hnext
    have hpc := pc_ne_finalPc_of_run_succ hnext
    rw [run_succ_of_ne hpc] at hnext
    obtain ⟨r, hr, h0⟩ := Option.bind_eq_some_iff.mp hnext
    exact ⟨hpc, Option.some.inj h0 ▸ hr⟩
  · rintro ⟨states, rfl, rfl, ht⟩
    exact ht.run

/-- A valid execution is the public boundary and an ordered trace from the initial to the final
registers. -/
theorem validExecution_iff_trace (prog : Program) (input : PublicInput) (t : Trace prog) :
    ValidExecution prog input t ↔ HasPublicBoundary input t ∧
      ∃ states : Fin (t.steps + 1) → Regs K,
        states 0 = Regs.initial ∧ states (Fin.last t.steps) = Regs.final prog ∧
          OrderedTrace prog t.image t.steps states := by
  rw [ValidExecution, run_eq_some_iff_trace]

end LeanerVMTests.Semantics.RunTrace
