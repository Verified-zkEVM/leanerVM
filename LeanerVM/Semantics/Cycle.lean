/-
  LeanerVM.Semantics.Cycle

  Executable validation of finite register traces and candidate padding cycles.
-/

module

public import LeanerVM.Semantics.RunTrace
public import LeanerVM.Semantics.Executable

/-!
# Checked register traces and filler cycles

A candidate filler is checked against a supplied immutable program and image. Every
transition is checked, no transition starts at the sentinel, and the last state equals the
first. The checker does not take a main run or itself assert disjointness from one. It also
does not prove lookup-count balance, row-height budgets, existence of scratch space, or a
whole satisfying assignment. Those remain separate obligations for leanISA T1 completeness
and the Rust T2 boundary.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-- Check every transition of a finite register trace, including the pre-fetch halt rule. -/
def checkRunTrace {κ : ℕ} (prog : Program) (image : MemImage κ) {n : ℕ}
    (states : Fin (n + 1) → Regs K) : Bool :=
  decide (∀ i : Fin n, (states i.castSucc).pc ≠ prog.finalPc ∧
    stepChecked prog image (states i.castSucc) = some (states i.succ))

/-- Trace checking agrees with the relational reference trace within the address domain. -/
theorem checkRunTrace_eq_true_iff {κ : ℕ} (hκ : κ < 64) (prog : Program)
    (image : MemImage κ) {n : ℕ} (states : Fin (n + 1) → Regs K) :
    checkRunTrace prog image states = true ↔ RunTrace prog image n states := by
  simp only [checkRunTrace, decide_eq_true_eq, stepChecked_eq_step hκ, RunTrace, ProgramStep]

/-- Untrusted registers for one proposed filler cycle. -/
structure Cycle where
  /-- Number of instruction rows, including the closing JUMP. -/
  steps : ℕ
  /-- Ordered states with the last state repeating the first. -/
  states : Fin (steps + 1) → Regs K

/-- A nonempty closed reference trace. No public initial/final states are imposed on fillers. -/
def Cycle.Valid {κ : ℕ} (prog : Program) (image : MemImage κ) (cycle : Cycle) : Prop :=
  0 < cycle.steps ∧ RunTrace prog image cycle.steps cycle.states ∧
    cycle.states (Fin.last cycle.steps) = cycle.states 0

/-- Check local execution, nonempty length, and closure of a proposed filler cycle. -/
def checkCycle {κ : ℕ} (prog : Program) (image : MemImage κ) (cycle : Cycle) : Bool :=
  decide (0 < cycle.steps) && checkRunTrace prog image cycle.states &&
    decide (cycle.states (Fin.last cycle.steps) = cycle.states 0)

/-- Successful cycle checking certifies exactly the reference execution and closure. -/
theorem checkCycle_eq_true_iff {κ : ℕ} (hκ : κ < 64) (prog : Program)
    (image : MemImage κ) (cycle : Cycle) :
    checkCycle prog image cycle = true ↔ cycle.Valid prog image := by
  simp only [checkCycle, Bool.and_eq_true, decide_eq_true_eq,
    checkRunTrace_eq_true_iff hκ, Cycle.Valid, and_assoc]

/-- A checked filler returns to its starting registers after its actual number of rows. -/
theorem Cycle.Valid.run {κ : ℕ} {prog : Program} {image : MemImage κ} {cycle : Cycle}
    (h : cycle.Valid prog image) :
    run prog image cycle.steps (cycle.states 0) = some (cycle.states 0) := by
  simpa only [h.2.2] using h.2.1.run

end
end LeanerVM.Semantics
