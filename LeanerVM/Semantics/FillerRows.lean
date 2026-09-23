/-
  LeanerVM.Semantics.FillerRows

  Checking an unordered collection of candidate filler rows.
-/

module

public import LeanerVM.Semantics.Executable

/-!
# Filler-row execution and state balance

Rust exports rows grouped by opcode, not as one ordered filler trace. The multiset of their
starting states must match the multiset of their checked successors. Keeping `Option` in this
comparison makes any failed step invalidate the check. Multiplicities are natural list
multiplicities, never sums in the characteristic-two field. This is a semantic row check;
it does not take a main run or establish disjointness from one. It also does not check
memory/bytecode lookup counts, table capacities, or Rust correspondence.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-- Every filler begins away from the sentinel, and the reference successors have exactly
the same natural multiplicities as the starting states. Failure cannot match a starting state. -/
def FillerRowsValid {κ : ℕ} (prog : Program) (image : MemImage κ)
    (starts : List (Regs K)) : Prop :=
  (∀ r ∈ starts, r.pc ≠ prog.finalPc) ∧
    (starts.map some).Perm (starts.map (step prog image))

/-- Check every filler row against the fixed image and check natural state multiplicities. -/
def checkFillerRows {κ : ℕ} (prog : Program) (image : MemImage κ)
    (starts : List (Regs K)) : Bool :=
  decide ((∀ r ∈ starts, r.pc ≠ prog.finalPc) ∧
    (starts.map some).Perm (starts.map (stepChecked prog image)))

/-- Executable filler-row checking has exactly the reference meaning within the address bound. -/
theorem checkFillerRows_eq_true_iff {κ : ℕ} (hκ : κ < 64) (prog : Program)
    (image : MemImage κ) (starts : List (Regs K)) :
    checkFillerRows prog image starts = true ↔ FillerRowsValid prog image starts := by
  unfold checkFillerRows FillerRowsValid
  rw [show stepChecked prog image = step prog image from
    funext (stepChecked_eq_step hκ prog image)]
  simp only [decide_eq_true_eq]

/-- Every accepted row has a real successor, and that successor occurs among the starts. -/
theorem FillerRowsValid.step_mem {κ : ℕ} {prog : Program} {image : MemImage κ}
    {starts : List (Regs K)} (h : FillerRowsValid prog image starts)
    {r : Regs K} (hr : r ∈ starts) :
    ∃ next ∈ starts, step prog image r = some next := by
  have hm : step prog image r ∈ starts.map some :=
    h.2.mem_iff.mpr (List.mem_map_of_mem hr)
  obtain ⟨next, hn, he⟩ := List.mem_map.mp hm
  exact ⟨next, hn, he.symm⟩

end
end LeanerVM.Semantics
