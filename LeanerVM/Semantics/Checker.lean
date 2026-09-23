/-
  LeanerVM.Semantics.Checker

  Fuel-bounded execution checking with explicit failure results.
-/

module

public import LeanerVM.Semantics.Executable

/-!
# Bounded checking

`runToHalt` searches for the first sentinel arrival within a supplied transition budget.
It distinguishes invalid steps, an incorrect final frame, and exhaustion of that budget.
`checkWithinFuel` additionally checks the public memory boundary. This is fixed-image
validation of the reference ISA at leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`;
it does not construct a witness or justify a Rust executor's success domain.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-- Failure modes of bounded execution checking. Exhausting fuel makes no claim that a
longer run is invalid; the other cases identify failed semantic or public-boundary checks. -/
inductive CheckError
  | publicBoundary
  | invalidStep
  | finalFrame
  | fuelExhausted
  deriving DecidableEq, Repr

/-- Run to the sentinel in at most `fuel` transitions. The result counts only main-run
steps; no filler rows are appended. At zero fuel an already halted state
succeeds, while a nonterminal state reports exhaustion. -/
def runToHalt {κ : ℕ} (prog : Program) (image : MemImage κ) :
    ℕ → Regs K → Except CheckError ℕ
  | fuel, r =>
    if r.pc = prog.finalPc then
      if r.fp = 1 then .ok 0 else .error .finalFrame
    else match fuel with
      | 0 => .error .fuelExhausted
      | fuel + 1 => match stepChecked prog image r with
        | none => .error .invalidStep
        | some next => (runToHalt prog image fuel next).map (· + 1)

/-- Check public memory and find a valid exact main-run length within the supplied fuel.
The image is preserved verbatim; the returned count can be used in `Trace`. -/
def checkWithinFuel {κ : ℕ} (prog : Program) (input : PublicInput) (image : MemImage κ)
    (fuel : ℕ) : Except CheckError ℕ :=
  if checkBoundary input (⟨κ, image, 0⟩ : Trace prog) then
    runToHalt prog image fuel Regs.initial
  else .error .publicBoundary

/-! ## Refinement -/

/-- Every successful bounded check gives an exact reference execution of the reported
length, and every such execution within the budget is found. -/
theorem runToHalt_eq_ok_iff {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ)
    (fuel n : ℕ) (r : Regs K) :
    runToHalt prog image fuel r = .ok n ↔
      n ≤ fuel ∧ run prog image n r = some (Regs.final prog) := by
  induction fuel generalizing r n with
  | zero =>
    rw [runToHalt]
    split_ifs with hpc hfp
    · have hr : r = Regs.final prog := by cases r; cases hpc; cases hfp; rfl
      subst r
      cases n <;> simp
    · have hr : r ≠ Regs.final prog := fun h ↦ hfp (congrArg Regs.fp h)
      cases n <;> simp [hr]
    · have hr : r ≠ Regs.final prog := fun h ↦ hpc (congrArg Regs.pc h)
      cases n <;> simp [hr]
  | succ fuel ih =>
    rw [runToHalt]
    split_ifs with hpc hfp
    · have hr : r = Regs.final prog := by cases r; cases hpc; cases hfp; rfl
      subst r
      cases n with
      | zero => simp
      | succ n => simp [run_succ_of_eq hpc]
    · cases n with
      | zero =>
        have hr : r ≠ Regs.final prog := fun h ↦ hfp (congrArg Regs.fp h)
        simp [hr]
      | succ n => simp [run_succ_of_eq hpc]
    · rw [stepChecked_eq_step hκ]
      cases hs : step prog image r with
      | none =>
        cases n with
        | zero =>
          have hr : r ≠ Regs.final prog := fun h ↦ hpc (congrArg Regs.pc h)
          simp [hr]
        | succ n => simp [run_succ_of_ne hpc, hs]
      | some next =>
        cases n with
        | zero =>
          have hr : r ≠ Regs.final prog := fun h ↦ hpc (congrArg Regs.pc h)
          cases he : runToHalt prog image fuel next <;> simp [he, Except.map, hr]
        | succ n =>
          have hm : (runToHalt prog image fuel next).map (· + 1) = .ok (n + 1) ↔
              runToHalt prog image fuel next = .ok n := by
            cases runToHalt prog image fuel next <;> simp [Except.map]
          rw [hm, ih]
          simp only [Nat.add_le_add_iff_right, run_succ_of_ne hpc, hs, Option.bind_eq_bind, Option.bind_some]

/-- The public bounded checker accepts exactly valid executions whose length fits the
budget. This theorem also excludes oversized images and wrong public words. -/
theorem checkWithinFuel_eq_ok_iff {κ : ℕ} (prog : Program) (input : PublicInput)
    (image : MemImage κ) (fuel n : ℕ) :
    checkWithinFuel prog input image fuel = .ok n ↔
      n ≤ fuel ∧ ValidExecution prog input ⟨κ, image, n⟩ := by
  unfold checkWithinFuel
  split_ifs with hb
  · have hb' := (checkBoundary_eq_true_iff input _).mp hb
    have hκ : κ < 64 := lt_of_le_of_lt hb'.2.1 (by decide)
    rw [runToHalt_eq_ok_iff hκ]
    simp only [ValidExecution, show HasPublicBoundary input (⟨κ, image, n⟩ : Trace prog)
      from hb', true_and]
  · have hb' : ¬ HasPublicBoundary input (⟨κ, image, n⟩ : Trace prog) := by
      intro h
      exact hb ((checkBoundary_eq_true_iff input _).mpr h)
    simp [ValidExecution, hb']

end
end LeanerVM.Semantics
