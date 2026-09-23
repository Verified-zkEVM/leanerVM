/-
  LeanerVM.Semantics.TraceInput

  Checked adaptation of finite memory exports and main/filler instruction counts.
-/

module

public import LeanerVM.Semantics.Checker

/-!
# Finite execution exports

Rust leanVM `48a904208d682848dac0e18ef8b01ebfc40df9ad` reports `base_counts` before filling
and `cycles` after filling. `TraceInput` records the finite data needed to adapt that shape
without confusing the two lengths. Counts are natural numbers after unsigned conversion.
This adapter checks memory shape and accounting, then optionally validates the main run.
It does not certify exported counts against actual Rust rows, validate filler rows,
or establish a correspondence to the Rust source; those are distinct T2 obligations.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-- A finite final image together with main and total row-count announcements, in opcode
order XOR, MUL_NATIVE, SET_CONSTANT, DEREF, JUMP, BLAKE2S. All fields are untrusted input. -/
structure TraceInput where
  /-- Exact final memory, including padding and scratch cells. -/
  memory : Array E
  /-- Number of main-run rows per opcode, before filler traversal. -/
  mainCounts : Vector ℕ 6
  /-- Number of rows per opcode after filler traversal. -/
  rowCounts : Vector ℕ 6
  /-- Total instructions executed by witness generation, including fillers. -/
  cycles : ℕ

/-- Main-run transitions, summed in unbounded natural-number arithmetic. -/
def TraceInput.mainSteps (input : TraceInput) : ℕ := input.mainCounts.toList.sum

/-- Rows attributed to filler traversal, after the announced main-run counts. -/
def TraceInput.fillerSteps (input : TraceInput) : ℕ :=
  (input.rowCounts.toList.zipWith (· - ·) input.mainCounts.toList).sum

/-- Main counts cannot exceed total counts, and total rows agree with `cycles`.
These are accounting conditions, not proofs that any announced row exists or is valid. -/
def TraceInput.Accounted (input : TraceInput) : Prop :=
  (∀ i : Fin 6, input.mainCounts[i] ≤ input.rowCounts[i]) ∧
    input.cycles = input.rowCounts.toList.sum

instance (input : TraceInput) : Decidable input.Accounted :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Convert an export after checking its memory shape, memory caps and count accounting.
Every original word is retained; main-run validity is checked separately by `validateInput`.
The caller supplies the typed public program whose binding must be justified at the boundary. -/
def TraceInput.adapt (prog : Program) (input : TraceInput) : Option (Trace prog) :=
  let κ := Nat.log 2 input.memory.size
  if h : input.memory.size = 2 ^ κ ∧ minLogMem ≤ κ ∧ κ ≤ maxLogMem ∧ input.Accounted then
    some ⟨κ, fun i ↦ input.memory[i.val]'(by have := i.isLt; omega), input.mainSteps⟩
  else none

/-- Validate the main run in an adapted export against the supplied public program/input.
Success says nothing about the separate filler rows or a Rust producer's correctness. -/
def validateInput (prog : Program) (publicInput : PublicInput) (input : TraceInput) : Bool :=
  match input.adapt prog with
  | none => false
  | some t => checkTrace prog publicInput t

/-- Adapting preserves the exact whole image and uses the main count, never total cycles. -/
theorem TraceInput.adapt_preserves {prog : Program} {input : TraceInput} {t : Trace prog}
    (h : input.adapt prog = some t) :
    input.Accounted ∧ input.memory.size = 2 ^ t.κ ∧
      t.steps = input.mainSteps ∧
      ∀ i : Fin (2 ^ t.κ), input.memory[i.val]? = some (t.image i) := by
  unfold adapt at h
  dsimp only at h
  split_ifs at h with hs
  · cases h
    refine ⟨hs.2.2.2, hs.1, rfl, ?_⟩
    intro i
    have hi : i.val < 2 ^ Nat.log 2 input.memory.size := i.isLt
    exact Array.getElem?_eq_getElem (by omega)

/-- Export validation is equivalent to successful adaptation and a valid reference run. -/
theorem validateInput_eq_true_iff (prog : Program) (publicInput : PublicInput)
    (input : TraceInput) :
    validateInput prog publicInput input = true ↔
      ∃ t, input.adapt prog = some t ∧ ValidExecution prog publicInput t := by
  unfold validateInput
  cases h : input.adapt prog with
  | none => simp
  | some t =>
    simp only [checkTrace_eq_true_iff, Option.some.injEq]
    exact ⟨fun ht ↦ ⟨t, rfl, ht⟩, by rintro ⟨_, rfl, ht⟩; exact ht⟩

end
end LeanerVM.Semantics
