/-
  LeanerVM.Arithmetization.Tables.Basic

  The vocabulary the six opcode tables share, and that the boundary blocks of Layer 7 reuse: the
  state step and fetch of an opcode row, the row environment, and the two `Option` facts that
  turn a `guard` of `execute` into an equation.
-/

module

public import LeanerVM.Arithmetization.Channels

@[expose] public section

/-!
# Shared vocabulary of the tables

leanISA roadmap Layer 6 (`docs/roadmap/leanisa-blueprint.md`). Category A: nothing here is
transcribed. What the tables share beyond this file lives where it belongs: the limb
arithmetic (`add_limbs`, `mul_limbs`, `ofK_eq_ofLimbs`, `isInK_ofLimbs`, `ofLimbs_of_isInK`,
`ofLimbs_eq_zero_iff`, `E.ofCell`) is Layer 0's (`LeanerVM.Parameters.Field`), and reading a
word of the image back as a row's limbs (`MemImage.limbsAt`, `MemImage.cellAt`) is Layer 2's
(`LeanerVM.Semantics.Memory`). A row's three-limb column `v` is the word
`E.ofLimbs v[0] v[1] v[2]`, spelled as Layer 5's `MemPull.Guarantees` spells it.

* `instructionStep` is what every opcode row does first: pull its state `(pc, fp)`, push its
  successor, and read its bytecode entry at `pc`.
* `rowEnv data` is the prover environment of a row of a table without local witnesses: no
  witness slots, the data, no hints. `*_exec_complete` states completeness in it, and so do the
  boundary blocks of Layer 7 (`LeanerVM.Arithmetization.Boundary`).
* `guard_bind_eq_some_iff` and `guard_eq_some` are the `Option` facts the `*_spec_iff`
  characterisations and the row builders need: `execute` checks each relation with `guard`,
  and `guard p >>= f = some b` says `p` and `f () = some b`.
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

/-- The state step and fetch of an opcode row: pull the state `(pc, fp)`, push the successor
`next`, and read the bytecode entry `(op, operands)` at `pc` with count `rbc`. -/
def instructionStep (pc fp rbc : Expression K) (next : Var Regs K) (op : Opcode)
    (operands : Vector (Expression K) 7) : Circuit K Unit := do
  StatePull.pull ⟨pc, fp⟩
  StatePush.push next
  bytecodeRead pc rbc (Expression.const op.code) operands

/-- The prover environment of a row of a table without local witnesses: no witness slots
(every slot reads `0`), the data, no hints. -/
def rowEnv (data : ProverData K) : ProverEnvironment K := ⟨⟨fun _ ↦ 0, data⟩, default⟩

/-- A guarded `Option` computation succeeds exactly when the guard holds and the rest does. -/
theorem guard_bind_eq_some_iff {α : Type} (p : Prop) [Decidable p] (f : Unit → Option α)
    (b : α) : Option.bind (guard p) f = some b ↔ p ∧ f () = some b := by
  unfold guard
  split_ifs with h
  · simp [h]
  · simp [h]

/-- A guard that succeeds holds. -/
theorem guard_eq_some {p : Prop} [Decidable p] {u : Unit} (h : (guard p : Option Unit) = some u) :
    p := by
  unfold guard at h
  split_ifs at h with hp
  exact hp

end LeanerVM.Arithmetization
