/-
  LeanerVM.Semantics.WellFormedBytecode

  The program-shape conditions under which a witness of the constraint statement describes an
  execution.
-/

module

public import LeanerVM.Semantics.Execution

/-!
# Well-formed bytecode

Category A: the bytecode a compiler emits, as far as constraint soundness needs it. The sentinel
slot, the last bytecode slot, halts the machine and is never executed; it must not hold a `JUMP`
(`SentinelSafe`). A `JUMP` there lets the constraint system's state walk leave the sentinel and
return to it, so for some such program a witness of the constraint statement describes no
execution at all. leanVM's compiler pads the sentinel slot with `SET_CONSTANT`
(`crates/lean_compiler/src/lib.rs:162` at leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`).
Constraint completeness needs the fill blocks as well; they will be a later field, which no
soundness statement reads.
-/

namespace LeanerVM.Semantics

@[expose] public section

/-- **Well-formed bytecode**: the program-shape conditions of constraint soundness. -/
structure WellFormedBytecode (prog : Program) : Prop where
  /-- The sentinel slot is not a `JUMP`. -/
  sentinelSafe : SentinelSafe prog

/-- Well-formedness is decided from the last typed instruction. -/
instance (prog : Program) : Decidable (WellFormedBytecode prog) :=
  decidable_of_iff (SentinelSafe prog) ⟨fun h ↦ ⟨h⟩, fun h ↦ h.1⟩

end

end LeanerVM.Semantics
