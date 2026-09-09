module

public import LeanerVM.Parameters.Isa

/-!
# Layer 2 tests: opcode codes and instance caps

Kernel checks that the six codes are the words `1, 2, 4, 8, 16, 32`, bits `0` to `5` since
`g = x`, in the order of `crates/lean_vm/src/tables.rs:95-100`, and that the caps carry the
values of `cpu/mod.rs:51-64` and `crates/flock/src/hash.rs:283-286`. The caps are checked
against each other so that an announcement at the floor is admissible.
-/

namespace LeanerVMTests.Parameters

open LeanerVM.Parameters

public section

/-! ## Codes -/

/-- `OP_XOR = 1, OP_MUL = 2, OP_SET = 4, OP_DEREF = 8, OP_JUMP = 16, OP_BLAKE2S = 32`. -/
example : Opcode.xor.code = 0x01 ∧ Opcode.mulNative.code = 0x02 ∧ Opcode.setConstant.code = 0x04 ∧
    Opcode.deref.code = 0x08 ∧ Opcode.jump.code = 0x10 ∧ Opcode.blake2s.code = 0x20 := by
  decide +kernel

/-- The codes are the six lowest addresses, in order. -/
example : ∀ o : Opcode, o.code = gpow (Opcode.ctorIdx o) := by
  intro o; cases o <;> rfl

/-- Mutation: two codes never coincide; `code_injective` on the pair closest in the table. -/
example : Opcode.deref.code ≠ Opcode.jump.code :=
  fun h ↦ Opcode.noConfusion (Opcode.code_injective h)

/-! ## Caps -/

example : minLogMem = 16 ∧ maxLogMem = 32 ∧ maxLogRows = 32 ∧ maxLogBytecode = 32 ∧
    minLogRowsBlake2s = 3 := by
  decide

/-- The floors are below the caps: the smallest announcement is admissible. -/
example : minLogMem ≤ maxLogMem ∧ minLogRowsBlake2s ≤ maxLogRows := by decide

/-- Every cap keeps its address space inside the order of `g`, which `gLog?_spec` needs. -/
example : maxLogMem < 64 ∧ maxLogBytecode < 64 := by decide

end
end LeanerVMTests.Parameters
