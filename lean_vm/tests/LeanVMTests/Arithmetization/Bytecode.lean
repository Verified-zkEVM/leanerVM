module

public import LeanVM.Arithmetization.Bytecode
meta import LeanVM.Arithmetization.Bytecode

/-!
# Tests: the bytecode encoding

One instruction per constructor, `DEREF` in each of its three modes, laid out by `entry` and read
back by `decode` under compiled evaluation. The slot positions are
pinned against the table of specification §8.1 (`08-end-to-end-protocol.tex:12-23`):
`SET_CONSTANT`'s `k₂` at slot 7 and `KECCAK`'s ten operands at slots 4 to 13 (`o_{m₀..m₃}, o_tail,
o_b8, o_cap, o_out` and the two layout flags). The flag pairs and the opcode words are pinned
against `cpu/isa.rs` and `tables.rs:99-104` (leanVM `3375f7a1`).
The mutations at the end reject the flag pair `(1, 1)`, a non-Boolean flag (`DEREF`'s and
`KECCAK`'s), an unknown opcode, and a nonzero spare slot; the first is also derived from
`decode_eq_none_iff`, so the rejection is a theorem and not only an evaluation.

Vector equalities are stated on word lists (`Vector.toList`), because core's `DecidableEq` for
`Vector` is not exposed to module-system importers.
-/

namespace LeanVMTests.Arithmetization

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization

public section

/-! ## One instruction per constructor -/

def xorI : Instr := .xor (gpow 2) (gpow 3) (gpow 4)
def mulI : Instr := .mulNative (gpow 2) (gpow 3) (gpow 4)
def setI : Instr := .setConstant (gpow 2) (E.ofLimbs (K.ofBits 7) (K.ofBits 8) (K.ofBits 9))
def derefCellI : Instr := .deref (gpow 4) 1 (gpow 5) .cell
def derefPcI : Instr := .deref (gpow 4) 1 (gpow 5) .pc
def derefFpI : Instr := .deref (gpow 4) 1 (gpow 5) .fp
def jumpI : Instr := .jump (gpow 2) (gpow 3) (gpow 4)
def keccakI : Instr := .keccak ![gpow 6, gpow 7, gpow 6, gpow 7] (gpow 8) (gpow 12) (gpow 13) (gpow 17)
  false true

/-! ## The flags and the codes -/

-- `Cell = (0, 0)`, `Pc = (1, 0)`, `Fp = (0, 1)` (`isa.rs:68-75`).
#guard derefFlags .cell = (0, 0)
#guard derefFlags .pc = (1, 0)
#guard derefFlags .fp = (0, 1)
#guard derefMode? 0 0 = some .cell
#guard derefMode? 1 0 = some .pc
#guard derefMode? 0 1 = some .fp
#guard derefMode? 1 1 = none

-- The six codes are the words `1, 2, 4, 8, 16, 32`; `0x40` and `0` are no opcode.
#guard opcode? 0x01 = some .xor
#guard opcode? (K.ofBits 0x02) = some .mulNative
#guard opcode? (K.ofBits 0x04) = some .setConstant
#guard opcode? (K.ofBits 0x08) = some .deref
#guard opcode? (K.ofBits 0x10) = some .jump
#guard opcode? (K.ofBits 0x20) = some .keccak
#guard opcode? (K.ofBits 0x40) = none
#guard opcode? 0 = none

/-! ## Slots 3 to 10 (specification §8.1) -/

#guard (entry xorI).toList = [Opcode.xor.code, gpow 2, gpow 3, gpow 4, 0, 0, 0, 0, 0, 0, 0]
#guard (entry mulI).toList = [Opcode.mulNative.code, gpow 2, gpow 3, gpow 4, 0, 0, 0, 0, 0, 0, 0]
#guard (entry setI).toList =
  [Opcode.setConstant.code, gpow 2, K.ofBits 7, K.ofBits 8, K.ofBits 9, 0, 0, 0, 0, 0, 0]
#guard (entry derefCellI).toList = [Opcode.deref.code, gpow 4, 1, gpow 5, 0, 0, 0, 0, 0, 0, 0]
#guard (entry derefPcI).toList = [Opcode.deref.code, gpow 4, 1, gpow 5, 1, 0, 0, 0, 0, 0, 0]
#guard (entry derefFpI).toList = [Opcode.deref.code, gpow 4, 1, gpow 5, 0, 1, 0, 0, 0, 0, 0]
#guard (entry jumpI).toList = [Opcode.jump.code, gpow 2, gpow 3, gpow 4, 0, 0, 0, 0, 0, 0, 0]
#guard (entry keccakI).toList =
  [Opcode.keccak.code, gpow 6, gpow 7, gpow 6, gpow 7, gpow 8, gpow 12, gpow 13, gpow 17, 0, 1]

-- The sixteen slots: the opcode at 3, the operands at 4 to 13, zero elsewhere.
#guard (encodeSlots setI).toList =
  [0, 0, 0, Opcode.setConstant.code, gpow 2, K.ofBits 7, K.ofBits 8, K.ofBits 9, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (encodeSlots keccakI).toList =
  [0, 0, 0, Opcode.keccak.code, gpow 6, gpow 7, gpow 6, gpow 7, gpow 8, gpow 12, gpow 13, gpow 17,
    0, 1, 0, 0]

/-- Slot 3 is the opcode, through `encodeSlots_getElem` and `entry_getElem_zero`. -/
example : (encodeSlots setI)[3] = Opcode.setConstant.code := by
  simp [encodeSlots_getElem, entry_getElem_zero, setI, Instr.opcode]

/-- `k₂` rides slot 7, checked in the kernel. -/
example : (encodeSlots setI)[7] = K.ofBits 9 := by decide +kernel

/-! ## Round trips -/

#guard decode (entry xorI) = some xorI
#guard decode (entry mulI) = some mulI
#guard decode (entry setI) = some setI
#guard decode (entry derefCellI) = some derefCellI
#guard decode (entry derefPcI) = some derefPcI
#guard decode (entry derefFpI) = some derefFpI
#guard decode (entry jumpI) = some jumpI
#guard decode (entry keccakI) = some keccakI
#guard decode (entry (.keccak ![1, g, gpow 2, gpow 3] (gpow 4) (gpow 8) (gpow 9) (gpow 13) true false)) =
  some (.keccak ![1, g, gpow 2, gpow 3] (gpow 4) (gpow 8) (gpow 9) (gpow 13) true false)

/-- The literal entry of `SET_CONSTANT` decodes to it: `decode` is exact. -/
example : decode #v[Opcode.setConstant.code, gpow 2, K.ofBits 7, K.ofBits 8, K.ofBits 9, 0, 0, 0, 0, 0, 0] =
    some setI :=
  decode_eq_some_iff.mpr rfl

-- The `DEREF` modes are told apart by their entries.
#guard (entry derefPcI).toList ≠ (entry derefFpI).toList
example : derefPcI ≠ derefFpI := fun h ↦ by cases h

/-! ## Nearby false statements -/

-- The flag pair `(1, 1)` is not an instruction, nor is a non-Boolean flag.
#guard decode #v[Opcode.deref.code, gpow 4, 1, gpow 5, 1, 1, 0, 0, 0, 0, 0] = none
#guard decode #v[Opcode.deref.code, gpow 4, 1, gpow 5, g, 0, 0, 0, 0, 0, 0] = none
-- An unknown opcode is not an instruction.
#guard decode #v[gpow 6, gpow 2, gpow 3, gpow 4, 0, 0, 0, 0, 0, 0, 0] = none
#guard decode #v[0, gpow 2, gpow 3, gpow 4, 0, 0, 0, 0, 0, 0, 0] = none
-- A nonzero spare entry coordinate is outside the canonical typed-program encoding.
#guard decode #v[Opcode.xor.code, gpow 2, gpow 3, gpow 4, 1, 0, 0, 0, 0, 0, 0] = none
#guard decode #v[Opcode.setConstant.code, gpow 2, K.ofBits 7, K.ofBits 8, K.ofBits 9, 1, 0, 0, 0, 0, 0] = none
#guard decode #v[Opcode.deref.code, gpow 4, 1, gpow 5, 1, 0, 0, 1, 0, 0, 0] = none
#guard decode #v[Opcode.jump.code, gpow 2, gpow 3, gpow 4, 0, 0, 0, 1, 0, 0, 0] = none
#guard decode #v[Opcode.jump.code, gpow 2, gpow 3, gpow 4, 0, 0, 0, 0, 0, 0, 1] = none
-- A `KECCAK` layout flag must be `0` or `1`.
#guard decode #v[Opcode.keccak.code, gpow 6, gpow 7, gpow 6, gpow 7, gpow 8, gpow 12, gpow 13, gpow 17,
  g, 1] = none
#guard decode #v[Opcode.keccak.code, gpow 6, gpow 7, gpow 6, gpow 7, gpow 8, gpow 12, gpow 13, gpow 17,
  0, g] = none

/-- As a theorem: the flag pair `(1, 1)` is no mode's flags, so the vector is no instruction's
entry. -/
example : decode #v[Opcode.deref.code, gpow 4, 1, gpow 5, 1, 1, 0, 0, 0, 0, 0] = none := by
  refine decode_eq_none_iff.mpr fun i h ↦ ?_
  have h0 := congrArg (fun v : Vector K 11 ↦ v[0]) h
  have h4 := congrArg (fun v : Vector K 11 ↦ v[4]) h
  have h5 := congrArg (fun v : Vector K 11 ↦ v[5]) h
  cases i <;> simp [entry, Opcode.code_injective.eq_iff] at h0 h4 h5
  rename_i mode
  cases mode <;> simp [derefFlags] at h4 h5

/-- The same, decided by the kernel. -/
example : decode #v[Opcode.deref.code, gpow 4, 1, gpow 5, 1, 1, 0, 0, 0, 0, 0] = none := by
  decide +kernel

end
end LeanVMTests.Arithmetization
