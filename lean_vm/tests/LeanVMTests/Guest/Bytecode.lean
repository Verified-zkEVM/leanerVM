import LeanVM.Guest.Bytecode

/-!
# The guest bytecode

`guest_fetch_of` at the first and last pcs of the largest compiled function
(`verify_sig_lean_sphincs`, 100444 instructions over 50 chunks in six modules), at a `KECCAK` of
each layout, at `main`'s entry, at pc `0`, and the padding; each side condition is one
`decide +kernel`. The expected instructions are those of the guest's `DBG_DISASM` dump. And the
offset form of `KECCAK`'s cells.
-/

namespace LeanVMTests.Guest.Bytecode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

example : Data.functions.length = 884 := by decide +kernel

example : Data.codeLen = 362263 := rfl

/-- `verify_sig_lean_sphincs` is function 21. -/
theorem sphincs_mem : Data.f21 ∈ Data.functions := mem_functions (j := 21) rfl

example : Data.f21.name = "verify_sig_lean_sphincs" ∧ Data.f21.entryPc = 53169 ∧
    Data.f21.instructionCount = 100444 := ⟨rfl, rfl, rfl⟩

/-- Its first instruction, `DEREF *(fp[2]·g^1) = fp[4]`. -/
example : guestProgram.fetch (addressOfIndex 53169) = some (OffsetInstruction.deref 2 1 4
    .cell).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Its last, the return `JUMP if fp[26] ≠ 0: pc = fp[0], fp = fp[1]`. -/
example : guestProgram.fetch (addressOfIndex 153612) = some (OffsetInstruction.jump 26 0
    1).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 100443) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- A `KECCAK` writing the odd layout, `KECCAK fp[3296..+13] odd = keccak_f(fp[139], fp[140],
fp[141], fp[142], tail = fp[143..+4], b8 = fp[147], cap = fp[29..+4]) even`. -/
example : guestProgram.fetch (addressOfIndex (53169 + 76547)) =
    some (OffsetInstruction.keccak 139 140 141 142 143 147 29 3296 false
        true).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 76547) (by decide +kernel) rfl (by decide +kernel)

/-- `main`'s first instruction, `SET fp[10] = g^65535`, the immediate as its bits. -/
example : guestProgram.fetch (addressOfIndex 8456) = some (OffsetInstruction.set 10
    9272771591053052074 0 0).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f1) (mem_functions (j := 1) rfl) (i := 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- `main`'s `KECCAK`, both layouts even: the digest of the DA claim it checks directly
(`keccak([root_0, root_1], [vector_0, vector_1], own_da[0:2])`), `KECCAK fp[345..+13] even =
keccak_f(fp[339], fp[340], fp[341], fp[342], tail = fp[358..+4], b8 = fp[363], cap = fp[359..+4])
even`. -/
example : guestProgram.fetch (addressOfIndex 9093) =
    some (OffsetInstruction.keccak 339 340 341 342 358 363 359 345 false
        false).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f1) (mem_functions (j := 1) rfl) (i := 637) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The first instruction of the program, in `__jump_tables`, `SET fp[406] = g^159148`. -/
example : guestProgram.fetch (addressOfIndex 0) = some (OffsetInstruction.set 406
    13063652579795698784 0 0).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f0) (mem_functions (j := 0) rfl) (i := 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The last slot is padding. -/
example : guestProgram.fetch (addressOfIndex (2 ^ 19 - 1)) = some
    OffsetInstruction.padding.toLeanIsaInstruction :=
  guest_fetch_pad (by decide) (by decide)

/-- The code list agrees with `instructionAt`. -/
example : Data.f21.code[100443]? = some (OffsetInstruction.jump 26 0 1) := by
  rw [CompiledFunction.getElem?_code (CompiledFunction.wellChunked_of_mem sphincs_mem)
      (by decide +kernel)]
  decide +kernel

/-! ## `KECCAK`'s cells in offset form -/

example : keccakIns 139 140 141 142 143 147 29 =
    [139, 140, 141, 142, 143, 144, 145, 146, 147, 29, 30, 31, 32] := by decide

example : keccakOuts 3296 = (List.range 13).map (3296 + ·) := rfl

/-- The instruction's read addresses are the offsets `keccakIns`, its written ones `keccakOuts`. -/
example (c : Fin 13) :
    keccakInputCellOffset ![addressOfIndex 139, addressOfIndex 140, addressOfIndex 141,
        addressOfIndex 142] (addressOfIndex 143) (addressOfIndex 147) (addressOfIndex 29) c =
      addressOfIndex ((keccakIns 139 140 141 142 143 147 29).getD c 0) := by
  rw [keccakInOffset_gpow, keccakIns_getD _ _ _ _ _ _ _ c.isLt]

example (k : Fin 13) : g ^ k.val * addressOfIndex 3296 = addressOfIndex ((keccakOuts 3296).getD k
    0) := by
  rw [keccakOutOffset_gpow, keccakOuts_getD _ k.isLt]

end LeanVMTests.Guest.Bytecode
