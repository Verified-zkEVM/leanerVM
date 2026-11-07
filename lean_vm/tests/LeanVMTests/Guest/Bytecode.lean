import LeanVM.Guest.Bytecode

/-!
# The guest bytecode

`guest_fetch_of` at the first and last pcs of the largest compiled function after `__loop2`
(`sp_wots`, 23713 instructions over 12 chunks in three modules), at a `KECCAK` of each layout, at
the first and last
pcs of `verify_sig_lean_sphincs` and its first `KECCAK`, at `main`'s entry, at pc `0`, and the
padding; each side condition is one `decide +kernel`. The expected instructions are those of the guest's `DBG_DISASM` dump. And the
offset form of `KECCAK`'s cells.
-/

namespace LeanVMTests.Guest.Bytecode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

example : Data.functions.length = 992 := by decide +kernel

example : Data.codeLen = 490357 := rfl

/-- `sp_wots` is function 20, the largest after `__loop2` (function 37, 114219 instructions). -/
theorem spWots_mem : Data.f20 ∈ Data.functions := mem_functions (j := 20) rfl

example : Data.f20.name = "sp_wots" ∧ Data.f20.entryPc = 31267 ∧
    Data.f20.instructionCount = 23713 ∧ Data.f20.chunks.length = 12 := ⟨rfl, rfl, rfl, rfl⟩

/-- Its first instruction, `SET fp[9] = 1`. -/
example : guestProgram.fetch (addressOfIndex 31267) = some (OffsetInstruction.set 9 1 0
    0).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Its last, the return `JUMP if fp[9] ≠ 0: pc = fp[0], fp = fp[1]`. -/
example : guestProgram.fetch (addressOfIndex 54979) = some (OffsetInstruction.jump 9 0
    1).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 23712) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- A `KECCAK` writing the odd layout, `KECCAK fp[3358..+13] odd = keccak_f(fp[3371], fp[3372],
fp[3373], fp[3374], tail = fp[3375..+4], b8 = fp[3379], cap = fp[3345..+4]) even`. -/
example : guestProgram.fetch (addressOfIndex (31267 + 23699)) =
    some (OffsetInstruction.keccak 3371 3372 3373 3374 3375 3379 3345 3358 false
        true).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 23699) (by decide +kernel) rfl (by decide +kernel)

/-- The next, reading the odd layout, `KECCAK fp[3149..+13] even = keccak_f(fp[3380], fp[3381],
fp[3382], fp[3383], tail = fp[3384..+4], b8 = fp[3389], cap = fp[3367..+4]) odd`. -/
example : guestProgram.fetch (addressOfIndex (31267 + 23710)) =
    some (OffsetInstruction.keccak 3380 3381 3382 3383 3384 3389 3367 3149 true
        false).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 23710) (by decide +kernel) rfl (by decide +kernel)

/-- `verify_sig_lean_sphincs` is function 21 (after `sp_wots`, 20). -/
theorem sphincs_mem : Data.f21 ∈ Data.functions := mem_functions (j := 21) rfl

example : Data.f21.name = "verify_sig_lean_sphincs" ∧ Data.f21.entryPc = 54980 ∧
    Data.f21.instructionCount = 4616 := ⟨rfl, rfl, rfl⟩

/-- Its first instruction, `DEREF *(fp[2]·g^0) = fp[4]`. -/
example : guestProgram.fetch (addressOfIndex 54980) = some (OffsetInstruction.deref 2 0 4
    .cell).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Its last, the return `JUMP if fp[39] ≠ 0: pc = fp[0], fp = fp[1]`. -/
example : guestProgram.fetch (addressOfIndex 59595) = some (OffsetInstruction.jump 39 0
    1).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 4615) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- Its first `KECCAK`, `H_msg`'s first call, `KECCAK fp[9..+13] = keccak_f(fp[8], fp[4], fp[5],
fp[6], tail = fp[35..+4], b8 = fp[40], cap = fp[42..+4])`, both layouts even. -/
example : guestProgram.fetch (addressOfIndex (54980 + 15)) =
    some (OffsetInstruction.keccak 8 4 5 6 35 40 42 9 false
        false).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 15) (by decide +kernel) rfl (by decide +kernel)

/-- `main`'s first instruction, `SET fp[10] = g^65535`, the immediate as its bits. -/
example : guestProgram.fetch (addressOfIndex 16555) = some (OffsetInstruction.set 10
    9272771591053052074 0 0).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f1) (mem_functions (j := 1) rfl) (i := 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- `main`'s `KECCAK`, both layouts even: the digest of the DA claim it checks directly
(`keccak([root_0, root_1], [z_0, z_1], own_da[0:2])`), `KECCAK fp[396..+13] even =
keccak_f(fp[390], fp[391], fp[392], fp[393], tail = fp[409..+4], b8 = fp[414], cap = fp[410..+4])
even`. -/
example : guestProgram.fetch (addressOfIndex 17293) =
    some (OffsetInstruction.keccak 390 391 392 393 409 414 410 396 false
        false).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f1) (mem_functions (j := 1) rfl) (i := 738) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The first instruction of the program, in `__jump_tables`: `SET fp[455]` to a jump target, a
power of `g`. -/
example : guestProgram.fetch (addressOfIndex 0) = some (OffsetInstruction.set 455
    2720299075214271059 0 0).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f0) (mem_functions (j := 0) rfl) (i := 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The last slot is padding. -/
example : guestProgram.fetch (addressOfIndex (2 ^ 19 - 1)) = some
    OffsetInstruction.padding.toLeanIsaInstruction :=
  guest_fetch_pad (by decide) (by decide)

/-- The code list agrees with `instructionAt`. -/
example : Data.f21.code[4615]? = some (OffsetInstruction.jump 39 0 1) := by
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
