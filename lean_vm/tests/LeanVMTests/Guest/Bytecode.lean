import LeanVM.Guest.Bytecode

/-!
# The guest bytecode

`guest_fetch_of` at the first and last pcs of the largest compiled function after `__loop2`
(`sp_wots`, 23742 instructions over 12 chunks in three modules), at a `KECCAK` of each layout, at
the first and last
pcs of `verify_sig_lean_sphincs` and its first `KECCAK`, at `main`'s entry, at pc `0`, and the
padding; each side condition is one `decide +kernel`. The expected instructions are those of the guest's `DBG_DISASM` dump. And the
offset form of `KECCAK`'s cells.
-/

namespace LeanVMTests.Guest.Bytecode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

example : Data.functions.length = 992 := by decide +kernel

example : Data.codeLen = 488806 := rfl

/-- `sp_wots` is function 20, the largest after `__loop2` (function 37, 114219 instructions). -/
theorem spWots_mem : Data.f20 ∈ Data.functions := mem_functions (j := 20) rfl

example : Data.f20.name = "sp_wots" ∧ Data.f20.entryPc = 31267 ∧
    Data.f20.instructionCount = 23742 ∧ Data.f20.chunks.length = 12 := ⟨rfl, rfl, rfl, rfl⟩

/-- Its first instruction, `SET fp[2502] = 1`. -/
example : guestProgram.fetch (addressOfIndex 31267) = some (OffsetInstruction.set 2502 1 0
    0).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Its last, the return `JUMP if fp[2519] ≠ 0: pc = fp[0], fp = fp[1]`. -/
example : guestProgram.fetch (addressOfIndex 55008) = some (OffsetInstruction.jump 2519 0
    1).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 23741) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- A `KECCAK` writing the odd layout, `KECCAK fp[3291..+13] odd = keccak_f(fp[2], fp[3160],
fp[32], fp[71], tail = fp[3304..+4], b8 = fp[266], cap = fp[2520..+4]) even`. -/
example : guestProgram.fetch (addressOfIndex (31267 + 23668)) =
    some (OffsetInstruction.keccak 2 3160 32 71 3304 266 2520 3291 false
        true).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 23668) (by decide +kernel) rfl (by decide +kernel)

/-- The next, reading the odd layout, `KECCAK fp[3308..+13] even = keccak_f(fp[3321], fp[3322],
fp[3323], fp[3324], tail = fp[3325..+4], b8 = fp[3329], cap = fp[3300..+4]) odd`. -/
example : guestProgram.fetch (addressOfIndex (31267 + 23678)) =
    some (OffsetInstruction.keccak 3321 3322 3323 3324 3325 3329 3300 3308 true
        false).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 23678) (by decide +kernel) rfl (by decide +kernel)

/-- `verify_sig_lean_sphincs` is function 21 (after `sp_wots`, 20). -/
theorem sphincs_mem : Data.f21 ∈ Data.functions := mem_functions (j := 21) rfl

example : Data.f21.name = "verify_sig_lean_sphincs" ∧ Data.f21.entryPc = 55009 ∧
    Data.f21.instructionCount = 3036 := ⟨rfl, rfl, rfl⟩

/-- Its first instruction, `DEREF *(fp[2]·g^1) = fp[4]`. -/
example : guestProgram.fetch (addressOfIndex 55009) = some (OffsetInstruction.deref 2 1 4
    .cell).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Its last, the return `JUMP if fp[39] ≠ 0: pc = fp[0], fp = fp[1]`. -/
example : guestProgram.fetch (addressOfIndex 58044) = some (OffsetInstruction.jump 39 0
    1).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 3035) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The first digest call's `KECCAK`, `KECCAK fp[6..+13] = keccak_f(fp[4], fp[32], fp[33],
fp[34], tail = fp[35..+4], b8 = fp[40], cap = fp[42..+4])`, both layouts even. -/
example : guestProgram.fetch (addressOfIndex (55009 + 15)) =
    some (OffsetInstruction.keccak 4 32 33 34 35 40 42 6 false
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
    11064696544855033505 0 0).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f0) (mem_functions (j := 0) rfl) (i := 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The last slot is padding. -/
example : guestProgram.fetch (addressOfIndex (2 ^ 19 - 1)) = some
    OffsetInstruction.padding.toLeanIsaInstruction :=
  guest_fetch_pad (by decide) (by decide)

/-- The code list agrees with `instructionAt`. -/
example : Data.f21.code[3035]? = some (OffsetInstruction.jump 39 0 1) := by
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
