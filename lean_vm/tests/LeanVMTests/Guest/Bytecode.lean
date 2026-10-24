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

example : Data.functions.length = 900 := by decide +kernel

example : Data.codeLen = 363731 := rfl

/-- `verify_sig_lean_sphincs` is function 21. -/
theorem sphincs_mem : Data.f21 ∈ Data.functions := mem_functions (j := 21) rfl

example : Data.f21.name = "verify_sig_lean_sphincs" ∧ Data.f21.entry = 53220 ∧
    Data.f21.len = 100444 := ⟨rfl, rfl, rfl⟩

/-- Its first instruction, `DEREF *(fp[2]·g^1) = fp[4]`. -/
example : guest.fetch (gpow 53220) = some (OInstr.deref 2 1 4 .cell).toInstr :=
  guest_fetch_of sphincs_mem (i := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Its last, the return `JUMP if fp[26] ≠ 0: pc = fp[0], fp = fp[1]`. -/
example : guest.fetch (gpow 153663) = some (OInstr.jump 26 0 1).toInstr :=
  guest_fetch_of sphincs_mem (i := 100443) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- A `KECCAK` writing the odd layout, `KECCAK fp[3296..+13] odd = keccak_f(fp[139], fp[140],
fp[141], fp[142], tail = fp[143..+4], b8 = fp[147], cap = fp[29..+4]) even`. -/
example : guest.fetch (gpow (53220 + 76547)) =
    some (OInstr.keccak 139 140 141 142 143 147 29 3296 false true).toInstr :=
  guest_fetch_of sphincs_mem (i := 76547) (by decide +kernel) rfl (by decide +kernel)

/-- `main`'s first instruction, `SET fp[10] = g^65535`, the immediate as its bits. -/
example : guest.fetch (gpow 8473) = some (OInstr.set 10 9272771591053052074 0 0).toInstr :=
  guest_fetch_of (f := Data.f1) (mem_functions (j := 1) rfl) (i := 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- `main`'s first `KECCAK`, both layouts even. -/
example : guest.fetch (gpow 8595) =
    some (OInstr.keccak 80 81 84 85 112 117 113 99 false false).toInstr :=
  guest_fetch_of (f := Data.f1) (mem_functions (j := 1) rfl) (i := 122) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The first instruction of the program, in `__jump_tables`, `SET fp[427] = g^159283`. -/
example : guest.fetch (gpow 0) = some (OInstr.set 427 16960105817094266212 0 0).toInstr :=
  guest_fetch_of (f := Data.f0) (mem_functions (j := 0) rfl) (i := 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The last slot is padding. -/
example : guest.fetch (gpow (2 ^ 19 - 1)) = some OInstr.pad.toInstr :=
  guest_fetch_pad (by decide) (by decide)

/-- The code list agrees with `instrAt`. -/
example : Data.f21.code[100443]? = some (OInstr.jump 26 0 1) := by
  rw [CompiledFn.getElem?_code (CompiledFn.wellChunked_of_mem sphincs_mem) (by decide +kernel)]
  decide +kernel

/-! ## `KECCAK`'s cells in offset form -/

example : keccakIns 139 140 141 142 143 147 29 =
    [139, 140, 141, 142, 143, 144, 145, 146, 147, 29, 30, 31, 32] := by decide

example : keccakOuts 3296 = (List.range 13).map (3296 + ·) := rfl

/-- The instruction's read addresses are the offsets `keccakIns`, its written ones `keccakOuts`. -/
example (c : Fin 13) :
    keccakInOffset ![gpow 139, gpow 140, gpow 141, gpow 142] (gpow 143) (gpow 147) (gpow 29) c =
      gpow ((keccakIns 139 140 141 142 143 147 29).getD c 0) := by
  rw [keccakInOffset_gpow, keccakIns_getD _ _ _ _ _ _ _ c.isLt]

example (k : Fin 13) : g ^ k.val * gpow 3296 = gpow ((keccakOuts 3296).getD k 0) := by
  rw [keccakOutOffset_gpow, keccakOuts_getD _ k.isLt]

end LeanVMTests.Guest.Bytecode
