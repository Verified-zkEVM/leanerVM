/-
  LeanVM.Guest.B1.ExpKnownB

  `exponent_tables` under any semantics of `BLAKE2S`: it has no `BLAKE2S`, so its deployed
  meaning holds under every semantics.
-/

module

public import LeanVM.Guest.B1.Tables
public import LeanVM.Guest.SoundB

/-!
# `exponent_tables` under any semantics

`exponent_tables` (`B1.exponent_tables_iff`) neither hashes nor calls, so its relation is
the same under every `S : BlakeSem` (`Core.relB_iff_rel_of_freeOn`, the kernel checking that its
body has no `BLAKE2S` atom), and `main`'s second window may start from its tables under `S`
(`expKnownB`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- `exponent_tables` is free of `BLAKE2S` and calls nothing. -/
theorem freeOn_exponent_tables : coreProgram.FreeOn ["exponent_tables"] = true := by
  decide +kernel

/-- **`exponent_tables` under any semantics** is its deployed meaning. -/
theorem exponent_tables_iffB {S : BlakeSem} (rd : Reader) (args rets : List E) :
    coreProgram.RelB S rd "exponent_tables" args rets ↔ MeaningExponentTables rd args rets := by
  rw [relB_iff_rel_of_freeOn freeOn_exponent_tables (List.mem_singleton_self _),
    exponent_tables_iff]

/-- **`main`'s second window's fact, under any semantics.** -/
theorem expKnownB (S : BlakeSem) : End.ExpKnownB S :=
  fun rd _ _ h ↦ (exponent_tables_iffB rd [] _).mp h

end
end LeanVM.Guest.B1
