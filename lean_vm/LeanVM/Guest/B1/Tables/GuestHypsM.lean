/-
  LeanVM.Guest.B1.Tables.GuestHypsM

  The three fields of `Located.GuestHypsM` that `verify_bus_gkr`, `verify_tables` and
  `verify_flock` give, over every hash model, at the deployed guest's bytecode.
-/

module

public import LeanVM.Guest.End
public import LeanVM.Guest.B1.Tables.GkrM
public import LeanVM.Guest.B1.Tables.FlockM
public import LeanVM.Guest.B1.Tables.VerifyTablesM

/-!
# The tables' callees over every hash model

`guest_knowledge_model`'s hypotheses (`Located.GuestHypsM M`) that rest on group 5, on every
memory `Main.MemOk` admits, for every hash model `M`:

* `guestHypsM_gkr`: `verify_bus_gkr` (`verify_bus_gkr_model`);
* `guestHypsM_tables`: `verify_tables` at the guest's bytecode `End.bytecode` of `2^22` words,
  with the terminal's context `TCtx` (`verify_tables_model`);
* `guestHypsM_flock`: `verify_flock` (`verify_flock_model`, on every reader).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Value

@[expose] public section

/-- **`verify_bus_gkr` over every model**, on every memory `Main.MemOk` admits: the field `gkr`
of `Located.GuestHypsM M`. -/
theorem guestHypsM_gkr (M : HashModel) : ∀ rd, Main.MemOk rd → SoundGkrM M rd :=
  soundGkrM_model M

/-- **`verify_tables` over every model**, at the guest's bytecode, on every memory `Main.MemOk`
admits: the field `tables` of `Located.GuestHypsM M`. -/
theorem guestHypsM_tables (M : HashModel) :
    ∀ rd, Main.MemOk rd → SoundTablesM M End.bytecode TCtx rd :=
  soundTablesM_model M End.bytecode_length

/-- **`verify_flock` over every model**, on every memory `Main.MemOk` admits: the field `flock`
of `Located.GuestHypsM M`. -/
theorem guestHypsM_flock (M : HashModel) : ∀ rd, Main.MemOk rd → SoundFlockM M rd :=
  fun rd _ => verify_flock_model rd

end
end LeanVM.Guest.B1.VerifySub
