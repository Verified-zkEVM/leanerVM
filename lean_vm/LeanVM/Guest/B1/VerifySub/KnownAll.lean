/-
  LeanVM.Guest.B1.VerifySub.KnownAll

  `VsKnown`: the first `1592` statements of `verify_sub` put `kappa_base`'s entries among `g^e`,
  `e < kbBound i`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Known
public import LeanVM.Guest.B1.Tables.HoldsC

/-!
# `VsKnown`

`vsKnown_holds`: on a memory image of `2^κ` words, `minLogMem ≤ κ ≤ maxLogMem`, over the exponent
table at `verify_sub`'s argument `4`, the body's first `1592` statements (up to the call of
`check_opening_terminal`) put the `8` entries of `kappa_base` (`139`) among `g^e`, `e < kbBound i`.
They are the front (`vs_front`, through `verify_tables`: the tables' heights below `29` and
`kappa_base`), the ring map, `c_table` and the batching (no `ret`, skipped), and the first `6`
statements of the tail (`vsKnown_tail`). The callees are B1-c's proved specifications; the
bytecode `verify_tables` is read against is any of `2^23` words (its words do not enter).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`VsKnown`** (G5's obligation on `verify_sub`): `kappa_base`'s entries below `kbBound`. -/
theorem vsKnown_holds {κ : ℕ} (L : MemoryImage κ) (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (σ : Val) (hexp : B1.ExpTables L.read (σ (.n 4)))
    (h : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((Fn.body Data.core18).take 1592) True
      (fun _ ↦ True)) :
    ∀ i < 8, ∃ e < kbBound i, LoadHolds L.read (σ (.n 139)) i (ofK (addressOfIndex e)) :=
  have hκ : κ ≤ 32 := h32
  have hle : CallRel.Le (coreProgram.Rel L.read) (coreProgram.Rel L.read) := fun _ _ _ h ↦ h
  vsKnown_of L h16 h32 (Tables.verify_bus_gkr_holdsC hκ L hle)
    (Tables.verify_tables_holdsC hκ L _ List.length_replicate hle) (Tables.certify_placement_holds hκ L)
    σ hexp h

end
end LeanVM.Guest.B1.VerifySub
