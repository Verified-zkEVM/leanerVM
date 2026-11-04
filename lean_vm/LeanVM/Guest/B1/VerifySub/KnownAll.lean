/-
  LeanVM.Guest.B1.VerifySub.KnownAll

  `VsKnown`: the first `1592` statements of `verify_sub` put `kappa_base`'s entries among `g^e`,
  `e < kbBound i`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Known
public import LeanVM.Guest.B1.VerifySub.FrontAll
public import LeanVM.Guest.B1.VerifySub.Body
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

/-- The sections before the tail. -/
def vsPre : List Stmt :=
  vsHeadT ++ vsReadsT ++ vsSizesT ++ vsPushT ++ vsRootsT ++ vsAlphasT ++ vsFpwT ++
    vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT

theorem vsPre_length : vsPre.length = 1578 := by decide +kernel

theorem vsT_take : vsT.take 1592 = vsPre ++ vsTailT.take 14 := by
  rw [show vsT = vsPre ++ vsTailT from rfl, List.take_append, List.take_of_length_le
    (by rw [vsPre_length]; omega), vsPre_length]

theorem noRet_mid : Stmt.noRetList (vsMapsT ++ vsCtabT ++ vsLamT) = true := by decide +kernel

theorem vsTailT_take14 : vsTailT.take 14 = vsTailT.take 6 ++ (vsTailT.take 14).drop 6 := by
  rw [List.take_append_drop]
  rfl

/-- **`VsKnown`** (G5's obligation on `verify_sub`): `kappa_base`'s entries below `kbBound`. -/
theorem vsKnown_holds {κ : ℕ} (L : MemoryImage κ) (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (σ : Val) (hexp : B1.ExpTables L.read (σ (.n 4)))
    (h : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((Fn.body Data.core18).take 1592) True
      (fun _ ↦ True)) :
    ∀ i < 8, ∃ e < kbBound i, LoadHolds L.read (σ (.n 139)) i (ofK (addressOfIndex e)) := by
  have hκ : κ ≤ 32 := h32
  have hκ6 : 6 ≤ κ := by have : 16 ≤ κ := h16; omega
  have hle : CallRel.Le (coreProgram.Rel L.read) (coreProgram.Rel L.read) := fun _ _ _ h ↦ h
  rw [show Fn.body Data.core18 = vsT from vs_body, vsT_take, vsPre] at h
  rw [holdsList_append, holdsList_append, holdsList_append, holdsList_append] at h
  obtain ⟨⟨F⟩, h⟩ := vs_front hκ hκ6 L hle (List.replicate (2 ^ 23) 0)
    (Tables.verify_bus_gkr_holdsC hκ L hle)
    (Tables.verify_tables_holdsC hκ L _ List.length_replicate hle) hexp h
  rw [← holdsList_append, ← holdsList_append] at h
  have h' := ((holdsList_noRet _ noRet_mid _ _).1 h).2
  rw [vsTailT_take14, holdsList_append] at h'
  have hsL := tableHeights_length F.rowsN F.hrowsL
  obtain ⟨hm28, h5⟩ := vsKnown_tail hκ hκ6 L hle (Tables.certify_placement_holds hκ L) hexp F.hm32
    hsL F.hh29 F.hkb h'
  exact kb_bounds hsL F.hh29 hm28 h5 F.hkb

end
end LeanVM.Guest.B1.VerifySub
