/-
  LeanVM.Guest.B1.VerifySub.KnownAll

  `VsKnown`: the first `2098` statements of `verify_sub` put `col_kappas` among `g^e`, `e < 29`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Known
public import LeanVM.Guest.B1.VerifySub.FrontAll
public import LeanVM.Guest.B1.VerifySub.Body
public import LeanVM.Guest.B1.Tables.HoldsC

/-!
# `VsKnown`

`vsKnown_holds`: on a memory image of `2^κ` words, `minLogMem ≤ κ ≤ maxLogMem`, over the exponent
tables at `verify_sub`'s arguments `4`, `5`, the body's first `2098` statements (up to the call of
`check_opening_terminal`) put the `nCommittedCols` entries of `col_kappas` (`1889`) among `g^e`, `e < 29`.
They are the front (`vs_front`, through `verify_tables`: the tables' heights below `29` and
`kappa_base`), the ring map, `c_table` and the batching (no `ret`, skipped), and the first `14`
statements of the tail (`vsKnown_tail`). The callees are B1-c's proved specifications; the
bytecode `verify_tables` is read against is any of `2^23` words (its words do not enter).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The sections before the tail. -/
def vsPre : List Stmt :=
  vsHeadT ++ vsReadsT ++ vsSizesT ++ vsKappaT ++ vsPushT ++ vsRootsT ++ vsAlphasT ++ vsFpwT ++
    vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT

theorem vsPre_length : vsPre.length = 2084 := by decide +kernel

theorem vsT_take : vsT.take 2098 = vsPre ++ vsTailT.take 14 := by
  rw [show vsT = vsPre ++ vsTailT from rfl, List.take_append, List.take_of_length_le
    (by rw [vsPre_length]; omega), vsPre_length]

theorem noRet_mid : Stmt.noRetList (vsMapsT ++ vsCtabT ++ vsLamT) = true := by decide +kernel

/-- **`VsKnown`** (G5's obligation on `verify_sub`). -/
theorem vsKnown_holds {κ : ℕ} (L : MemoryImage κ) (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (σ : Val) (hexp : B1.ExpTables L.read (σ (.n 4)) (σ (.n 5)))
    (h : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((Fn.body Data.core18).take 2098) True
      (fun _ ↦ True)) :
    ∀ c < Tables.nCommittedCols, ∃ e < 29, LoadHolds L.read (σ (.n 1889)) c (ofK (gpow e)) := by
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
  exact vsKnown_tail hκ hκ6 L hle hexp F.hm32
    (tableHeights_length F.rowsN F.hrowsL) F.hh29 F.hkb h'

end
end LeanVM.Guest.B1.VerifySub
