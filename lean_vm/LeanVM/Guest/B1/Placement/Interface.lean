/-
  LeanVM.Guest.B1.Placement.Interface

  B1 of `certify_placement`: the committed columns' log sizes, their order and offsets in the
  stack, as `check_opening_terminal` reads them (`PCtx`), and the statement of its soundness.
-/

module

public import LeanVM.Guest.B1.Tables.Base

/-!
# `certify_placement` (TRIAGE G #67): the interface

`certify_placement(kappa_base, g_squares)` (G:2989-3022) builds each committed column's `g^κ`
from its source in `kappa_base = [1, g^log_mem, g^τ_0, …, g^τ_5]` (`COL_KAPPA_SRC`,
`COL_KAPPA_ADJ`, here `colKappaSrc`, `colKappaAdj`), reads the hinted order `col_sort_order`,
certifies it to be `stackOffsets`'s (V:830: sizes non-increasing, ties by ascending index, every
column once by write-once offsets), and returns `g^(Σ 2^κ)` over the committed columns and two
buffers: `g^offset` and `g^κ` per committed column.

The committed columns are `placementsOf`'s (V:1261-1282): every global column but the `KECCAK`
value lanes, `99` of the `163` (`committedCols`), in global order. `columnKappas log_mem 19 τ`
(V:1250) are the sizes of all `163`; the bytecode's log size is the guest's own, `19`
(`BYTECODE_LOG`).

* `PCtx rd kappas off kap`: `kap` holds `g^κ` and `off` holds `g^offset` per committed column;
* `certify_placement_Spec`: under its precondition the function's relation gives `PCtx` and the
  total;
* `HypKappa`: once the stack is at most `2^28`, every committed column's `κ` is below `29` (the
  range of `column_selector`'s 29 specializations, which `check_opening_terminal` dispatches on).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The committed columns, in global order (`placementsOf`'s `blockCols`, V:1271): every column
but the `KECCAK` value lanes. -/
def committedCols (n : ℕ) : List ℕ :=
  (List.range n).filter fun c ↦ (keccakSlot c).isNone ∧ c ∉ keccakOutputColumns

/-- The committed columns' sizes, in that order. -/
def committedKappas (kappas : List ℕ) : List ℕ := (committedCols kappas.length).map (kappas.getD · 0)

/-- The stack's size before rounding: `Σ 2^κ` over the committed columns. -/
def stackTotal (kappas : List ℕ) : ℕ := ((committedKappas kappas).map (2 ^ ·)).sum

/-- `BYTECODE_LOG`: the guest's bytecode, `2^19` slots of `16` words each, has `logBytecode = 19`. -/
abbrev guestLogBytecode : ℕ := 19

/-- `N_COMMITTED_COLS`. -/
abbrev nCommittedCols : ℕ := 99

/-- `COL_KAPPA_SRC[c]`: the `kappa_base` entry of committed column `c` (`0` the constant, `1` the
memory, `2 + t` table `t`). -/
def colKappaSrc (c : ℕ) : ℕ :=
  if c < 4 then 1 else if c = 4 then 0 else if c = 5 then 7 else if c < 21 then 2
  else if c < 36 then 3 else if c < 44 then 4 else if c < 59 then 5 else if c < 73 then 6 else 7

/-- `COL_KAPPA_ADJ[c]`: the bytecode's log size `19`, and `q_keccak`'s slot bits `6`. -/
def colKappaAdj (c : ℕ) : ℕ := if c = 4 then 19 else if c = 5 then 6 else 0

/-- **What `certify_placement` hands `check_opening_terminal`**: `kappas` are the `163` columns'
sizes, `kap` holds `g^κ` and `off` holds `g^offset` per committed column, the offsets
`stackOffsets`'s (V:830). -/
def PCtx (rd : Reader) (kappas : List ℕ) (off kap : E) : Prop :=
  kappas.length = 163 ∧ TbReadsAt rd kap ((committedKappas kappas).map (gen ^ ·)) ∧
    TbReadsAt rd off ((stackOffsets (committedKappas kappas)).1.map (gen ^ ·))

/-- **`certify_placement` is sound**: over the base `[1, g^log_mem, g^τ_0, …, g^τ_5]` and the
squares table, it returns `g^(Σ 2^κ)` over the committed columns of `columnKappas log_mem 19 τ`
and two buffers of which `PCtx` holds. -/
def certify_placement_Spec (rd : Reader) : Prop :=
  ∀ (logMem : ℕ) (hs : List ℕ) (kb sq : E) (rets : List E), logMem ≤ 32 → hs.length = 6 →
    (∀ h ∈ hs, h < 29) → TbReadsAt rd kb (1 :: gen ^ logMem :: hs.map (gen ^ ·)) →
    TbReadsAt rd sq gSquaresList →
    coreProgram.Rel rd "certify_placement" [kb, sq] rets →
      ∃ off kap, rets = [gen ^ stackTotal (columnKappas logMem guestLogBytecode hs), off, kap] ∧
        PCtx rd (columnKappas logMem guestLogBytecode hs) off kap

/-- Every committed column's log, in `col_kappas`, is below `N_COLUMN_LOGS = 29`. -/
def KappasBelow (rd : Reader) (kap : E) : Prop :=
  ∀ c < nCommittedCols, ∃ κ < 29, LoadHolds rd kap c (gen ^ κ)

/-- **The columns' logs are in range** once the stack is at most `2^28`. -/
def HypKappa (rd : Reader) : Prop :=
  ∀ kappas off kap, PCtx rd kappas off kap → log2Ceil (stackTotal kappas) ≤ 28 → KappasBelow rd kap

end
end LeanVM.Guest.B1.Tables
