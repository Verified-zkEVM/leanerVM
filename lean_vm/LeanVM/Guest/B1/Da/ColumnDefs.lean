/-
  LeanVM.Guest.B1.Da.ColumnDefs

  The checks of `da_verify_column`'s two specializations and their loops.
-/

module

public import LeanVM.Guest.B1.Da.Tree

/-!
# `da_verify_column` (G:3992-4014), checked

`da_verify_column(xb, n_blob_g, n_pad_g, gap_g, g_log_pad, prefix_bases, coltree, rowbase,
column_digests)` (`__L1`, `store = 1`, core `769`; `__L0`, core `770`): the column's weights
(`da_vector_cell` at `column_digests·xb²`), the row loop (`__loop415`, `__loop417`: a cell per row,
`rowOk`), the gap loop (`__loop416`, `__loop418`: padding cells, `gapOk`), the column's root
(`da_levels` dispatched on `g_log_pad`) written at `coltree·xb²` (`colOk`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-- `da_levels`' eleven specializations, the dispatch's arms. -/
def dlNames : List String := (List.range 11).map daLevelsName

/-- **A column's body, checked**, its row loop `rl` and gap loop `gl`. -/
def colOk (fn : Fn) (rl gl : String) : Bool :=
  decide (fn.params = (List.range 9).map V.n) &&
  match splitRet fn.body with
  | some (P, vs) =>
    let A := atomsIn P
    decide (vs = []) && P.all Stmt.flat &&
    isMul A (.n 9) (.n 0) (.n 0) && isMul A (.n 10) (.n 8) (.n 9) &&
    hasCall P "da_vector_cell" [.n 10] [.n 11] &&
    guardOk P (.n 16) rl (.n 17) (.n 1) [.n 11, .n 7, .n 0, .n 14, .n 5] &&
    guardOk P (.n 19) gl (.n 20) (.n 3) [.n 14, .n 1] &&
    P.any (stmtEqb · (.dispatch (.n 4) dlNames [.n 14] [.n 21, .n 22])) &&
    isMul A (.n 23) (.n 0) (.n 0) && isMul A (.n 24) (.n 6) (.n 23) &&
    A.any (isLoadAt (.n 21) (.n 24) 0) && A.any (isLoadAt (.n 22) (.n 24) 1)
  | none => false

/-- **A row loop's body, checked** (`store`: the cell's digest also into the row's prefix). -/
def rowOk (fn : Fn) (f : String) (store : Bool) : Bool :=
  let P := loopPre fn
  let A := atomsIn P
  loopShapeF fn f && decide (fn.params.length = 7) &&
  hasCall P "da_verify_cell" [.n 2] [.n 7, .n 8, .n 9] &&
  isMul A (.n 10) (.n 3) (.n 0) && A.any (isLoadAt (.n 11) (.n 10) 0) &&
  isMul A (.n 12) (.n 11) (.n 4) && A.any (isLoadAt (.n 13) (.n 12) 0) &&
  A.any (isAddAt (.n 14) (.n 13) (.n 9)) && A.any (isLoadAt (.n 14) (.n 12) 1) &&
  isMul A (.n 15) (.n 0) (.n 0) && isMul A (.n 16) (.n 5) (.n 15) &&
  A.any (isLoadAt (.n 7) (.n 16) 0) && A.any (isLoadAt (.n 8) (.n 16) 1) &&
  (!store || (isMul A (.n 17) (.n 6) (.n 0) && A.any (isLoadAt (.n 18) (.n 17) 0) &&
    isMul A (.n 19) (.n 4) (.n 4) && isMul A (.n 20) (.n 18) (.n 19) &&
    A.any (isLoadAt (.n 7) (.n 20) 0) && A.any (isLoadAt (.n 8) (.n 20) 1)))

/-- **A gap loop's body, checked**: the constants `(lo0, hi0)`, `(lo1, hi1)` written at
`tree·n_blob_g²·x²`. -/
def gapOk (fn : Fn) (f : String) (lo0 hi0 lo1 hi1 : ℕ) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn f && decide (fn.params.length = 4) &&
  isMul A (.n 4) (.n 3) (.n 3) && isMul A (.n 5) (.n 2) (.n 4) && isMul A (.n 6) (.n 0) (.n 0) &&
  isMul A (.n 7) (.n 5) (.n 6) && A.any (isConstAt (.n 8) lo0 hi0) &&
  A.any (isLoadAt (.n 8) (.n 7) 0) && A.any (isConstAt (.n 9) lo1 hi1) &&
  A.any (isLoadAt (.n 9) (.n 7) 1)

/-- The padding cell's constants (`DA_PAD_CELL_0/1`). -/
abbrev padCellLo : ℕ × ℕ × ℕ × ℕ :=
  (15569472805043175342, 18354418831448413762, 11782766640862828499, 15718207409690975807)

/-- The padding row's constants (`DA_PAD_ROW_0/1`). -/
abbrev padRowLo : ℕ × ℕ × ℕ × ℕ :=
  (4665334884586258498, 1553031596697948144, 7487832681283088925, 14683883899259534590)

end
end LeanVM.Guest.B1.Da
