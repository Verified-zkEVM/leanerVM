/-
  LeanVM.Guest.B1.Da.VerifyDefs

  The checks of `da_verify`'s body and of its loops.
-/

module

public import LeanVM.Guest.B1.Da.Column
public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.B1.Da.ChainSplit

/-!
# `da_verify` (G:3920-3982), checked

`da_verify(g_squares)` (`core25`): the shape (`da_row_shape`), the rows' prefix bases
(`__loop18`: `prefix_bases[x] = prefix_digests·x^128`), the rows' running sums (`__loop19`:
`rowbase[x] = acc·x^129`, its first word `0`), the columns (`__loop20`, `__loop21`:
`da_verify_column__L1` on columns `0 … 63`, `__L0` on `64 … 127`), the sums' check (`__loop22`:
word `128` of every row's sum is `0`), the column tree (`da_levels__L128_L7`), the row tree
(`__loop23`: each row's digest from its prefix cells; `__loop24`: the padding rows; `da_levels`
dispatched on `g_log_pad`), the root (`keccak` of the two trees' roots) and the vector's digest
(`keccak_cells` of the `256` column-digest cells).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-! ## The loops -/

/-- `__loop18`: `prefix_bases[x] = prefix_digests·x^128`. -/
def l18Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop18" && decide (fn.params.length = 4) &&
  monoIs A (.n 11) (.n 3) (.n 0) 128 && isMul A (.n 12) (.n 2) (.n 0) &&
  A.any (isLoadAt (.n 11) (.n 12) 0)

/-- `__loop19`: `rowbase[x] = acc·x^129`, its word `0` zero. -/
def l19Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop19" && decide (fn.params.length = 4) &&
  monoIs A (.n 12) (.n 2) (.n 0) 129 && isMul A (.n 13) (.n 3) (.n 0) &&
  A.any (isLoadAt (.n 12) (.n 13) 0) && A.any (isConstAt (.n 14) 0 0) &&
  A.any (isLoadAt (.n 14) (.n 12) 0)

/-- `__loop22`: word `128` of `rowbase[x]` is zero. -/
def l22Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop22" && decide (fn.params.length = 3) &&
  isMul A (.n 3) (.n 2) (.n 0) && A.any (isLoadAt (.n 4) (.n 3) 0) &&
  A.any (isLoadAt (.n 5) (.n 4) 128) && A.any (isConstAt (.n 6) 0 0) &&
  A.any (isAssertEqAt (.n 5) (.n 6))

/-- `__loop23`'s chain: the `128` cells loaded through `prefix_bases[x]`. -/
def rowSpec (atoms : List Atom) : ChainSpec :=
  ⟨(List.range 128).map fun i => some (.n (6 + i)), 2048, true, none, keccakBlocks atoms⟩

/-- `__loop23`: row `x`'s digest, from the `128` cells at `prefix_bases[x]`, written at
`rowtree·x²`. -/
def l23Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop23" && decide (fn.params.length = 4) &&
  isMul A (.n 4) (.n 2) (.n 0) && A.any (isLoadAt (.n 5) (.n 4) 0) &&
  loadsOk A (.n 5) ((List.range 128).map fun i => some (.n (6 + i))) &&
  (rowSpec A).check A && isMul A (.n 477) (.n 0) (.n 0) && isMul A (.n 478) (.n 3) (.n 477) &&
  A.any (isLoadAt ((rowSpec A).outV ((rowSpec A).nb - 1) 0) (.n 478) 0) &&
  A.any (isLoadAt ((rowSpec A).outV ((rowSpec A).nb - 1) 1) (.n 478) 1)

/-- The body of the column loops `__loop20`, `__loop21`: the column at `x`, then the next. -/
def colLoopBody (col loop : String) (endLo : ℕ) : List Stmt :=
  [.call col ((List.range 9).map V.n) [],
    .atom (.const (.n 9) (word 2 0 0)), .atom (.mul (.n 10) (.n 0) (.n 9)),
    .atom (.const (.n 11) (word endLo 0 0)), .atom (.add (.n 12) (.n 10) (.n 11)),
    .atom (.const (.n 13) (word 2 0 0)), .atom (.mul (.n 14) (.n 0) (.n 13)),
    .callIf (.n 12) loop (.n 14 :: (List.range 8).map fun k => V.n (k + 1)), .ret []]

/-- A column loop, checked. -/
def colLoopOk (fn : Fn) (col loop : String) (endLo : ℕ) : Bool :=
  decide (fn.params = (List.range 9).map V.n) && stmtsEqb fn.body (colLoopBody col loop endLo)

/-! ## The body -/

/-- The root's chain: the row tree's root, then the column tree's, `64` bytes. -/
def rootSpec (atoms : List Atom) : ChainSpec :=
  ⟨[some (.n 48), some (.n 49), some (.n 37), some (.n 38)], 64, true, none,
    (keccakBlocks atoms).take 1⟩

/-- The vector's chain: the `256` column-digest cells, `4096` bytes. -/
def vdSpec (atoms : List Atom) : ChainSpec :=
  ⟨(List.range 256).map fun i => some (.n (69 + i)), 4096, true, none, (keccakBlocks atoms).drop 1⟩

/-- `da_verify`'s block (its body but the final `ret`). -/
noncomputable def dvP : List Stmt := (Fn.body Data.core25).dropLast

/-- **`da_verify`'s block, checked** (but the vector's chain). -/
noncomputable def dvOk : Bool :=
  let P := dvP
  let A := atomsIn P
  decide (Data.core25.params = [.n 0]) &&
  stmtsEqb (Fn.body Data.core25) (P ++ [.ret [.n 993, .n 994, .n 995, .n 996]]) &&
  P.all Stmt.flat &&
  hasCall P "da_row_shape" [.n 1, .n 2, .n 0] [.n 3, .n 4] &&
  monoIs A (.n 11) (.n 3) (.n 3) 127 &&
  guardOk P (.n 15) "__loop18" (.n 16) (.n 1) [.n 13, .n 12] &&
  monoIs A (.n 25) (.n 1) (.n 1) 128 &&
  guardOk P (.n 29) "__loop19" (.n 30) (.n 1) [.n 26, .n 27] &&
  A.any (isConstAt (.n 32) 1 0) &&
  hasCall P "__loop20" [.n 32, .n 1, .n 3, .n 4, .n 2, .n 13, .n 31, .n 27, .n 17] [] &&
  A.any (isConstAt (.n 33) 27 0) &&
  hasCall P "__loop21" [.n 33, .n 1, .n 3, .n 4, .n 2, .n 13, .n 31, .n 27, .n 17] [] &&
  guardOk P (.n 35) "__loop22" (.n 36) (.n 1) [.n 27] &&
  hasCall P "da_levels__L128_L7" [.n 31] [.n 37, .n 38] &&
  monoIs A (.n 40) (.n 3) (.n 3) 3 &&
  guardOk P (.n 43) "__loop23" (.n 44) (.n 1) [.n 13, .n 41] &&
  guardOk P (.n 46) "__loop24" (.n 47) (.n 4) [.n 41, .n 1] &&
  P.any (stmtEqb · (.dispatch (.n 2) dlNames [.n 41] [.n 48, .n 49])) &&
  (rootSpec A).check A &&
  A.any (isCopyAt (.n 993) ((rootSpec A).outV ((rootSpec A).nb - 1) 0)) &&
  A.any (isCopyAt (.n 994) ((rootSpec A).outV ((rootSpec A).nb - 1) 1)) &&
  loadsOk A (.n 17) ((List.range 256).map fun i => some (.n (69 + i))) &&
  (vdSpec A).shapeOk && decide ((vdSpec A).nb = 31) &&
  A.any (isCopyAt (.n 995) ((vdSpec A).outV ((vdSpec A).nb - 1) 0)) &&
  A.any (isCopyAt (.n 996) ((vdSpec A).outV ((vdSpec A).nb - 1) 1))

end
end LeanVM.Guest.B1.Da
