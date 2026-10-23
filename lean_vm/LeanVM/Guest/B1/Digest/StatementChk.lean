/-
  LeanVM.Guest.B1.Digest.StatementChk

  `statement_digest`'s template, evaluated: its values defined in order, no store, its `KECCAK`
  inputs canonical from the header and pair cells, its side conditions in the header and pairs
  (by kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Digest.Statement
public import LeanVM.Guest.B1.Fwd.Canon

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `statement_digest`'s body, as its template. -/
def sdBody : List Stmt := sdAtoms.map Stmt.atom ++ [.ret [.n 443, .n 444]]

/-- The values known canonical: the header cells, the pairs' cells, the constants. -/
def sdA : List ℕ :=
  [6, 7, 8, 9, 10, 11] ++ (List.range 12).flatMap (fun p => [12 + 27 * p + 8, 12 + 27 * p + 17,
    12 + 27 * p + 26]) ++ [336, 337, 338, 339, 340, 428]

set_option maxRecDepth 100000 in
theorem sd_chk : chk 6 sdBody = some 445 := by decide +kernel

set_option maxRecDepth 100000 in
theorem sd_stores : storesOf 6 sdBody = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem sd_canon : canonChk sdA sdAtoms = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem sd_needs : sdAtoms.filter needsSide = sdHdr.filter needsSide ++
    (List.range 12).flatMap (fun p => (pairAtoms (.n 5) (2 * p) (12 + 27 * p)).filter needsSide) := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
