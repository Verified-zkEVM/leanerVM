/-
  LeanVM.Guest.B1.Main.KidCChk

  `__loop4`'s block (a child), evaluated (by kernel evaluation), for its placed completeness.
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.Memory.Uniform

/-!
# A child's block, evaluated

`l5Pre`: `__loop4`'s statements before its tail call (`l5_body`). `l5COk`: the evaluator's pattern
(`chk`), the stores (`l5S`: the statement's digest's two cells into `child_pi_table`, the next
running count), no `KECCAK` of its own, every side condition a load of `written[x]` or of the
child's DA digest's two hinted cells, a store or a range check.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `__loop4`'s statements before its tail call. -/
def l5Pre : List Stmt := [
    .atom (.mul (.n 16) (.n 2) (.n 0)),
    .atom (.load (.n 17) (.n 16) 0),
    .atom (.hint (.witness "child_meta" (.stack [.n 18, .n 19]))),
    .atom (.const (.n 20) (word 9272771591053052074 0 0)),
    .atom (.rangeCheck (.n 18) (.n 21) (.n 22) (.n 23) (.n 20)),
    .atom (.const (.n 24) (word 9272771591053052074 0 0)),
    .atom (.rangeCheck (.n 19) (.n 25) (.n 26) (.n 27) (.n 24)),
    .atom (.mul (.n 28) (.n 18) (.n 19)),
    .atom (.const (.n 29) (word 1 0 0)),
    .call "child_claim_list_digest" [.n 3, .n 4, .n 17, .n 29, .n 5, .n 18] [.n 30, .n 31],
    .atom (.mul (.n 32) (.n 17) (.n 18)),
    .call "child_claim_list_digest" [.n 6, .n 4, .n 32, .n 5, .n 7, .n 19] [.n 33, .n 34],
    .atom (.mul (.n 35) (.n 0) (.n 0)),
    .atom (.mul (.n 36) (.n 35) (.n 0)),
    .atom (.mul (.n 37) (.n 36) (.n 36)),
    .atom (.mul (.n 38) (.n 37) (.n 37)),
    .atom (.mul (.n 39) (.n 38) (.n 38)),
    .atom (.mul (.n 40) (.n 8) (.n 39)),
    .atom (.hint (.witness "child_defer" (.heap (.n 40) 0 24))),
    .atom (.mul (.n 41) (.n 0) (.n 0)),
    .atom (.mul (.n 42) (.n 9) (.n 41)),
    .atom (.hint (.witness "child_da" (.heap (.n 42) 0 2))),
    .atom (.load (.n 43) (.n 42) 0),
    .atom (.load (.n 44) (.n 42) 1),
    .call "statement_digest" [.n 10, .n 11, .n 30, .n 31, .n 33, .n 34, .n 43, .n 44, .n 40] [.n
      45, .n 46],
    .atom (.mul (.n 47) (.n 0) (.n 0)),
    .atom (.mul (.n 48) (.n 12) (.n 47)),
    .atom (.load (.n 45) (.n 48) 0),
    .atom (.mul (.n 49) (.n 12) (.n 47)),
    .atom (.load (.n 46) (.n 49) 1),
    .atom (.mul (.n 50) (.n 0) (.n 0)),
    .atom (.mul (.n 51) (.n 50) (.n 0)),
    .atom (.mul (.n 52) (.n 51) (.n 51)),
    .atom (.mul (.n 53) (.n 52) (.n 52)),
    .atom (.mul (.n 54) (.n 53) (.n 53)),
    .atom (.mul (.n 55) (.n 15) (.n 54)),
    .call "verify_sub" [.n 45, .n 46, .n 10, .n 11, .n 13, .n 14, .n 55] [],
    .atom (.mul (.n 56) (.n 17) (.n 28)),
    .atom (.mul (.n 57) (.n 2) (.n 0)),
    .atom (.load (.n 56) (.n 57) 1),
    .atom (.const (.n 58) (word 2 0 0)),
    .atom (.mul (.n 59) (.n 0) (.n 58)),
    .atom (.add (.n 60) (.n 59) (.n 1)),
    .atom (.const (.n 61) (word 2 0 0)),
    .atom (.mul (.n 62) (.n 0) (.n 61))]

/-- `__loop4`'s tail call. -/
def l5Tail : Stmt :=
  .callIf (.n 60) "__loop4" [.n 62, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n
    11, .n 12, .n 13, .n 14, .n 15]

set_option maxRecDepth 100000 in
theorem l5_body : Fn.body (coreProgram.getD 34 default) = l5Pre ++ [l5Tail, .ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l5_params : (coreProgram.getD 34 default).params = (List.range 16).map V.n := by
  decide +kernel

/-- `__loop4`'s stores. -/
def l5S : List Atom :=
  [.load (.n 45) (.n 48) 0, .load (.n 46) (.n 49) 1, .load (.n 56) (.n 57) 1]

/-- A range check. -/
def isRcB : Atom → Bool
  | .rangeCheck .. => true
  | _ => false

/-- The block's atoms but the stores. -/
def l5A' : List Atom := (atomsIn l5Pre).filter fun a => decide (a ∉ l5S)

/-- The calls of the block. -/
def l5Calls : List Stmt :=
  [.call "child_claim_list_digest" [.n 3, .n 4, .n 17, .n 29, .n 5, .n 18] [.n 30, .n 31],
    .call "child_claim_list_digest" [.n 6, .n 4, .n 32, .n 5, .n 7, .n 19] [.n 33, .n 34],
    .call "statement_digest" [.n 10, .n 11, .n 30, .n 31, .n 33, .n 34, .n 43, .n 44, .n 40]
      [.n 45, .n 46]]

/-- **`__loop4`'s block, evaluated.** -/
def l5COk : Bool :=
  (chk 16 (l5Pre ++ [l5Tail, .ret []])).isSome &&
  decide (storesOf 16 (l5Pre ++ [l5Tail, .ret []]) = l5S) &&
  canonChk [] l5A' &&
  (atomsIn l5Pre).all (fun a => !needsSide a || decide (a ∈ l5S) ||
    decide (a = .load (.n 17) (.n 16) 0) || decide (a = .load (.n 43) (.n 42) 0) ||
    decide (a = .load (.n 44) (.n 42) 1) || isRcB a) &&
  l5Calls.all (fun c => l5Pre.any (stmtEqb · c))

set_option maxRecDepth 100000 in
theorem l5c_ok : l5COk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
