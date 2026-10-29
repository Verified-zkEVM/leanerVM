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
running count), no `KECCAK` of its own, every side condition a load of `written[x]`, a store or a
range check.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `__loop4`'s statements before its tail call. -/
def l5Pre : List Stmt := [
    .atom (.mul (.n 18) (.n 2) (.n 0)),
    .atom (.load (.n 19) (.n 18) 0),
    .atom (.hint (.witness "child_meta" (.stack [.n 20, .n 21]))),
    .atom (.const (.n 22) (word 9272771591053052074 0 0)),
    .atom (.rangeCheck (.n 20) (.n 23) (.n 24) (.n 25) (.n 22)),
    .atom (.const (.n 26) (word 9272771591053052074 0 0)),
    .atom (.rangeCheck (.n 21) (.n 27) (.n 28) (.n 29) (.n 26)),
    .atom (.mul (.n 30) (.n 20) (.n 21)),
    .atom (.const (.n 31) (word 1 0 0)),
    .call "child_claim_list_digest" [.n 3, .n 4, .n 19, .n 31, .n 5, .n 20] [.n 32, .n 33],
    .atom (.mul (.n 34) (.n 19) (.n 20)),
    .call "child_claim_list_digest" [.n 6, .n 4, .n 34, .n 5, .n 7, .n 21] [.n 35, .n 36],
    .atom (.mul (.n 37) (.n 0) (.n 0)),
    .atom (.mul (.n 38) (.n 37) (.n 0)),
    .atom (.mul (.n 39) (.n 38) (.n 38)),
    .atom (.mul (.n 40) (.n 39) (.n 39)),
    .atom (.mul (.n 41) (.n 40) (.n 40)),
    .atom (.mul (.n 42) (.n 8) (.n 41)),
    .atom (.hint (.witness "child_defer" (.heap (.n 42) 0 24))),
    .atom (.hint (.witness "child_da_count" (.stack [.n 43]))),
    .atom (.const (.n 44) (word 65536 0 0)),
    .atom (.rangeCheck (.n 43) (.n 45) (.n 46) (.n 47) (.n 44)),
    .atom (.mul (.n 48) (.n 43) (.n 43)),
    .atom (.mul (.n 49) (.n 48) (.n 48)),
    .atom (.hint (.allocDyn (.n 50) (.n 49))),
    .atom (.const (.n 51) (word 1 0 0)),
    .atom (.add (.n 52) (.n 51) (.n 43)),
    .atom (.const (.n 53) (word 1 0 0)),
    .callIf (.n 52) "__loop28" [.n 53, .n 43, .n 50, .n 9, .n 10, .n 11, .n 19, .n 30],
    .call "da_list_digest" [.n 50, .n 43] [.n 54, .n 55],
    .call "statement_digest" [.n 12, .n 13, .n 32, .n 33, .n 35, .n 36, .n 54, .n 55, .n 42] [.n 56, .n 57],
    .atom (.mul (.n 58) (.n 0) (.n 0)),
    .atom (.mul (.n 59) (.n 14) (.n 58)),
    .atom (.load (.n 56) (.n 59) 0),
    .atom (.mul (.n 60) (.n 14) (.n 58)),
    .atom (.load (.n 57) (.n 60) 1),
    .atom (.mul (.n 61) (.n 0) (.n 0)),
    .atom (.mul (.n 62) (.n 61) (.n 0)),
    .atom (.mul (.n 63) (.n 62) (.n 62)),
    .atom (.mul (.n 64) (.n 63) (.n 63)),
    .atom (.mul (.n 65) (.n 64) (.n 64)),
    .atom (.mul (.n 66) (.n 17) (.n 65)),
    .call "verify_sub" [.n 56, .n 57, .n 12, .n 13, .n 15, .n 16, .n 66] [],
    .atom (.mul (.n 67) (.n 19) (.n 30)),
    .atom (.mul (.n 68) (.n 67) (.n 43)),
    .atom (.mul (.n 69) (.n 2) (.n 0)),
    .atom (.load (.n 68) (.n 69) 1),
    .atom (.const (.n 70) (word 2 0 0)),
    .atom (.mul (.n 71) (.n 0) (.n 70)),
    .atom (.add (.n 72) (.n 71) (.n 1)),
    .atom (.const (.n 73) (word 2 0 0)),
    .atom (.mul (.n 74) (.n 0) (.n 73))]

/-- `__loop4`'s tail call. -/
def l5Tail : Stmt :=
  .callIf (.n 72) "__loop4" [.n 74, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10,
    .n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17]

set_option maxRecDepth 100000 in
theorem l5_body : Fn.body (coreProgram.getD 34 default) = l5Pre ++ [l5Tail, .ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l5_params : (coreProgram.getD 34 default).params = (List.range 18).map V.n := by
  decide +kernel

/-- `__loop4`'s stores. -/
def l5S : List Atom :=
  [.load (.n 56) (.n 59) 0, .load (.n 57) (.n 60) 1, .load (.n 68) (.n 69) 1]

/-- A range check. -/
def isRcB : Atom → Bool
  | .rangeCheck .. => true
  | _ => false

/-- The block's atoms but the stores. -/
def l5A' : List Atom := (atomsIn l5Pre).filter fun a => decide (a ∉ l5S)

/-- The calls of the block. -/
def l5Calls : List Stmt :=
  [.call "child_claim_list_digest" [.n 3, .n 4, .n 19, .n 31, .n 5, .n 20] [.n 32, .n 33],
    .call "child_claim_list_digest" [.n 6, .n 4, .n 34, .n 5, .n 7, .n 21] [.n 35, .n 36],
    .call "da_list_digest" [.n 50, .n 43] [.n 54, .n 55],
    .call "statement_digest" [.n 12, .n 13, .n 32, .n 33, .n 35, .n 36, .n 54, .n 55, .n 42]
      [.n 56, .n 57]]

/-- **`__loop4`'s block, evaluated.** -/
def l5COk : Bool :=
  (chk 18 (l5Pre ++ [l5Tail, .ret []])).isSome &&
  decide (storesOf 18 (l5Pre ++ [l5Tail, .ret []]) = l5S) &&
  canonChk [] l5A' &&
  (atomsIn l5Pre).all (fun a => !needsSide a || decide (a ∈ l5S) ||
    decide (a = .load (.n 19) (.n 18) 0) || isRcB a) &&
  l5Calls.all (fun c => l5Pre.any (stmtEqb · c))

set_option maxRecDepth 100000 in
theorem l5c_ok : l5COk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
