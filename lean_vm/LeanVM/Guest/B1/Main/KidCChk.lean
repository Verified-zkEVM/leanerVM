/-
  LeanVM.Guest.B1.Main.KidCChk

  `__loop5`'s block (a child), evaluated (by kernel evaluation), for its placed completeness.
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.Memory.Uniform

/-!
# A child's block, evaluated

`l5Pre`: `__loop5`'s statements before its tail call (`l5_body`). `l5COk`: the evaluator's pattern
(`chk`), the stores (`l5S`: the signer-set digest's two cells into `child_pi`, the statement's
digest's two cells into `child_pi_table`, the next running count), the `KECCAK` inputs canonical
from the two claim lists' digests, every side condition a load of `written[x]`, a store or a range
check, the pair hash's chain and its outputs `.n 43`, `.n 44`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `__loop5`'s statements before its tail call. -/
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
    .atom (.const (.n 37) (word 1 0 0)),
    .atom (.const (.n 38) (word 0 0 0)),
    .atom (.const (.n 39) (word 0 0 0)),
    .atom (.const (.n 40) (word 0 0 0)),
    .atom (.const (.n 41) (word 0 0 0)),
    .atom (.const (.n 42) (word 9223372036854775808 0 0)),
    .atom (.keccak [.n 32, .n 33, .n 35, .n 36, .n 37, .n 38, .n 39, .n 40, .n 42, .n 38, .n 39, .n 40, .n 41] [.n 43, .n 44, .n 45, .n 46, .n 47, .n 48, .n 49, .n 50, .n 51, .n 52, .n 53, .n 54, .n 55] false false),
    .atom (.hint (.alloc (.n 56) 2)),
    .atom (.load (.n 43) (.n 56) 0),
    .atom (.load (.n 44) (.n 56) 1),
    .atom (.mul (.n 57) (.n 0) (.n 0)),
    .atom (.mul (.n 58) (.n 57) (.n 0)),
    .atom (.mul (.n 59) (.n 58) (.n 58)),
    .atom (.mul (.n 60) (.n 59) (.n 59)),
    .atom (.mul (.n 61) (.n 60) (.n 60)),
    .atom (.mul (.n 62) (.n 8) (.n 61)),
    .atom (.hint (.witness "child_defer" (.heap (.n 62) 0 24))),
    .atom (.hint (.witness "child_da_count" (.stack [.n 63]))),
    .atom (.const (.n 64) (word 65536 0 0)),
    .atom (.rangeCheck (.n 63) (.n 65) (.n 66) (.n 67) (.n 64)),
    .atom (.mul (.n 68) (.n 63) (.n 63)),
    .atom (.mul (.n 69) (.n 68) (.n 68)),
    .atom (.hint (.allocDyn (.n 70) (.n 69))),
    .atom (.const (.n 71) (word 1 0 0)),
    .atom (.add (.n 72) (.n 71) (.n 63)),
    .atom (.const (.n 73) (word 1 0 0)),
    .callIf (.n 72) "__loop28" [.n 73, .n 63, .n 70, .n 9, .n 10, .n 11, .n 19, .n 30],
    .call "da_list_digest" [.n 70, .n 63] [.n 74, .n 75],
    .call "statement_digest" [.n 12, .n 13, .n 56, .n 74, .n 75, .n 62] [.n 76, .n 77],
    .atom (.mul (.n 78) (.n 0) (.n 0)),
    .atom (.mul (.n 79) (.n 14) (.n 78)),
    .atom (.load (.n 76) (.n 79) 0),
    .atom (.mul (.n 80) (.n 14) (.n 78)),
    .atom (.load (.n 77) (.n 80) 1),
    .atom (.mul (.n 81) (.n 0) (.n 0)),
    .atom (.mul (.n 82) (.n 81) (.n 0)),
    .atom (.mul (.n 83) (.n 82) (.n 82)),
    .atom (.mul (.n 84) (.n 83) (.n 83)),
    .atom (.mul (.n 85) (.n 84) (.n 84)),
    .atom (.mul (.n 86) (.n 17) (.n 85)),
    .call "verify_sub" [.n 76, .n 77, .n 12, .n 13, .n 15, .n 16, .n 86] [],
    .atom (.mul (.n 87) (.n 19) (.n 30)),
    .atom (.mul (.n 88) (.n 87) (.n 63)),
    .atom (.mul (.n 89) (.n 2) (.n 0)),
    .atom (.load (.n 88) (.n 89) 1),
    .atom (.const (.n 90) (word 2 0 0)),
    .atom (.mul (.n 91) (.n 0) (.n 90)),
    .atom (.add (.n 92) (.n 91) (.n 1)),
    .atom (.const (.n 93) (word 2 0 0)),
    .atom (.mul (.n 94) (.n 0) (.n 93))]

/-- `__loop5`'s tail call. -/
def l5Tail : Stmt :=
  .callIf (.n 92) "__loop5" [.n 94, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10,
    .n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17]

set_option maxRecDepth 100000 in
theorem l5_body : Fn.body (coreProgram.getD 37 default) = l5Pre ++ [l5Tail, .ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l5_params : (coreProgram.getD 37 default).params = (List.range 18).map V.n := by
  decide +kernel

/-- `__loop5`'s stores. -/
def l5S : List Atom :=
  [.load (.n 43) (.n 56) 0, .load (.n 44) (.n 56) 1, .load (.n 76) (.n 79) 0,
    .load (.n 77) (.n 80) 1, .load (.n 88) (.n 89) 1]

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
    .call "da_list_digest" [.n 70, .n 63] [.n 74, .n 75],
    .call "statement_digest" [.n 12, .n 13, .n 56, .n 74, .n 75, .n 62] [.n 76, .n 77]]

/-- **`__loop5`'s block, evaluated.** -/
def l5COk : Bool :=
  (chk 18 (l5Pre ++ [l5Tail, .ret []])).isSome &&
  decide (storesOf 18 (l5Pre ++ [l5Tail, .ret []]) = l5S) &&
  canonChk [32, 33, 35, 36] l5A' &&
  (atomsIn l5Pre).all (fun a => !needsSide a || decide (a ∈ l5S) ||
    decide (a = .load (.n 19) (.n 18) 0) || isRcB a) &&
  (pairSpec (.n 32) (.n 33) (.n 35) (.n 36) l5A').check l5A' &&
  decide ((pairSpec (.n 32) (.n 33) (.n 35) (.n 36) l5A').outV
    ((pairSpec (.n 32) (.n 33) (.n 35) (.n 36) l5A').nb - 1) 0 = .n 43) &&
  decide ((pairSpec (.n 32) (.n 33) (.n 35) (.n 36) l5A').outV
    ((pairSpec (.n 32) (.n 33) (.n 35) (.n 36) l5A').nb - 1) 1 = .n 44) &&
  l5Calls.all (fun c => l5Pre.any (stmtEqb · c))

set_option maxRecDepth 100000 in
theorem l5c_ok : l5COk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
