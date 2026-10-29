/-
  LeanVM.Guest.B1.Da.VerifyCChk

  `da_verify`'s body, evaluated (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Da.LevelsTab
public import LeanVM.Guest.B1.Fwd.Canon

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- A load of the column digests' cell `i < 256` through `.n 17`. -/
def isCdLoad : Atom → Bool
  | .load d p i => decide (p = .n 17) && decide (d = .n (69 + i)) && decide (i < 256)
  | _ => false

/-- `da_verify`'s calls. -/
def dvCalls : List Stmt :=
  [.call "da_row_shape" [.n 1, .n 2, .n 0] [.n 3, .n 4],
    .callIf (.n 15) "__loop17" [.n 16, .n 1, .n 13, .n 12],
    .callIf (.n 29) "__loop18" [.n 30, .n 1, .n 26, .n 27],
    .call "__loop19" [.n 32, .n 1, .n 3, .n 4, .n 2, .n 13, .n 31, .n 27, .n 17] [],
    .call "__loop20" [.n 33, .n 1, .n 3, .n 4, .n 2, .n 13, .n 31, .n 27, .n 17] [],
    .callIf (.n 35) "__loop21" [.n 36, .n 1, .n 27],
    .call "da_levels__L128_L7" [.n 31] [.n 37, .n 38],
    .callIf (.n 43) "__loop22" [.n 44, .n 1, .n 13, .n 41],
    .callIf (.n 46) "__loop23" [.n 47, .n 4, .n 41, .n 1],
    .dispatch (.n 2) dlNames [.n 41] [.n 48, .n 49]]

/-- `da_verify`'s hints. -/
def dvHints : List Atom :=
  [.hint (.witness "da_shape" (.stack [.n 1, .n 2])), .hint (.allocDyn (.n 12) (.n 11)),
    .hint (.allocDyn (.n 13) (.n 1)), .hint (.alloc (.n 17) 256), .hint (.allocDyn (.n 26) (.n 25)),
    .hint (.allocDyn (.n 27) (.n 1)), .hint (.alloc (.n 31) 512), .hint (.allocDyn (.n 41) (.n 40))]

/-- **`da_verify`'s body, evaluated.** -/
noncomputable def dvCOk : Bool :=
  (chk 1 (Fn.body Data.core25)).isSome && (storesOf 1 (Fn.body Data.core25)).isEmpty &&
  canonChk ([37, 38, 48, 49] ++ (List.range 256).map (69 + ·)) (atomsIn dvP) &&
  (atomsIn dvP).all (fun a => !needsSide a || isCdLoad a) &&
  dvP.all (fun s => match s with
    | .atom _ => true
    | _ => dvCalls.any (stmtEqb s)) &&
  dvHints.all (fun a => decide (a ∈ atomsIn dvP)) &&
  dvCalls.all (fun c => dvP.any (stmtEqb · c))

set_option maxRecDepth 100000 in
theorem dvc_ok : dvCOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
