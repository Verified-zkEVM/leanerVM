/-
  LeanVM.Guest.B1.Main.AggL26CChk

  `__loop25` (a child's lambdas) and `__loop26` (a child's weight), evaluated (by kernel
  evaluation), for their completeness.
-/

module

public import LeanVM.Guest.B1.Main.AggCLib

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-! ## `__loop25` -/

/-- A load of the row's word `o < 13` through `.n 11` into `.n (12 + o)`. -/
def isL26RowLoad : Atom → Bool
  | .load d p o => decide (p = .n 11) && decide (d = .n (12 + o)) && decide (o < 13)
  | _ => false

/-- `__loop25`'s other loads: the running claim, the pointers to the child's claims, their
values. -/
def l26Loads : List Atom :=
  [.load (.n 89) (.n 11) 13, .load (.n 78) (.n 77) 0, .load (.n 80) (.n 79) 0,
    .load (.n 90) (.n 78) 23, .load (.n 93) (.n 80) 23]

/-- `__loop25`'s stores: the lambdas, then the next row's capacity, zero rate and claim. -/
def l26Stores : List Atom :=
  [.load (.n 48) (.n 75) 0, .load (.n 73) (.n 76) 1] ++
    (List.range 5).map (fun i => .load (.n (62 + i)) (.n 11) (14 + i)) ++
    (List.range 8).map (fun c => .load (.n (81 + c)) (.n 11) (19 + c)) ++
    [.load (.n 95) (.n 11) 27]

/-- `__loop25`'s atoms but its stores. -/
noncomputable def l26A : List Atom :=
  (atomsIn (loopPre (coreProgram.getD 375 default))).filter fun a => decide (a ∉ l26Stores)

theorem mem_l26A {a : Atom} :
    a ∈ l26A ↔ a ∈ atomsIn (loopPre (coreProgram.getD 375 default)) ∧ a ∉ l26Stores := by
  simp [l26A]

set_option maxRecDepth 100000 in
theorem l26_stores : storesOf 6 (coreProgram.getD 375 default).body = l26Stores := by
  decide +kernel

/-- **`__loop25`, evaluated**: its values defined in order, its atoms but its stores holding from
its loads and challenges, and the facts of its block on them. -/
noncomputable def l26COk : Bool :=
  let fn := coreProgram.getD 375 default
  let A := l26A
  let P := (atomsIn (loopPre fn)).filter pureB
  (chk 6 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  canonChk ((List.range 13).map (12 + ·)) A &&
  A.all (fun a => !needsSide a || decide (a = .assertInK (.n 42) (.n 45)) ||
    decide (a = .assertInK (.n 67) (.n 70)) || isL26RowLoad a || decide (a ∈ l26Loads)) &&
  (List.range 13).all (fun o => decide (Atom.load (.n (12 + o)) (.n 11) o ∈ A)) &&
  l26Loads.all (fun a => decide (a ∈ A)) &&
  monoIs P (.n 11) (.n 2) (.n 0) 14 &&
  decide (Atom.keccak k1i k1o false false ∈ A) && rowInOk A (.n 11) k1i &&
  allIn A (challA (.n 29) (.n 30) 42) &&
  (List.range 4).all (fun i => P.any (isConstAt (.n (50 + i)) 0 0)) &&
  decide (Atom.keccak k2i k2o false false ∈ A) &&
  allIn A (challA (.n 54) (.n 55) 67) &&
  isMul P (.n 74) (.n 0) (.n 0) && isMul P (.n 75) (.n 3) (.n 74) &&
  isMul P (.n 76) (.n 3) (.n 74) && isMul P (.n 77) (.n 4) (.n 0) && isMul P (.n 79) (.n 5) (.n 0) &&
  (List.range 8).all (fun c => P.any (isConstAt (.n (81 + c)) 0 0)) &&
  isMul P (.n 91) (.n 48) (.n 90) && P.any (isAddAt (.n 92) (.n 89) (.n 91)) &&
  isMul P (.n 94) (.n 73) (.n 93) && P.any (isAddAt (.n 95) (.n 92) (.n 94))

set_option maxRecDepth 100000 in
theorem l26_shape : loopShapeF (coreProgram.getD 375 default) "__loop25" = true ∧
    (coreProgram.getD 375 default).params.length = 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem l26c_ok : l26COk = true := by decide +kernel

/-! ## `__loop26` -/

/-- `__loop26`'s store: the next weight. -/
def l27Stores : List Atom := [.load (.n 272) (.n 273) 1]

/-- `__loop26`'s atoms but its store. -/
noncomputable def l27A : List Atom :=
  (atomsIn (loopPre (coreProgram.getD 377 default))).filter fun a => decide (a ∉ l27Stores)

theorem mem_l27A {a : Atom} :
    a ∈ l27A ↔ a ∈ atomsIn (loopPre (coreProgram.getD 377 default)) ∧ a ∉ l27Stores := by
  simp [l27A]

/-- A load of `__loop26`: the pointers to the child's claims, the lambdas, the weight, and
coordinate `o < 23` of the claims' points and of the sumcheck's point. -/
def isL27Load : Atom → Bool
  | .load _ p o => (decide (p = .n 7) && decide (o = 0)) || (decide (p = .n 9) && decide (o = 0)) ||
      (decide (p = .n 263) && decide (o = 0)) || (decide (p = .n 265) && decide (o = 0)) ||
      (decide (p = .n 269) && decide (o = 1)) ||
      ((decide (p = .n 4) || decide (p = .n 8) || decide (p = .n 10)) && decide (o < 23))
  | _ => false

set_option maxRecDepth 100000 in
theorem l27_stores : storesOf 7 (coreProgram.getD 377 default).body = l27Stores := by
  decide +kernel

/-- **`__loop26`, evaluated**: its values defined in order, its atoms but its store holding from
its loads, and the facts of its block on them. -/
noncomputable def l27COk : Bool :=
  let fn := coreProgram.getD 377 default
  let A := l27A
  let P := (atomsIn (loopPre fn)).filter pureB
  (chk 7 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  canonChk [] A && A.all (fun a => !needsSide a || isL27Load a) &&
  isMul P (.n 7) (.n 2) (.n 0) && A.any (isLoadAt (.n 8) (.n 7) 0) &&
  isMul P (.n 9) (.n 3) (.n 0) && A.any (isLoadAt (.n 10) (.n 9) 0) &&
  eqChainOk A (.n 8) (.n 4) 23 (.n 256) && eqChainOk A (.n 10) (.n 4) 23 (.n 261) &&
  isMul P (.n 262) (.n 0) (.n 0) &&
  isMul P (.n 263) (.n 5) (.n 0) && A.any (isLoadAt (.n 264) (.n 263) 0) &&
  isMul P (.n 265) (.n 6) (.n 262) && A.any (isLoadAt (.n 266) (.n 265) 0) &&
  isMul P (.n 267) (.n 266) (.n 256) && P.any (isAddAt (.n 268) (.n 264) (.n 267)) &&
  isMul P (.n 269) (.n 6) (.n 262) && A.any (isLoadAt (.n 270) (.n 269) 1) &&
  isMul P (.n 271) (.n 270) (.n 261) && P.any (isAddAt (.n 272) (.n 268) (.n 271)) &&
  isMul P (.n 273) (.n 5) (.n 0)

set_option maxRecDepth 100000 in
theorem l27_shape : loopShapeF (coreProgram.getD 377 default) "__loop26" = true ∧
    (coreProgram.getD 377 default).params.length = 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem l27c_ok : l27COk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
