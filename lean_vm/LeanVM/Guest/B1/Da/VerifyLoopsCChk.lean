/-
  LeanVM.Guest.B1.Da.VerifyLoopsCChk

  `da_verify`'s small loops as templates (by kernel evaluation), for their completeness.
-/

module

public import LeanVM.Guest.B1.Da.VerifyLoopsChk
public import LeanVM.Guest.B1.Da.ColumnCChk

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Digest

@[expose] public section

/-- `x^128` by seven squarings from `.n 4`. -/
def sq7 : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)),
    .atom (.mul (.n 6) (.n 5) (.n 5)), .atom (.mul (.n 7) (.n 6) (.n 6)),
    .atom (.mul (.n 8) (.n 7) (.n 7)), .atom (.mul (.n 9) (.n 8) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9))]

/-- The step and guard from `.n c`. -/
def stepAt (c : ℕ) : List Stmt :=
  [.atom (.const (.n c) (word 2 0 0)), .atom (.mul (.n (c + 1)) (.n 0) (.n c)),
    .atom (.add (.n (c + 2)) (.n (c + 1)) (.n 1)), .atom (.const (.n (c + 3)) (word 2 0 0)),
    .atom (.mul (.n (c + 4)) (.n 0) (.n (c + 3)))]

/-- `__loop17`'s block. -/
def l18Pre : List Stmt :=
  sq7 ++ [.atom (.mul (.n 11) (.n 3) (.n 10)), .atom (.mul (.n 12) (.n 2) (.n 0)),
    .atom (.load (.n 11) (.n 12) 0)] ++ stepAt 13

/-- `__loop18`'s block. -/
def l19Pre : List Stmt :=
  sq7 ++ [.atom (.mul (.n 11) (.n 10) (.n 0)), .atom (.mul (.n 12) (.n 2) (.n 11)),
    .atom (.mul (.n 13) (.n 3) (.n 0)), .atom (.load (.n 12) (.n 13) 0),
    .atom (.const (.n 14) (word 0 0 0)), .atom (.load (.n 14) (.n 12) 0)] ++ stepAt 15

/-- `__loop21`'s block. -/
def l22Pre : List Stmt :=
  [.atom (.mul (.n 3) (.n 2) (.n 0)), .atom (.load (.n 4) (.n 3) 0),
    .atom (.load (.n 5) (.n 4) 128), .atom (.const (.n 6) (word 0 0 0)),
    .atom (.assertEq (.n 5) (.n 6))] ++ stepAt 7

/-- `__loop23`'s block: the padding row's two cells at the row tree. -/
def l24Pre : List Stmt :=
  [.atom (.mul (.n 4) (.n 3) (.n 3)), .atom (.mul (.n 5) (.n 2) (.n 4)),
    .atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 5) (.n 6)),
    .atom (.const (.n 8) (word 4665334884586258498 1553031596697948144 0)),
    .atom (.load (.n 8) (.n 7) 0),
    .atom (.const (.n 9) (word 7487832681283088925 14683883899259534590 0)),
    .atom (.load (.n 9) (.n 7) 1)] ++ stepAt 10

set_option maxRecDepth 100000 in
theorem core356_body : Fn.body (coreProgram.getD 356 default) =
    l18Pre ++ [.callIf (.n 15) "__loop17" [.n 17, .n 1, .n 2, .n 3], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem core357_body : Fn.body (coreProgram.getD 357 default) =
    l19Pre ++ [.callIf (.n 17) "__loop18" [.n 19, .n 1, .n 2, .n 3], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem core360_body : Fn.body (coreProgram.getD 360 default) =
    l22Pre ++ [.callIf (.n 9) "__loop21" [.n 11, .n 1, .n 2], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem core363_body : Fn.body (coreProgram.getD 363 default) =
    l24Pre ++ [.callIf (.n 12) "__loop23" [.n 14, .n 1, .n 2, .n 3], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem dvloops_shape :
    (loopShapeF (coreProgram.getD 356 default) "__loop17" = true ∧
      (coreProgram.getD 356 default).params.length = 4) ∧
    (loopShapeF (coreProgram.getD 357 default) "__loop18" = true ∧
      (coreProgram.getD 357 default).params.length = 4) ∧
    (loopShapeF (coreProgram.getD 360 default) "__loop21" = true ∧
      (coreProgram.getD 360 default).params.length = 3) ∧
    (loopShapeF (coreProgram.getD 363 default) "__loop23" = true ∧
      (coreProgram.getD 363 default).params.length = 4) := by decide +kernel

end
end LeanVM.Guest.B1.Da
