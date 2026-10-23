/-
  LeanVM.Guest.B1.Da.ColumnCChk

  `da_verify_column`'s specializations and loops as templates (by kernel evaluation), for their
  completeness.
-/

module

public import LeanVM.Guest.B1.Da.ColumnChk

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Digest

@[expose] public section

/-- A row loop's block: the cell check, the running sum, the node, and, when `store`, the
prefix. -/
def rowPre (store : Bool) : List Stmt :=
  [.call "da_verify_cell" [.n 2] [.n 7, .n 8, .n 9], .atom (.mul (.n 10) (.n 3) (.n 0)),
    .atom (.load (.n 11) (.n 10) 0), .atom (.mul (.n 12) (.n 11) (.n 4)),
    .atom (.load (.n 13) (.n 12) 0), .atom (.add (.n 14) (.n 13) (.n 9)),
    .atom (.load (.n 14) (.n 12) 1), .atom (.mul (.n 15) (.n 0) (.n 0)),
    .atom (.mul (.n 16) (.n 5) (.n 15)), .atom (.load (.n 7) (.n 16) 0),
    .atom (.load (.n 8) (.n 16) 1)] ++
  (if store then
    [.atom (.mul (.n 17) (.n 6) (.n 0)), .atom (.load (.n 18) (.n 17) 0),
      .atom (.mul (.n 19) (.n 4) (.n 4)), .atom (.mul (.n 20) (.n 18) (.n 19)),
      .atom (.load (.n 7) (.n 20) 0), .atom (.load (.n 8) (.n 20) 1)] else []) ++
  (let c := if store then 21 else 17
   [.atom (.const (.n c) (word 2 0 0)), .atom (.mul (.n (c + 1)) (.n 0) (.n c)),
    .atom (.add (.n (c + 2)) (.n (c + 1)) (.n 1)), .atom (.const (.n (c + 3)) (word 2 0 0)),
    .atom (.mul (.n (c + 4)) (.n 0) (.n (c + 3)))])

/-- A row loop's body. -/
def rowBody (store : Bool) (f : String) : List Stmt :=
  let c := if store then 21 else 17
  rowPre store ++ [.callIf (.n (c + 2)) f [.n (c + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], .ret []]

/-- A gap loop's block: the padding cell's two cells at the node. -/
def gapPre : List Stmt :=
  [.atom (.mul (.n 4) (.n 3) (.n 3)), .atom (.mul (.n 5) (.n 2) (.n 4)),
    .atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 5) (.n 6)),
    .atom (.const (.n 8) (word 15569472805043175342 18354418831448413762 0)),
    .atom (.load (.n 8) (.n 7) 0),
    .atom (.const (.n 9) (word 11782766640862828499 15718207409690975807 0)),
    .atom (.load (.n 9) (.n 7) 1), .atom (.const (.n 10) (word 2 0 0)),
    .atom (.mul (.n 11) (.n 0) (.n 10)), .atom (.add (.n 12) (.n 11) (.n 1)),
    .atom (.const (.n 13) (word 2 0 0)), .atom (.mul (.n 14) (.n 0) (.n 13))]

/-- A gap loop's body. -/
def gapBody (f : String) : List Stmt :=
  gapPre ++ [.callIf (.n 12) f [.n 14, .n 1, .n 2, .n 3], .ret []]

/-- A column's body. -/
def colBody (rl gl : String) : List Stmt :=
  [.atom (.mul (.n 9) (.n 0) (.n 0)), .atom (.mul (.n 10) (.n 8) (.n 9)),
    .call "da_vector_cell" [.n 10] [.n 11], .atom (.mul (.n 12) (.n 2) (.n 2)),
    .atom (.mul (.n 13) (.n 12) (.n 12)), .atom (.hint (.allocDyn (.n 14) (.n 13))),
    .atom (.const (.n 15) (word 1 0 0)), .atom (.add (.n 16) (.n 15) (.n 1)),
    .atom (.const (.n 17) (word 1 0 0)),
    .callIf (.n 16) rl [.n 17, .n 1, .n 11, .n 7, .n 0, .n 14, .n 5],
    .atom (.const (.n 18) (word 1 0 0)), .atom (.add (.n 19) (.n 18) (.n 3)),
    .atom (.const (.n 20) (word 1 0 0)), .callIf (.n 19) gl [.n 20, .n 3, .n 14, .n 1],
    .dispatch (.n 4) dlNames [.n 14] [.n 21, .n 22], .atom (.mul (.n 23) (.n 0) (.n 0)),
    .atom (.mul (.n 24) (.n 6) (.n 23)), .atom (.load (.n 21) (.n 24) 0),
    .atom (.load (.n 22) (.n 24) 1), .ret []]

set_option maxRecDepth 100000 in
theorem core895_body : Fn.body (coreProgram.getD 895 default) = rowBody true "__loop417" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem core897_body : Fn.body (coreProgram.getD 897 default) = rowBody false "__loop419" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem core896_body : Fn.body (coreProgram.getD 896 default) = gapBody "__loop418" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem core898_body : Fn.body (coreProgram.getD 898 default) = gapBody "__loop420" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem core769_body : Fn.body (coreProgram.getD 769 default) = colBody "__loop417" "__loop418" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem core770_body : Fn.body (coreProgram.getD 770 default) = colBody "__loop419" "__loop420" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Da
