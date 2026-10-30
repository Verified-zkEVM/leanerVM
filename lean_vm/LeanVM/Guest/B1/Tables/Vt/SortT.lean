/-
  LeanVM.Guest.B1.Tables.Vt.SortT

  The templates of `verify_tables`' block table and its two certified block orders, checked
  against the body by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Base

/-!
# The block certification's templates (G:1953-1986)

* `vtSideT`: `block_side_tab[g^b] = BLOCK_SIDE[b]` for the 153 blocks (statements 11-316);
* `vtRank0T v R s`, `vtRankT v R s pk pc gin`: rank `R` of side `s`'s certification, its values
  from `v`; the first rank of a side (no comparison), the others comparing with the previous
  rank's size `pk` and block `pc`, writing the running offset `gin`.

The push side's ranks `0 .. 53` sit at statement `318` (values from `186`) and the count side's
`108 .. 152` at `1339` (values from `1525`); rank `r ≥ 1` is `14 + 19 (r - 1)` statements on and
its values `14 + 25 (r - 1)` on.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- `BLOCK_SIDE`: push `0 .. 53`, pull `54 .. 107`, count `108 .. 152`. -/
def vtBlockSide (b : ℕ) : ℕ := if b < 54 then 0 else if b < 108 then 1 else 2

/-- `block_side_tab`'s stores. -/
def vtSideT : List Stmt :=
  ((List.range 153).map fun b ↦ [.atom (.const (.n (32 + b)) (word (vtBlockSide b) 0 0)),
    .atom (.load (.n (32 + b)) (.n 31) b)]).flatten

/-- `g^152` and `g^33`, as the data writes them. -/
abbrev vtW152 : E := word 5452595200 0 0
abbrev vtW33 : E := word 8589934592 0 0

/-- A side's first rank. -/
def vtRank0T (v R s : ℕ) : List Stmt :=
  [.atom (.load (.n v) (.n 30) R), .atom (.const (.n (v + 1)) vtW152),
    .atom (.rangeCheck (.n v) (.n (v + 2)) (.n (v + 3)) (.n (v + 4)) (.n (v + 1))),
    .atom (.mul (.n (v + 5)) (.n 31) (.n v)), .atom (.load (.n (v + 6)) (.n (v + 5)) 0),
    .atom (.const (.n (v + 7)) (word s 0 0)), .atom (.assertEq (.n (v + 6)) (.n (v + 7))),
    .atom (.mul (.n (v + 8)) (.n 12) (.n v)), .atom (.load (.n (v + 9)) (.n (v + 8)) 0),
    .atom (.const (.n (v + 10)) (word 1 0 0)), .atom (.mul (.n (v + 11)) (.n 185) (.n v)),
    .atom (.load (.n (v + 10)) (.n (v + 11)) 0), .atom (.mul (.n (v + 12)) (.n 13) (.n (v + 9))),
    .atom (.load (.n (v + 13)) (.n (v + 12)) 0)]

/-- A later rank. -/
def vtRankT (v R s pk pc gin : ℕ) : List Stmt :=
  [.atom (.load (.n v) (.n 30) R), .atom (.const (.n (v + 1)) vtW152),
    .atom (.rangeCheck (.n v) (.n (v + 2)) (.n (v + 3)) (.n (v + 4)) (.n (v + 1))),
    .atom (.mul (.n (v + 5)) (.n 31) (.n v)), .atom (.load (.n (v + 6)) (.n (v + 5)) 0),
    .atom (.const (.n (v + 7)) (word s 0 0)), .atom (.assertEq (.n (v + 6)) (.n (v + 7))),
    .atom (.mul (.n (v + 8)) (.n 12) (.n v)), .atom (.load (.n (v + 9)) (.n (v + 8)) 0),
    .atom (.const (.n (v + 10)) vtW33), .atom (.mul (.n pk) (.n (v + 11)) (.n (v + 9))),
    .atom (.rangeCheck (.n (v + 11)) (.n (v + 12)) (.n (v + 13)) (.n (v + 14)) (.n (v + 10))),
    .atom (.add (.n (v + 15)) (.n pk) (.n (v + 9))),
    .ite (.n (v + 15)) [.atom (.const (.n (v + 16)) vtW152),
      .atom (.mul (.n v) (.n (v + 17)) (.n pc)),
      .atom (.rangeCheck (.n (v + 17)) (.n (v + 18)) (.n (v + 19)) (.n (v + 20)) (.n (v + 16)))] [],
    .atom (.mul (.n (v + 21)) (.n 185) (.n v)), .atom (.load (.n gin) (.n (v + 21)) 0),
    .atom (.mul (.n (v + 22)) (.n 13) (.n (v + 9))), .atom (.load (.n (v + 23)) (.n (v + 22)) 0),
    .atom (.mul (.n (v + 24)) (.n gin) (.n (v + 23)))]

/-- Rank `r`'s values, from the side's `v0`. -/
def vtRv (v0 r : ℕ) : ℕ := if r = 0 then v0 else v0 + 14 + 25 * (r - 1)

/-- Rank `r`'s template, `r ≥ 1`. -/
def vtRankAt (v0 R0 s r : ℕ) : List Stmt :=
  vtRankT (vtRv v0 r) (R0 + r) s (vtRv v0 (r - 1) + 9) (vtRv v0 (r - 1))
    (if r = 1 then v0 + 13 else vtRv v0 (r - 1) + 24)

/-- Rank `r`'s first statement, from the side's `p0`. -/
def vtRp (p0 r : ℕ) : ℕ := if r = 0 then p0 else p0 + 14 + 19 * (r - 1)

theorem vtSideT_check : tbStmtsEqb vtSideT ((vtPre.drop 11).take vtSideT.length) = true := by
  decide +kernel

theorem vtPush0_check :
    tbStmtsEqb (vtRank0T 186 0 0) ((vtPre.drop 318).take (vtRank0T 186 0 0).length) = true := by
  decide +kernel

theorem vtCount0_check :
    tbStmtsEqb (vtRank0T 1525 108 2) ((vtPre.drop 1339).take (vtRank0T 1525 108 2).length) =
      true := by
  decide +kernel

theorem vtPush_check : ∀ r < 54, 1 ≤ r →
    tbStmtsEqb (vtRankAt 186 0 0 r) ((vtPre.drop (vtRp 318 r)).take (vtRankAt 186 0 0 r).length) =
      true := by
  decide +kernel

theorem vtCount_check : ∀ r < 45, 1 ≤ r →
    tbStmtsEqb (vtRankAt 1525 108 2 r)
      ((vtPre.drop (vtRp 1339 r)).take (vtRankAt 1525 108 2 r).length) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Tables
