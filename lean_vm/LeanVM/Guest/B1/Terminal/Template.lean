/-
  LeanVM.Guest.B1.Terminal.Template

  `check_opening_terminal`'s body as a template: its head, the 113 column selectors, one block
  per claim the opening batches, and the tail.
-/

module

public import LeanVM.Guest.B1.Terminal.Interface

/-!
# `check_opening_terminal`, as a template

The guest unrolls the claims' loop (G:3101-3131) at compile time on its tables `CLAIM_POINT_BUF`,
`CLAIM_COMMITTED_COL` and `CLAIM_QKECCAK_SLOT_BITS`; here they are `termKind`, `termCol` and the
slot `j - 85`:

* claims `0 .. 4`, the bus's, on the prefix chain at `zeta` (kind `0`), committed columns `0 .. 4`;
* claims `5 .. 84` and `135 .. 161`, the tables', on the chain at `chi` (kind `1`);
* claims `85 .. 109`, `KECCAK`'s input lanes, on the chain at `chi` and their slot's bits
  (kind `2`), on `q_keccak` (committed column `5`);
* claims `110 .. 134`, `KECCAK`'s output lanes, skipped (kind `4`);
* claims `162 .. 164`, the public input's, on the chain of `(rm, 0, …, 0)` (kind `3`).

`termT` is the body (`term_body`, by kernel evaluation in `Terminal/Body`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1

@[expose] public section

/-- The kind of claim `j`'s low point (`CLAIM_POINT_BUF`): `0` the bus point, `1` the table
point, `2` a `q_keccak` lane, `3` the public input's, `4` a `KECCAK` output lane. -/
def termKind (j : ℕ) : ℕ :=
  if j < 5 then 0 else if j < 85 then 1 else if j < 110 then 2 else if j < 135 then 4
  else if j < 162 then 1 else 3

/-- Claim `j`'s committed column (`CLAIM_COMMITTED_COL`). -/
def termCol (j : ℕ) : ℕ :=
  if j < 5 then j else if j < 85 then j + 1 else if j < 110 then 5 else if j < 162 then j - 49
  else j - 162

/-- The selectors' specializations, `column_selector__L{κ}`, `κ < 29`. -/
def colSelNames : List String := (List.range 29).map (Tables.lName "column_selector")

/-- The value of committed column `c`'s selector. -/
def selV (c : ℕ) : ℕ := 38 + 3 * c

/-- The head (G:3083-3095): the chains at `zeta` (`19`) and `chi` (`21`), the slot points (`23`,
`24`), the public input's chain (`25`, its loop `__loop15`) and its value (`33`), the selector
tables (`34`, `35`). -/
def termHeadT : List Stmt :=
  [.atom (.hint (.alloc (.n 19) 35)), .atom (.const (.n 20) (word 1 0 0)),
    .call "eq_prefix_chain" [.n 19, .n 20, .n 0, .n 15, .n 3] [],
    .atom (.hint (.alloc (.n 21) 35)), .atom (.const (.n 22) (word 1 0 0)),
    .call "eq_prefix_chain" [.n 21, .n 22, .n 1, .n 15, .n 4] [],
    .atom (.mul (.n 23) (.n 14) (.n 6)), .atom (.mul (.n 24) (.n 15) (.n 6)),
    .atom (.hint (.alloc (.n 25) 35)), .atom (.const (.n 26) (word 1 0 0)),
    .atom (.load (.n 26) (.n 25) 0), .atom (.load (.n 27) (.n 15) 0),
    .atom (.add (.n 28) (.n 2) (.n 27)), .atom (.load (.n 28) (.n 25) 1),
    .atom (.const (.n 29) (word 2 0 0)), .atom (.add (.n 30) (.n 29) (.n 5)),
    .atom (.const (.n 31) (word 2 0 0)),
    .callIf (.n 30) "__loop15" [.n 31, .n 5, .n 25, .n 15],
    .atom (.mul (.n 32) (.n 25) (.n 5)), .atom (.load (.n 33) (.n 32) 0),
    .call "selector_tables" [.n 14, .n 15] [.n 34, .n 35]]

/-- Committed column `c`'s selector (G:3097-3100). -/
def selBlockT (c : ℕ) : List Stmt :=
  [.atom (.load (.n (36 + 3 * c)) (.n 10) c), .atom (.load (.n (37 + 3 * c)) (.n 11) c),
    .dispatch (.n (37 + 3 * c)) colSelNames [.n (36 + 3 * c), .n 34, .n 35] [.n (selV c)]]

/-- The 113 selectors. -/
def selsT : List Stmt := (List.range 113).flatMap selBlockT

/-- A claim on a prefix chain at `ch` (kinds `0`, `1`), from value `r`, the sum so far at `acc`. -/
def zrT (ch j c r acc : ℕ) : List Stmt :=
  [.atom (.load (.n r) (.n 7) j), .atom (.mul (.n (r + 1)) (.n ch) (.n r)),
    .atom (.load (.n (r + 2)) (.n (r + 1)) 0), .atom (.load (.n (r + 3)) (.n 11) c),
    .atom (.assertEq (.n r) (.n (r + 3))), .atom (.load (.n (r + 4)) (.n 9) j),
    .atom (.mul (.n (r + 5)) (.n (r + 4)) (.n (r + 2))),
    .atom (.mul (.n (r + 6)) (.n (r + 5)) (.n (selV c))),
    .atom (.add (.n (r + 7)) (.n acc) (.n (r + 6)))]

/-- Slot bit `k` of `s`'s point: `slot_point` (`23`) at a one, `slot_point1` (`24`) at a zero. -/
def slotPt (s k : ℕ) : ℕ := if s.testBit k then 23 else 24

/-- A `q_keccak` lane's claim (kind `2`) at slot `s`. -/
def qT (j s r acc : ℕ) : List Stmt :=
  [.atom (.load (.n r) (.n 7) j), .atom (.load (.n (r + 1)) (.n (slotPt s 5)) 5),
    .atom (.load (.n (r + 2)) (.n (slotPt s 4)) 4),
    .atom (.mul (.n (r + 3)) (.n (r + 1)) (.n (r + 2))),
    .atom (.load (.n (r + 4)) (.n (slotPt s 3)) 3),
    .atom (.mul (.n (r + 5)) (.n (r + 3)) (.n (r + 4))),
    .atom (.load (.n (r + 6)) (.n (slotPt s 2)) 2),
    .atom (.mul (.n (r + 7)) (.n (r + 5)) (.n (r + 6))),
    .atom (.load (.n (r + 8)) (.n (slotPt s 1)) 1),
    .atom (.mul (.n (r + 9)) (.n (r + 7)) (.n (r + 8))),
    .atom (.load (.n (r + 10)) (.n (slotPt s 0)) 0),
    .atom (.mul (.n (r + 11)) (.n (r + 9)) (.n (r + 10))),
    .atom (.mul (.n (r + 12)) (.n 21) (.n r)), .atom (.load (.n (r + 13)) (.n (r + 12)) 0),
    .atom (.mul (.n (r + 14)) (.n (r + 11)) (.n (r + 13))),
    .atom (.const (.n (r + 15)) (word 64 0 0)), .atom (.mul (.n (r + 16)) (.n r) (.n (r + 15))),
    .atom (.load (.n (r + 17)) (.n 11) 5), .atom (.assertEq (.n (r + 16)) (.n (r + 17))),
    .atom (.load (.n (r + 18)) (.n 9) j), .atom (.mul (.n (r + 19)) (.n (r + 18)) (.n (r + 14))),
    .atom (.mul (.n (r + 20)) (.n (r + 19)) (.n (selV 5))),
    .atom (.add (.n (r + 21)) (.n acc) (.n (r + 20)))]

/-- A public input's claim (kind `3`). -/
def pT (j c r acc : ℕ) : List Stmt :=
  [.atom (.load (.n r) (.n 11) c), .atom (.assertEq (.n 5) (.n r)),
    .atom (.load (.n (r + 1)) (.n 9) j), .atom (.mul (.n (r + 2)) (.n (r + 1)) (.n 33)),
    .atom (.mul (.n (r + 3)) (.n (r + 2)) (.n (selV c))),
    .atom (.add (.n (r + 4)) (.n acc) (.n (r + 3)))]

/-- Claim `j`'s block, the values it takes, and its sum's value. -/
def claimT (j r acc : ℕ) : List Stmt × ℕ × ℕ :=
  match termKind j with
  | 0 => (zrT 19 j (termCol j) r acc, r + 8, r + 7)
  | 1 => (zrT 21 j (termCol j) r acc, r + 8, r + 7)
  | 2 => (qT j (j - 85) r acc, r + 22, r + 21)
  | 3 => (pT j (termCol j) r acc, r + 5, r + 4)
  | _ => ([], r, acc)

/-- The claims `js` from value `r`, the sum so far at `acc`: the statements, the next value and
the sum's value. -/
def claimsT : List ℕ → ℕ → ℕ → List Stmt × ℕ × ℕ
  | [], r, acc => ([], r, acc)
  | j :: js, r, acc =>
      let b := claimT j r acc
      let rest := claimsT js b.2.1 b.2.2
      (b.1 ++ rest.1, rest.2.1, rest.2.2)

/-- The tail (G:3133-3144): the outputs' chain, the ring switch's weight, the terminal check. -/
def termTailT : List Stmt :=
  [.atom (.const (.n 1836) (word 64 0 0)), .atom (.mul (.n 1837) (.n 6) (.n 1836)),
    .atom (.load (.n 1838) (.n 11) 5), .atom (.assertEq (.n 1837) (.n 1838)),
    .atom (.hint (.alloc (.n 1839) 41)), .atom (.const (.n 1840) (word 1 0 0)),
    .atom (.const (.n 1841) (word 64 0 0)), .atom (.mul (.n 1842) (.n 6) (.n 1841)),
    .call "eq_prefix_chain" [.n 1839, .n 1840, .n 12, .n 15, .n 1842] [],
    .atom (.const (.n 1843) (word 549755813888 0 0)), .atom (.mul (.n 1844) (.n 12) (.n 1843)),
    .atom (.const (.n 1845) (word 64 0 0)), .atom (.mul (.n 1846) (.n 6) (.n 1845)),
    .call "ring_switch_weight" [.n 1844, .n 15, .n 13, .n 1846] [.n 1847],
    .atom (.mul (.n 1848) (.n 1839) (.n 6)), .atom (.load (.n 1849) (.n 1848) 6),
    .atom (.mul (.n 1850) (.n 8) (.n 1849)), .atom (.add (.n 1851) (.n 1847) (.n 1850)),
    .atom (.mul (.n 1852) (.n 1851) (.n (selV 5))), .atom (.add (.n 1853) (.n 1835) (.n 1852)),
    .atom (.mul (.n 1854) (.n 1853) (.n 17)), .atom (.assertEq (.n 1854) (.n 18)), .ret []]

/-- **`check_opening_terminal`'s body.** -/
def termT : List Stmt := termHeadT ++ selsT ++ (claimsT (List.range 165) 375 16).1 ++ termTailT

end
end LeanVM.Guest.B1.VerifySub
