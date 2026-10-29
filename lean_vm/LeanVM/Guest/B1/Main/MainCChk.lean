/-
  LeanVM.Guest.B1.Main.MainCChk

  `main`'s body as one evaluated block (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# `main`'s body, evaluated

`mFlat` is `main`'s body with both branches of the direct DA check and the leaf's branch inlined
(`mPre`, `mDa`, `mMid`, `mLeaf`, `mPost`), every value defined at its first occurrence (`chk`); the
batching's branch defines nothing. The atoms needing a side condition are the range checks, the
loads through `main`'s buffers and the header, the seven equality checks and the nonzero check
(`mSideOk`); `main` itself has no `KECCAK` (`canonChk`), each block checked on its own.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `main`'s body, both conditional blocks inlined. -/
noncomputable def mFlat : List Stmt := mPre ++ mDa ++ mMid ++ mLeaf ++ mPost

/-- The evaluated block: `mFlat` without the hinted inverse of its nonzero check (statement `61`),
whose value the check itself defines; the hint holds of every valuation. -/
noncomputable def mFlatE : List Stmt := mFlat.eraseIdx 61

/-- `main`'s stores: the byte table, the first running count, the leaf's deferred claim. -/
def mStoresL : List Atom :=
  (List.range 256).map (fun v => .load (.n (100 + v)) (.n 99) v) ++ [.load (.n 391) (.n 389) 0] ++
    (List.range 23).map (fun k => .load (.n (401 + k)) (.n 397) k) ++ [.load (.n 400) (.n 397) 23]

/-- `main`'s loads, by their words' numbers: the three reads, then the stores. -/
def mLoadOk (d p o : ℕ) : Bool :=
  decide ((d, p, o) ∈ [(396, 395, 0), (427, 426, 0), (431, 430, 0)]) ||
  (decide (p = 99) && decide (d = 100 + o) && decide (o < 256)) ||
  (decide (p = 389) && decide (d = 391) && decide (o = 0)) ||
  (decide (p = 397) && (decide (o < 23 ∧ d = 401 + o) || decide (o = 23 ∧ d = 400)))

/-- The range checks: the checked value and the bound's constant. -/
def rcPairs : List (ℕ × ℕ) :=
  [(0, 8), (1, 12), (2, 16), (3, 20), (4, 24), (5, 28), (6, 32), (7, 36), (40, 42), (41, 46),
    (50, 51), (58, 59)]

/-- The atoms of `main` whose side conditions its completeness discharges. -/
def mSideOk : Atom → Bool
  | .rangeCheck x y _ _ k => decide ((x.idx, k.idx) ∈ rcPairs) && decide (x = .n x.idx) &&
      decide (k = .n k.idx) && decide (k.idx < y.idx)
  | .load d p o => decide (d = .n d.idx) && decide (p = .n p.idx) && mLoadOk d.idx p.idx o
  | .assertEq x y => decide ((x, y) ∈ [(V.n 364, V.n 369), (.n 365, .n 370), (.n 366, .n 371),
      (.n 367, .n 372), (.n 396, .n 58), (.n 427, .n 424), (.n 431, .n 425)])
  | .assertNe x _ _ => decide (x = .n 94)
  | _ => false

/-- The stores of `main`'s body. -/
noncomputable def mStores : List Atom := storesOf 0 mFlatE

/-- A block's atoms but the stores. -/
noncomputable def noStores (P : List Stmt) : List Atom :=
  (atomsIn P).filter fun a => decide (a ∉ mStores)

/-- **`main`'s body, evaluated.** -/
noncomputable def mainCOk : Bool :=
  (chk 0 mFlatE).isSome && stmtEqb (mFlat.getD 61 default) (.atom (.hint (.inverse (.n 94) (.n 95)))) &&
  canonChk [81, 82, 83, 84] (noStores (mPre ++ mMid ++ mPost)) &&
  canonChk [] (noStores mDa) && canonChk [] (noStores mLeaf) &&
  (atomsIn mFlat).all (fun a => !needsSide a || mSideOk a)

set_option maxRecDepth 100000 in
theorem mainc_ok : mainCOk = true := by decide +kernel

/-- The statements defining `main`'s oracle values: hints, `HeapBuf`s, calls' returns. -/
def mOrcStmts : List Stmt :=
  [.atom (.hint (.witness "meta" (.stack [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]))),
    .atom (.hint (.witness "da_meta" (.stack [.n 40, .n 41]))),
    .atom (.hint (.witness "fs_seed" (.stack [.n 63, .n 64]))),
    .call "exponent_tables" [] [.n 65, .n 66], .atom (.hint (.allocDyn (.n 69) (.n 68))),
    .call "da_list_digest" [.n 69, .n 40] [.n 73, .n 74], .atom (.hint (.allocDyn (.n 77) (.n 76))),
    .atom (.hint (.allocDyn (.n 80) (.n 79))), .call "claim_list_digest" [.n 77, .n 0] [.n 81, .n 82],
    .call "claim_list_digest" [.n 80, .n 3] [.n 83, .n 84],
    .atom (.hint (.allocDyn (.n 97) (.n 58))), .atom (.hint (.alloc (.n 99) 256)),
    .call "da_verify" [.n 66] [.n 364, .n 365, .n 366, .n 367],
    .call "cover_da_root" [.n 69, .n 98, .n 50, .n 368] [.n 369, .n 370, .n 371, .n 372],
    .atom (.hint (.allocDyn (.n 374) (.n 373))), .atom (.hint (.allocDyn (.n 380) (.n 379))),
    .atom (.hint (.allocDyn (.n 386) (.n 385))), .atom (.hint (.allocDyn (.n 389) (.n 388))),
    .atom (.hint (.alloc (.n 397) 24)), .atom (.hint (.witness "leaf_defer" (.stack [.n 400]))),
    .call "statement_digest" [.n 63, .n 64, .n 81, .n 82, .n 83, .n 84, .n 73, .n 74, .n 397]
      [.n 424, .n 425]]

/-- The atoms defining `main`'s words the proof reads. -/
def mDefAtoms : List Atom :=
  [.mul (.n 50) (.n 40) (.n 41), .mul (.n 55) (.n 0) (.n 1), .mul (.n 56) (.n 3) (.n 4),
    .mul (.n 57) (.n 55) (.n 56), .mul (.n 58) (.n 57) (.n 50), .mul (.n 67) (.n 50) (.n 50),
    .mul (.n 68) (.n 67) (.n 67), .const (.n 70) (word 1 0 0), .add (.n 71) (.n 70) (.n 50),
    .const (.n 72) (word 1 0 0), .mul (.n 75) (.n 55) (.n 55), .mul (.n 76) (.n 75) (.n 75),
    .mul (.n 78) (.n 56) (.n 56), .mul (.n 79) (.n 78) (.n 78), .const (.n 85) (word 1 0 0),
    .add (.n 86) (.n 85) (.n 1), .const (.n 87) (word 1 0 0), .const (.n 88) (word 1 0 0),
    .add (.n 89) (.n 88) (.n 4), .const (.n 90) (word 1 0 0), .mul (.n 91) (.n 0) (.n 3),
    .mul (.n 92) (.n 91) (.n 40), .const (.n 93) (word 1 0 0), .add (.n 94) (.n 92) (.n 93),
    .mul (.n 98) (.n 97) (.n 57), .const (.n 356) (word 1 0 0), .add (.n 357) (.n 356) (.n 2),
    .const (.n 358) (word 1 0 0), .const (.n 359) (word 1 0 0), .add (.n 360) (.n 359) (.n 5),
    .const (.n 361) (word 1 0 0), .const (.n 362) (word 2 0 0), .add (.n 363) (.n 7) (.n 362),
    .mul (.n 368) (.n 2) (.n 5), .mul (.n 373) (.n 6) (.n 6), .mul (.n 375) (.n 6) (.n 6),
    .mul (.n 376) (.n 375) (.n 6), .mul (.n 377) (.n 376) (.n 376), .mul (.n 378) (.n 377) (.n 377),
    .mul (.n 379) (.n 378) (.n 378), .mul (.n 381) (.n 6) (.n 6), .mul (.n 382) (.n 381) (.n 6),
    .mul (.n 383) (.n 382) (.n 382), .mul (.n 384) (.n 383) (.n 383), .mul (.n 385) (.n 384) (.n 384),
    .const (.n 387) (word 2 0 0), .mul (.n 388) (.n 6) (.n 387), .mul (.n 390) (.n 2) (.n 5),
    .mul (.n 391) (.n 390) (.n 7), .const (.n 392) (word 1 0 0), .add (.n 393) (.n 392) (.n 6),
    .const (.n 394) (word 1 0 0), .mul (.n 395) (.n 389) (.n 6), .const (.n 398) (word 1 0 0),
    .add (.n 399) (.n 6) (.n 398), .const (.n 426) (word 1 0 0), .const (.n 428) (word 1 0 0),
    .const (.n 429) (word 2 0 0), .mul (.n 430) (.n 428) (.n 429),
    .const (.n 8) (word 9272771591053052074 0 0), .const (.n 12) (word 9272771591053052074 0 0),
    .const (.n 16) (word 9272771591053052074 0 0), .const (.n 20) (word 9272771591053052074 0 0),
    .const (.n 24) (word 9272771591053052074 0 0), .const (.n 28) (word 9272771591053052074 0 0),
    .const (.n 32) (word 65536 0 0), .const (.n 36) (word 2 0 0), .const (.n 42) (word 65536 0 0),
    .const (.n 46) (word 139298 0 0), .const (.n 51) (word 139298 0 0),
    .const (.n 59) (word 9272771591053052074 0 0), .assertNe (.n 94) (.n 95) (.n 96), .load (.n 396) (.n 395) 0, .load (.n 427) (.n 426) 0,
    .load (.n 431) (.n 430) 0]

/-- A store of the leaf's deferred claim. -/
def isLeafStore : Atom → Bool
  | .load _ p _ => decide (p = .n 397)
  | _ => false



end
end LeanVM.Guest.B1.Main
