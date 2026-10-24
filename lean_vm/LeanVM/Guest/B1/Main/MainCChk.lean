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
(`mSideOk`); the signer set's hash reads the two claim lists' digests (`canonChk`), each block
checked on its own.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `main`'s body, both conditional blocks inlined. -/
noncomputable def mFlat : List Stmt := mPre ++ mDa ++ mMid ++ mLeaf ++ mPost

/-- The evaluated block: `mFlat` without the hinted inverse of its nonzero check (statement `61`),
whose value the check itself defines; the hint holds of every valuation. -/
noncomputable def mFlatE : List Stmt := mFlat.eraseIdx 61

/-- `main`'s stores: the signer set's digest, the byte table, the first running count, the
leaf's deferred claim. -/
def mStoresL : List Atom :=
  [.load (.n 103) (.n 116) 0, .load (.n 104) (.n 116) 1] ++
    (List.range 256).map (fun v => .load (.n (120 + v)) (.n 119) v) ++ [.load (.n 411) (.n 409) 0] ++
    (List.range 23).map (fun k => .load (.n (421 + k)) (.n 417) k) ++ [.load (.n 420) (.n 417) 23]

/-- `main`'s loads, by their words' numbers: the three reads, then the stores. -/
def mLoadOk (d p o : ℕ) : Bool :=
  decide ((d, p, o) ∈ [(416, 415, 0), (447, 446, 0), (451, 450, 0)]) ||
  (decide (p = 116) && (decide (d = 103 ∧ o = 0) || decide (d = 104 ∧ o = 1))) ||
  (decide (p = 119) && decide (d = 120 + o) && decide (o < 256)) ||
  (decide (p = 409) && decide (d = 411) && decide (o = 0)) ||
  (decide (p = 417) && (decide (o < 23 ∧ d = 421 + o) || decide (o = 23 ∧ d = 420)))

/-- The range checks: the checked value and the bound's constant. -/
def rcPairs : List (ℕ × ℕ) :=
  [(0, 8), (1, 12), (2, 16), (3, 20), (4, 24), (5, 28), (6, 32), (7, 36), (40, 42), (41, 46),
    (50, 51), (58, 59)]

/-- The atoms of `main` whose side conditions its completeness discharges. -/
def mSideOk : Atom → Bool
  | .rangeCheck x y _ _ k => decide ((x.idx, k.idx) ∈ rcPairs) && decide (x = .n x.idx) &&
      decide (k = .n k.idx) && decide (k.idx < y.idx)
  | .load d p o => decide (d = .n d.idx) && decide (p = .n p.idx) && mLoadOk d.idx p.idx o
  | .assertEq x y => decide ((x, y) ∈ [(V.n 384, V.n 389), (.n 385, .n 390), (.n 386, .n 391),
      (.n 387, .n 392), (.n 416, .n 58), (.n 447, .n 444), (.n 451, .n 445)])
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
    .call "claim_list_digest" [.n 80, .n 3] [.n 83, .n 84], .atom (.hint (.alloc (.n 116) 2)),
    .atom (.hint (.allocDyn (.n 117) (.n 58))), .atom (.hint (.alloc (.n 119) 256)),
    .call "da_verify" [.n 66] [.n 384, .n 385, .n 386, .n 387],
    .call "cover_da_root" [.n 69, .n 118, .n 50, .n 388] [.n 389, .n 390, .n 391, .n 392],
    .atom (.hint (.allocDyn (.n 394) (.n 393))), .atom (.hint (.allocDyn (.n 400) (.n 399))),
    .atom (.hint (.allocDyn (.n 406) (.n 405))), .atom (.hint (.allocDyn (.n 409) (.n 408))),
    .atom (.hint (.alloc (.n 417) 24)), .atom (.hint (.witness "leaf_defer" (.stack [.n 420]))),
    .call "statement_digest" [.n 63, .n 64, .n 116, .n 73, .n 74, .n 417] [.n 444, .n 445]]

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
    .mul (.n 118) (.n 117) (.n 57), .const (.n 376) (word 1 0 0), .add (.n 377) (.n 376) (.n 2),
    .const (.n 378) (word 1 0 0), .const (.n 379) (word 1 0 0), .add (.n 380) (.n 379) (.n 5),
    .const (.n 381) (word 1 0 0), .const (.n 382) (word 2 0 0), .add (.n 383) (.n 7) (.n 382),
    .mul (.n 388) (.n 2) (.n 5), .mul (.n 393) (.n 6) (.n 6), .mul (.n 395) (.n 6) (.n 6),
    .mul (.n 396) (.n 395) (.n 6), .mul (.n 397) (.n 396) (.n 396), .mul (.n 398) (.n 397) (.n 397),
    .mul (.n 399) (.n 398) (.n 398), .mul (.n 401) (.n 6) (.n 6), .mul (.n 402) (.n 401) (.n 6),
    .mul (.n 403) (.n 402) (.n 402), .mul (.n 404) (.n 403) (.n 403), .mul (.n 405) (.n 404) (.n 404),
    .const (.n 407) (word 2 0 0), .mul (.n 408) (.n 6) (.n 407), .mul (.n 410) (.n 2) (.n 5),
    .mul (.n 411) (.n 410) (.n 7), .const (.n 412) (word 1 0 0), .add (.n 413) (.n 412) (.n 6),
    .const (.n 414) (word 1 0 0), .mul (.n 415) (.n 409) (.n 6), .const (.n 418) (word 1 0 0),
    .add (.n 419) (.n 6) (.n 418), .const (.n 446) (word 1 0 0), .const (.n 448) (word 1 0 0),
    .const (.n 449) (word 2 0 0), .mul (.n 450) (.n 448) (.n 449),
    .const (.n 8) (word 9272771591053052074 0 0), .const (.n 12) (word 9272771591053052074 0 0),
    .const (.n 16) (word 9272771591053052074 0 0), .const (.n 20) (word 9272771591053052074 0 0),
    .const (.n 24) (word 9272771591053052074 0 0), .const (.n 28) (word 9272771591053052074 0 0),
    .const (.n 32) (word 65536 0 0), .const (.n 36) (word 2 0 0), .const (.n 42) (word 65536 0 0),
    .const (.n 46) (word 139298 0 0), .const (.n 51) (word 139298 0 0),
    .const (.n 59) (word 9272771591053052074 0 0), .assertNe (.n 94) (.n 95) (.n 96), .load (.n 416) (.n 415) 0, .load (.n 447) (.n 446) 0,
    .load (.n 451) (.n 450) 0]

/-- A store of the leaf's deferred claim. -/
def isLeafStore : Atom → Bool
  | .load _ p _ => decide (p = .n 417)
  | _ => false



end
end LeanVM.Guest.B1.Main
