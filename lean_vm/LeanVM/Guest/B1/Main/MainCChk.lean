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
(`mPre`, `mDa`, `mDaZ`, `mMid`, `mLeaf`, `mPost`), every value defined at its first occurrence
(`chk`); the batching's branch defines nothing. The atoms needing a side condition are the range
checks, the loads through `main`'s buffers and the header, and the four equality checks
(`mSideOk`); the only `KECCAK` is the own DA claim's digest, on `da_verify`'s returns
(`canonChk`), each block checked on its own.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `main`'s body, both branches of each conditional block inlined. -/
noncomputable def mFlat : List Stmt := mPre ++ mDa ++ mDaZ ++ mMid ++ mLeaf ++ mPost

/-- The evaluated block: `mFlat` itself (`main` hints no inverse). -/
noncomputable def mFlatE : List Stmt := mFlat

/-- `main`'s stores: the byte table, the own DA digest (both branches), the first running count,
the leaf's deferred claim. -/
def mStoresL : List Atom :=
  (List.range 256).map (fun v => .load (.n (69 + v)) (.n 68) v) ++
    [.load (.n 349) (.n 336) 0, .load (.n 350) (.n 336) 1, .load (.n 362) (.n 336) 0,
      .load (.n 363) (.n 336) 1, .load (.n 381) (.n 380) 0] ++
    (List.range 23).map (fun k => .load (.n (406 + k)) (.n 402) k) ++ [.load (.n 405) (.n 402) 23]

/-- `main`'s loads, by their words' numbers: the five reads, then the stores. -/
def mLoadOk (d p o : ℕ) : Bool :=
  decide ((d, p, o) ∈ [(386, 385, 0), (429, 401, 0), (430, 401, 1), (434, 433, 0),
    (438, 437, 0)]) ||
  (decide (p = 68) && decide (d = 69 + o) && decide (o < 256)) ||
  decide ((d, p, o) ∈ [(349, 336, 0), (350, 336, 1), (362, 336, 0), (363, 336, 1),
    (381, 380, 0)]) ||
  (decide (p = 402) && (decide (o < 23 ∧ d = 406 + o) || decide (o = 23 ∧ d = 405)))

/-- The range checks: the checked value and the bound's constant. -/
def rcPairs : List (ℕ × ℕ) :=
  [(0, 8), (1, 12), (2, 16), (3, 20), (4, 24), (5, 28), (6, 32), (7, 36), (42, 43), (387, 391)]

/-- The atoms of `main` whose side conditions its completeness discharges. -/
def mSideOk : Atom → Bool
  | .rangeCheck x y _ _ k => decide ((x.idx, k.idx) ∈ rcPairs) && decide (x = .n x.idx) &&
      decide (k = .n k.idx) && decide (k.idx < y.idx)
  | .load d p o => decide (d = .n d.idx) && decide (p = .n p.idx) && mLoadOk d.idx p.idx o
  | .assertEq x y => decide ((x, y) ∈ [(V.n 386, V.n 42), (.n 398, .n 399), (.n 434, .n 431),
      (.n 438, .n 432)])
  | _ => false

/-- The stores of `main`'s body. -/
noncomputable def mStores : List Atom := storesOf 0 mFlatE

/-- A block's atoms but the stores. -/
noncomputable def noStores (P : List Stmt) : List Atom :=
  (atomsIn P).filter fun a => decide (a ∉ mStores)

/-- **`main`'s body, evaluated.** -/
noncomputable def mainCOk : Bool :=
  (chk 0 mFlatE).isSome &&
  canonChk [] (noStores (mPre ++ mMid ++ mPost)) &&
  canonChk [339, 340, 341, 342] (noStores mDa) && canonChk [] (noStores mDaZ) &&
  canonChk [] (noStores mLeaf) &&
  (atomsIn mFlat).all (fun a => !needsSide a || mSideOk a)

set_option maxRecDepth 100000 in
theorem mainc_ok : mainCOk = true := by decide +kernel

/-- The statements defining `main`'s oracle values: hints, `HeapBuf`s, calls' returns. -/
def mOrcStmts : List Stmt :=
  [.atom (.hint (.witness "meta" (.stack [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]))),
    .atom (.hint (.witness "fs_seed" (.stack [.n 47, .n 48]))),
    .call "exponent_tables" [] [.n 49, .n 50], .atom (.hint (.allocDyn (.n 53) (.n 52))),
    .atom (.hint (.allocDyn (.n 56) (.n 55))),
    .call "claim_list_digest" [.n 53, .n 0] [.n 57, .n 58],
    .call "claim_list_digest" [.n 56, .n 3] [.n 59, .n 60],
    .atom (.hint (.allocDyn (.n 67) (.n 42))), .atom (.hint (.alloc (.n 68) 256)),
    .atom (.hint (.allocDyn (.n 334) (.n 333))),
    .call "da_verify" [.n 50] [.n 339, .n 340, .n 341, .n 342],
    .atom (.hint (.allocDyn (.n 365) (.n 364))), .atom (.hint (.allocDyn (.n 371) (.n 370))),
    .atom (.hint (.allocDyn (.n 377) (.n 376))), .atom (.hint (.allocDyn (.n 380) (.n 379))),
    .atom (.hint (.witness "da_pick" (.stack [.n 387]))),
    .atom (.hint (.alloc (.n 402) 24)), .atom (.hint (.witness "leaf_defer" (.stack [.n 405]))),
    .call "statement_digest" [.n 47, .n 48, .n 57, .n 58, .n 59, .n 60, .n 429, .n 430, .n 402]
      [.n 431, .n 432]]

/-- The atoms defining `main`'s words the proof reads. -/
def mDefAtoms : List Atom :=
  [.mul (.n 40) (.n 0) (.n 1), .mul (.n 41) (.n 3) (.n 4), .mul (.n 42) (.n 40) (.n 41),
    .mul (.n 51) (.n 40) (.n 40), .mul (.n 52) (.n 51) (.n 51),
    .mul (.n 54) (.n 41) (.n 41), .mul (.n 55) (.n 54) (.n 54),
    .const (.n 61) (word 1 0 0), .add (.n 62) (.n 61) (.n 1), .const (.n 63) (word 1 0 0),
    .const (.n 64) (word 1 0 0), .add (.n 65) (.n 64) (.n 4), .const (.n 66) (word 1 0 0),
    .const (.n 325) (word 1 0 0), .add (.n 326) (.n 325) (.n 2), .const (.n 327) (word 1 0 0),
    .const (.n 328) (word 1 0 0), .add (.n 329) (.n 328) (.n 5), .const (.n 330) (word 1 0 0),
    .const (.n 331) (word 2 0 0), .mul (.n 332) (.n 6) (.n 331), .mul (.n 333) (.n 332) (.n 332),
    .mul (.n 335) (.n 6) (.n 6), .mul (.n 336) (.n 334) (.n 335),
    .const (.n 337) (word 2 0 0), .add (.n 338) (.n 7) (.n 337),
    .mul (.n 364) (.n 6) (.n 6), .mul (.n 366) (.n 6) (.n 6), .mul (.n 367) (.n 366) (.n 6),
    .mul (.n 368) (.n 367) (.n 367), .mul (.n 369) (.n 368) (.n 368),
    .mul (.n 370) (.n 369) (.n 369), .mul (.n 372) (.n 6) (.n 6), .mul (.n 373) (.n 372) (.n 6),
    .mul (.n 374) (.n 373) (.n 373), .mul (.n 375) (.n 374) (.n 374),
    .mul (.n 376) (.n 375) (.n 375), .const (.n 378) (word 2 0 0), .mul (.n 379) (.n 6) (.n 378),
    .mul (.n 381) (.n 2) (.n 5), .const (.n 382) (word 1 0 0), .add (.n 383) (.n 382) (.n 6),
    .const (.n 384) (word 1 0 0), .mul (.n 385) (.n 380) (.n 6),
    .const (.n 388) (word 2 0 0), .mul (.n 389) (.n 6) (.n 388),
    .const (.n 390) (word 9223372036854775821 0 0), .mul (.n 391) (.n 389) (.n 390),
    .add (.n 395) (.n 387) (.n 6), .const (.n 396) (word 1 0 0), .add (.n 397) (.n 7) (.n 396),
    .mul (.n 398) (.n 395) (.n 397), .const (.n 399) (word 0 0 0),
    .mul (.n 400) (.n 387) (.n 387), .mul (.n 401) (.n 334) (.n 400),
    .const (.n 403) (word 1 0 0), .add (.n 404) (.n 6) (.n 403),
    .const (.n 433) (word 1 0 0), .const (.n 435) (word 1 0 0), .const (.n 436) (word 2 0 0),
    .mul (.n 437) (.n 435) (.n 436),
    .const (.n 8) (word 9272771591053052074 0 0), .const (.n 12) (word 9272771591053052074 0 0),
    .const (.n 16) (word 9272771591053052074 0 0), .const (.n 20) (word 9272771591053052074 0 0),
    .const (.n 24) (word 9272771591053052074 0 0), .const (.n 28) (word 9272771591053052074 0 0),
    .const (.n 32) (word 65536 0 0), .const (.n 36) (word 2 0 0),
    .const (.n 43) (word 9272771591053052074 0 0),
    .load (.n 386) (.n 385) 0, .load (.n 429) (.n 401) 0, .load (.n 430) (.n 401) 1,
    .load (.n 434) (.n 433) 0, .load (.n 438) (.n 437) 0]

end
end LeanVM.Guest.B1.Main
