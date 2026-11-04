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
    [.load (.n 400) (.n 387) 0, .load (.n 401) (.n 387) 1, .load (.n 413) (.n 387) 0,
      .load (.n 414) (.n 387) 1, .load (.n 432) (.n 431) 0] ++
    (List.range 23).map (fun k => .load (.n (453 + k)) (.n 449) k) ++ [.load (.n 452) (.n 449) 23]

/-- `main`'s loads, by their words' numbers: the five reads, then the stores. -/
def mLoadOk (d p o : ℕ) : Bool :=
  decide ((d, p, o) ∈ [(437, 436, 0), (476, 448, 0), (477, 448, 1), (481, 480, 0),
    (485, 484, 0)]) ||
  (decide (p = 68) && decide (d = 69 + o) && decide (o < 256)) ||
  decide ((d, p, o) ∈ [(400, 387, 0), (401, 387, 1), (413, 387, 0), (414, 387, 1),
    (432, 431, 0)]) ||
  (decide (p = 449) && (decide (o < 23 ∧ d = 453 + o) || decide (o = 23 ∧ d = 452)))

/-- The range checks: the checked value and the bound's constant. -/
def rcPairs : List (ℕ × ℕ) :=
  [(0, 8), (1, 12), (2, 16), (3, 20), (4, 24), (5, 28), (6, 32), (7, 36), (42, 43), (438, 6)]

/-- The atoms of `main` whose side conditions its completeness discharges. -/
def mSideOk : Atom → Bool
  | .rangeCheck x y _ _ k => decide ((x.idx, k.idx) ∈ rcPairs) && decide (x = .n x.idx) &&
      decide (k = .n k.idx) && decide (k.idx < y.idx)
  | .load d p o => decide (d = .n d.idx) && decide (p = .n p.idx) && mLoadOk d.idx p.idx o
  | .assertEq x y => decide ((x, y) ∈ [(V.n 437, V.n 42), (.n 445, .n 446), (.n 481, .n 478),
      (.n 485, .n 479)])
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
  canonChk [390, 391, 392, 393] (noStores mDa) && canonChk [] (noStores mDaZ) &&
  canonChk [] (noStores mLeaf) &&
  (atomsIn mFlat).all (fun a => !needsSide a || mSideOk a)

set_option maxRecDepth 100000 in
theorem mainc_ok : mainCOk = true := by decide +kernel

/-- The statements defining `main`'s oracle values: hints, `HeapBuf`s, calls' returns. -/
def mOrcStmts : List Stmt :=
  [.atom (.hint (.witness "meta" (.stack [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]))),
    .atom (.hint (.witness "fs_seed" (.stack [.n 47, .n 48]))),
    .call "exponent_tables" [] [.n 49], .atom (.hint (.allocDyn (.n 52) (.n 51))),
    .atom (.hint (.allocDyn (.n 55) (.n 54))),
    .call "claim_list_digest" [.n 52, .n 0] [.n 56, .n 57],
    .call "claim_list_digest" [.n 55, .n 3] [.n 58, .n 59],
    .atom (.hint (.allocDyn (.n 66) (.n 42))), .atom (.hint (.alloc (.n 68) 256)),
    .atom (.hint (.allocDyn (.n 385) (.n 384))),
    .call "da_verify" [.n 49] [.n 390, .n 391, .n 392, .n 393],
    .atom (.hint (.allocDyn (.n 416) (.n 415))), .atom (.hint (.allocDyn (.n 422) (.n 421))),
    .atom (.hint (.allocDyn (.n 428) (.n 427))), .atom (.hint (.allocDyn (.n 431) (.n 430))),
    .atom (.hint (.witness "da_pick" (.stack [.n 438]))),
    .atom (.hint (.alloc (.n 449) 24)), .atom (.hint (.witness "leaf_defer" (.stack [.n 452]))),
    .call "statement_digest" [.n 47, .n 48, .n 56, .n 57, .n 58, .n 59, .n 476, .n 477, .n 449]
      [.n 478, .n 479]]

/-- The atoms defining `main`'s words the proof reads. -/
def mDefAtoms : List Atom :=
  [.mul (.n 40) (.n 0) (.n 1), .mul (.n 41) (.n 3) (.n 4), .mul (.n 42) (.n 40) (.n 41),
    .mul (.n 50) (.n 40) (.n 40), .mul (.n 51) (.n 50) (.n 50),
    .mul (.n 53) (.n 41) (.n 41), .mul (.n 54) (.n 53) (.n 53), .mul (.n 67) (.n 66) (.n 40),
    .const (.n 60) (word 1 0 0), .add (.n 61) (.n 60) (.n 1), .const (.n 62) (word 1 0 0),
    .const (.n 63) (word 1 0 0), .add (.n 64) (.n 63) (.n 4), .const (.n 65) (word 1 0 0),
    .const (.n 376) (word 1 0 0), .add (.n 377) (.n 376) (.n 2), .const (.n 378) (word 1 0 0),
    .const (.n 379) (word 1 0 0), .add (.n 380) (.n 379) (.n 5), .const (.n 381) (word 1 0 0),
    .const (.n 382) (word 2 0 0), .mul (.n 383) (.n 6) (.n 382), .mul (.n 384) (.n 383) (.n 383),
    .mul (.n 386) (.n 6) (.n 6), .mul (.n 387) (.n 385) (.n 386),
    .const (.n 388) (word 2 0 0), .add (.n 389) (.n 7) (.n 388),
    .mul (.n 415) (.n 6) (.n 6), .mul (.n 417) (.n 6) (.n 6), .mul (.n 418) (.n 417) (.n 6),
    .mul (.n 419) (.n 418) (.n 418), .mul (.n 420) (.n 419) (.n 419),
    .mul (.n 421) (.n 420) (.n 420), .mul (.n 423) (.n 6) (.n 6), .mul (.n 424) (.n 423) (.n 6),
    .mul (.n 425) (.n 424) (.n 424), .mul (.n 426) (.n 425) (.n 425),
    .mul (.n 427) (.n 426) (.n 426), .const (.n 429) (word 2 0 0), .mul (.n 430) (.n 6) (.n 429),
    .mul (.n 432) (.n 2) (.n 5), .const (.n 433) (word 1 0 0), .add (.n 434) (.n 433) (.n 6),
    .const (.n 435) (word 1 0 0), .mul (.n 436) (.n 431) (.n 6),
    .add (.n 442) (.n 438) (.n 6), .const (.n 443) (word 1 0 0), .add (.n 444) (.n 7) (.n 443),
    .mul (.n 445) (.n 442) (.n 444), .const (.n 446) (word 0 0 0),
    .mul (.n 447) (.n 438) (.n 438), .mul (.n 448) (.n 385) (.n 447),
    .const (.n 450) (word 1 0 0), .add (.n 451) (.n 6) (.n 450),
    .const (.n 480) (word 1 0 0), .const (.n 482) (word 1 0 0), .const (.n 483) (word 2 0 0),
    .mul (.n 484) (.n 482) (.n 483),
    .const (.n 8) (word 9272771591053052074 0 0), .const (.n 12) (word 9272771591053052074 0 0),
    .const (.n 16) (word 9272771591053052074 0 0), .const (.n 20) (word 9272771591053052074 0 0),
    .const (.n 24) (word 9272771591053052074 0 0), .const (.n 28) (word 9272771591053052074 0 0),
    .const (.n 32) (word 65536 0 0), .const (.n 36) (word 2 0 0),
    .const (.n 43) (word 9272771591053052074 0 0),
    .load (.n 437) (.n 436) 0, .load (.n 476) (.n 448) 0, .load (.n 477) (.n 448) 1,
    .load (.n 481) (.n 480) 0, .load (.n 485) (.n 484) 0] ++
  (List.range 51).map fun j => .const (.n (325 + j)) (word (lxTagVals.getD j 0) 0 0)

end
end LeanVM.Guest.B1.Main
