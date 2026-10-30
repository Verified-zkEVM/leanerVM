/-
  LeanVM.Guest.B1.KeccakGkr.VkT

  `verify_keccak`'s body as a template (G:2766-2937), section by section.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
public import LeanVM.Guest.B1.Eq.EqTree

/-!
# `verify_keccak` as a template

The sections, in order:

* `vkHeadT`: the capacity copied, `pack_g`, `y_g`, the bits of `y` (pinned boolean) and `half_g`,
  `odd_g`, `y_last` (`assert half_g·y_last = y_g`); the instance coordinates copied to `z_vals`;
  the point's pack coordinates copied (`__loop10`); the segment and the lane coordinates
  squeezed (`sqZeroT`); the committed outputs' value read;
* the first claim's record: `KC_KAPPA`, `KC_POINT`, the instance weights (`eqtreeT`, `muCopyT`),
  the lanes (`eqtreeT`), the segment weights (`eqtreeT`), the value (`dotLoadsT`);
* twelve steps (`stepT`): the claim's segment weights, its `ι` term (`flipsT`, `iotaSegT`), and
  `keccak_layer` by `odd_g` (`stepTailT`);
* the committed outputs: `keccak_plain_rounds` over the slot, the word, the slot's lane weights
  (`slotLanesT`), their check; the pack coordinates copied (`__loop11`);
* the inputs: `keccak_plain_rounds` over the pack, `μ(low)`, over the slot, the 64 slices
  (`slicesT`), the ring map's first challenge, the slot's lane weights, the shifts of the slices
  (`foldT`), `keccak_form` (`formAll`), the check; the pack coordinates copied (`__loop12`); the
  return.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Squeezes with nothing waiting -/

/-- A squeeze with nothing waiting, on the capacity from `capb` (the zero cells `66 .. 69`),
outputs from `o`, the challenge at `o + 19`. -/
def sqZeroT (capb o : ℕ) : List Stmt :=
  [keccakA ([.n 66, .n 66, .n 66, .n 66, .n 66, .n 67, .n 68, .n 69] ++ cap5 capb)
    ((List.range 13).map fun k ↦ .n (o + k))] ++ challengeT (.n o) (.n (o + 1)) (o + 13)

/-! ## Copies and dot products -/

/-- `dst[dOff + i] = src[sOff + i]` through the values `b + i`, `i < n`. -/
def copyWordsT (src dst : V) (sOff dOff b n : ℕ) : List Stmt :=
  ((List.range n).map fun i ↦ [.atom (.load (.n (b + i)) src (sOff + i)),
    .atom (.load (.n (b + i)) dst (dOff + i))]).flatten

/-- `Σ_k x_k·p[off + k]` from `b`: per `k` a load, a product, an addition after the first. -/
def dotLoadsT (xs : List ℕ) (p : V) (off b : ℕ) : List Stmt :=
  ((List.range xs.length).map fun k ↦
    if k = 0 then [.atom (.load (.n b) p off), .atom (.mul (.n (b + 1)) (.n (xs.getD 0 0)) (.n b))]
    else [.atom (.load (.n (b + 3 * k - 1)) p (off + k)),
      .atom (.mul (.n (b + 3 * k)) (.n (xs.getD k 0)) (.n (b + 3 * k - 1))),
      .atom (.add (.n (b + 3 * k + 1)) (.n (if k = 1 then b + 1 else b + 3 * k - 2))
        (.n (b + 3 * k)))]).flatten

/-- The value of `dotLoadsT` over `n ≥ 1` terms. -/
def dotLoadsV (b n : ℕ) : ℕ := if n = 1 then b + 1 else b + 3 * (n - 1) + 1

/-- `Σ_k p[o_k.1]·q[o_k.2]`, both loaded, from `b`. -/
def pairsDotT (p q : V) (offs : List (ℕ × ℕ)) (b : ℕ) : List Stmt :=
  ((List.range offs.length).map fun k ↦
    if k = 0 then [.atom (.load (.n b) p (offs.getD 0 (0, 0)).1),
      .atom (.load (.n (b + 1)) q (offs.getD 0 (0, 0)).2),
      .atom (.mul (.n (b + 2)) (.n b) (.n (b + 1)))]
    else [.atom (.load (.n (b + 4 * k - 1)) p (offs.getD k (0, 0)).1),
      .atom (.load (.n (b + 4 * k)) q (offs.getD k (0, 0)).2),
      .atom (.mul (.n (b + 4 * k + 1)) (.n (b + 4 * k - 1)) (.n (b + 4 * k))),
      .atom (.add (.n (b + 4 * k + 2)) (.n (if k = 1 then b + 2 else b + 4 * k - 2))
        (.n (b + 4 * k + 1)))]).flatten

/-- The value of `pairsDotT` over `n ≥ 2` terms. -/
def pairsDotV (b n : ℕ) : ℕ := b + 4 * (n - 1) + 2

/-- Consecutive offsets. -/
def consecOffs (pOff qOff n : ℕ) : List (ℕ × ℕ) := (List.range n).map fun k ↦ (pOff + k, qOff + k)

/-- A chain of additions over the values `vs` from `b` (none for one value). -/
def addChainT (vs : List ℕ) (b : ℕ) : List Stmt :=
  ((List.range (vs.length - 1)).map fun k ↦
    .atom (.add (.n (b + k)) (.n (if k = 0 then vs.getD 0 0 else b + k - 1)) (.n (vs.getD (k + 1) 0))))

/-- The value of `addChainT`. -/
def addChainV (vs : List ℕ) (b : ℕ) : ℕ := if vs.length ≤ 1 then vs.getD 0 0 else b + vs.length - 2

/-! ## A step's `ι` term -/

/-- The bits `i` whose positions `2^i - 1` of the round constant segment `m` of step `s` uses. -/
def iotaIdx (s m : ℕ) : List ℕ :=
  (List.range 7).filter fun i ↦ (keccakRC.getD (12 * (m + 1) - s - 1) 0).toNat.testBit (2 ^ i - 1)

/-- The bits either segment uses. -/
def iotaUsed (s : ℕ) : List ℕ :=
  (List.range 7).filter fun i ↦ i ∈ iotaIdx s 0 || i ∈ iotaIdx s 1

/-- The lane and slice offsets of a later claim's weight at position `2^i - 1` of lane 0: `θ`'s
transpose through `ρ`, `π`. -/
def flipOffs (i : ℕ) : List (ℕ × ℕ) :=
  (keccakPi 0, (2 ^ i - 1 + keccakRho.getD 0 0) % 64) ::
    (List.range 5).flatMap fun y ↦
      [(keccakPi (1 + 5 * y), (2 ^ i - 1 + keccakRho.getD (1 + 5 * y) 0) % 64),
        (keccakPi (4 + 5 * y), (2 ^ i + keccakRho.getD (4 + 5 * y) 0) % 64)]

/-- The size of a flip's block. -/
def flipSz (s : ℕ) : ℕ := if s = 0 then 3 else 46

/-- Flip `i` of step `s` from `b`: the first claim's word bit, a later claim's transpose. -/
def flipT (s i b : ℕ) : List Stmt :=
  if s = 0 then
    [.atom (.load (.n b) (.n 274) 30), .atom (.const (.n (b + 1)) (word (2 ^ (2 ^ i - 1)) 0 0)),
      .atom (.mul (.n (b + 2)) (.n b) (.n (b + 1)))]
  else
    [.atom (.load (.n b) (.n 201) (22 * s + 3)), .atom (.load (.n (b + 1)) (.n 201) (22 * s + 5))] ++
      pairsDotT (.n b) (.n (b + 1)) (flipOffs i) (b + 2) ++
      [.atom (.copy (.n (b + 45)) (.n (pairsDotV (b + 2) 11)))]

/-- The value of flip `j` (in the used order) from `b`. -/
def flipV (s b j : ℕ) : ℕ := b + flipSz s * j + flipSz s - 1

/-- The flips of step `s` from `b`. -/
def flipsT (s b : ℕ) : List Stmt :=
  ((List.range (iotaUsed s).length).map fun j ↦ flipT s ((iotaUsed s).getD j 0) (b + flipSz s * j)).flatten

/-- The value of flip `i`. -/
def flipOf (s b i : ℕ) : ℕ := flipV s b ((iotaUsed s).idxOf i)

/-- The `ι` term from `c`, the segment weights at `st`: per segment the flips summed, times its
weight, the two added. -/
def iotaSegT (s b c st : ℕ) : List Stmt :=
  let v0 := (iotaIdx s 0).map (flipOf s b)
  let v1 := (iotaIdx s 1).map (flipOf s b)
  let c1 := c + (v0.length - 1) + 2
  addChainT v0 c ++
    [.atom (.load (.n (c + (v0.length - 1))) (.n st) 0),
      .atom (.mul (.n (c + (v0.length - 1) + 1)) (.n (c + (v0.length - 1))) (.n (addChainV v0 c)))] ++
    addChainT v1 c1 ++
    [.atom (.load (.n (c1 + (v1.length - 1))) (.n st) 1),
      .atom (.mul (.n (c1 + (v1.length - 1) + 1)) (.n (c1 + (v1.length - 1))) (.n (addChainV v1 c1))),
      .atom (.add (.n (c1 + (v1.length - 1) + 2)) (.n (c + (v0.length - 1) + 1))
        (.n (c1 + (v1.length - 1) + 1)))]

/-- The value after `iotaSegT`, and the `ι` term's value. -/
def iotaSegEnd (s c : ℕ) : ℕ :=
  c + ((iotaIdx s 0).length - 1) + 2 + ((iotaIdx s 1).length - 1) + 3

/-- The words of `g^(22·s)`, as the data writes them (`claims·g^(22 s)`). -/
def vkGw : ℕ → ℕ
  | 1 => 4194304
  | 2 => 17592186044416
  | 3 => 108
  | 4 => 452984832
  | 5 => 1899956092796928
  | 6 => 5200
  | 7 => 21810380800
  | 8 => 91479367430963200
  | 9 => 486848
  | 10 => 2041988513792
  | 11 => 8564720591351840768
  | _ => 0

/-- The call of step `s` from `b`: the next claim's pointer, `keccak_layer` by `odd_g` on the
capacity `cap`, the waiting cells (step `0`), the cursor `cur` and the `ι` term `io`. -/
def stepTailT (s b : ℕ) (cap : List ℕ) (cur io : ℕ) (gw : ℕ → ℕ) : List Stmt :=
  if s = 0 then
    [.atom (.const (.n b) (word 2 0 0)), .atom (.mul (.n (b + 1)) (.n 5) (.n b)),
      .atom (.const (.n (b + 2)) (word 2 0 0)), .atom (.mul (.n (b + 3)) (.n 17) (.n (b + 2))),
      .atom (.const (.n (b + 4)) (word (gw 1) 0 0)), .atom (.mul (.n (b + 5)) (.n 201) (.n (b + 4))),
      .dispatch (.n 47) ["keccak_layer__L1_L0", "keccak_layer__L1_L1"]
        (cap.map .n ++ [.n 198, .n 200, .n (b + 1), .n (b + 3), .n 43, .n 48, .n 201, .n (b + 5),
          .n io]) ((List.range 6).map fun j ↦ .n (b + 6 + j))]
  else
    [.atom (.const (.n b) (word 0 0 0)), .atom (.const (.n (b + 1)) (word 0 0 0)),
      .atom (.const (.n (b + 2)) (word 2 0 0)), .atom (.mul (.n (b + 3)) (.n 17) (.n (b + 2))),
      .atom (.const (.n (b + 4)) (word (gw s) 0 0)), .atom (.mul (.n (b + 5)) (.n 201) (.n (b + 4))),
      .atom (.const (.n (b + 6)) (word (gw s) 0 0)), .atom (.mul (.n (b + 7)) (.n 201) (.n (b + 6))),
      .atom (.const (.n (b + 8)) (word (gw 1) 0 0)),
      .atom (.mul (.n (b + 9)) (.n (b + 7)) (.n (b + 8))),
      .dispatch (.n 47) ["keccak_layer__L0_L0", "keccak_layer__L0_L1"]
        (cap.map .n ++ [.n b, .n (b + 1), .n cur, .n (b + 3), .n 43, .n 48, .n (b + 5), .n (b + 9),
          .n io]) ((List.range 6).map fun j ↦ .n (b + 10 + j))]

/-- The size of `stepTailT`'s values. -/
def stepTailSz (s : ℕ) : ℕ := if s = 0 then 12 else 16

/-- **Step `s`** from `b`: the claim's point, its segment weights, the flips, the `ι` term, the
call. -/
def stepT (s b : ℕ) (cap : List ℕ) (cur : ℕ) (gw : ℕ → ℕ) : List Stmt :=
  let f0 := b + 6
  let c := f0 + flipSz s * (iotaUsed s).length
  [.atom (.load (.n b) (.n 201) (22 * s + 2)), .atom (.hint (.alloc (.n (b + 1)) 2)),
    .atom (.mul (.n (b + 2)) (.n b) (.n 17))] ++
  eqtreeT (.n (b + 2)) (.n (b + 1)) 0 (b + 3) 1 ++ flipsT s f0 ++ iotaSegT s f0 c (b + 1) ++
  stepTailT s (iotaSegEnd s c) cap cur (iotaSegEnd s c - 1) gw

/-- The value after step `s`. -/
def stepEnd (s b : ℕ) : ℕ :=
  iotaSegEnd s (b + 6 + flipSz s * (iotaUsed s).length) + stepTailSz s
/-! ## The head -/

/-- `pack_g`, `y_g`, the bits of `y`, `half_g`, `odd_g`, `y_last` and their check. -/
def vkBitsT : List Stmt :=
  [.atom (.const (.n 16) (word 8070450532247928836 0 0)), .atom (.mul (.n 17) (.n 6) (.n 16)),
    .atom (.const (.n 18) (word 2 0 0)), .atom (.mul (.n 19) (.n 17) (.n 18)),
    .atom (.hint (.bitsExp (.n 19) 5 (.stack [.n 20, .n 21, .n 22, .n 23, .n 24]))),
    .atom (.mul (.n 20) (.n 20) (.n 20)), .atom (.mul (.n 21) (.n 21) (.n 21)),
    .atom (.const (.n 25) (word 1 0 0)), .atom (.const (.n 26) (word 3 0 0)),
    .atom (.mul (.n 27) (.n 21) (.n 26)), .atom (.add (.n 28) (.n 25) (.n 27)),
    .atom (.mul (.n 22) (.n 22) (.n 22)), .atom (.const (.n 29) (word 1 0 0)),
    .atom (.const (.n 30) (word 5 0 0)), .atom (.mul (.n 31) (.n 22) (.n 30)),
    .atom (.add (.n 32) (.n 29) (.n 31)), .atom (.mul (.n 33) (.n 28) (.n 32)),
    .atom (.mul (.n 23) (.n 23) (.n 23)), .atom (.const (.n 34) (word 1 0 0)),
    .atom (.const (.n 35) (word 17 0 0)), .atom (.mul (.n 36) (.n 23) (.n 35)),
    .atom (.add (.n 37) (.n 34) (.n 36)), .atom (.mul (.n 38) (.n 33) (.n 37)),
    .atom (.mul (.n 24) (.n 24) (.n 24)), .atom (.const (.n 39) (word 1 0 0)),
    .atom (.const (.n 40) (word 257 0 0)), .atom (.mul (.n 41) (.n 24) (.n 40)),
    .atom (.add (.n 42) (.n 39) (.n 41)), .atom (.mul (.n 43) (.n 38) (.n 42)),
    .atom (.const (.n 44) (word 1 0 0)), .atom (.const (.n 45) (word 3 0 0)),
    .atom (.mul (.n 46) (.n 20) (.n 45)), .atom (.add (.n 47) (.n 44) (.n 46)),
    .atom (.mul (.n 48) (.n 43) (.n 47)), .atom (.mul (.n 49) (.n 43) (.n 48)),
    .atom (.const (.n 50) (word 2 0 0)), .atom (.mul (.n 51) (.n 17) (.n 50)),
    .atom (.assertEq (.n 49) (.n 51))]

/-- The point's allocation and the copy of its pack coordinates (`__loop10`). -/
def vkPointT : List Stmt :=
  [.atom (.const (.n 56) (word 2 0 0)), .atom (.mul (.n 57) (.n 17) (.n 56)),
    .atom (.hint (.allocDyn (.n 58) (.n 57))), .atom (.const (.n 59) (word 1 0 0)),
    .atom (.add (.n 60) (.n 59) (.n 17)), .atom (.const (.n 61) (word 1 0 0)),
    .atom (.const (.n 62) (word 16 0 0)), .atom (.mul (.n 63) (.n 7) (.n 62)),
    .callIf (.n 60) "__loop10" [.n 61, .n 17, .n 58, .n 63],
    .atom (.mul (.n 64) (.n 58) (.n 17)), .atom (.const (.n 65) (word 1 0 0)),
    .atom (.const (.n 66) (word 0 0 0)), .atom (.const (.n 67) (word 0 0 0)),
    .atom (.const (.n 68) (word 0 0 0)), .atom (.const (.n 69) (word 0 0 0))]

/-- The segment and the five lane coordinates squeezed. -/
def vkSqueezesT : List Stmt :=
  sqZeroT 11 70 ++ [.atom (.load (.n 89) (.n 64) 0), .atom (.hint (.alloc (.n 90) 5))] ++
    ((List.range 5).map fun i ↦
      sqZeroT (if i = 0 then 78 else 79 + 20 * i) (91 + 20 * i) ++ [.atom (.load (.n (110 + 20 * i)) (.n 90) i)]).flatten

/-- **The head.** -/
def vkHeadT : List Stmt :=
  (List.range 5).map (fun i ↦ .atom (.copy (.n (11 + i)) (.n i))) ++ vkBitsT ++
    copyWordsT (.n 7) (.n 9) 0 0 52 4 ++ vkPointT ++ vkSqueezesT ++ fsNextT (.n 5) 0 191

/-- **The first claim's record.** -/
def vkFirstT : List Stmt :=
  [.atom (.hint (.alloc (.n 201) 286)), .atom (.const (.n 202) (word 1 0 0)),
    .atom (.load (.n 202) (.n 201) 1), .atom (.load (.n 58) (.n 201) 2),
    .atom (.hint (.alloc (.n 203) 30))] ++
  eqtreeT (.n 9) (.n 203) 0 204 4 ++ copyWordsT (.n 203) (.n 201) 14 6 258 16 ++
  [.atom (.hint (.alloc (.n 274) 62))] ++ eqtreeT (.n 90) (.n 274) 0 275 5 ++
  [.atom (.const (.n 380) (word 1073741824 0 0)), .atom (.mul (.n 381) (.n 274) (.n 380)),
    .atom (.load (.n 381) (.n 201) 3), .atom (.hint (.alloc (.n 382) 2))] ++
  eqtreeT (.n 64) (.n 382) 0 383 1 ++ pairsDotT (.n 274) (.n 8) (consecOffs 30 0 25) 386 ++
  [.atom (.load (.n 485) (.n 382) 1), .atom (.mul (.n 486) (.n 485) (.n 484)),
    .atom (.add (.n 487) (.n 191) (.n 486)), .atom (.load (.n 487) (.n 201) 0)]

/-! ## The openings -/

/-- An opening's lane weights at the slot point `slot` and segment point `segp` from `b`: the
slot's equality weights (`eqfT`, the first 50), the segment's, and per lane the segments'
`first .. first + count` weighted (`keccak_slot_lanes`, G:2750-2763). -/
def slotLanesT (slot segp b first count : ℕ) : List Stmt :=
  eqfT (.n slot) 0 6 50 b ++ eqfLevel0T (.n segp) 0 (b + 129) ++
  ((List.range 25).map fun lane ↦
    if count = 1 then
      [.atom (.mul (.n (b + 133 + 2 * lane)) (.n (b + 131))
          (.n (eqfVal b 6 50 5 (25 * first + lane)))),
        .atom (.copy (.n (b + 134 + 2 * lane)) (.n (b + 133 + 2 * lane)))]
    else
      [.atom (.mul (.n (b + 133 + 4 * lane)) (.n (b + 131)) (.n (eqfVal b 6 50 5 (25 * first + lane)))),
        .atom (.mul (.n (b + 134 + 4 * lane)) (.n (b + 132))
          (.n (eqfVal b 6 50 5 (25 * (first + 1) + lane)))),
        .atom (.add (.n (b + 135 + 4 * lane)) (.n (b + 133 + 4 * lane)) (.n (b + 134 + 4 * lane))),
        .atom (.copy (.n (b + 136 + 4 * lane)) (.n (b + 135 + 4 * lane)))]).flatten

/-- Lane `lane`'s weight in `slotLanesT`. -/
def slotLaneV (b count lane : ℕ) : ℕ :=
  if count = 1 then b + 134 + 2 * lane else b + 136 + 4 * lane

/-- The value after `slotLanesT`. -/
def slotLanesEnd (b count : ℕ) : ℕ := if count = 1 then b + 183 else b + 233

/-- Read `z` of the slices from `b`. -/
def slB (b z : ℕ) : ℕ := b + 10 * z + 13 * (z / 4)

/-- The permutation before group `g` of four slices. -/
def slP (b g : ℕ) : ℕ := b + 40 * g + 13 * (g - 1)

/-- The capacity before group `g`. -/
def slCap (capb b g : ℕ) : ℕ := if g = 0 then capb else slP b g + 8

/-- The cells of group `g`'s four reads. -/
def slCells (b g : ℕ) : List V :=
  ((List.range 4).map fun j ↦ [V.n (slB b (4 * g + j) + 7), .n (slB b (4 * g + j) + 9)]).flatten

/-- **The 64 slices** (G:2917-2924): read at the cursor and stored, four to a permutation, then the
ring map's first challenge squeezed (at `b + 854`). -/
def slicesT (cur : V) (capb b : ℕ) : List Stmt :=
  ((List.range 16).map fun g ↦
    (if g = 0 then [] else
      [keccakA (slCells b (g - 1) ++ cap5 (slCap capb b (g - 1)))
        ((List.range 13).map fun k ↦ .n (slP b g + k))]) ++
    ((List.range 4).map fun j ↦
      fsNextT cur (4 * g + j) (slB b (4 * g + j)) ++
        [.atom (.load (.n (slB b (4 * g + j))) (.n 10) (4 * g + j))]).flatten).flatten ++
  [keccakA (slCells b 15 ++ cap5 (slCap capb b 15)) ((List.range 13).map fun k ↦ .n (b + 835 + k))] ++
  challengeT (.n (b + 835)) (.n (b + 836)) (b + 848)

/-! ## The shifts of the slices -/

/-- The values of level `t` (`level t j`), from the slices `src` at level `0`. -/
def foldVal (src : ℕ → ℕ) (b : ℕ) : ℕ → ℕ → ℕ
  | 0, j => src j
  | t + 1, j =>
    let n := 2 ^ (6 - t)
    b + 193 * t + 1 + 3 * (foldPos' t (j / (n / 2)) * (n / 2) + j % (n / 2)) + 2
where
  /-- A node's position in the order the guest folds them: `(p, b)` with `q = p + 2^t·b`. -/
  foldPos' (t q : ℕ) : ℕ := ((List.range (2 ^ (t + 1))).filter fun q' ↦
    t + 1 < 6 || shiftUsed.contains (q' / 2 + 2 ^ t * (q' % 2))).idxOf (q % 2 ^ t * 2 + q / 2 ^ t)

/-- **`fold_shifts`, level `t`** (G:2388-2416) from `B`, the coordinate at `a·g^t`. -/
def foldLevelT (src : ℕ → ℕ) (b : ℕ) (a : V) (t : ℕ) : List Stmt :=
  let n := 2 ^ (6 - t)
  let B := b + 193 * t
  .atom (.load (.n B) a t) ::
  ((List.range (2 ^ (t + 1))).filter (fun q' ↦
      t + 1 < 6 || shiftUsed.contains (q' / 2 + 2 ^ t * (q' % 2)))).zipIdx.flatMap fun (q', c) ↦
    let p := q' / 2
    let bb := q' % 2
    (List.range (n / 2)).flatMap fun k ↦
      let x0 := foldVal src b t (p * n + (2 * k + (n - 1) * bb) % n)
      let x1 := foldVal src b t (p * n + (2 * k + 1 + (n - 1) * bb) % n)
      let d := B + 1 + 3 * (c * (n / 2) + k)
      [.atom (.add (.n d) (.n x0) (.n x1)), .atom (.mul (.n (d + 1)) (.n B) (.n d)),
        .atom (.add (.n (d + 2)) (.n x0) (.n (d + 1)))]

/-- **`fold_shifts`** over the six levels. -/
def foldT (src : ℕ → ℕ) (b : ℕ) (a : V) : List Stmt :=
  ((List.range 6).map (foldLevelT src b a)).flatten

/-! ## The template -/

/-- The twelve steps. -/
def vkStepsT : List Stmt :=
  stepT 0 488 [179, 180, 181, 182, 183] 0 vkGw ++
  stepT 1 531 [525, 526, 527, 528, 529] 530 vkGw ++
  stepT 2 746 [740, 741, 742, 743, 744] 745 vkGw ++
  stepT 3 960 [954, 955, 956, 957, 958] 959 vkGw ++
  stepT 4 1315 [1309, 1310, 1311, 1312, 1313] 1314 vkGw ++
  stepT 5 1624 [1618, 1619, 1620, 1621, 1622] 1623 vkGw ++
  stepT 6 1979 [1973, 1974, 1975, 1976, 1977] 1978 vkGw ++
  stepT 7 2192 [2186, 2187, 2188, 2189, 2190] 2191 vkGw ++
  stepT 8 2501 [2495, 2496, 2497, 2498, 2499] 2500 vkGw ++
  stepT 9 2763 [2757, 2758, 2759, 2760, 2761] 2762 vkGw ++
  stepT 10 3074 [3068, 3069, 3070, 3071, 3072] 3073 vkGw ++
  stepT 11 3383 [3377, 3378, 3379, 3380, 3381] 3382 vkGw

/-- The committed outputs' opening (G:2858-2871). -/
def vkOutT : List Stmt :=
  [.atom (.mul (.n 3691) (.n 9) (.n 6)), .atom (.const (.n 3692) (word 0 0 0)),
    .atom (.const (.n 3693) (word 0 0 0)),
    .call "keccak_plain_rounds__L6_L0" [.n 3685, .n 3686, .n 3687, .n 3688, .n 3689, .n 3692,
      .n 3693, .n 3690, .n 191, .n 3691] ((List.range 7).map fun j ↦ .n (3694 + j))] ++
  fsNextT (.n 3699) 0 3701 ++ [.atom (.mul (.n 3711) (.n 58) (.n 17))] ++
  slotLanesT 3691 3711 3712 1 1 ++ dotLoadsT ((List.range 25).map (slotLaneV 3712 1)) (.n 274) 30 3895 ++
  [.atom (.mul (.n 3969) (.n 3968) (.n 3701)), .atom (.assertEq (.n 3969) (.n 3700)),
    .atom (.const (.n 3970) (word 1 0 0)), .atom (.add (.n 3971) (.n 3970) (.n 17)),
    .atom (.const (.n 3972) (word 1 0 0)), .atom (.const (.n 3973) (word 16 0 0)),
    .atom (.mul (.n 3974) (.n 9) (.n 3973)),
    .callIf (.n 3971) "__loop11" [.n 3972, .n 17, .n 3974, .n 58]]

/-- The inputs' opening up to the slices and the ring map's first challenge (G:2873-2925). -/
def vkInT : List Stmt :=
  [.atom (.const (.n 3975) (word 2 0 0)), .atom (.mul (.n 3976) (.n 3699) (.n 3975)),
    .atom (.load (.n 3977) (.n 201) 264), .atom (.const (.n 3978) (word 549755813888 0 0)),
    .atom (.mul (.n 3979) (.n 9) (.n 3978)),
    .call "keccak_plain_rounds__L4_L1" [.n 3694, .n 3695, .n 3696, .n 3697, .n 3698, .n 3708,
      .n 3710, .n 3976, .n 3977, .n 3979] ((List.range 7).map fun j ↦ .n (3980 + j)),
    .atom (.hint (.alloc (.n 3987) 30))] ++
  eqtreeT (.n 9) (.n 3987) 39 3988 4 ++ pairsDotT (.n 3987) (.n 201) (consecOffs 14 270 16) 4042 ++
  [.atom (.const (.n 4105) (word 549755813888 0 0)), .atom (.mul (.n 4106) (.n 9) (.n 4105)),
    .atom (.mul (.n 4107) (.n 4106) (.n 6)), .atom (.const (.n 4108) (word 0 0 0)),
    .atom (.const (.n 4109) (word 0 0 0)),
    .call "keccak_plain_rounds__L6_L0" [.n 3980, .n 3981, .n 3982, .n 3983, .n 3984, .n 4108,
      .n 4109, .n 3985, .n 3986, .n 4107] ((List.range 7).map fun j ↦ .n (4110 + j))] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (4117 + j)) (.n (4110 + j)))) ++
  slicesT (.n 4115) 4117 4122

/-- The shifts of the slices' values. -/
def vkSh (r : ℕ) : ℕ := foldVal (fun j ↦ 5213 + j) 5277 6 r

/-- The inputs' check, the copy of their pack coordinates, the return (G:2926-2938). -/
def vkFinT : List Stmt :=
  [.atom (.load (.n 4977) (.n 201) 266), .atom (.mul (.n 4978) (.n 4977) (.n 17))] ++
  slotLanesT 4107 4978 4979 0 2 ++ [.atom (.load (.n 5212) (.n 201) 268)] ++
  (List.range 64).map (fun z ↦ .atom (.load (.n (5213 + z)) (.n 10) z)) ++
  foldT (fun j ↦ 5213 + j) 5277 (.n 5212) ++ [.atom (.load (.n 6363) (.n 201) 267)] ++
  (formAll (.n 6363) vkSh (slotLaneV 4979 2) 6364).1 ++
  [.atom (.mul (.n 6578) (.n 4104) (.n (formAll (.n 6363) vkSh (slotLaneV 4979 2) 6364).2.2)),
    .atom (.assertEq (.n 6578) (.n 4116)), .atom (.const (.n 6579) (word 1 0 0)),
    .atom (.add (.n 6580) (.n 6579) (.n 17)), .atom (.const (.n 6581) (word 1 0 0)),
    .atom (.const (.n 6582) (word 8796093022208 0 0)), .atom (.mul (.n 6583) (.n 9) (.n 6582)),
    .callIf (.n 6580) "__loop12" [.n 6581, .n 17, .n 6583, .n 4977]] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (6584 + j)) (.n (4965 + j)))) ++
  [.atom (.const (.n 6589) (word 27 0 0)), .atom (.mul (.n 6590) (.n 4115) (.n 6589)),
    .atom (.copy (.n 6591) (.n 6590)), .atom (.copy (.n 6592) (.n 3701)),
    .atom (.copy (.n 6593) (.n 4976)),
    .ret [.n 6584, .n 6585, .n 6586, .n 6587, .n 6588, .n 6591, .n 6592, .n 6593]]

/-- **`verify_keccak`'s body.** -/
def vkT : List Stmt := vkHeadT ++ vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinT

end
end LeanVM.Guest.B1.VerifySub
