/-
  LeanVM.Guest.B1.Sig.SphincsDigestT

  The message digest of `verify_sig_lean_sphincs` as a template: the statements from the claim's
  loads to the digest's check (`lean_ethereum.py:3769-3841, 3972-4046` at leanVM 834e6614), with the
  values numbered as the renumbered expansion numbers them.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsT

/-!
# The message digest as a template

`verify_sig_lean_sphincs(signer, byte_bits)` (`G:3972-4074`; `G` is `lean_ethereum.py`): `signer` is
the parameter `n0`, `byte_bits` `n1`; `PK.seed` is `n2` (`sPP`, `signer[1]`, offset `0`), `PK.root`
`n3` (`sRoot`, offset `1`). Its first statements, up to the digest's check, are `sDigestBlock`:

* `sMsg` (`G:3976-3998`): the message `M`'s 32 bytes hinted in the exponent (`n4 … n35`), each lane
  `j` rebuilt as its three low bytes (`sLo j`) and five high ones (`sHi j`) by `sp_from_bytes`
  (`sFromBytes`, `G:3769-3779`), the lanes checked to be the claim's two message cells (offsets `2`,
  `3`), and the cells `M'` puts `M` in after its 13 framing bytes (`sM0`, `sM1`, `sM2`);
* `sDigests` (`G:3999-4003`): `R` hinted (`sRand`), `H_msg`'s two calls `H(R | PK.seed | PK.root | M' |
  BE_32(i))`, 97 bytes, one block each, the first setting the padding run (`n353 …`, `sPad`); their
  outputs from `sHm0` (`n358`) and `sHm1` (`n379`);
* `sBitsHint`, `sBooleans` (`G:4010-4020`): the first call's two cells' bits hinted (`n392 …`, `n520 …`)
  and the second's low sixteen (`n648 …`), each pinned Boolean;
* `sForsFields` (`sp_fors_field`, `G:3793-3800`, through `sp_md_bit`, `G:3783-3789`): each FORS leaf
  read most significant bit first from the digest's bytes and its right shifts, `vals[10 c + z]` at
  `sFVal c z`;
* `sLeafShifts` (`sp_leaf_shifts`, `G:3835-3841`, through `sp_leaf_bit`, `G:3821-3831`): the three
  layers' leaves and their right shifts, `lvals[i]` at `sLVal i`;
* `sMdBytes` (`sp_md_byte`, `G:3804-3817`): the digest's first 30 bytes rebuilt where the first call's
  cells hold them, `md0`, `md1`;
* `sCheck` (`G:4036-4046`): the tree index's middle byte (`sTreeMid`), its high byte's six unused bits,
  the first call's cells asserted to be the rebuilt ones, the second call's unused bytes read
  (`sp_unused`) and its high lane checked into `K`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## Values and constants -/

/-- `PK.seed`, `signer[1]` (offset `0`). -/
def sPP : V := .n 2
/-- `PK.root`, `signer[GEN]` (offset `1`). -/
def sRoot : V := .n 3
/-- The padding run of `verify_sig_lean_sphincs`, set by `H_msg`'s first call. -/
def sPad : Nat := 353
/-- `R`, the randomizer. -/
def sRand : V := .n 347
/-- The first call's output run and its two digest cells. -/
def sHm0 : V := .n 358
def sHm0b : V := .n 359
/-- The second call's output run and its first cell. -/
def sHm1 : V := .n 379

/-- `g^255`, as the compiler writes it: the bound of a byte's range check. -/
def g255W : E := word 9223372036854810629 0 0

/-- The word `2^s`, `s < 128`: in the low limb or the `y` limb. -/
def pw (s : Nat) : E := if s < 64 then word (2 ^ s) 0 0 else word 0 (2 ^ (s - 64)) 0

/-- `M'`'s framing as its cell holds it: `0x00 | 11 | "leanSPHINCS"`, 13 bytes (`SP_FRAMING`). -/
def spFraming : E := word 5788091310693681920 357611489608 0

/-! ## `sp_from_bytes` -/

/-- One byte from base `b`: its range check below `256`, the table's address and value at `b + 5`. -/
def sByte (mark : V) (b : Nat) : List Stmt :=
  rangeS mark g255W b ++ [mulS (.n (b + 4)) (.n 1) mark, loadS (.n (b + 5)) (.n (b + 4)) 0]

/-- The bytes after the top one, folding `val`. -/
def sFromBytesRest : List V → Nat → V → List Stmt × Nat × V
  | [], b, val => ([], b, val)
  | m :: ms, b, val =>
      let rest := sFromBytesRest ms (b + 9) (.n (b + 8))
      (sByte m b ++ [cst (b + 6) (word 256 0 0), mulS (.n (b + 7)) val (.n (b + 6)),
        addS (.n (b + 8)) (.n (b + 5)) (.n (b + 7))] ++ rest.1, rest.2.1, rest.2.2)

/-- `sp_from_bytes` of the marks `top :: rest` (high byte first) from base `b`: the statements, the
next base and the value. -/
def sFromBytes (top : V) (rest : List V) (b : Nat) : List Stmt × Nat × V :=
  let r := sFromBytesRest rest (b + 6) (.n (b + 5))
  (sByte top b ++ r.1, r.2.1, r.2.2)

/-- The marks of an `n`-byte integer hinted at `b …`, low byte first: the top first. -/
def sMarks (b n : Nat) : V × List V :=
  (.n (b + n - 1), (List.range (n - 1)).reverse.map fun k => .n (b + k))

/-- `sp_from_bytes` of the `n` bytes hinted at `b …`, from base `x`. -/
def sFromMarks (b n x : Nat) : List Stmt × Nat × V := sFromBytes (sMarks b n).1 (sMarks b n).2 x

/-! ## The message -/

/-- The base of lane `j`'s statements: `sp_from_bytes` of its three low bytes and a copy, then of
its five high bytes and a copy, 68 values. -/
def sLaneBase (j : Nat) : Nat := 36 + 68 * j

/-- `lo[j]`, the lane's three low bytes. -/
def sLo (j : Nat) : V := .n (sLaneBase j + 24)
/-- `hi[j]`, the lane's five high bytes. -/
def sHi (j : Nat) : V := .n (sLaneBase j + 67)

/-- Lane `j`'s two `sp_from_bytes`, each stored. -/
def sLaneBytes (j : Nat) : List Stmt :=
  (sFromMarks (4 + 8 * j) 3 (sLaneBase j)).1 ++ [copyS (sLo j) (sFromMarks (4 + 8 * j) 3 (sLaneBase j)).2.2] ++
    (sFromMarks (7 + 8 * j) 5 (sLaneBase j + 25)).1 ++
      [copyS (sHi j) (sFromMarks (7 + 8 * j) 5 (sLaneBase j + 25)).2.2]

/-- `lane[j] = lo[j] + hi[j] · g^24`, at `n(310 + 3 j)`. -/
def sLane (j : Nat) : V := .n (310 + 3 * j)

def sLanes : List Stmt :=
  (List.range 4).flatMap fun j =>
    [cst (308 + 3 * j) (word (2 ^ 24) 0 0), mulS (.n (309 + 3 * j)) (sHi j) (.n (308 + 3 * j)),
      addS (sLane j) (sLo j) (.n (309 + 3 * j))]

/-- The message cell `signer[GEN^(2 + k)]` checked to be `lane[2k] + lane[2k + 1] · y`, from `b`. -/
def sMsgCheck (k b : Nat) : List Stmt :=
  [cst b (word 0 1 0), mulS (.n (b + 1)) (sLane (2 * k + 1)) (.n b),
    addS (.n (b + 2)) (sLane (2 * k)) (.n (b + 1)), loadS (.n (b + 3)) (.n 0) (2 + k),
    .atom (.assertEq (.n (b + 2)) (.n (b + 3)))]

/-- `M'`'s cells after its framing: `m0 = SP_FRAMING + lo[0] · 2^104` (`n331`), `m1 = hi[0] + lo[1] ·
g^40 + (hi[1] + lo[2] · g^40) · y` (`n340`), `m2 = hi[2] + lo[3] · g^40 + hi[3] · y` (`n346`). -/
def sM0 : V := .n 331
def sM1 : V := .n 340
def sM2 : V := .n 346

def sMCells : List Stmt :=
  [cst 328 spFraming, cst 329 (pw 104), mulS (.n 330) (sLo 0) (.n 329), addS sM0 (.n 328) (.n 330),
    cst 332 (pw 40), mulS (.n 333) (sLo 1) (.n 332), addS (.n 334) (sHi 0) (.n 333),
    cst 335 (pw 40), mulS (.n 336) (sLo 2) (.n 335), addS (.n 337) (sHi 1) (.n 336),
    cst 338 (word 0 1 0), mulS (.n 339) (.n 337) (.n 338), addS sM1 (.n 334) (.n 339),
    cst 341 (pw 40), mulS (.n 342) (sLo 3) (.n 341), addS (.n 343) (sHi 2) (.n 342),
    cst 344 (word 0 1 0), mulS (.n 345) (sHi 3) (.n 344), addS sM2 (.n 343) (.n 345)]

/-- The claim's keys loaded, the message hinted, its lanes rebuilt and checked, and `M'`'s cells. -/
def sMsg : List Stmt :=
  [loadS sPP (.n 0) 0, loadS sRoot (.n 0) 1, hintW "sp_msg" (runV 4 32)] ++
    ((List.range 4).flatMap sLaneBytes) ++ sLanes ++ sMsgCheck 0 320 ++ sMsgCheck 1 324 ++ sMCells

/-! ## `H_msg` -/

/-- The inputs of `H_msg`'s call whose tail run is at `t`: `R`, `PK.seed`, `PK.root`, `m0`, the tail
`[m1, m2, BE_32(i)'s last byte with the 0x01 after it, 0]`, the `0x80` at `t + 4`, the zero run. -/
def sHIns (t : Nat) : List V :=
  [sRand, sPP, sRoot, sM0, .n t, .n (t + 1), .n (t + 2), .n (t + 3), .n (t + 4),
    .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)]

/-- `R` hinted, then `H_msg`'s two calls: the first (`i = 0`) with the padding run after its
inputs, the second (`i = 1`) with its counter `1` XORed with the `0x01` byte. -/
def sDigests : List Stmt :=
  [hintW "sp_rand" [sRand], copyS (.n 348) sM1, copyS (.n 349) sM2, cst 350 (word 256 0 0),
    cst 351 (word 0 0 0), cst 352 (word (2 ^ 63) 0 0)] ++ padRun sPad ++
  [kecS (sHIns 348) (runV 358 13) false false,
    cst 371 (word 1 0 0), cst 372 (word 256 0 0), addS (.n 373) (.n 371) (.n 372),
    copyS (.n 374) sM1, copyS (.n 375) sM2, copyS (.n 376) (.n 373), cst 377 (word 0 0 0),
    cst 378 (word (2 ^ 63) 0 0), kecS (sHIns 374) (runV 379 13) false false]

/-! ## The digest's bits -/

/-- The first call's two cells' bits (`bits0`, `bits1`: one run from `n392`) and the second's low
sixteen (`bits2`, from `n648`), hinted. -/
def sBitsHint : List Stmt :=
  [.atom (.hint (.bits sHm0 0 128 (.stack (runV 392 128)))),
    .atom (.hint (.bits sHm0b 0 128 (.stack (runV 520 128)))),
    .atom (.hint (.bits sHm1 0 16 (.stack (runV 648 16))))]

/-- The bits pinned Boolean: `bits0[b]`, `bits1[b]` in turn, then `bits2`. -/
def sBooleans : List Stmt :=
  ((List.range 128).flatMap fun b => [mulS (.n (392 + b)) (.n (392 + b)) (.n (392 + b)),
    mulS (.n (520 + b)) (.n (520 + b)) (.n (520 + b))]) ++ booleans 648 16

/-- **Bit `p` of the digest read most significant first** (`sp_md_bit`): bit `7 - p % 8` of byte
`p / 8`, in the bit run of the first call's cells. -/
def sMdBit (p : Nat) : V := .n (392 + 8 * (p / 8) + 7 - p % 8)

/-- **Bit `b` of the layers' leaves, bottom first** (`sp_leaf_bit`): the bottom leaf the digest's
byte 33 (the second call's byte 1), the middle one byte 32 (its byte 0), the top one byte 31 then
the low two bits of byte 30 (the first call's). -/
def sLeafBit (b : Nat) : V :=
  if b < 16 then .n (648 + (b + 8) % 16) else if b < 24 then .n (520 + b + 104) else .n (520 + b + 88)

/-! ## Fields and their shifts -/

/-- A field of `n` bits read most significant first, bit `r` at `bit r`, and its right shifts:
the field shifted right by `n - 1 - r` at `outBase + 3 r` (`shifts`, with any bit order). -/
def shiftsG (bit : Nat → V) (n outBase : Nat) : List Stmt :=
  copyS (.n outBase) (bit 0) ::
  (List.range (n - 1)).flatMap fun r' => let r := r' + 1;
    [cst (outBase + 3 * r - 2) (word 2 0 0),
      mulS (.n (outBase + 3 * r - 1)) (.n (outBase + 3 * r - 2)) (.n (outBase + 3 * r - 3)),
      addS (.n (outBase + 3 * r)) (bit r) (.n (outBase + 3 * r - 1))]

/-- FORS tree `c`'s leaf and its shifts: `vals[10 c + z]`, the leaf shifted right by `z`. -/
def sFVal (c z : Nat) : V := .n (664 + 28 * c + 3 * (9 - z))

/-- `sp_fors_field` of every tree (`G:4021-4023`). -/
def sForsFields : List Stmt :=
  (List.range 24).flatMap fun c => shiftsG (fun r => sMdBit (10 * c + r)) 10 (664 + 28 * c)

/-- The layers' leaves: layer `l`'s first leaf bit and height. -/
def sLeafOff (l : Nat) : Nat := 8 * l
def sLeafLen (l : Nat) : Nat := if l = 2 then 10 else 8
/-- Where layer `l`'s shifts start. -/
def sLeafBase (l : Nat) : Nat := 1336 + 22 * l

/-- `lvals[i]`: the leaf of the layer of leaf bit `i` shifted right by `i - off`. -/
def sLVal (i : Nat) : V :=
  if i < 8 then .n (1336 + 3 * (7 - i)) else if i < 16 then .n (1358 + 3 * (15 - i))
  else .n (1380 + 3 * (25 - i))

/-- `sp_leaf_shifts` of the three layers (`G:4024-4027`). -/
def sLeafShifts : List Stmt :=
  (List.range 3).flatMap fun l =>
    shiftsG (fun r => sLeafBit (sLeafOff l + sLeafLen l - 1 - r)) (sLeafLen l) (sLeafBase l)

/-! ## The digest's bytes -/

/-- A byte inside FORS tree `c`'s leaf from base `b`: the leaf shifted by `z`, masked to its low byte
(`mask`) unless nothing is above it. The statements, the next base and the value. -/
def mdIn (c z b : Nat) (mask : Bool) : List Stmt × Nat × V :=
  if mask then
    ([cst b (word 256 0 0), mulS (.n (b + 1)) (sFVal c (z + 8)) (.n b),
      addS (.n (b + 2)) (sFVal c z) (.n (b + 1))], b + 3, .n (b + 2))
  else ([], b, sFVal c z)

/-- A byte placed at bit `s` of its cell: none for `s = 0`. -/
def mdScale (s : Nat) (m : List Stmt × Nat × V) : List Stmt × Nat × V :=
  if s = 0 then m
  else (m.1 ++ [cst m.2.1 (pw s), mulS (.n (m.2.1 + 1)) m.2.2 (.n m.2.1)], m.2.1 + 2, .n (m.2.1 + 1))

/-- A byte across FORS trees `c` and `c + 1` from base `b`, placed at bit `s`: `c`'s low `k1` bits
raised past `c + 1`'s high `8 - k1` ones. -/
def mdAcross (c k1 s b : Nat) : List Stmt × Nat × V :=
  let hi : List Stmt := [cst b (pw k1), mulS (.n (b + 1)) (sFVal c k1) (.n b),
    addS (.n (b + 2)) (sFVal c 0) (.n (b + 1)), cst (b + 3) (pw (s + 8 - k1)),
    mulS (.n (b + 4)) (.n (b + 2)) (.n (b + 3))]
  if s = 0 then (hi ++ [addS (.n (b + 5)) (.n (b + 4)) (sFVal (c + 1) (2 + k1))], b + 6, .n (b + 5))
  else (hi ++ [cst (b + 5) (pw s), mulS (.n (b + 6)) (sFVal (c + 1) (2 + k1)) (.n (b + 5)),
    addS (.n (b + 7)) (.n (b + 4)) (.n (b + 6))], b + 8, .n (b + 7))

/-- **`sp_md_byte(vals, i, 8 i / 10)` from base `b`**: digest byte `i < 30` placed at bit
`8 (i % 16)` of its cell, from the field its first bit is in and the next if it reaches it. The
statements, the next base and the value. -/
def sMdByte (i b : Nat) : List Stmt × Nat × V :=
  if (8 * i + 7) / 10 = 8 * i / 10 then
    mdScale (8 * (i % 16)) (mdIn (8 * i / 10) (10 * (8 * i / 10) + 2 - 8 * i) b (8 * i != 10 * (8 * i / 10)))
  else mdAcross (8 * i / 10) (10 * (8 * i / 10) + 10 - 8 * i) (8 * (i % 16)) b

/-- Bytes `i ..< i + m` added to the running sum `acc` from base `b`: the statements, the next base,
the sum. -/
def sMdSum : Nat → Nat → V → Nat → List Stmt × Nat × V
  | 0, _, acc, b => ([], b, acc)
  | m + 1, i, acc, b =>
      let x := sMdByte i b
      let rest := sMdSum m (i + 1) (.n x.2.1) (x.2.1 + 1)
      (x.1 ++ [addS (.n x.2.1) acc x.2.2] ++ rest.1, rest.2.1, rest.2.2)

/-- `md0`: bytes `0 ..< 16`, from `n1408`. -/
def sMd0 : List Stmt × Nat × V := sMdSum 15 1 (sMdByte 0 1408).2.2 (sMdByte 0 1408).2.1

/-- `md1`: bytes `16 ..< 30`. -/
def sMd1 : List Stmt × Nat × V :=
  let x := sMdByte 16 sMd0.2.1
  let r := sMdSum 13 17 x.2.2 x.2.1
  (x.1 ++ r.1, r.2.1, r.2.2)

/-- The digest's first 30 bytes (`G:4028-4035`). -/
def sMdBytes : List Stmt := (sMdByte 0 1408).1 ++ sMd0.1 ++ sMd1.1

/-! ## The check -/

/-- The tree index's middle byte, the top leaf's low byte (`G:4036`). -/
def sTreeMid : V := .n 1620

/-- The six unused bits of the tree index's high byte, most significant first (`G:4037-4039`). -/
def sPadBits : List Stmt :=
  (List.range 5).flatMap fun b => let x := 1621 + 3 * b;
    [cst x (word 2 0 0), mulS (.n (x + 1)) (.n (if b = 0 then 639 else x - 1)) (.n x),
      addS (.n (x + 2)) (.n (638 - b)) (.n (x + 1))]

/-- The second call's unused bytes, `sp_unused`, read from `n1650`. -/
def sUnused : List Stmt × Nat × V := sFromMarks 1644 6 1650

/-- The check (`G:4036-4046`): the tree's middle byte, the high byte's unused bits, `d0[0] = md0`,
`d0[1] = md1 + (lvals[24] + pad · g^2) · 2^112 + tree_mid · 2^120`, the unused bytes, and
`(d1[0] + lvals[8] + lvals[0] · g^8 + unused · g^16) · y⁻¹` in `K`. -/
def sCheck : List Stmt :=
  [cst 1618 (word 256 0 0), mulS (.n 1619) (sLVal 24) (.n 1618), addS sTreeMid (sLVal 16) (.n 1619)] ++
    sPadBits ++
  [copyS sHm0 sMd0.2.2, cst 1636 (word 4 0 0), mulS (.n 1637) (.n 1635) (.n 1636),
    addS (.n 1638) (sLVal 24) (.n 1637), cst 1639 (pw 112), mulS (.n 1640) (.n 1638) (.n 1639),
    addS (.n 1641) sMd1.2.2 (.n 1640), cst 1642 (pw 120), mulS (.n 1643) sTreeMid (.n 1642),
    addS sHm0b (.n 1641) (.n 1643), hintW "sp_unused" (runV 1644 6)] ++ sUnused.1 ++
  [addS (.n 1701) sHm1 (sLVal 8), cst 1702 (word 256 0 0), mulS (.n 1703) (sLVal 0) (.n 1702),
    addS (.n 1704) (.n 1701) (.n 1703), cst 1705 (word 65536 0 0),
    mulS (.n 1706) sUnused.2.2 (.n 1705), addS (.n 1707) (.n 1704) (.n 1706),
    cst 1708 (word 1 0 1), mulS (.n 1709) (.n 1707) (.n 1708),
    .atom (.assertInK (.n 1709) sUnused.2.2)]

/-- **The message digest's block**: `verify_sig_lean_sphincs`'s statements up to the digest's
check; the next value is `n1710`. -/
def sDigestBlock : List Stmt :=
  sMsg ++ sDigests ++ sBitsHint ++ sBooleans ++ sForsFields ++ sLeafShifts ++ sMdBytes ++ sCheck

end
end LeanVM.Guest.B1.Sig
