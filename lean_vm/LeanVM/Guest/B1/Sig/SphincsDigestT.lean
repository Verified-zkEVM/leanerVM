/-
  LeanVM.Guest.B1.Sig.SphincsDigestT

  The message digest of `verify_sig_lean_sphincs` as a template: the statements from the claim's
  loads to the digest's check (`lean_ethereum.py:3763-3836, 3967-4025` at leanVM d1c4c8f7), with the
  values numbered as the renumbered expansion numbers them.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsT

/-!
# The message digest as a template

`verify_sig_lean_sphincs(signer, byte_bits)` (`G:3967-4053`; `G` is `lean_ethereum.py`): `signer` is
the parameter `n0`, `byte_bits` `n1`; `PK.seed` is `n2` (`sPP`, `signer[1]`, offset `0`), `PK.root`
`n3` (`sRoot`, offset `1`). Its first statements, up to the digest's check, are `sDigestBlock`:

* `sMsg` (`G:3971-3977`): the claim's four cells loaded, the message `M`'s two (`sM0` = `n4`, `sM1`
  = `n5`, offsets `2`, `3`) after the keys;
* `sDigests` (`G:3978-3982`): `R` hinted (`sRand`), `H_msg`'s two calls `H(R | PK.seed | PK.root | M |
  BE_32(i))`, 84 bytes, one block each, the first setting the padding run (`n12 …`, `sPad`); their
  outputs from `sHm0` (`n17`) and `sHm1` (`n38`);
* `sBitsHint`, `sBooleans` (`G:3989-3999`): the first call's two cells' bits hinted (`n51 …`, `n179 …`)
  and the second's low sixteen (`n307 …`), each pinned Boolean;
* `sForsFields` (`sp_fors_field`, `G:3787-3794`, through `sp_md_bit`, `G:3777-3783`): each FORS leaf
  read most significant bit first from the digest's bytes and its right shifts, `vals[10 c + z]` at
  `sFVal c z`;
* `sLeafShifts` (`sp_leaf_shifts`, `G:3830-3836`, through `sp_leaf_bit`, `G:3816-3826`): the three
  layers' leaves and their right shifts, `lvals[i]` at `sLVal i`;
* `sMdBytes` (`sp_md_byte`, `G:3798-3812`): the digest's first 30 bytes rebuilt where the first call's
  cells hold them, `md0`, `md1`;
* `sCheck` (`G:4015-4025`): the tree index's middle byte (`sTreeMid`), its high byte's six unused bits,
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
def sPad : Nat := 12
/-- `R`, the randomizer. -/
def sRand : V := .n 6
/-- The first call's output run and its two digest cells. -/
def sHm0 : V := .n 17
def sHm0b : V := .n 18
/-- The second call's output run and its first cell. -/
def sHm1 : V := .n 38

/-- `g^255`, as the compiler writes it: the bound of a byte's range check. -/
def g255W : E := word 9223372036854810629 0 0

/-- The word `2^s`, `s < 128`: in the low limb or the `y` limb. -/
def pw (s : Nat) : E := if s < 64 then word (2 ^ s) 0 0 else word 0 (2 ^ (s - 64)) 0

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

/-- `m0`, `m1`: the message `M`'s two cells, `signer[GEN^2]`, `signer[GEN^3]` (offsets `2`, `3`),
which `H_msg` hashes as they are. -/
def sM0 : V := .n 4
def sM1 : V := .n 5

/-- The claim's four cells loaded: `PK.seed`, `PK.root`, `m0`, `m1` (`G:3971-3977`). -/
def sMsg : List Stmt :=
  [loadS sPP (.n 0) 0, loadS sRoot (.n 0) 1, loadS sM0 (.n 0) 2, loadS sM1 (.n 0) 3]

/-! ## `H_msg` -/

/-- The inputs of `H_msg`'s call whose tail run is at `t`: `R`, `PK.seed`, `PK.root`, `m0`, the tail
`[m1, ctr, 0, 0]` (`ctr` the counter's cell: `BE_32(i)`, whose last byte `i` is at bit `24`, and the
`0x01` after it at bit `32`), the `0x80` at `t + 4`, the zero run. -/
def sHIns (t : Nat) : List V :=
  [sRand, sPP, sRoot, sM0, .n t, .n (t + 1), .n (t + 2), .n (t + 3), .n (t + 4),
    .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)]

/-- `R` hinted, then `H_msg`'s two calls (`G:3978-3982`), 84 bytes each: the first (`i = 0`) with the
padding run after its inputs, its counter cell the `0x01` byte at bit `32`; the second (`i = 1`)
with its counter `SP_COUNTER_ONE = 2^24` (byte `3`) added to it. -/
def sDigests : List Stmt :=
  [hintW "sp_rand" [sRand], copyS (.n 7) sM1, cst 8 (word (2 ^ 32) 0 0), cst 9 (word 0 0 0),
    cst 10 (word 0 0 0), cst 11 (word (2 ^ 63) 0 0)] ++ padRun sPad ++
  [kecS (sHIns 7) (runV 17 13) false false,
    cst 30 (word (2 ^ 24) 0 0), cst 31 (word (2 ^ 32) 0 0), addS (.n 32) (.n 30) (.n 31),
    copyS (.n 33) sM1, copyS (.n 34) (.n 32), cst 35 (word 0 0 0), cst 36 (word 0 0 0),
    cst 37 (word (2 ^ 63) 0 0), kecS (sHIns 33) (runV 38 13) false false]

/-! ## The digest's bits -/

/-- The first call's two cells' bits (`bits0`, `bits1`: one run from `n51`) and the second's low
sixteen (`bits2`, from `n307`), hinted. -/
def sBitsHint : List Stmt :=
  [.atom (.hint (.bits sHm0 0 128 (.stack (runV 51 128)))),
    .atom (.hint (.bits sHm0b 0 128 (.stack (runV 179 128)))),
    .atom (.hint (.bits sHm1 0 16 (.stack (runV 307 16))))]

/-- The bits pinned Boolean: `bits0[b]`, `bits1[b]` in turn, then `bits2`. -/
def sBooleans : List Stmt :=
  ((List.range 128).flatMap fun b => [mulS (.n (51 + b)) (.n (51 + b)) (.n (51 + b)),
    mulS (.n (179 + b)) (.n (179 + b)) (.n (179 + b))]) ++ booleans 307 16

/-- **Bit `p` of the digest read most significant first** (`sp_md_bit`): bit `7 - p % 8` of byte
`p / 8`, in the bit run of the first call's cells. -/
def sMdBit (p : Nat) : V := .n (51 + 8 * (p / 8) + 7 - p % 8)

/-- **Bit `b` of the layers' leaves, bottom first** (`sp_leaf_bit`): the bottom leaf the digest's
byte 33 (the second call's byte 1), the middle one byte 32 (its byte 0), the top one byte 31 then
the low two bits of byte 30 (the first call's). -/
def sLeafBit (b : Nat) : V :=
  if b < 16 then .n (307 + (b + 8) % 16) else if b < 24 then .n (179 + b + 104) else .n (179 + b + 88)

/-! ## Fields and their shifts -/

/-- A field of `n` bits read most significant first, bit `r` at `bit r`, and its right shifts:
the field shifted right by `n - 1 - r` at `outBase + 3 r` (`shifts`, with any bit order). -/
def shiftsG (bit : Nat → V) (n outBase : Nat) : List Stmt :=
  copyS (.n outBase) (bit 0) ::
  (List.range (n - 1)).flatMap fun r' => let r := r' + 1;
    [cst (outBase + 3 * r - 2) (word 2 0 0),
      mulS (.n (outBase + 3 * r - 1)) (.n (outBase + 3 * r - 2)) (.n (outBase + 3 * r - 3)),
      addS (.n (outBase + 3 * r)) (bit r) (.n (outBase + 3 * r - 1))]

/-- FORS tree `c`'s leaf and its shifts with the tree's place: `vals[10 c + z]`, the leaf shifted
right by `z` plus `c · 2^(10 - z)`. -/
def sFVal (c z : Nat) : V := .n (323 + 29 * c + 3 * (9 - z))

/-- `sp_fors_field` of tree `c` (`G:3787-3795`): its top bit plus the place `const(2 c)` (a copy for
`c = 0`, the constant at `322 + 29 c` otherwise), then the shifts. -/
def sForsField (c : Nat) : List Stmt :=
  (if c = 0 then [copyS (.n 323) (sMdBit 0)]
    else [cst (322 + 29 * c) (word (2 * c) 0 0),
      addS (.n (323 + 29 * c)) (sMdBit (10 * c)) (.n (322 + 29 * c))]) ++
  (shiftsG (fun r => sMdBit (10 * c + r)) 10 (323 + 29 * c)).tail

/-- `sp_fors_field` of every tree (`G:4013-4015`). -/
def sForsFields : List Stmt := (List.range 24).flatMap sForsField

/-- The layers' leaves: layer `l`'s first leaf bit and height. -/
def sLeafOff (l : Nat) : Nat := 8 * l
def sLeafLen (l : Nat) : Nat := if l = 2 then 10 else 8
/-- Where layer `l`'s shifts start. -/
def sLeafBase (l : Nat) : Nat := 1018 + 22 * l

/-- `lvals[i]`: the leaf of the layer of leaf bit `i` shifted right by `i - off`. -/
def sLVal (i : Nat) : V :=
  if i < 8 then .n (1018 + 3 * (7 - i)) else if i < 16 then .n (1040 + 3 * (15 - i))
  else .n (1062 + 3 * (25 - i))

/-- `sp_leaf_shifts` of the three layers (`G:4003-4006`). -/
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

/-- **`sp_md_byte(vals, i)` from base `b`**: digest byte `i < 30` placed at bit
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

/-- `md0`: bytes `0 ..< 16`, from `n1090`. -/
def sMd0 : List Stmt × Nat × V := sMdSum 15 1 (sMdByte 0 1090).2.2 (sMdByte 0 1090).2.1

/-- `md1`: bytes `16 ..< 30`. -/
def sMd1 : List Stmt × Nat × V :=
  let x := sMdByte 16 sMd0.2.1
  let r := sMdSum 13 17 x.2.2 x.2.1
  (x.1 ++ r.1, r.2.1, r.2.2)

/-- The digest's first 30 bytes (`G:4007-4014`). -/
def sMdBytes : List Stmt := (sMdByte 0 1090).1 ++ sMd0.1 ++ sMd1.1

/-! ## The check -/

/-- The tree index's middle byte, the top leaf's low byte (`G:4015`). -/
def sTreeMid : V := .n 1302

/-- The six unused bits of the tree index's high byte, most significant first (`G:4016-4018`). -/
def sPadBits : List Stmt :=
  (List.range 5).flatMap fun b => let x := 1303 + 3 * b;
    [cst x (word 2 0 0), mulS (.n (x + 1)) (.n (if b = 0 then 298 else x - 1)) (.n x),
      addS (.n (x + 2)) (.n (297 - b)) (.n (x + 1))]

/-- The second call's unused bytes, `sp_unused`, read from `n1335`. -/
def sUnused : List Stmt × Nat × V := sFromMarks 1329 6 1335

/-- `corr0`, `corr1` (`G:4025-4038`): the trees' places that `md0`, `md1` carry, a constant per
byte, summed: in a byte inside a field only where the field starts (`c · 256`), in a byte across
two the second field's (`(c + 1) · 2^(8 i + 8 - 10 (c + 1))`), each at bit `8 (i % 16)`. -/
def corr0W : E := word 7008726920298774528 49075504283816 0
def corr1W : E := word 5558655801016247104 401131962368 0

/-- The check (`G:4041-4051`): the tree's middle byte, the high byte's unused bits, `d0[0] = md0 +
corr0`, `d0[1] = md1 + corr1 + (lvals[24] + pad · g^2) · 2^112 + tree_mid · 2^120`, the unused
bytes, and `(d1[0] + lvals[8] + lvals[0] · g^8 + unused · g^16) · y⁻¹` in `K`. -/
def sCheck : List Stmt :=
  [cst 1300 (word 256 0 0), mulS (.n 1301) (sLVal 24) (.n 1300), addS sTreeMid (sLVal 16) (.n 1301)] ++
    sPadBits ++
  [cst 1318 corr0W, addS sHm0 sMd0.2.2 (.n 1318), cst 1319 corr1W,
    addS (.n 1320) sMd1.2.2 (.n 1319), cst 1321 (word 4 0 0), mulS (.n 1322) (.n 1317) (.n 1321),
    addS (.n 1323) (sLVal 24) (.n 1322), cst 1324 (pw 112), mulS (.n 1325) (.n 1323) (.n 1324),
    addS (.n 1326) (.n 1320) (.n 1325), cst 1327 (pw 120), mulS (.n 1328) sTreeMid (.n 1327),
    addS sHm0b (.n 1326) (.n 1328), hintW "sp_unused" (runV 1329 6)] ++ sUnused.1 ++
  [addS (.n 1386) sHm1 (sLVal 8), cst 1387 (word 256 0 0), mulS (.n 1388) (sLVal 0) (.n 1387),
    addS (.n 1389) (.n 1386) (.n 1388), cst 1390 (word 65536 0 0),
    mulS (.n 1391) sUnused.2.2 (.n 1390), addS (.n 1392) (.n 1389) (.n 1391),
    cst 1393 (word 1 0 1), mulS (.n 1394) (.n 1392) (.n 1393),
    .atom (.assertInK (.n 1394) sUnused.2.2)]

/-- **The message digest's block**: `verify_sig_lean_sphincs`'s statements up to the digest's
check; the next value is `n1395`. -/
def sDigestBlock : List Stmt :=
  sMsg ++ sDigests ++ sBitsHint ++ sBooleans ++ sForsFields ++ sLeafShifts ++ sMdBytes ++ sCheck

end
end LeanVM.Guest.B1.Sig
