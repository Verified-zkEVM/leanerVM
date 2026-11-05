/-
  LeanVM.Guest.B1.Sig.SphincsT

  The body of `verify_sig_lean_sphincs` as a template, written from the guest's structure
  (`lean_ethereum.py:3691-3929` at leanVM 1a379148) with the values numbered as the renumbered
  expansion numbers them.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsT

/-!
# `verify_sig_lean_sphincs` as a template

`verify_sig_lean_sphincs(signer, byte_bits)` (`G:3842-3929`; `G` is `lean_ethereum.py`): `signer` is
the parameter `n0`, `byte_bits` `n1`, `P` the cell `n2` (`sPP`). The message digest's first call
allocates the padding run, at `n12 … n16` (`sPad`); every later one-block hash reads it.

* `sDigest`, `sDigests` (`G:3848-3854`): digest call `c`, `D_c = H(P | A_msg(c) | m | ρ)`, 80
  bytes;
* `sBits`, `sBooleans`, `sShifts` (`G:3860-3874`): the digest's bits hinted (`bits0`, `bits1`, the
  first ten of `bits2`, all the run `n51 …`, `sBit i`), pinned Boolean, and each field's value and
  right shifts (`sp_shifts`, the shared `shifts`; `sVal i` the value from bit `i`);
* `sPlace`, `sPlaces` (`sp_place`, `G:3734-3753`): the fields placed into the 64-bit lanes, the
  index `idx` the lane after the hypertree's fields (`sIdx`);
* `sFromBytes` (`sp_from_bytes`, `G:3694-3708`): each byte mark range checked and read off
  `byte_bits`, the value folded high byte first;
* `sCheck` (`G:3876-3884`): the digest's cells rebuilt from the lanes, the unused bytes, and the
  high lane checked to be a lane;
* `sForsTree` (`sp_fors_tree`, `G:3756-3775`): a FORS tree's leaf hashed from its secret, climbed
  up the hinted ordered pairs, its two top nodes hinted into the FORS key;
* `sLanes` (`G:3897-3906`): the hypertree's addresses; `sPath` (`sp_path`, `G:3811-3828`): a path
  in one tree; `sUpper` (`sp_upper_layer`, `G:3831-3839`): a layer above the bottom;
* `sBody`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-- The padding run of `verify_sig_lean_sphincs`, set by the first digest call. -/
def sPad : Nat := 12
/-- The public parameter `P`, `signer[1]`. -/
def sPP : V := .n 2
/-- Bit `i` of the digest's fields: `bits0`, `bits1` and `bits2` are one run of cells. -/
def sBit (i : Nat) : V := .n (51 + i)

/-- `g^255`, `g^63`, as the compiler writes them. -/
def g255W : E := word 9223372036854810629 0 0
def g63W : E := word (2 ^ 63) 0 0

/-- The fields of the digest: the hypertree's three (heights 8, 8, 10), then the 24 FORS trees'
(10 bits each): field `f`'s first bit and width. -/
def sFieldOff (f : Nat) : Nat := if f = 0 then 0 else if f = 1 then 8 else 16 + 10 * (f - 2)
def sFieldLen (f : Nat) : Nat := if f < 2 then 8 else 10

/-- Where field `f`'s shifts start: after the fields before, `1 + 3 (n - 1)` values each. -/
def sFieldBase (f : Nat) : Nat := if f = 0 then 317 else if f = 1 then 339 else 361 + 28 * (f - 2)

/-- The field of bit `i`. -/
def sFieldOf (i : Nat) : Nat := if i < 8 then 0 else if i < 16 then 1 else 2 + (i - 16) / 10

/-- The value from bit `i` of its field: the field shifted right by `i - off`
(`vals[i]`, `sp_shifts`). -/
def sVal (i : Nat) : V :=
  .n (sFieldBase (sFieldOf i) + 3 * (sFieldOff (sFieldOf i) + sFieldLen (sFieldOf i) - 1 - i))

/-! ## `sp_from_bytes` -/

/-- One byte from base `b`: its range check against `bound`, the table's address and value at
`b + 5`. -/
def sByte (mark : V) (bound : E) (b : Nat) : List Stmt :=
  rangeS mark bound b ++ [mulS (.n (b + 4)) (.n 1) mark, loadS (.n (b + 5)) (.n (b + 4)) 0]

/-- The bytes after the top one, folding `val`. -/
def sFromBytesRest : List V → Nat → V → List Stmt × Nat × V
  | [], b, val => ([], b, val)
  | m :: ms, b, val =>
      let rest := sFromBytesRest ms (b + 9) (.n (b + 8))
      (sByte m g255W b ++ [cst (b + 6) (word 256 0 0), mulS (.n (b + 7)) val (.n (b + 6)),
        addS (.n (b + 8)) (.n (b + 5)) (.n (b + 7))] ++ rest.1, rest.2.1, rest.2.2)

/-- `sp_from_bytes` of the marks `top :: rest` (high byte first) from base `b`: the statements, the
next base and the value. -/
def sFromBytes (top : V) (rest : List V) (bound : E) (b : Nat) : List Stmt × Nat × V :=
  let r := sFromBytesRest rest (b + 6) (.n (b + 5))
  (sByte top bound b ++ r.1, r.2.1, r.2.2)

/-- The marks of an `n`-byte integer hinted at `b …`: the top first. -/
def sMarks (b n : Nat) : V × List V := (.n (b + n - 1), (List.range (n - 1)).reverse.map fun k => .n (b + k))

/-! ## The digest and its fields -/

/-- Digest call `c` from base `b` with its padding run at `pad`: the address `TW_MSG + c·2^32`, the
message reloaded, and `keccak([P, A], [m0, m1], out, tail=[ρ, 0, 0, 0], len=80)`: the tail's run
copied (`ρ`, the `0x01` byte, zeros), the last byte's `0x80`, the outputs at `o`. -/
def sDigest (pad c b o : Nat) : List Stmt :=
  [cst b (word (tw 12 + c * hiMul) 0 0), loadS (.n (b + 1)) (.n 0) 2, loadS (.n (b + 2)) (.n 0) 3,
    copyS (.n (b + 3)) (.n 3), cst (b + 4) (word 1 0 0), cst (b + 5) (word 0 0 0),
    cst (b + 6) (word 0 0 0), cst (b + 7) (word (2 ^ 63) 0 0)] ++
  (if c = 0 then padRun pad else []) ++
  [kecS [sPP, .n b, .n (b + 1), .n (b + 2), .n (b + 3), .n (b + 4), .n (b + 5), .n (b + 6),
    .n (b + 7), .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)] (runV o 13) false false]

/-- The two digest calls after `P` and the randomizer `n3`: the first allocates the padding run
(`n12 … n16`, its output at `n17`), the second's output is at `n38`. -/
def sDigests : List Stmt :=
  [loadS sPP (.n 0) 1, hintW "sp_rand" [.n 3]] ++ sDigest sPad 0 4 17 ++ sDigest sPad 1 30 38

/-- The digest's bits hinted: `n17`'s 128, `n18`'s 128, `n38`'s first ten. -/
def sBits : List Stmt :=
  [.atom (.hint (.bits (.n 17) 0 128 (.stack (runV 51 128)))),
    .atom (.hint (.bits (.n 18) 0 128 (.stack (runV 179 128)))),
    .atom (.hint (.bits (.n 38) 0 10 (.stack (runV 307 10))))]

/-- The bits pinned Boolean: `bits0[b]`, `bits1[b]` in turn, then `bits2`. -/
def sBooleans : List Stmt :=
  ((List.range 128).flatMap fun b => [mulS (.n (51 + b)) (.n (51 + b)) (.n (51 + b)),
    mulS (.n (179 + b)) (.n (179 + b)) (.n (179 + b))]) ++ booleans 307 10

/-- Each field's value and right shifts (`sp_shifts`). -/
def sShifts : List Stmt :=
  (List.range 27).flatMap fun f => shifts (51 + sFieldOff f) (sFieldLen f) (sFieldBase f)

/-- `sp_place` of the field of `n` bits from bit `off` into the lane `lane`, from base `b`: the
statements, the next base, the lane after, and the lane completed (its index and value). -/
def sPlace (lane : V) (off n b : Nat) : List Stmt × Nat × V × Option (Nat × V) :=
  if (off + n - 1) / 64 = off / 64 then
    let s : List Stmt × Nat × V := if off % 64 = 0 then ([], b, sVal off)
      else ([cst b (word (2 ^ (off % 64)) 0 0), mulS (.n (b + 1)) (sVal off) (.n b),
        addS (.n (b + 2)) lane (.n (b + 1))], b + 3, .n (b + 2))
    if (off + n) % 64 = 0 then
      (s.1 ++ [copyS (.n s.2.1) s.2.2], s.2.1 + 1, s.2.2, some (off / 64, .n s.2.1))
    else (s.1, s.2.1, s.2.2, none)
  else
    let k := 64 - off % 64
    ([cst b (word (2 ^ k) 0 0), mulS (.n (b + 1)) (sVal (off + k)) (.n b),
      addS (.n (b + 2)) (sVal off) (.n (b + 1)), cst (b + 3) (word (2 ^ (off % 64)) 0 0),
      mulS (.n (b + 4)) (.n (b + 2)) (.n (b + 3)), addS (.n (b + 5)) lane (.n (b + 4))],
      b + 6, sVal (off + k), some (off / 64, .n (b + 5)))

/-- Fields `f ..< f + m` placed from the lane `lane`, from base `b`: the statements, the next base,
the lane after, the lanes completed, and the lane after field `2` (the index), if reached. -/
def sPlaces : Nat → Nat → V → Nat → List Stmt × Nat × V × List (Nat × V)
  | 0, _, lane, b => ([], b, lane, [])
  | m + 1, f, lane, b =>
      let x := sPlace lane (sFieldOff f) (sFieldLen f) b
      let rest := sPlaces m (f + 1) x.2.2.1 x.2.1
      (x.1 ++ rest.1, rest.2.1, rest.2.2.1, x.2.2.2.toList ++ rest.2.2.2)

/-- The placements, after the lane's literal `0` at `n1061`. -/
def sPl : List Stmt × Nat × V × List (Nat × V) := sPlaces 27 0 (.n 1061) 1062

/-- The index `idx`: the lane after the hypertree's three fields. -/
def sIdx : V := (sPlaces 3 0 (.n 1061) 1062).2.2.1

/-- Lane `j`, as `sPl` completes it. -/
def sLane (j : Nat) : V := ((sPl.2.2.2.find? fun p => p.1 == j).map Prod.snd).getD (.n 0)

/-- The fields' checks from base `b`: the digest's first two cells rebuilt from the lanes, the
unused bytes read, the second call's high lane checked to be a lane. -/
def sCheck (b : Nat) : List Stmt × Nat :=
  let mk := sMarks (b + 4) 7
  let u := sFromBytes mk.1 mk.2 g63W (b + 11)
  let c := u.2.1
  ([cst b (word 0 1 0), mulS (.n (b + 1)) (sLane 1) (.n b), addS (.n 17) (sLane 0) (.n (b + 1)),
    cst (b + 2) (word 0 1 0), mulS (.n (b + 3)) (sLane 3) (.n (b + 2)),
    addS (.n 18) (sLane 2) (.n (b + 3)), hintW "sp_unused" (runV (b + 4) 7)] ++ u.1 ++
    [addS (.n c) (.n 38) sPl.2.2.1, cst (c + 1) (word 1024 0 0), mulS (.n (c + 2)) u.2.2 (.n (c + 1)),
      addS (.n (c + 3)) (.n c) (.n (c + 2)), cst (c + 4) (word 1 0 1),
      mulS (.n (c + 5)) (.n (c + 3)) (.n (c + 4)), .atom (.assertInK (.n (c + 5)) u.2.2)], c + 6)

/-! ## FORS -/

/-- `keccak([P, a], [v, 0], out, len=48)` at the padding run: its last byte's constant at `c`, the
outputs from `o`. -/
def k48 (a v : V) (c o : Nat) : List Stmt := k48At sPP sPad a v c o

/-- `is_child(node, kids, k, bit)` with the children at `k0`, `k1`, the check's cells at `b`,
`b + 1`. -/
def isChildS (node k0 k1 bit : V) (b : Nat) : List Stmt :=
  [addS (.n b) node k0, addS (.n (b + 1)) k0 k1, mulS (.n b) bit (.n (b + 1))]

/-- Level `l` of FORS tree `c` from base `x`, from the node `cur`, the tree's node address before
its level at `base`: the children hinted and checked, the parent hashed. The statements, the next
base and the parent. -/
def sForsLevel (c l : Nat) (base cur : V) (x : Nat) : List Stmt × Nat × V :=
  let f := 26 + 10 * c
  ([hintW "sp_fors_nodes" [.n x, .n (x + 1)]] ++ isChildS cur (.n x) (.n (x + 1)) (sBit (f + l)) (x + 2) ++
    [cst (x + 4) (word (64 * (l + 1) * hiMul) 0 0), addS (.n (x + 5)) base (.n (x + 4)),
      cst (x + 6) (word (2 ^ 42) 0 0), mulS (.n (x + 7)) (sVal (f + l + 1)) (.n (x + 6)),
      addS (.n (x + 8)) (.n (x + 5)) (.n (x + 7))] ++
    k64 sPad sPP (.n (x + 8)) (.n x) (.n (x + 1)) (x + 9) (x + 10), x + 23, .n (x + 10))

/-- Levels `l ..< l + m` of FORS tree `c` from `cur`, from base `x`. -/
def sForsLevels (c : Nat) (base : V) : Nat → Nat → V → Nat → List Stmt × Nat × V
  | 0, _, cur, x => ([], x, cur)
  | m + 1, l, cur, x =>
      let a := sForsLevel c l base cur x
      let rest := sForsLevels c base m (l + 1) a.2.2 a.2.1
      (a.1 ++ rest.1, rest.2.1, rest.2.2)

/-- FORS tree `c` from base `b` (`sp_fors_tree`): the secret hinted, the leaf hashed at
`idx + (TW_FLEAF + c·2^32) + s·2^38`, nine levels, the two top nodes hinted into the FORS key and the
node reached checked to be the one the top bit names. The statements, the next base and the two
top nodes. -/
def sForsTree (c b : Nat) : List Stmt × Nat × V × V :=
  let f := 26 + 10 * c
  let lv := sForsLevels c (.n (b + 21)) 9 0 (.n (b + 7)) (b + 22)
  let t := lv.2.1
  ([hintW "sp_fors_secrets" [.n b], cst (b + 1) (word (tw 15 + c * hiMul) 0 0),
      addS (.n (b + 2)) sIdx (.n (b + 1)), cst (b + 3) (word (2 ^ 38) 0 0),
      mulS (.n (b + 4)) (sVal f) (.n (b + 3)), addS (.n (b + 5)) (.n (b + 2)) (.n (b + 4))] ++
    k48 (.n (b + 5)) (.n b) (b + 6) (b + 7) ++
    [cst (b + 20) (word (tw 17 + c * hiMul) 0 0), addS (.n (b + 21)) sIdx (.n (b + 20))] ++ lv.1 ++
    [hintW "sp_fors_nodes" [.n t, .n (t + 1)]] ++ isChildS lv.2.2 (.n t) (.n (t + 1)) (sBit (f + 9)) (t + 2),
    t + 4, .n t, .n (t + 1))

/-- FORS trees `c ..< c + m` from base `b`: the statements, the next base, the top nodes. -/
def sForsTrees : Nat → Nat → Nat → List Stmt × Nat × List V
  | 0, _, b => ([], b, [])
  | m + 1, c, b =>
      let t := sForsTree c b
      let rest := sForsTrees m (c + 1) t.2.1
      (t.1 ++ rest.1, rest.2.1, t.2.2.1 :: t.2.2.2 :: rest.2.2)

/-! ## The hypertree -/

/-- The hypertree's addresses from base `b` (`G:3897-3906`): `lane_b` at `b + 4`, `lane_m` at
`b + 8`, `at_b` at `b + 9`, `at_m` at `b + 10`, `at_t` at `b + 12`. -/
def sLanes (b : Nat) : List Stmt :=
  [cst b (word 256 0 0), mulS (.n (b + 1)) (sVal 16) (.n b), addS (.n (b + 2)) (sVal 8) (.n (b + 1)),
    cst (b + 3) (word 0 256 0), mulS (.n (b + 4)) (.n (b + 2)) (.n (b + 3)),
    cst (b + 5) (word 0 256 0), mulS (.n (b + 6)) (sVal 16) (.n (b + 5)), cst (b + 7) (word 0 1 0),
    addS (.n (b + 8)) (.n (b + 6)) (.n (b + 7)), addS (.n (b + 9)) (sVal 0) (.n (b + 4)),
    addS (.n (b + 10)) (sVal 8) (.n (b + 8)), cst (b + 11) (word 0 2 0),
    addS (.n (b + 12)) (sVal 16) (.n (b + 11))]

/-- `sp_path` from `node`, `height` levels of the tree whose leaf index is the field from bit
`off`, every address plus `lane`, from base `x`: the statements, the next base and the root. -/
def sPath (lane : V) (off : Nat) : Nat → Nat → V → Nat → List Stmt × Nat × V
  | 0, _, cur, x => ([], x, cur)
  | m + 1, l, cur, x =>
      let pre := [hintW "siblings" [.n x, .n (x + 1)]] ++ isChildS cur (.n x) (.n (x + 1)) (sBit (off + l))
        (x + 2) ++ [cst (x + 4) (word (tw 3 + (l + 1) * hiMul) 0 0), addS (.n (x + 5)) lane (.n (x + 4))]
      if m = 0 then
        (pre ++ k64 sPad sPP (.n (x + 5)) (.n x) (.n (x + 1)) (x + 6) (x + 7), x + 20, .n (x + 7))
      else
        let rest := sPath lane off m (l + 1) (.n (x + 8)) (x + 21)
        (pre ++ addS (.n (x + 6)) (.n (x + 5)) (sVal (off + l + 1)) ::
          k64 sPad sPP (.n (x + 6)) (.n x) (.n (x + 1)) (x + 7) (x + 8) ++ rest.1, rest.2.1, rest.2.2)

/-- A one-time key's leaf, by a call of `sp_wots` at the address `adr` with the encoding digest's
first cell `enc`; the leaf is at `b`. -/
def sWotsCall (adr enc : V) (b : Nat) : Stmt := .call "sp_wots" [sPP, adr, enc] [.n b]

/-- A layer above the bottom from base `b` (`sp_upper_layer`): its counter hinted and rebuilt, the
encoding of the root `below` (52 bytes), the key's leaf, the path of `height` levels from bit `off`
plus `lane`. The statements, the next base and the root. -/
def sUpper (adr below lane : V) (off height b : Nat) : List Stmt × Nat × V :=
  let mk := sMarks b 4
  let fb := sFromBytes mk.1 mk.2 g255W (b + 4)
  let c := fb.2.1
  let k := kMsg sPad [.cell sPP, .cell (.n (c + 1)), .cell below, .cell fb.2.2] 52 false none (c + 2)
  let p := sPath lane off height 0 (.n k.2.1) (k.2.1 + 1)
  ([hintW "sp_counter" (runV b 4)] ++ fb.1 ++ [cst c (word (tw 4) 0 0), addS (.n (c + 1)) adr (.n c)] ++
    k.1 ++ [sWotsCall adr (.n k.2.2) k.2.1] ++ p.1, p.2.1, p.2.2)

/-! ## The body -/

/-- The FORS trees, from `n1225`, after the key's first cell `n1224 = P`. -/
def sFors : List Stmt × Nat × List V := sForsTrees 24 0 1225

/-- The base after the FORS trees: the hypertree's addresses there. -/
def sH : Nat := sFors.2.1

/-- The bottom layer's counter, from `sH + 15`. -/
def sCtrB : List Stmt × Nat × V := sFromBytes (sMarks (sH + 15) 4).1 (sMarks (sH + 15) 4).2 g255W (sH + 19)

/-- The bottom layer's encoding message: `P`, `at_b + SP_TW_ENC`, the FORS key, the counter. -/
def sEncCells : List V := [.n 1224, .n (sH + 14)] ++ sFors.2.2 ++ [.n sCtrB.2.1]

/-- The bottom encoding's `keccak_cells` (804 bytes). -/
def sEncB : List Stmt × Nat × Nat := kMsg sPad (sEncCells.map KC.cell) 804 true none (sCtrB.2.1 + 1)

/-- The bottom layer's path, from the leaf `sp_wots` returns. -/
def sPathB : List Stmt × Nat × V := sPath (.n (sH + 4)) 0 8 0 (.n sEncB.2.1) (sEncB.2.1 + 1)

/-- The middle layer. -/
def sUpperM : List Stmt × Nat × V := sUpper (.n (sH + 10)) sPathB.2.2 (.n (sH + 8)) 8 8 sPathB.2.1

/-- The top layer, its lane `lane_t = 2·2^64` set at its start. -/
def sUpperT : List Stmt × Nat × V :=
  sUpper (.n (sH + 12)) sUpperM.2.2 (.n sUpperM.2.1) 16 10 (sUpperM.2.1 + 1)

/-- The body of `verify_sig_lean_sphincs`. -/
def sBody : List Stmt :=
  sDigests ++ sBits ++ sBooleans ++ sShifts ++ [cst 1061 (word 0 0 0)] ++ sPl.1 ++ (sCheck sPl.2.1).1 ++
    [copyS (.n 1224) sPP] ++ sFors.1 ++ sLanes sH ++
    [cst (sH + 13) (word (tw 4) 0 0), addS (.n (sH + 14)) (.n (sH + 9)) (.n (sH + 13)),
      hintW "sp_counter" (runV (sH + 15) 4)] ++ sCtrB.1 ++ [copyS (.n sCtrB.2.1) sCtrB.2.2] ++ sEncB.1 ++
    [sWotsCall (.n (sH + 9)) (.n sEncB.2.2) sEncB.2.1] ++ sPathB.1 ++ sUpperM.1 ++
    [cst sUpperM.2.1 (word 0 2 0)] ++ sUpperT.1 ++
    [loadS (.n sUpperT.2.1) (.n 0) 0, .atom (.assertEq sUpperT.2.2 (.n sUpperT.2.1)), .ret []]

end
end LeanVM.Guest.B1.Sig
