/-
  LeanVM.Guest.B1.Sig.SphincsT

  The body of `verify_sig_lean_sphincs` as a template, written from the guest's structure
  (`lean_ethereum.py:3763-4052` at leanVM d1c4c8f7) with the values numbered as the renumbered
  expansion numbers them: the digest block (`SphincsDigestT`), then FORS and the hypertree
  (`SphincsForsT`'s templates, instantiated here).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsDigestT
public import LeanVM.Guest.B1.Sig.SphincsForsT

/-!
# `verify_sig_lean_sphincs` as a template

`verify_sig_lean_sphincs(signer, byte_bits)` (`G:3967-4052`; `G` is `lean_ethereum.py` at leanVM
d1c4c8f7). Its first 1332 statements, through the digest's check, are `sDigestBlock`
(`SphincsDigestT`); the next value is `n1369`. After them:

* `sForsAddrs` (`G:4029-4030`): `a0_b` at `n1376` (`sA0B`), `key_b` at `n1378` (`sKeyB`);
* `sForsB` (`G:4032-4037`): `SphincsForsT.sForsBlock` from `n1379`: `fors_at` at `n1380`
  (`sForsA1`), the 24 trees (tree `c` from `sForsBase c`, its root at `sRootOf c`), `T_k` over the
  roots, the FORS key at `n8623` (`sForsPk`); the trees read the digest's bits through `sForsBit`
  and the values `vals[k]` through `sVals`;
* `sLayerAt l` (`sp_layer`, `G:3953-3964`), layer `l` from `sLayerBase l`: its counter hinted
  (`sp_counter`) and read (`sFromMarks`, 4 bytes, `sCtrOf l`), then `SphincsForsT.sHtLayer`: the
  encoding digest (`sEncOf l`), the call of `sp_wots` (`sWotsCall`, its leaf `sLeafOf l`) and the
  path of `sHeightOf l` levels from leaf bit `sOffOf l` up to the layer's root;
* `sLayerB`, `sMidAddrs`, `sLayerM`, `sTopAddrs`, `sLayerT` (`G:4042-4052`): the three layers with
  their addresses (`sA0Of l`, `sA1Of l`) between them, then `root[0] == pk_root`;
* `sBody = sDigestBlock ++ sAfterDigest`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## FORS -/

/-- `vals[k]`, the index of FORS tree `k / 10`'s leaf's ancestor at height `k % 10`. -/
def sVals (k : Nat) : V := sFVal (k / 10) (k % 10)

/-- The bit FORS tree `k / 10`'s level `k % 10` checks its node against:
`sp_md_bit(bits0, bits1, 10 c + 9 - z)` (`G:3872`). -/
def sForsBit (k : Nat) : V := sMdBit (10 * (k / 10) + 9 - k % 10)

/-- `a0_b` (the bottom key's layer `0` and tree: `lvals[8] · 2^120 + tree_mid · 2^112 + lvals[24] ·
2^104`), `key_b` (its leaf, `lvals[0] · 2^56`), and `fors_at = key_b + SP_FORS_TREE`. -/
def sA0B : V := .n 1376
def sKeyB : V := .n 1378
def sForsA1 : V := .n 1380

/-- `a0_b`, `key_b` (`G:4029-4030`), from `n1369`. -/
def sForsAddrs : List Stmt :=
  [cst 1369 (lit (2 ^ 120)), mulS (.n 1370) (sLVal 8) (.n 1369), cst 1371 (lit (2 ^ 112)),
    mulS (.n 1372) sTreeMid (.n 1371), addS (.n 1373) (.n 1370) (.n 1372), cst 1374 (lit (2 ^ 104)),
    mulS (.n 1375) (sLVal 24) (.n 1374), addS sA0B (.n 1373) (.n 1375),
    cst 1377 (lit (2 ^ 56)), mulS sKeyB (sLVal 0) (.n 1377)]

/-- FORS (`G:4032-4037`) from `n1379`: the statements, the next base (`n8636`) and the FORS key's
output run's base. -/
def sForsB : List Stmt × Nat × Nat := sForsBlock sPad sPP sA0B sKeyB sForsBit sVals 1379

/-- Tree `c`'s base, its secret's cell: tree `0`'s leaf address has no constant, two values
fewer. -/
def sForsBase (c : Nat) : Nat := if c = 0 then 1381 else 1379 + 299 * c

/-- Tree `c`'s root, `roots[13 c]`. -/
def sRootOf (c : Nat) : V := .n (1665 + 299 * c)

/-- The FORS public key, `fors_pk[0]`. -/
def sForsPk : V := .n 8623

/-! ## The hypertree -/

/-- Layer `l`'s first leaf bit (`0`, `SP_MID = 8`, `SP_TOP = 16`) and its height (8, 8, 10). -/
def sOffOf (l : Nat) : Nat := sLeafOff l
def sHeightOf (l : Nat) : Nat := sLeafLen l

/-- Layer `l`'s base, its counter's first mark. -/
def sLayerBase (l : Nat) : Nat := if l = 0 then 8636 else if l = 1 then 8910 else 9181

/-- Layer `l`'s `a0`, its key pair's `A1` (`sp_wots`'s `a1`), its counter, its encoding digest's
first cell and its leaf (`sp_wots`'s return). -/
def sA0Of (l : Nat) : V := if l = 0 then sA0B else if l = 1 then .n 8907 else .n 9180
def sA1Of (l : Nat) : V := if l = 0 then sKeyB else if l = 1 then .n 8909 else .n 9179
def sCtrOf (l : Nat) : V := .n (sLayerBase l + 36)
def sEncOf (l : Nat) : V := .n (sLayerBase l + 46)
def sLeafOf (l : Nat) : V := .n (sLayerBase l + 59)

/-- The one-time key's leaf, by a call of `sp_wots(pp, a0, a1, encoding)`, at `b`: the call
`SphincsForsT.sHtLayer` writes. -/
def sWotsCall (a0 a1 enc : V) (b : Nat) : Stmt := .call "sp_wots" [sPP, a0, a1, enc] [.n b]

/-- Layer `l` (`sp_layer`, `G:3953-3964`) signing `signed`, at `a0` with its key pair `a1`: the
counter's four bytes hinted at `sLayerBase l …` and read, then the layer. The statements, the next
base and the root. -/
def sLayerAt (l : Nat) (a0 a1 signed : V) : List Stmt × Nat × V :=
  let c := sFromMarks (sLayerBase l) 4 (sLayerBase l + 4)
  let L := sHtLayer sPad sPP a0 a1 signed c.2.2 sLeafBit sLVal (sOffOf l) (sHeightOf l) c.2.1
  ([hintW "sp_counter" (runV (sLayerBase l) 4)] ++ c.1 ++ L.1, L.2.1, L.2.2)

/-- The bottom layer (`G:4042-4043`): `a0_b`, `key_b`, signing the FORS key. -/
def sLayerB : List Stmt × Nat × V := sLayerAt 0 sA0B sKeyB sForsPk

/-- `a0_m = SP_LAYER_MUL + tree_mid · 2^120 + lvals[24] · 2^112`, `key_m = lvals[8] · 2^56`
(`G:4044-4045`), from `n8901`. -/
def sMidAddrs : List Stmt :=
  [cst 8901 (lit (2 ^ 24)), cst 8902 (lit (2 ^ 120)), mulS (.n 8903) sTreeMid (.n 8902),
    addS (.n 8904) (.n 8901) (.n 8903), cst 8905 (lit (2 ^ 112)),
    mulS (.n 8906) (sLVal 24) (.n 8905), addS (sA0Of 1) (.n 8904) (.n 8906),
    cst 8908 (lit (2 ^ 56)), mulS (sA1Of 1) (sLVal 8) (.n 8908)]

/-- The middle layer (`G:4046-4047`), signing the bottom root. -/
def sLayerM : List Stmt × Nat × V := sLayerAt 1 (sA0Of 1) (sA1Of 1) sLayerB.2.2

/-- `key_t = tree_mid · 2^56 + lvals[24] · 2^48` (`G:4049`), from `n9175`, then `a0_t = 2 ·
SP_LAYER_MUL` (`G:4048`): a constant, bound to a value as `sp_layer`'s argument. -/
def sTopAddrs : List Stmt :=
  [cst 9175 (lit (2 ^ 56)), mulS (.n 9176) sTreeMid (.n 9175), cst 9177 (lit (2 ^ 48)),
    mulS (.n 9178) (sLVal 24) (.n 9177), addS (sA1Of 2) (.n 9176) (.n 9178),
    cst 9180 (lit (2 ^ 25))]

/-- The top layer (`G:4050-4051`), signing the middle root. -/
def sLayerT : List Stmt × Nat × V := sLayerAt 2 (sA0Of 2) (sA1Of 2) sLayerM.2.2

/-! ## The body -/

/-- The statements after the digest block: FORS, the three layers, `root[0] == pk_root`
(`G:4052`). -/
def sAfterDigest : List Stmt :=
  sForsAddrs ++ sForsB.1 ++ sLayerB.1 ++ sMidAddrs ++ sLayerM.1 ++ sTopAddrs ++ sLayerT.1 ++
    [.atom (.assertEq sLayerT.2.2 sRoot), .ret []]

/-- The body of `verify_sig_lean_sphincs`. -/
def sBody : List Stmt := sDigestBlock ++ sAfterDigest

end
end LeanVM.Guest.B1.Sig
