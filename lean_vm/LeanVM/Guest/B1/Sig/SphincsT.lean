/-
  LeanVM.Guest.B1.Sig.SphincsT

  The body of `verify_sig_lean_sphincs` as a template, written from the guest's structure
  (`lean_ethereum.py:3769-4073` at leanVM 834e6614) with the values numbered as the renumbered
  expansion numbers them: the digest block (`SphincsDigestT`), then FORS and the hypertree
  (`SphincsForsT`'s templates, instantiated here).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsDigestT
public import LeanVM.Guest.B1.Sig.SphincsForsT

/-!
# `verify_sig_lean_sphincs` as a template

`verify_sig_lean_sphincs(signer, byte_bits)` (`G:3972-4073`; `G` is `lean_ethereum.py` at leanVM
834e6614). Its first 1580 statements, through the digest's check, are `sDigestBlock`
(`SphincsDigestT`); the next value is `n1710`. After them:

* `sForsAddrs` (`G:4050-4051`): `a0_b` at `n1717` (`sA0B`), `key_b` at `n1719` (`sKeyB`);
* `sForsB` (`G:4053-4058`): `SphincsForsT.sForsBlock` from `n1720`: `fors_at` at `n1721`
  (`sForsA1`), the 24 trees (tree `c` from `sForsBase c`, its root at `sRootOf c`), `T_k` over the
  roots, the FORS key at `n8964` (`sForsPk`); the trees read the digest's bits through `sForsBit`
  and the values `vals[k]` through `sVals`;
* `sLayerAt l` (`sp_layer`, `G:3958-3969`), layer `l` from `sLayerBase l`: its counter hinted
  (`sp_counter`) and read (`sFromMarks`, 4 bytes, `sCtrOf l`), then `SphincsForsT.sHtLayer`: the
  encoding digest (`sEncOf l`), the call of `sp_wots` (`sWotsCall`, its leaf `sLeafOf l`) and the
  path of `sHeightOf l` levels from leaf bit `sOffOf l` up to the layer's root;
* `sLayerB`, `sMidAddrs`, `sLayerM`, `sTopAddrs`, `sLayerT` (`G:4063-4073`): the three layers with
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
`sp_md_bit(bits0, bits1, 10 c + 9 - z)` (`G:3877`). -/
def sForsBit (k : Nat) : V := sMdBit (10 * (k / 10) + 9 - k % 10)

/-- `a0_b` (the bottom key's layer `0` and tree: `lvals[8] · 2^120 + tree_mid · 2^112 + lvals[24] ·
2^104`), `key_b` (its leaf, `lvals[0] · 2^56`), and `fors_at = key_b + SP_FORS_TREE`. -/
def sA0B : V := .n 1717
def sKeyB : V := .n 1719
def sForsA1 : V := .n 1721

/-- `a0_b`, `key_b` (`G:4050-4051`), from `n1710`. -/
def sForsAddrs : List Stmt :=
  [cst 1710 (lit (2 ^ 120)), mulS (.n 1711) (sLVal 8) (.n 1710), cst 1712 (lit (2 ^ 112)),
    mulS (.n 1713) sTreeMid (.n 1712), addS (.n 1714) (.n 1711) (.n 1713), cst 1715 (lit (2 ^ 104)),
    mulS (.n 1716) (sLVal 24) (.n 1715), addS sA0B (.n 1714) (.n 1716),
    cst 1718 (lit (2 ^ 56)), mulS sKeyB (sLVal 0) (.n 1718)]

/-- FORS (`G:4053-4058`) from `n1720`: the statements, the next base (`n8977`) and the FORS key's
output run's base. -/
def sForsB : List Stmt × Nat × Nat := sForsBlock sPad sPP sA0B sKeyB sForsBit sVals 1720

/-- Tree `c`'s base, its secret's cell: tree `0`'s leaf address has no constant, two values
fewer. -/
def sForsBase (c : Nat) : Nat := if c = 0 then 1722 else 1720 + 299 * c

/-- Tree `c`'s root, `roots[13 c]`. -/
def sRootOf (c : Nat) : V := .n (2006 + 299 * c)

/-- The FORS public key, `fors_pk[0]`. -/
def sForsPk : V := .n 8964

/-! ## The hypertree -/

/-- Layer `l`'s first leaf bit (`0`, `SP_MID = 8`, `SP_TOP = 16`) and its height (8, 8, 10). -/
def sOffOf (l : Nat) : Nat := sLeafOff l
def sHeightOf (l : Nat) : Nat := sLeafLen l

/-- Layer `l`'s base, its counter's first mark. -/
def sLayerBase (l : Nat) : Nat := if l = 0 then 8977 else if l = 1 then 9251 else 9522

/-- Layer `l`'s `a0`, its key pair's `A1` (`sp_wots`'s `a1`), its counter, its encoding digest's
first cell and its leaf (`sp_wots`'s return). -/
def sA0Of (l : Nat) : V := if l = 0 then sA0B else if l = 1 then .n 9248 else .n 9521
def sA1Of (l : Nat) : V := if l = 0 then sKeyB else if l = 1 then .n 9250 else .n 9520
def sCtrOf (l : Nat) : V := .n (sLayerBase l + 36)
def sEncOf (l : Nat) : V := .n (sLayerBase l + 46)
def sLeafOf (l : Nat) : V := .n (sLayerBase l + 59)

/-- The one-time key's leaf, by a call of `sp_wots(pp, a0, a1, encoding)`, at `b`: the call
`SphincsForsT.sHtLayer` writes. -/
def sWotsCall (a0 a1 enc : V) (b : Nat) : Stmt := .call "sp_wots" [sPP, a0, a1, enc] [.n b]

/-- Layer `l` (`sp_layer`, `G:3958-3969`) signing `signed`, at `a0` with its key pair `a1`: the
counter's four bytes hinted at `sLayerBase l …` and read, then the layer. The statements, the next
base and the root. -/
def sLayerAt (l : Nat) (a0 a1 signed : V) : List Stmt × Nat × V :=
  let c := sFromMarks (sLayerBase l) 4 (sLayerBase l + 4)
  let L := sHtLayer sPad sPP a0 a1 signed c.2.2 sLeafBit sLVal (sOffOf l) (sHeightOf l) c.2.1
  ([hintW "sp_counter" (runV (sLayerBase l) 4)] ++ c.1 ++ L.1, L.2.1, L.2.2)

/-- The bottom layer (`G:4063-4064`): `a0_b`, `key_b`, signing the FORS key. -/
def sLayerB : List Stmt × Nat × V := sLayerAt 0 sA0B sKeyB sForsPk

/-- `a0_m = SP_LAYER_MUL + tree_mid · 2^120 + lvals[24] · 2^112`, `key_m = lvals[8] · 2^56`
(`G:4065-4066`), from `n9242`. -/
def sMidAddrs : List Stmt :=
  [cst 9242 (lit (2 ^ 24)), cst 9243 (lit (2 ^ 120)), mulS (.n 9244) sTreeMid (.n 9243),
    addS (.n 9245) (.n 9242) (.n 9244), cst 9246 (lit (2 ^ 112)),
    mulS (.n 9247) (sLVal 24) (.n 9246), addS (sA0Of 1) (.n 9245) (.n 9247),
    cst 9249 (lit (2 ^ 56)), mulS (sA1Of 1) (sLVal 8) (.n 9249)]

/-- The middle layer (`G:4067-4068`), signing the bottom root. -/
def sLayerM : List Stmt × Nat × V := sLayerAt 1 (sA0Of 1) (sA1Of 1) sLayerB.2.2

/-- `key_t = tree_mid · 2^56 + lvals[24] · 2^48` (`G:4070`), from `n9516`, then `a0_t = 2 ·
SP_LAYER_MUL` (`G:4069`): a constant, bound to a value as `sp_layer`'s argument. -/
def sTopAddrs : List Stmt :=
  [cst 9516 (lit (2 ^ 56)), mulS (.n 9517) sTreeMid (.n 9516), cst 9518 (lit (2 ^ 48)),
    mulS (.n 9519) (sLVal 24) (.n 9518), addS (sA1Of 2) (.n 9517) (.n 9519),
    cst 9521 (lit (2 ^ 25))]

/-- The top layer (`G:4071-4072`), signing the middle root. -/
def sLayerT : List Stmt × Nat × V := sLayerAt 2 (sA0Of 2) (sA1Of 2) sLayerM.2.2

/-! ## The body -/

/-- The statements after the digest block: FORS, the three layers, `root[0] == pk_root`
(`G:4073`). -/
def sAfterDigest : List Stmt :=
  sForsAddrs ++ sForsB.1 ++ sLayerB.1 ++ sMidAddrs ++ sLayerM.1 ++ sTopAddrs ++ sLayerT.1 ++
    [.atom (.assertEq sLayerT.2.2 sRoot), .ret []]

/-- The body of `verify_sig_lean_sphincs`. -/
def sBody : List Stmt := sDigestBlock ++ sAfterDigest

end
end LeanVM.Guest.B1.Sig
