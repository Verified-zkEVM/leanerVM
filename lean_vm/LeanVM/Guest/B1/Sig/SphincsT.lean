/-
  LeanVM.Guest.B1.Sig.SphincsT

  The body of `verify_sig_lean_sphincs` as a template, written from the guest's structure
  (`lean_ethereum.py:3763-4079` at leanVM 56a4109f) with the values numbered as the renumbered
  expansion numbers them: the digest block (`SphincsDigestT`), then FORS and the hypertree
  (`SphincsForsT`'s templates, instantiated here).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsDigestT
public import LeanVM.Guest.B1.Sig.SphincsForsT

/-!
# `verify_sig_lean_sphincs` as a template

`verify_sig_lean_sphincs(signer, byte_bits)` (`G:3979-4079`; `G` is `lean_ethereum.py` at leanVM
56a4109f). Its first 1358 statements, through the digest's check, are `sDigestBlock`
(`SphincsDigestT`); the next value is `n1395`. After them:

* `sForsAddrs` (`G:4056-4057`): `a0_b` at `n1402` (`sA0B`), `key_b` at `n1404` (`sKeyB`);
* `sForsB` (`G:4059-4064`): `SphincsForsT.sForsBlock` from `n1405`: `fors_at` at `n1406`
  (`sForsA1`), the 24 trees (tree `c` from `sForsBase c`, its root at `sRootOf c`), `T_k` over the
  roots, the FORS key at `n8443` (`sForsPk`); the trees read the digest's bits through `sForsBit`
  and the values `vals[k]` through `sVals`;
* `sLayerAt l` (`sp_layer`, `G:3965-3976`), layer `l` from `sLayerBase l`: its counter hinted
  (`sp_counter`) and read (`sFromMarks`, 4 bytes, `sCtrOf l`), then `SphincsForsT.sHtLayer`: the
  encoding digest (`sEncOf l`), the call of `sp_wots` (`sWotsCall`, its leaf `sLeafOf l`) and the
  path of `sHeightOf l` levels from leaf bit `sOffOf l` up to the layer's root;
* `sLayerB`, `sMidAddrs`, `sLayerM`, `sTopAddrs`, `sLayerT` (`G:4069-4079`): the three layers with
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
`sp_md_bit(bits0, bits1, 10 c + 9 - z)` (`G:3883`). -/
def sForsBit (k : Nat) : V := sMdBit (10 * (k / 10) + 9 - k % 10)

/-- `a0_b` (the bottom key's layer `0` and tree: `lvals[8] · 2^120 + tree_mid · 2^112 + lvals[24] ·
2^104`), `key_b` (its leaf, `lvals[0] · 2^56`), and `fors_at = key_b + SP_FORS_TREE`. -/
def sA0B : V := .n 1402
def sKeyB : V := .n 1404
def sForsA1 : V := .n 1406

/-- `a0_b`, `key_b` (`G:4056-4057`), from `n1395`. -/
def sForsAddrs : List Stmt :=
  [cst 1395 (lit (2 ^ 120)), mulS (.n 1396) (sLVal 8) (.n 1395), cst 1397 (lit (2 ^ 112)),
    mulS (.n 1398) sTreeMid (.n 1397), addS (.n 1399) (.n 1396) (.n 1398), cst 1400 (lit (2 ^ 104)),
    mulS (.n 1401) (sLVal 24) (.n 1400), addS sA0B (.n 1399) (.n 1401),
    cst 1403 (lit (2 ^ 56)), mulS sKeyB (sLVal 0) (.n 1403)]

/-- FORS (`G:4059-4064`) from `n1405`: the statements, the next base (`n8456`) and the FORS key's
output run's base. -/
def sForsB : List Stmt × Nat × Nat := sForsBlock sPad sPP sA0B sKeyB sForsBit sVals 1405

/-- Tree `c`'s base, its secret's cell. -/
def sForsBase (c : Nat) : Nat := 1407 + ((List.range c).map forsTreeW).sum

/-- Tree `c`'s root, `roots[13 c]`: the last level's output, thirteen values before the next tree. -/
def sRootOf (c : Nat) : V := .n (sForsBase (c + 1) - 13)

/-- The FORS public key, `fors_pk[0]`. -/
def sForsPk : V := .n 8443

/-! ## The hypertree -/

/-- Layer `l`'s first leaf bit (`0`, `SP_MID = 8`, `SP_TOP = 16`) and its height (8, 8, 10). -/
def sOffOf (l : Nat) : Nat := sLeafOff l
def sHeightOf (l : Nat) : Nat := sLeafLen l

/-- Layer `l`'s base, its counter's first mark. -/
def sLayerBase (l : Nat) : Nat := if l = 0 then 8456 else if l = 1 then 8722 else 8985

/-- Layer `l`'s `a0`, its key pair's `A1` (`sp_wots`'s `a1`), its counter, its encoding digest's
first cell and its leaf (`sp_wots`'s return). -/
def sA0Of (l : Nat) : V := if l = 0 then sA0B else if l = 1 then .n 8719 else .n 8984
def sA1Of (l : Nat) : V := if l = 0 then sKeyB else if l = 1 then .n 8721 else .n 8983
def sCtrOf (l : Nat) : V := .n (sLayerBase l + 36)
def sEncOf (l : Nat) : V := .n (sLayerBase l + 46)
def sLeafOf (l : Nat) : V := .n (sLayerBase l + 59)

/-- The one-time key's leaf, by a call of `sp_wots(pp, a0, a1, encoding)`, at `b`: the call
`SphincsForsT.sHtLayer` writes. -/
def sWotsCall (a0 a1 enc : V) (b : Nat) : Stmt := .call "sp_wots" [sPP, a0, a1, enc] [.n b]

/-- Layer `l` (`sp_layer`, `G:3965-3976`) signing `signed`, at `a0` with its key pair `a1`: the
counter's four bytes hinted at `sLayerBase l …` and read, then the layer. The statements, the next
base and the root. -/
def sLayerAt (l : Nat) (a0 a1 signed : V) : List Stmt × Nat × V :=
  let c := sFromMarks (sLayerBase l) 4 (sLayerBase l + 4)
  let L := sHtLayer sPad sPP a0 a1 signed c.2.2 sLeafBit sLVal (sOffOf l) (sHeightOf l) c.2.1
  ([hintW "sp_counter" (runV (sLayerBase l) 4)] ++ c.1 ++ L.1, L.2.1, L.2.2)

/-- The bottom layer (`G:4069-4070`): `a0_b`, `key_b`, signing the FORS key. -/
def sLayerB : List Stmt × Nat × V := sLayerAt 0 sA0B sKeyB sForsPk

/-- `a0_m = SP_LAYER_MUL + tree_mid · 2^120 + lvals[24] · 2^112`, `key_m = lvals[8] · 2^56`
(`G:4071-4072`), from `n8713`. -/
def sMidAddrs : List Stmt :=
  [cst 8713 (lit (2 ^ 24)), cst 8714 (lit (2 ^ 120)), mulS (.n 8715) sTreeMid (.n 8714),
    addS (.n 8716) (.n 8713) (.n 8715), cst 8717 (lit (2 ^ 112)),
    mulS (.n 8718) (sLVal 24) (.n 8717), addS (sA0Of 1) (.n 8716) (.n 8718),
    cst 8720 (lit (2 ^ 56)), mulS (sA1Of 1) (sLVal 8) (.n 8720)]

/-- The middle layer (`G:4073-4074`), signing the bottom root. -/
def sLayerM : List Stmt × Nat × V := sLayerAt 1 (sA0Of 1) (sA1Of 1) sLayerB.2.2

/-- `key_t = tree_mid · 2^56 + lvals[24] · 2^48` (`G:4076`), from `n8979`, then `a0_t = 2 ·
SP_LAYER_MUL` (`G:4075`): a constant, bound to a value as `sp_layer`'s argument. -/
def sTopAddrs : List Stmt :=
  [cst 8979 (lit (2 ^ 56)), mulS (.n 8980) sTreeMid (.n 8979), cst 8981 (lit (2 ^ 48)),
    mulS (.n 8982) (sLVal 24) (.n 8981), addS (sA1Of 2) (.n 8980) (.n 8982),
    cst 8984 (lit (2 ^ 25))]

/-- The top layer (`G:4077-4078`), signing the middle root. -/
def sLayerT : List Stmt × Nat × V := sLayerAt 2 (sA0Of 2) (sA1Of 2) sLayerM.2.2

/-! ## The body -/

/-- The statements after the digest block: FORS, the three layers, `root[0] == pk_root`
(`G:4079`). -/
def sAfterDigest : List Stmt :=
  sForsAddrs ++ sForsB.1 ++ sLayerB.1 ++ sMidAddrs ++ sLayerM.1 ++ sTopAddrs ++ sLayerT.1 ++
    [.atom (.assertEq sLayerT.2.2 sRoot), .ret []]

/-- The body of `verify_sig_lean_sphincs`. -/
def sBody : List Stmt := sDigestBlock ++ sAfterDigest

end
end LeanVM.Guest.B1.Sig
