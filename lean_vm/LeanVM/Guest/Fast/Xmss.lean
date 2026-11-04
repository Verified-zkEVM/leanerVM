module

public import LeanVM.Guest.Fast.XmssTables
public import LeanVM.Guest.Fast.LogG
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.B1.Sig.XmssSegT
public import LeanVM.Guest.B1.Sig.XmssScheme

/-!
# leanXMSS's signature reader, computable

The leanXMSS check is inline in `main`'s raw-signature loop `__loop2` (b7a8d0cb,
`B1/Sig/XmssSegT.lean`: `xSeg`, statements `9` to `321` of its body), so a signature is read off
an iteration's frame `σ`, at the cells the template gives:

* the leaf index from the four windows' dispatches: window `w`'s word `σ (.n (71 + w)) = g^k`,
  `k < 256` its `8` bits (`lxIndex`);
* per layer (bottom at base `88`, top at base `107749`): the randomizer `ρ`; chain `4p + r`'s
  start in the arm `k` group `p`'s dispatch takes (its digit word `σ (.n (dg + p)) = g^k`), at the
  group's base (`lxGroupBase`) plus its offset off the literal tables (`lxFold`, `lxRest`,
  `lxTail`, `Fast/XmssTables.lean`); level `l`'s sibling in the arm window `2·layer + l / 8` takes
  (`lxArmBase`, `lxSibAt`: arm `0` holds the window's output, the other arms one size).

`xmssSigOfA T σ` reads it off the tables `T` as arrays (`XmssTabs`: the lanes of `g^k` and the
chain-start tables), built once by the caller (`xmssTabs`); each dispatch's exponent is read once
off the lanes (`logGTWith`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

/-- leanXMSS's tables, as arrays: the lanes of `g^k` (`gLanes`), the chain starts of group `0`,
of groups `1` to `13` and of group `14` (`lxFold`, `lxRest`, `lxTail`). -/
structure XmssTabs where
  lanes : List ℕ
  fold : Array (Array ℕ)
  rest : Array (Array ℕ)
  tail : Array (Array ℕ)

/-- **leanXMSS's tables**, built from the literals. -/
def xmssTabs : XmssTabs := ⟨gLanes, tabA lxFold, tabA lxRest, tabA lxTail⟩

/-- Layer `layer`'s first value (`sLayer`'s base): `88`, then `107749`. -/
def lxLayerBase (layer : ℕ) : ℕ := if layer = 0 then 88 else 107749

/-- Layer `layer`'s randomizer cell (`sRho`). -/
def lxRhoCell (layer : ℕ) : ℕ := if layer = 0 then 88 else 107751

/-- Layer `layer`'s first digit word (`sCw`'s `dg`). -/
def lxDigitBase (layer : ℕ) : ℕ := if layer = 0 then 122 else 107774

/-- Group `p`'s base, the groups' first at `vb0`: group `0` takes `2973` values, the others
`2717`. -/
def lxGroupBase (vb0 p : ℕ) : ℕ := if p = 0 then vb0 else vb0 + 2973 + 2717 * (p - 1)

/-- Group `p`'s table of chain starts. -/
def lxGroupTab (T : XmssTabs) (p : ℕ) : Array (Array ℕ) :=
  if p = 0 then T.fold else if p < 14 then T.rest else T.tail

/-- The arms the `15` dispatches of a layer take, its digit words from `dg`. -/
def lxArmsTaken (lanes : List ℕ) (σ : Val) (dg : ℕ) : List ℕ :=
  (List.range 15).map fun p ↦ logGTWith lanes (σ (.n (dg + p))) 256

/-- Chain `i`'s start cell, the arms taken `ks`, the groups from `vb0`. -/
def lxChainCell (T : XmssTabs) (ks : List ℕ) (vb0 i : ℕ) : ℕ :=
  lxGroupBase vb0 (i / 4) + offAtA (lxGroupTab T (i / 4)) (i % 4) (ks.getD (i / 4) 0)

/-- Window `w`'s base (`lxWindowT`'s). -/
def lxWinBase (w : ℕ) : ℕ :=
  if w = 0 then 40133 else if w = 1 then 73941 else if w = 2 then 147785 else 181593

/-- Arm `k`'s base in window `w`: arm `0` from the window's base plus `5`, its size `143` (`128` in
the top window), the others `132` (`115`). -/
def lxArmBase (w k : ℕ) : ℕ :=
  lxWinBase w + 5 +
    (if k = 0 then 0 else (if w = 3 then 128 else 143) + (if w = 3 then 115 else 132) * (k - 1))

/-- Level `r`'s hinted sibling in arm `k` of window `w`: levels `18` values apart (`16` in the
top window), the sibling the level's third value (its first in the top window, the last level's
second elsewhere). -/
def lxSibAt (w k r : ℕ) : ℕ :=
  if w = 3 then lxArmBase w k + 16 * r
  else if r = 7 then lxArmBase w k + 18 * r + 2 else lxArmBase w k + 18 * r + 3

/-- **A layer's signature, off the tables `T`**: the windows' arms `kw` given. -/
def xPartA (T : XmssTabs) (kw : List ℕ) (layer : ℕ) (σ : Val) : LeanXmss.LayerSignature :=
  let ks := lxArmsTaken T.lanes σ (lxDigitBase layer)
  ⟨xv (σ (.n (lxRhoCell layer))),
    fun i ↦ xv (σ (.n (lxChainCell T ks (lxDigitBase layer + 70) i.val))),
    fun l ↦ xv (σ (.n (lxSibAt (2 * layer + l.val / 8) (kw.getD (2 * layer + l.val / 8) 0)
      (l.val % 8))))⟩

/-- The leaf index from the windows' arms `kw` (`lxIndex`), below `2^32`. -/
def lxLeafOf (kw : List ℕ) : ℕ :=
  (kw.getD 0 0 + 256 * kw.getD 1 0 + 65536 * kw.getD 2 0 + 16777216 * kw.getD 3 0) % 2 ^ 32

theorem lxLeafOf_eq (kw : List ℕ) : lxLeafOf kw = lxIndex (fun w ↦ kw.getD w 0) % 2 ^ 32 := rfl

theorem lxLeafOf_lt (kw : List ℕ) :
    lxLeafOf kw < LeanXmss.lifetime :=
  Nat.mod_lt _ (by norm_num)

/-- **The leanXMSS signature `__loop2`'s iteration checks, off the tables `T`**, from its frame. -/
def xmssSigOfA (T : XmssTabs) (σ : Val) : LeanXmss.Signature :=
  let kw := (List.range 4).map fun w ↦ logGTWith T.lanes (σ (.n (71 + w))) 256
  ⟨⟨lxLeafOf kw, lxLeafOf_lt kw⟩, fun lay ↦ xPartA T kw lay.val σ⟩

/-- **The leanXMSS signature `__loop2`'s iteration checks**, off the tables built. -/
def xmssSigOfN (σ : Val) : LeanXmss.Signature := xmssSigOfA xmssTabs σ

end
end LeanVM.Guest.Fast
