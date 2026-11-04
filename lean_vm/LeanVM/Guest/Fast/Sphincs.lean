module

public import LeanVM.Guest.Fast.SpWots
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.Fast.FunctionNames
public import LeanVM.Guest.B1.Sig.Interface
public import LeanVM.Guest.B1.Sig.Bytes

/-!
# leanSPHINCS's signature reader, computable

`verify_sig_lean_sphincs` (`Data.core21`, its template `B1/Sig/SphincsT.lean`) hints the
randomizer, the FORS openings, the counters and the paths into its own frame, at cells its body
fixes, and calls `sp_wots` (`Data.core20`) once a layer, whose frame holds the layer's chain starts
at cells its digit words select (`spStartAt`, `Fast/SpWots.lean`). The reader takes
`verify_sig_lean_sphincs`' valuation `σ` and the three `sp_wots` frames `w0`, `w1`, `w2`:

* `forsOpeningA σ c`: FORS tree `c`'s opening, from its base `1225 + 233·c` (its secret, then nine
  levels of `23` cells, the hinted children at `+22`, the last two the tree's top nodes), each
  sibling the hinted child the bit does not name (`sibN`), the bit of the digest's field at
  `77 + 10·c` on;
* `layerA T σ w ctr path bit layer`: a layer's counter (the cell `sp_from_bytes` folds), its chain
  starts off `sp_wots`' frame `w` (`cwCellA` over `sp_wots`' tables `T`), its path (levels of `21`
  cells from `path`, the bits from `bit`);
* `sphincsSigOfA T σ w0 w1 w2`; `spWotsArgs σ l`, `spWotsRets σ l`: the words of layer `l`'s call
  of `sp_wots` (`P`, the key's address, the encoding's first cell; the leaf), by which the frame
  map finds its frame.

`SpTabs`, `spTabs`: `sp_wots`' tables as arrays, built once by the caller.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

/-- `sp_wots`' tables, as arrays: the lanes of `g^k` (`gLanes`), the groups' selector cells and the
chain starts' tables. -/
structure SpTabs where
  lanes : List ℕ
  sel : Array ℕ
  first : Array (Array ℕ)
  rest : Array (Array ℕ)
  last : Array (Array ℕ)

/-- **`sp_wots`' tables**, built from the literals. -/
def spTabs : SpTabs := ⟨gLanes, spSel.toArray, tabA spFirst, tabA spRest, tabA spLast⟩

/-- **FORS tree `c`'s opening**, off `verify_sig_lean_sphincs`' valuation. -/
def forsOpeningA (σ : Val) (c : ℕ) : Sphincs.ForsTreeOpening :=
  ⟨cellVal (σ (.n (1225 + 233 * c))),
    fun l ↦ cellVal (sibN σ (77 + 10 * c + l.val) (1247 + 233 * c + 23 * l.val))⟩

/-- **A layer's signature**: its counter's cell, its `sp_wots` frame `w`, its path's first level
and its first bit. -/
def layerA (T : SpTabs) (σ w : Val) (ctr path bit : ℕ) (layer : Sphincs.Layer) :
    Sphincs.LayerSignature layer :=
  ⟨BitVec.ofNat 32 (cellNat (σ (.n ctr))),
    fun i ↦ cellVal (w (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last w i.val))),
    fun l ↦ cellVal (sibN σ (bit + l.val) (path + 21 * l.val))⟩

/-- Layer `l`'s counter cell, path base and first bit. -/
def spCtr (l : ℕ) : ℕ := if l = 0 then 6868 else if l = 1 then 7201 else 7425
def spPath (l : ℕ) : ℕ := if l = 0 then 6998 else if l = 1 then 7221 else 7445
def spBit (l : ℕ) : ℕ := 51 + 8 * l

/-- Layer `l`'s call of `sp_wots`: its arguments (`P`, the key's address, the encoding's first
cell) and its return (the leaf). -/
def spWotsArgs (σ : Val) (l : ℕ) : List E :=
  [σ (.n 2), σ (.n (if l = 0 then 6826 else if l = 1 then 6827 else 6829)),
    σ (.n (if l = 0 then 6984 else if l = 1 then 7207 else 7431))]
def spWotsRets (σ : Val) (l : ℕ) : List E :=
  [σ (.n (if l = 0 then 6997 else if l = 1 then 7220 else 7444))]

/-- **The leanSPHINCS signature `verify_sig_lean_sphincs` checks**, off its valuation `σ` and its
three `sp_wots` frames. -/
def sphincsSigOfA (T : SpTabs) (σ w0 w1 w2 : Val) : Sphincs.Signature :=
  ⟨cellVal (σ (.n 3)), fun c ↦ forsOpeningA σ c.val, fun layer ↦
    layerA T σ (if layer.val = 0 then w0 else if layer.val = 1 then w1 else w2)
      (spCtr layer.val) (spPath layer.val) (spBit layer.val) layer⟩

/-- **The signature off the frame map keyed by index**: `sp_wots` is function `21`. -/
def sphincsSigOfN (σ : Val) (Vn : NFrames) : Sphincs.Signature :=
  sphincsSigOfA spTabs σ (Vn 21 (spWotsArgs σ 0) (spWotsRets σ 0))
    (Vn 21 (spWotsArgs σ 1) (spWotsRets σ 1)) (Vn 21 (spWotsArgs σ 2) (spWotsRets σ 2))

end
end LeanVM.Guest.Fast
