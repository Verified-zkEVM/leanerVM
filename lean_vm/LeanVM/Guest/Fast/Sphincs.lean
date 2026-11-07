module

public import LeanVM.Guest.Fast.SpWots
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.Fast.FunctionNames
public import LeanVM.Guest.B1.Sig.Interface
public import LeanVM.Guest.B1.Sig.SphincsSig
public import LeanVM.Guest.B1.Sig.Bytes
public import LeanVM.Cost.Rules

/-!
# leanSPHINCS's signature reader, computable

`verify_sig_lean_sphincs` (`Data.core20`, compiled function `21`, its template
`B1/Sig/SphincsT.lean`, at leanVM 56a4109f) hints the randomizer, each FORS tree's secret and the
ordered children on its climb, each layer's counter and the ordered children on its path into its
own frame, at cells its body fixes, and calls `sp_wots` (`Data.core19`, function `20`) once a
layer, whose frame holds the layer's chain starts at cells its digit words select (`spStartAt`,
`Fast/SpWots.lean`). The reader takes `verify_sig_lean_sphincs`' valuation `σ` and the three
`sp_wots` frames `w0`, `w1`, `w2`:

* `forsOpeningA T σ c`: FORS tree `c`'s opening, its secret at `spForsBase c`, at each height
  `z` the hinted child the bit does not name (`sibN`), the pair's and the bit's cells off the
  tables `T.forsKid`, `T.forsBit` (row `c`, entry `z`);
* `layerA T σ w l layer`: layer `l`'s counter (the cell `sp_from_bytes` folds), its chain
  starts off `sp_wots`' frame `w` (`cwCellA` over `sp_wots`' tables), its path (the pairs' and
  bits' cells off `T.pathKid`, `T.pathBit`, row `l`);
* `sphincsSigOfA T σ w0 w1 w2`, its layers by `depFin3` (the compiler's dependent function of
  `Fin 3`); `spWotsArgs σ l`, `spWotsRets σ l`: the words of layer `l`'s call of `sp_wots`
  (`PK.seed`, the key's two address cells, the encoding's first cell; the leaf), by which the
  frame map finds its frame;
* **`sphincsSigOfN_eq`**: off the frame map re-keyed by index, the reader is B1's witness
  `sphincsSigOf` (`B1/Sig/SphincsSig.lean`): the template's positions checked by the kernel
  (`sForsPositions`, `sPathPositions`, `sLayerPositions`), the chain starts by
  `spStartAt_eq_cwCell`.

`SpTabs`, `spTabs`: the tables as arrays, built once by the caller.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Sig

@[expose] public section

/-- FORS tree `c`'s hinted pair at height `z` (`sForsKid c z`): row `c`, entry `z`. -/
def spForsKids : List (List Nat) := [
  [1405, 1438, 1465, 1492, 1519, 1546, 1573, 1600, 1627, 1654],
  [1704, 1737, 1764, 1791, 1818, 1845, 1872, 1899, 1926, 1953],
  [2003, 2036, 2063, 2090, 2117, 2144, 2171, 2198, 2225, 2252],
  [2302, 2335, 2362, 2389, 2416, 2443, 2470, 2497, 2524, 2551],
  [2601, 2634, 2661, 2688, 2715, 2742, 2769, 2796, 2823, 2850],
  [2900, 2933, 2960, 2987, 3014, 3041, 3068, 3095, 3122, 3149],
  [3199, 3232, 3259, 3286, 3313, 3340, 3367, 3394, 3421, 3448],
  [3498, 3531, 3558, 3585, 3612, 3639, 3666, 3693, 3720, 3747],
  [3797, 3830, 3857, 3884, 3911, 3938, 3965, 3992, 4019, 4046],
  [4096, 4129, 4156, 4183, 4210, 4237, 4264, 4291, 4318, 4345],
  [4395, 4428, 4455, 4482, 4509, 4536, 4563, 4590, 4617, 4644],
  [4694, 4727, 4754, 4781, 4808, 4835, 4862, 4889, 4916, 4943],
  [4993, 5026, 5053, 5080, 5107, 5134, 5161, 5188, 5215, 5242],
  [5292, 5325, 5352, 5379, 5406, 5433, 5460, 5487, 5514, 5541],
  [5591, 5624, 5651, 5678, 5705, 5732, 5759, 5786, 5813, 5840],
  [5890, 5923, 5950, 5977, 6004, 6031, 6058, 6085, 6112, 6139],
  [6189, 6222, 6249, 6276, 6303, 6330, 6357, 6384, 6411, 6438],
  [6488, 6521, 6548, 6575, 6602, 6629, 6656, 6683, 6710, 6737],
  [6787, 6820, 6847, 6874, 6901, 6928, 6955, 6982, 7009, 7036],
  [7086, 7119, 7146, 7173, 7200, 7227, 7254, 7281, 7308, 7335],
  [7385, 7418, 7445, 7472, 7499, 7526, 7553, 7580, 7607, 7634],
  [7684, 7717, 7744, 7771, 7798, 7825, 7852, 7879, 7906, 7933],
  [7983, 8016, 8043, 8070, 8097, 8124, 8151, 8178, 8205, 8232],
  [8282, 8315, 8342, 8369, 8396, 8423, 8450, 8477, 8504, 8531]]

/-- The bit `is_child` reads at FORS tree `c`'s height `z` (`sForsBit (10 c + z)`). -/
def spForsBits : List (List Nat) := [
  [65, 66, 51, 52, 53, 54, 55, 56, 57, 58],
  [71, 72, 73, 74, 59, 60, 61, 62, 63, 64],
  [77, 78, 79, 80, 81, 82, 67, 68, 69, 70],
  [83, 84, 85, 86, 87, 88, 89, 90, 75, 76],
  [105, 106, 91, 92, 93, 94, 95, 96, 97, 98],
  [111, 112, 113, 114, 99, 100, 101, 102, 103, 104],
  [117, 118, 119, 120, 121, 122, 107, 108, 109, 110],
  [123, 124, 125, 126, 127, 128, 129, 130, 115, 116],
  [145, 146, 131, 132, 133, 134, 135, 136, 137, 138],
  [151, 152, 153, 154, 139, 140, 141, 142, 143, 144],
  [157, 158, 159, 160, 161, 162, 147, 148, 149, 150],
  [163, 164, 165, 166, 167, 168, 169, 170, 155, 156],
  [185, 186, 171, 172, 173, 174, 175, 176, 177, 178],
  [191, 192, 193, 194, 179, 180, 181, 182, 183, 184],
  [197, 198, 199, 200, 201, 202, 187, 188, 189, 190],
  [203, 204, 205, 206, 207, 208, 209, 210, 195, 196],
  [225, 226, 211, 212, 213, 214, 215, 216, 217, 218],
  [231, 232, 233, 234, 219, 220, 221, 222, 223, 224],
  [237, 238, 239, 240, 241, 242, 227, 228, 229, 230],
  [243, 244, 245, 246, 247, 248, 249, 250, 235, 236],
  [265, 266, 251, 252, 253, 254, 255, 256, 257, 258],
  [271, 272, 273, 274, 259, 260, 261, 262, 263, 264],
  [277, 278, 279, 280, 281, 282, 267, 268, 269, 270],
  [283, 284, 285, 286, 287, 288, 289, 290, 275, 276]]

/-- Layer `l`'s hinted pair at path level `j` (`sPathKid l j`). -/
def spPathKids : List (List Nat) := [
  [8696, 8722, 8748, 8774, 8800, 8826, 8852, 8878],
  [8970, 8996, 9022, 9048, 9074, 9100, 9126, 9152],
  [9241, 9273, 9299, 9325, 9351, 9377, 9403, 9429, 9455, 9481]]

/-- The bit `is_child` reads at layer `l`'s level `j` (`sLeafBit (8 l + j)`). -/
def spPathBits : List (List Nat) := [
  [315, 316, 317, 318, 319, 320, 321, 322],
  [307, 308, 309, 310, 311, 312, 313, 314],
  [299, 300, 301, 302, 303, 304, 305, 306, 291, 292]]


/-- `verify_sig_lean_sphincs`' and `sp_wots`' tables, as arrays: the lanes of `g^k` (`gLanes`),
`sp_wots`' groups' selector cells and chain starts' tables, the FORS trees' and the layers' pairs
and bits. -/
structure SpTabs where
  lanes : List ℕ
  sel : Array ℕ
  first : Array (Array ℕ)
  rest : Array (Array ℕ)
  last : Array (Array ℕ)
  forsKid : Array (Array ℕ)
  forsBit : Array (Array ℕ)
  pathKid : Array (Array ℕ)
  pathBit : Array (Array ℕ)

/-- **The tables**, built from the literals. -/
def spTabs : SpTabs := ⟨gLanes, spSel.toArray, tabA spFirst, tabA spRest, tabA spLast,
  tabA spForsKids, tabA spForsBits, tabA spPathKids, tabA spPathBits⟩

/-- FORS tree `c`'s base: its secret's cell (`sForsBase`). -/
def spForsBase (c : ℕ) : ℕ := if c = 0 then 1381 else 1379 + 299 * c

/-- **FORS tree `c`'s opening**, off `verify_sig_lean_sphincs`' valuation. -/
def forsOpeningA (T : SpTabs) (σ : Val) (c : ℕ) : Sphincs.ForsTreeOpening :=
  ⟨cellVal (σ (.n (spForsBase c))),
    fun z ↦ cellVal (sibN σ (offAtA T.forsBit c z.val) (offAtA T.forsKid c z.val))⟩

/-- Layer `l`'s base (`sLayerBase`): its counter at `+ 36`, its encoding at `+ 46`, its leaf at
`+ 59`. -/
def spLayerBase (l : ℕ) : ℕ := if l = 0 then 8636 else if l = 1 then 8910 else 9181
def spCtr (l : ℕ) : ℕ := spLayerBase l + 36
def spEnc (l : ℕ) : ℕ := spLayerBase l + 46
def spLeaf (l : ℕ) : ℕ := spLayerBase l + 59

/-- Layer `l`'s key's address cells (`sA0Of`, `sA1Of`). -/
def spA0 (l : ℕ) : ℕ := if l = 0 then 1376 else if l = 1 then 8907 else 9180
def spA1 (l : ℕ) : ℕ := if l = 0 then 1378 else if l = 1 then 8909 else 9179

/-- **Layer `l`'s signature**: its counter's cell, its `sp_wots` frame `w`, its path's pairs and
bits (row `l` of the tables). -/
def layerA (T : SpTabs) (σ w : Val) (l : ℕ) (layer : Sphincs.Layer) :
    Sphincs.LayerSignature layer :=
  ⟨BitVec.ofNat 32 (beWordAt 0 (cellNat (σ (.n (spCtr l))))),
    fun i ↦ cellVal (w (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last w i.val))),
    fun j ↦ cellVal (sibN σ (offAtA T.pathBit l j.val) (offAtA T.pathKid l j.val))⟩

/-- Layer `l`'s call of `sp_wots`: its arguments (`PK.seed`, the key's two address cells, the
encoding's first cell) and its return (the leaf). -/
def spWotsArgs (σ : Val) (l : ℕ) : List E :=
  [σ (.n 2), σ (.n (spA0 l)), σ (.n (spA1 l)), σ (.n (spEnc l))]
def spWotsRets (σ : Val) (l : ℕ) : List E := [σ (.n (spLeaf l))]

/-- **The layers as the reader builds them** (`LeanVM.Cost.depFin3`, a dependent function of
`Fin 3`), encoded as the statement encodes a signature's layers: the array of their values
(`depFinEncoding`). Stated here, at `Fin 3`: `depFin3`'s domain is `Fin 3`, which instance search
does not unify with `Sphincs.Layer = Fin layerCount` (`layerCount` is not reducible), so neither
`depFinEncoding` nor the statement's encoding of a layer's signature is found for it; and
`Cost/Rules.lean`, where `depFin3` is, does not see the statement's schemes. -/
instance layersEncodingFin3 :
    LeanVM.Cost.MachineEncoding ((i : Fin 3) → Sphincs.LayerSignature i) :=
  @LeanVM.Cost.depFinEncoding 3 (fun i ↦ Sphincs.LayerSignature i)
    fun i ↦ LeanVM.Cost.instMachineEncodingLayerSignature_1 i

/-- **The leanSPHINCS signature `verify_sig_lean_sphincs` checks**, off its valuation `σ` and its
three `sp_wots` frames. -/
def sphincsSigOfA (T : SpTabs) (σ w0 w1 w2 : Val) : Sphincs.Signature :=
  ⟨cellVal (σ (.n 6)), fun c ↦ forsOpeningA T σ c.val,
    LeanVM.Cost.depFin3 (layerA T σ w0 0 0) (layerA T σ w1 1 1) (layerA T σ w2 2 2)⟩

/-- **The signature off the frame map keyed by index**: `sp_wots` is function `20`. -/
def sphincsSigOfN (σ : Val) (Vn : NFrames) : Sphincs.Signature :=
  sphincsSigOfA spTabs σ (Vn 20 (spWotsArgs σ 0) (spWotsRets σ 0))
    (Vn 20 (spWotsArgs σ 1) (spWotsRets σ 1)) (Vn 20 (spWotsArgs σ 2) (spWotsRets σ 2))

/-! ## The reader is the witness's -/

/-- The template's positions (`SphincsT.lean`, `SphincsSig.lean`): each FORS tree's secret, and
at each height its hinted pair and the bit `is_child` reads. -/
theorem sForsPositions : ∀ c < 24, sForsBase c = spForsBase c ∧ ∀ z < 10,
    offAt spForsKids c z = sForsKid c z ∧ sForsBit (10 * c + z) = .n (offAt spForsBits c z) := by
  decide +kernel

/-- The template's positions: each layer's path's hinted pairs and bits. -/
theorem sPathPositions : ∀ l < 3, ∀ j < 10, l = 2 ∨ j < 8 →
    offAt spPathKids l j = sPathKid l j ∧ sLeafBit (sOffOf l + j) = .n (offAt spPathBits l j) := by
  decide +kernel

/-- The template's positions: each layer's call, counter. -/
theorem sLayerPositions : ∀ l < 3, sA0Of l = .n (spA0 l) ∧ sA1Of l = .n (spA1 l) ∧
    sEncOf l = .n (spEnc l) ∧ sLeafOf l = .n (spLeaf l) ∧ sCtrOf l = .n (spCtr l) := by
  decide +kernel

theorem forsTreeOpening_ext {a b : Sphincs.ForsTreeOpening} (h1 : a.secret = b.secret)
    (h2 : a.path = b.path) : a = b := by
  cases a; cases b; cases h1; cases h2; rfl

theorem forsOpeningA_eq (σ : Val) {c : ℕ} (hc : c < 24) :
    forsOpeningA spTabs σ c = sForsOpeningOf σ c := by
  obtain ⟨hb, hz⟩ := sForsPositions c hc
  have e1 : spTabs.forsBit = tabA spForsBits := rfl
  have e2 : spTabs.forsKid = tabA spForsKids := rfl
  apply forsTreeOpening_ext
  · show cellVal (σ (.n (spForsBase c))) = cellVal (σ (.n (sForsBase c)))
    rw [hb]
  funext z
  show cellVal (sibN σ (offAtA spTabs.forsBit c z.val) (offAtA spTabs.forsKid c z.val)) =
    cellVal (siblingOf σ (sForsBit (10 * c + z.val)) (sForsKid c z.val))
  rw [e1, e2]
  obtain ⟨hk, hbit⟩ := hz z.val (by have := z.isLt; simpa [Sphincs.forsTreeHeight] using this)
  rw [offAtA_tabA, offAtA_tabA, hk, hbit]
  rfl

/-- `sp_wots`' tables off arrays read the chain starts `sChainValuesOf` reads. -/
theorem layerChains_eq (w : Val) (i : Sphincs.ChainIndex) :
    cellVal (w (.n (cwCellA spTabs.lanes 21 spTabs.sel spTabs.first spTabs.rest spTabs.last w
      i.val))) = sChainValuesOf w i := by
  show _ = cellVal (w (spRen (spStartAt (spK w) i.val)))
  rw [spStartAt_eq_cwCell w i.isLt]
  exact congrArg (fun k ↦ cellVal (w (.n k))) (cwCellA_eq 21 spSel spFirst spRest spLast w i.val)

theorem layerSignature_ext {l : Sphincs.Layer} {a b : Sphincs.LayerSignature l}
    (h1 : a.counter = b.counter) (h2 : a.chainValues = b.chainValues)
    (h3 : a.authenticationPath = b.authenticationPath) : a = b := by
  cases a; cases b; cases h1; cases h2; cases h3; rfl

theorem signature_ext {a b : Sphincs.Signature} (h1 : a.randomizer = b.randomizer)
    (h2 : a.forsOpening = b.forsOpening) (h3 : a.layers = b.layers) : a = b := by
  cases a; cases b; cases h1; cases h2; cases h3; rfl

theorem layerA_eq (σ : Val) (V : FrameMap) (l : Sphincs.Layer) :
    layerA spTabs σ (V "sp_wots" (spWotsArgs σ l.val) (spWotsRets σ l.val)) l.val l =
      sLayerOf σ V l := by
  obtain ⟨ha, hb, he, hf, hc⟩ := sLayerPositions l.val l.isLt
  apply layerSignature_ext
  · simp only [layerA, sLayerOf, hc]
    rfl
  · funext i
    simp only [layerA, sLayerOf, spWotsArgs, spWotsRets, layerChains_eq, ha, hb, he, hf, sPP]
  · funext j
    have hj := j.isLt
    unfold Sphincs.layerHeight at hj
    obtain ⟨hk, hbit⟩ := sPathPositions l.val l.isLt j.val (by split at hj <;> omega)
      (by split at hj <;> omega)
    have e1 : spTabs.pathBit = tabA spPathBits := rfl
    have e2 : spTabs.pathKid = tabA spPathKids := rfl
    simp only [layerA, sLayerOf, e1, e2, offAtA_tabA, hk, hbit, siblingOf, sibN]
    rfl

/-- **The readers are equal**: off the frame map re-keyed by index, the reader is the witness
`sphincsSigOf` (`B1/Sig/SphincsSig.lean`). -/
theorem sphincsSigOfN_eq (σ : Val) (V : FrameMap) :
    sphincsSigOfN σ (fun k ↦ V (decoderFunctionName k)) = sphincsSigOf σ V := by
  apply signature_ext
  · rfl
  · exact funext fun c ↦ forsOpeningA_eq σ c.isLt
  · funext l
    simp only [sphincsSigOfN, sphincsSigOfA, sphincsSigOf, name_sp_wots]
    match l with
    | ⟨0, _⟩ => exact layerA_eq σ V 0
    | ⟨1, _⟩ => exact layerA_eq σ V 1
    | ⟨2, _⟩ => exact layerA_eq σ V 2

end
end LeanVM.Guest.Fast
