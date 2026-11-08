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
`B1/Sig/SphincsT.lean`, at leanVM 5e3ade21) hints the randomizer, each FORS tree's secret and the
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
  [1428, 1457, 1483, 1509, 1535, 1561, 1587, 1613, 1639, 1665],
  [1709, 1738, 1766, 1792, 1818, 1844, 1870, 1896, 1922, 1948],
  [1994, 2023, 2051, 2079, 2105, 2131, 2157, 2183, 2209, 2235],
  [2281, 2310, 2338, 2366, 2392, 2418, 2444, 2470, 2496, 2522],
  [2568, 2597, 2625, 2653, 2681, 2707, 2733, 2759, 2785, 2811],
  [2857, 2886, 2914, 2942, 2970, 2996, 3022, 3048, 3074, 3100],
  [3146, 3175, 3203, 3231, 3259, 3285, 3311, 3337, 3363, 3389],
  [3435, 3464, 3492, 3520, 3548, 3574, 3600, 3626, 3652, 3678],
  [3724, 3753, 3781, 3809, 3837, 3865, 3891, 3917, 3943, 3969],
  [4015, 4044, 4072, 4100, 4128, 4156, 4182, 4208, 4234, 4260],
  [4306, 4335, 4363, 4391, 4419, 4447, 4473, 4499, 4525, 4551],
  [4597, 4626, 4654, 4682, 4710, 4738, 4764, 4790, 4816, 4842],
  [4888, 4917, 4945, 4973, 5001, 5029, 5055, 5081, 5107, 5133],
  [5179, 5208, 5236, 5264, 5292, 5320, 5346, 5372, 5398, 5424],
  [5470, 5499, 5527, 5555, 5583, 5611, 5637, 5663, 5689, 5715],
  [5761, 5790, 5818, 5846, 5874, 5902, 5928, 5954, 5980, 6006],
  [6052, 6081, 6109, 6137, 6165, 6193, 6221, 6247, 6273, 6299],
  [6345, 6374, 6402, 6430, 6458, 6486, 6514, 6540, 6566, 6592],
  [6638, 6667, 6695, 6723, 6751, 6779, 6807, 6833, 6859, 6885],
  [6931, 6960, 6988, 7016, 7044, 7072, 7100, 7126, 7152, 7178],
  [7224, 7253, 7281, 7309, 7337, 7365, 7393, 7419, 7445, 7471],
  [7517, 7546, 7574, 7602, 7630, 7658, 7686, 7712, 7738, 7764],
  [7810, 7839, 7867, 7895, 7923, 7951, 7979, 8005, 8031, 8057],
  [8103, 8132, 8160, 8188, 8216, 8244, 8272, 8298, 8324, 8350]]

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
  [8516, 8541, 8566, 8591, 8616, 8641, 8666, 8691],
  [8782, 8807, 8832, 8857, 8882, 8907, 8932, 8957],
  [9045, 9073, 9098, 9123, 9148, 9173, 9198, 9223, 9248, 9273]]

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

/-- FORS tree `c`'s base: its secret's cell (`sForsBase`), 21 values before its first pair. Tree
`k`'s width is `281 + 2·([k ≠ 0] + bitlen k)` (`sp_fors_at`'s constants, nonzero at the root for
`k ≠ 0` and at heights `2..9` while `k >>> (z - 2) ≠ 0`), so the bases are linear on each run of
equal bit lengths; arithmetic, as the decoder computes it cheaply (`sForsPositions` checks it). -/
def spForsBase (c : ℕ) : ℕ :=
  if c = 0 then 1407 else if c < 2 then 1688 else if c < 4 then 1973 + 287 * (c - 2)
  else if c < 8 then 2547 + 289 * (c - 4) else if c < 16 then 3703 + 291 * (c - 8)
  else 6031 + 293 * (c - 16)

/-- **FORS tree `c`'s opening**, off `verify_sig_lean_sphincs`' valuation. -/
def forsOpeningA (T : SpTabs) (σ : Val) (c : ℕ) : Sphincs.ForsTreeOpening :=
  ⟨cellVal (σ (.n (spForsBase c))),
    fun z ↦ cellVal (sibN σ (offAtA T.forsBit c z.val) (offAtA T.forsKid c z.val))⟩

/-- Layer `l`'s base (`sLayerBase`): its counter at `+ 36`, its encoding at `+ 46`, its leaf at
`+ 59`. -/
def spLayerBase (l : ℕ) : ℕ := if l = 0 then 8456 else if l = 1 then 8722 else 8985
def spCtr (l : ℕ) : ℕ := spLayerBase l + 36
def spEnc (l : ℕ) : ℕ := spLayerBase l + 46
def spLeaf (l : ℕ) : ℕ := spLayerBase l + 59

/-- Layer `l`'s key's address cells (`sA0Of`, `sA1Of`). -/
def spA0 (l : ℕ) : ℕ := if l = 0 then 1402 else if l = 1 then 8719 else 8984
def spA1 (l : ℕ) : ℕ := if l = 0 then 1404 else if l = 1 then 8721 else 8983

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
