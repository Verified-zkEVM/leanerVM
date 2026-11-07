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
`B1/Sig/SphincsT.lean`, at leanVM 834e6614) hints the randomizer, each FORS tree's secret and the
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
  [1746, 1779, 1806, 1833, 1860, 1887, 1914, 1941, 1968, 1995],
  [2045, 2078, 2105, 2132, 2159, 2186, 2213, 2240, 2267, 2294],
  [2344, 2377, 2404, 2431, 2458, 2485, 2512, 2539, 2566, 2593],
  [2643, 2676, 2703, 2730, 2757, 2784, 2811, 2838, 2865, 2892],
  [2942, 2975, 3002, 3029, 3056, 3083, 3110, 3137, 3164, 3191],
  [3241, 3274, 3301, 3328, 3355, 3382, 3409, 3436, 3463, 3490],
  [3540, 3573, 3600, 3627, 3654, 3681, 3708, 3735, 3762, 3789],
  [3839, 3872, 3899, 3926, 3953, 3980, 4007, 4034, 4061, 4088],
  [4138, 4171, 4198, 4225, 4252, 4279, 4306, 4333, 4360, 4387],
  [4437, 4470, 4497, 4524, 4551, 4578, 4605, 4632, 4659, 4686],
  [4736, 4769, 4796, 4823, 4850, 4877, 4904, 4931, 4958, 4985],
  [5035, 5068, 5095, 5122, 5149, 5176, 5203, 5230, 5257, 5284],
  [5334, 5367, 5394, 5421, 5448, 5475, 5502, 5529, 5556, 5583],
  [5633, 5666, 5693, 5720, 5747, 5774, 5801, 5828, 5855, 5882],
  [5932, 5965, 5992, 6019, 6046, 6073, 6100, 6127, 6154, 6181],
  [6231, 6264, 6291, 6318, 6345, 6372, 6399, 6426, 6453, 6480],
  [6530, 6563, 6590, 6617, 6644, 6671, 6698, 6725, 6752, 6779],
  [6829, 6862, 6889, 6916, 6943, 6970, 6997, 7024, 7051, 7078],
  [7128, 7161, 7188, 7215, 7242, 7269, 7296, 7323, 7350, 7377],
  [7427, 7460, 7487, 7514, 7541, 7568, 7595, 7622, 7649, 7676],
  [7726, 7759, 7786, 7813, 7840, 7867, 7894, 7921, 7948, 7975],
  [8025, 8058, 8085, 8112, 8139, 8166, 8193, 8220, 8247, 8274],
  [8324, 8357, 8384, 8411, 8438, 8465, 8492, 8519, 8546, 8573],
  [8623, 8656, 8683, 8710, 8737, 8764, 8791, 8818, 8845, 8872]]

/-- The bit `is_child` reads at FORS tree `c`'s height `z` (`sForsBit (10 c + z)`). -/
def spForsBits : List (List Nat) := [
  [406, 407, 392, 393, 394, 395, 396, 397, 398, 399],
  [412, 413, 414, 415, 400, 401, 402, 403, 404, 405],
  [418, 419, 420, 421, 422, 423, 408, 409, 410, 411],
  [424, 425, 426, 427, 428, 429, 430, 431, 416, 417],
  [446, 447, 432, 433, 434, 435, 436, 437, 438, 439],
  [452, 453, 454, 455, 440, 441, 442, 443, 444, 445],
  [458, 459, 460, 461, 462, 463, 448, 449, 450, 451],
  [464, 465, 466, 467, 468, 469, 470, 471, 456, 457],
  [486, 487, 472, 473, 474, 475, 476, 477, 478, 479],
  [492, 493, 494, 495, 480, 481, 482, 483, 484, 485],
  [498, 499, 500, 501, 502, 503, 488, 489, 490, 491],
  [504, 505, 506, 507, 508, 509, 510, 511, 496, 497],
  [526, 527, 512, 513, 514, 515, 516, 517, 518, 519],
  [532, 533, 534, 535, 520, 521, 522, 523, 524, 525],
  [538, 539, 540, 541, 542, 543, 528, 529, 530, 531],
  [544, 545, 546, 547, 548, 549, 550, 551, 536, 537],
  [566, 567, 552, 553, 554, 555, 556, 557, 558, 559],
  [572, 573, 574, 575, 560, 561, 562, 563, 564, 565],
  [578, 579, 580, 581, 582, 583, 568, 569, 570, 571],
  [584, 585, 586, 587, 588, 589, 590, 591, 576, 577],
  [606, 607, 592, 593, 594, 595, 596, 597, 598, 599],
  [612, 613, 614, 615, 600, 601, 602, 603, 604, 605],
  [618, 619, 620, 621, 622, 623, 608, 609, 610, 611],
  [624, 625, 626, 627, 628, 629, 630, 631, 616, 617]]

/-- Layer `l`'s hinted pair at path level `j` (`sPathKid l j`). -/
def spPathKids : List (List Nat) := [
  [9037, 9063, 9089, 9115, 9141, 9167, 9193, 9219],
  [9311, 9337, 9363, 9389, 9415, 9441, 9467, 9493],
  [9582, 9614, 9640, 9666, 9692, 9718, 9744, 9770, 9796, 9822]]

/-- The bit `is_child` reads at layer `l`'s level `j` (`sLeafBit (8 l + j)`). -/
def spPathBits : List (List Nat) := [
  [656, 657, 658, 659, 660, 661, 662, 663],
  [648, 649, 650, 651, 652, 653, 654, 655],
  [640, 641, 642, 643, 644, 645, 646, 647, 632, 633]]


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
def spForsBase (c : ℕ) : ℕ := if c = 0 then 1722 else 1720 + 299 * c

/-- **FORS tree `c`'s opening**, off `verify_sig_lean_sphincs`' valuation. -/
def forsOpeningA (T : SpTabs) (σ : Val) (c : ℕ) : Sphincs.ForsTreeOpening :=
  ⟨cellVal (σ (.n (spForsBase c))),
    fun z ↦ cellVal (sibN σ (offAtA T.forsBit c z.val) (offAtA T.forsKid c z.val))⟩

/-- Layer `l`'s base (`sLayerBase`): its counter at `+ 36`, its encoding at `+ 46`, its leaf at
`+ 59`. -/
def spLayerBase (l : ℕ) : ℕ := if l = 0 then 8977 else if l = 1 then 9251 else 9522
def spCtr (l : ℕ) : ℕ := spLayerBase l + 36
def spEnc (l : ℕ) : ℕ := spLayerBase l + 46
def spLeaf (l : ℕ) : ℕ := spLayerBase l + 59

/-- Layer `l`'s key's address cells (`sA0Of`, `sA1Of`). -/
def spA0 (l : ℕ) : ℕ := if l = 0 then 1717 else if l = 1 then 9248 else 9521
def spA1 (l : ℕ) : ℕ := if l = 0 then 1719 else if l = 1 then 9250 else 9520

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
  ⟨cellVal (σ (.n 347)), fun c ↦ forsOpeningA T σ c.val,
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
