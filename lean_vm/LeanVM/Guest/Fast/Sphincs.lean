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

`verify_sig_lean_sphincs` (`Data.core21`, compiled function `22`, its template
`B1/Sig/SphincsT.lean`) hints the
randomizer, the FORS openings, the counters and the paths into its own frame, at cells its body
fixes, and calls `sp_wots` (`Data.core20`, function `21`) once a layer, whose frame holds the layer's chain starts
at cells its digit words select (`spStartAt`, `Fast/SpWots.lean`). The reader takes
`verify_sig_lean_sphincs`' valuation `σ` and the three `sp_wots` frames `w0`, `w1`, `w2`:

* `forsOpeningA σ c`: FORS tree `c`'s opening, from its base `1225 + 233·c` (its secret, then ten
  levels of `23` cells, the hinted children at `+22`, the last two the tree's top nodes), each
  sibling the hinted child the bit does not name (`sibN`), the bit of the digest's field at
  `77 + 10·c` on;
* `layerA T σ w ctr path bit layer`: a layer's counter (the cell `sp_from_bytes` folds), its chain
  starts off `sp_wots`' frame `w` (`cwCellA` over `sp_wots`' tables `T`), its path (levels of `21`
  cells from `path`, the bits from `bit`);
* `sphincsSigOfA T σ w0 w1 w2`, its layers by `depFin3` (the compiler's dependent function of
  `Fin 3`); `spWotsArgs σ l`, `spWotsRets σ l`: the words of layer `l`'s call of `sp_wots` (`P`,
  the key's address, the encoding's first cell; the leaf), by which the frame map finds its frame;
* **`sphincsSigOfN_eq`**: off the frame map re-keyed by index, the reader is B1's witness
  `sphincsSigOf` (`B1/Sig/SphincsSig.lean`): the template's positions checked by the kernel
  (`sForsBase_eq`, `sLayerPositions`), the chain starts by `spStartAt_eq_cwCell`.

`SpTabs`, `spTabs`: `sp_wots`' tables as arrays, built once by the caller.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Sig

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

/-- Layer `l`'s call of `sp_wots`: the key's address cell, the encoding's first cell, the leaf. -/
def spAt (l : ℕ) : ℕ := if l = 0 then 6826 else if l = 1 then 6827 else 6829
def spEnc (l : ℕ) : ℕ := if l = 0 then 6984 else if l = 1 then 7207 else 7431
def spLeaf (l : ℕ) : ℕ := if l = 0 then 6997 else if l = 1 then 7220 else 7444

/-- Layer `l`'s call of `sp_wots`: its arguments (`P`, the key's address, the encoding's first
cell) and its return (the leaf). -/
def spWotsArgs (σ : Val) (l : ℕ) : List E := [σ (.n 2), σ (.n (spAt l)), σ (.n (spEnc l))]
def spWotsRets (σ : Val) (l : ℕ) : List E := [σ (.n (spLeaf l))]

/-- **The leanSPHINCS signature `verify_sig_lean_sphincs` checks**, off its valuation `σ` and its
three `sp_wots` frames. -/
def sphincsSigOfA (T : SpTabs) (σ w0 w1 w2 : Val) : Sphincs.Signature :=
  ⟨cellVal (σ (.n 3)), fun c ↦ forsOpeningA σ c.val,
    LeanVM.Cost.depFin3 (layerA T σ w0 (spCtr 0) (spPath 0) (spBit 0) 0)
      (layerA T σ w1 (spCtr 1) (spPath 1) (spBit 1) 1) (layerA T σ w2 (spCtr 2) (spPath 2) (spBit 2) 2)⟩

/-- **The signature off the frame map keyed by index**: `sp_wots` is function `21`. -/
def sphincsSigOfN (σ : Val) (Vn : NFrames) : Sphincs.Signature :=
  sphincsSigOfA spTabs σ (Vn 21 (spWotsArgs σ 0) (spWotsRets σ 0))
    (Vn 21 (spWotsArgs σ 1) (spWotsRets σ 1)) (Vn 21 (spWotsArgs σ 2) (spWotsRets σ 2))

/-! ## The reader is the witness's -/

/-- The template's positions (`SphincsT.lean`, `SphincsSig.lean`): FORS tree `c`'s base. -/
theorem sForsBase_eq : ∀ c < 24, sForsBase c = 1225 + 233 * c := by decide +kernel

/-- The template's positions: each layer's call, counter, path and bits. -/
theorem sLayerPositions : ∀ l < 3, sAtOf l = .n (spAt l) ∧ sEncOf l = .n (spEnc l) ∧
    sLeafOf l = spLeaf l ∧ sCtrOf l = .n (spCtr l) ∧ spPath l = sLeafOf l + 1 ∧
    spBit l = 51 + sOffOf l := by
  decide +kernel

theorem forsOpeningA_eq (σ : Val) {c : ℕ} (hc : c < 24) : forsOpeningA σ c = sForsOpeningOf σ c := by
  have h1 : ∀ l : ℕ, 51 + (26 + 10 * c + l) = 77 + 10 * c + l := fun l ↦ by omega
  have h2 : ∀ l : ℕ, 1225 + 233 * c + 22 + 23 * l = 1247 + 233 * c + 23 * l := fun l ↦ by omega
  simp only [forsOpeningA, sForsOpeningOf, sForsBase_eq c hc, siblingOf, sibN, sBit, h1, h2]

/-- `sp_wots`' tables off arrays read the chain starts `spValues` reads. -/
theorem layerChains_eq (w : Val) (i : Sphincs.ChainIndex) :
    cellVal (w (.n (cwCellA spTabs.lanes 21 spTabs.sel spTabs.first spTabs.rest spTabs.last w i.val))) =
      spValues w i := by
  have hK : spDigitWord w = spK w := rfl
  show _ = cellVal (w (spStartAt (spDigitWord w) i.val))
  rw [hK, spStartAt_eq_cwCell w i.isLt]
  exact congrArg (fun k ↦ cellVal (w (.n k))) (cwCellA_eq 21 spSel spFirst spRest spLast w i.val)

theorem layerSignature_ext {l : Sphincs.Layer} {a b : Sphincs.LayerSignature l}
    (h1 : a.counter = b.counter) (h2 : a.chainValues = b.chainValues)
    (h3 : a.authenticationPath = b.authenticationPath) : a = b := by
  cases a; cases b; cases h1; cases h2; cases h3; rfl

theorem signature_ext {a b : Sphincs.Signature} (h1 : a.randomizer = b.randomizer)
    (h2 : a.forsOpening = b.forsOpening) (h3 : a.layers = b.layers) : a = b := by
  cases a; cases b; cases h1; cases h2; cases h3; rfl

theorem layerA_eq (σ : Val) (V : FrameMap) (l : Sphincs.Layer) :
    layerA spTabs σ (V "sp_wots" (spWotsArgs σ l.val) (spWotsRets σ l.val)) (spCtr l.val)
      (spPath l.val) (spBit l.val) l = sLayerOf σ V l := by
  obtain ⟨ha, he, hf, hc, hp, hb⟩ := sLayerPositions l.val l.isLt
  apply layerSignature_ext
  · simp only [layerA, sLayerOf, hc]
    rfl
  · funext i
    simp only [layerA, sLayerOf, spWotsArgs, spWotsRets, layerChains_eq, ha, he, hf, sPP]
  · funext j
    simp only [layerA, sLayerOf, hp, hb, hf, siblingOf, sibN, sBit, Nat.add_assoc]
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
