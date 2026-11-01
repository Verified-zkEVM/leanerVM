module

public import LeanVM.Guest.Fast.XmssTablesCheck
public import LeanVM.Guest.Fast.Wots
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.B1.Sig.XmssSound

/-!
# leanXMSS's signature reader, computable

`xmssSigOf σ` (`B1/Sig/XmssSound.lean`) reads the signature `verify_lean_xmss` checks off its
valuation `σ`, at cells the template generators compute (`cwStart` over a `WotsT`, `kMsg`,
`merkleT`) and through a classical exponent search (`logG`). `xmssSigOfN σ` reads the same cells
off the literal tables of `Fast/XmssTables.lean` and searches the exponents through `logGT`;
`xmssSigOfN_eq`: they are equal.

* `bitsN σ base n`: the integer of the `n` bits from cell `base` (`bitsOf`);
* `xPartN rho bitBase sel path σ`: a layer's signature, from its randomizer cell, its first bit,
  its codeword groups' selector cells and its path bases (`xPart`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

/-- The integer of the `n` bits from cell `base`, the cell holding `1` a set bit (`bitsOf`). -/
def bitsN (σ : Val) (base : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bitsN σ base n + 2 ^ n * (decide (σ (.n (base + n)) = 1)).toNat

theorem bitsOf_eq (σ : Val) (base : ℕ) : ∀ n, bitsOf σ base n = bitsN σ base n
  | 0 => rfl
  | n + 1 => by
      rw [bitsN, ← bitsOf_eq σ base n]
      rfl

/-- **A layer's signature**, from its randomizer cell, its first bit, its codeword groups'
selector cells and its path bases (`xPart`). -/
def xPartN (rho bitBase : ℕ) (sel path : List ℕ) (σ : Val) : LeanXmss.LayerSignature :=
  ⟨xv (σ (.n rho)), fun i ↦ xv (σ (.n (cwCell 19 sel xFirst xRest xLast σ i.val))),
    fun l ↦ xv (sibN σ (bitBase + l.val) (path.getD l.val 0))⟩

theorem bitsN_lt (σ : Val) : bitsN σ 2 32 < 2 ^ (LeanXmss.numLayers * LeanXmss.layerHeight) := by
  rw [← bitsOf_eq]; exact xLeaf_lt σ

/-- **The leanXMSS signature `verify_lean_xmss` checks**, read off its valuation (`xmssSigOf`). -/
def xmssSigOfN (σ : Val) : LeanXmss.Signature :=
  ⟨⟨bitsN σ 2 32, bitsN_lt σ⟩, fun lay ↦
    if lay.val = 0 then xPartN 196 2 xSel0 xPath0 σ else xPartN 12604 18 xSel1 xPath1 σ⟩

/-! ## Equal to the original -/

theorem xPart0_eq (σ : Val) : xPart 0 196 σ = xPartN 196 2 xSel0 xPath0 σ := by
  have hc (i : LeanXmss.ChainIndex) : cwStart (xW 0 196) 19 (xA 0 196 + 6) σ i.val =
      .n (cwCell 19 xSel0 xFirst xRest xLast σ i.val) :=
    cwStart_eq_cwCell (W := xW 0 196) (G := 19) (b := 230) xSel0_eq xTabs (by norm_num) σ
      (by have := i.isLt; simp only [LeanXmss.numChains] at this; omega)
  have hp (l : Fin LeanXmss.layerHeight) :
      mSib σ (xBitOf 0) l.val (mBase (xNodeOf 0) 0 l.val (xLeafK 0 196).2.1) =
        sibN σ (2 + l.val) (xPath0.getD l.val 0) := by
    have hl : l.val < 16 := l.isLt
    rw [xPath0_eq, getD_map_range hl]
    unfold mSib sibN xBitOf xBit
    rw [show 2 + (16 * 0 + l.val) = 2 + l.val by omega]
  simp only [xPart, xPartN, hc, hp, xRho, ↓reduceIte]

theorem xPart1_eq (σ : Val) : xPart 1 12602 σ = xPartN 12604 18 xSel1 xPath1 σ := by
  have hc (i : LeanXmss.ChainIndex) : cwStart (xW 1 12602) 19 (xA 1 12602 + 6) σ i.val =
      .n (cwCell 19 xSel1 xFirst xRest xLast σ i.val) :=
    cwStart_eq_cwCell (W := xW 1 12602) (G := 19) (b := 12627) xSel1_eq xTabs (by norm_num) σ
      (by have := i.isLt; simp only [LeanXmss.numChains] at this; omega)
  have hp (l : Fin LeanXmss.layerHeight) :
      mSib σ (xBitOf 1) l.val (mBase (xNodeOf 1) 0 l.val (xLeafK 1 12602).2.1) =
        sibN σ (18 + l.val) (xPath1.getD l.val 0) := by
    have hl : l.val < 16 := l.isLt
    rw [xPath1_eq, getD_map_range hl]
    unfold mSib sibN xBitOf xBit
    rw [show 2 + (16 * 1 + l.val) = 18 + l.val by omega]
  simp only [xPart, xPartN, hc, hp, xRho, one_ne_zero, ↓reduceIte]

/-- **The readers are equal.** -/
theorem xmssSigOfN_eq (σ : Val) : xmssSigOfN σ = xmssSigOf σ := by
  unfold xmssSigOfN xmssSigOf
  rw [LeanXmss.Signature.mk.injEq]
  refine ⟨Fin.ext (bitsOf_eq σ 2 32).symm, funext fun lay ↦ ?_⟩
  rw [xLayer0_end, ← xPart0_eq, ← xPart1_eq]
  by_cases h : lay.val = 0
  · have : lay = LeanXmss.bottomLayer := Fin.ext h
    rw [ite_eq_left h, ite_eq_left this]
  · have : lay ≠ LeanXmss.bottomLayer := fun e ↦ h (by rw [e]; rfl)
    rw [ite_eq_right h, ite_eq_right this]

end
end LeanVM.Guest.Fast
