/-
  LeanVM.Guest.B1.Sig.XmssSegCoreC

  A layer of leanXMSS's check inline in `__loop2`, after its message digest, completes, given the
  path windows' completeness (`LxWindowsC`), and reads the signature's layer back (`sPart_eq`).
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegLayerC
public import LeanVM.Guest.B1.Sig.XmssSegDigestC
public import LeanVM.Guest.B1.Sig.XmssSegWinSpec

/-!
# A layer after its digest, complete

* `LxWindowsC`: what the path windows' completeness establishes (`XmssSegPathC`): a layer's two
  windows complete from the leaf, the root canonical and the hinted siblings the given ones;
* `sCore_complete`: the step addresses, the codeword, the leaf and the two windows complete;
* `xVals`, `xSibs`, `sPart_eq`: the layer signature as cells, read back off the valuation;
* `digest_digits`, `layerRoot_decode`, `cellPairVal_cellOf128`: the scheme's side.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

attribute [local irreducible] kMsg sCodewordT lxWindowT

/-! ## The scheme's side -/

theorem canon_lit (N : Nat) : IsCanonical128 (lit N) := canon_word _ _

/-- **A canonical digest that decodes** is the literal of its `58` digits, which sum to `106`. -/
theorem digest_digits {x : E} {enc : LeanXmss.Encoding} (hx : IsCanonical128 x)
    (hd : LeanXmss.Codeword.decode (xv x) = some enc) :
    x = lit (∑ i ∈ Finset.range 58, (xv x).toNat / 4 ^ i % 4 * 4 ^ i) ∧
      ∑ i ∈ Finset.range 58, (xv x).toNat / 4 ^ i % 4 = 106 := by
  obtain ⟨-, hs, he⟩ := decode_some hd
  refine ⟨?_, hs⟩
  have he' : (xv x).toNat = ∑ i ∈ Finset.range 58, (xv x).toNat / 4 ^ i % 4 * 4 ^ i := he
  rw [← he']
  apply cellVal_inj hx (canon_lit _)
  rw [cellVal_lit]
  show cellVal x = BitVec.ofNat 128 (cellVal x).toNat
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cellPairVal_cellOf128 (m : HashSig.Message) :
    cellPairVal (cellOf128 (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128)) = m := by
  apply BitVec.eq_of_toNat_eq
  have hm : m.toNat < 2 ^ 256 := m.isLt
  rw [cellPairVal, BitVec.toNat_append, cellVal_cellOf128, cellVal_cellOf128, BitVec.extractLsb'_toNat,
    BitVec.extractLsb'_toNat, Nat.shiftLeft_eq, mul_comm, two_pow_mul_or (Nat.mod_lt _ (by positivity)),
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero, Nat.mod_eq_of_lt (a := m.toNat / 2 ^ 128) (by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa using hm)]
  exact Nat.div_add_mod _ _

/-- **A layer's root exists only when its message digest decodes.** -/
theorem layerRoot_decode {P : HashSig.PublicParameter} {lay : LeanXmss.Layer} {key : LeanXmss.KeyIndex}
    {M : HashSig.HashInput} {part : LeanXmss.LayerSignature} {r : HashSig.Digest}
    (h : @LeanXmss.Verification.layerRootWithHash Id _ ⟨Node.keccakBits⟩ P lay key M part = some r) :
    ∃ enc, LeanXmss.Codeword.decode
      (@LeanXmss.Verification.messageDigestWithHash Id _ ⟨Node.keccakBits⟩ P lay key M part.randomizer) =
        some enc := by
  rw [layerRoot_id, otsLeaf_id] at h
  cases hd : LeanXmss.Codeword.decode
      (@LeanXmss.Verification.messageDigestWithHash Id _ ⟨Node.keccakBits⟩ P lay key M part.randomizer) with
  | none => rw [hd] at h; simp at h
  | some enc => exact ⟨enc, rfl⟩

/-- A layer's chains' starts as cells. -/
def xVals (part : LeanXmss.LayerSignature) (i : Nat) : E :=
  if h : i < 58 then cellOf128 (part.chainValues ⟨i, h⟩) else 0

/-- A layer's siblings as cells. -/
def xSibs (part : LeanXmss.LayerSignature) (l : Nat) : E :=
  if h : l < 16 then cellOf128 (part.authenticationPath ⟨l, h⟩) else 0

theorem xVals_canon (part : LeanXmss.LayerSignature) (i : Nat) : IsCanonical128 (xVals part i) := by
  unfold xVals; split
  · exact isCanonical128_cellOf128 _
  · exact canon_zero

theorem xSibs_canon (part : LeanXmss.LayerSignature) (l : Nat) : IsCanonical128 (xSibs part l) := by
  unfold xSibs; split
  · exact isCanonical128_cellOf128 _
  · exact canon_zero

/-- **The valuation holds the layer's signature** when it holds its randomizer, its starts and its
siblings. -/
theorem sPart_eq {layer b : Nat} {σ : Val} {part : LeanXmss.LayerSignature}
    (hr : σ (sRho layer b) = cellOf128 part.randomizer)
    (hs : ∀ i < 58, σ (sStart (sW layer b) σ (sA layer b + 6) (sA layer b + 6 + 70) i) = xVals part i)
    (hp : ∀ l < 16, sSibAt σ layer b l = xSibs part l) :
    sPart layer b σ = part := by
  cases part with
  | mk r cv pa =>
    simp only [sPart, LeanXmss.LayerSignature.mk.injEq]
    refine ⟨by rw [hr]; exact cellVal_cellOf128 _, funext fun i => ?_, funext fun l => ?_⟩
    · have hi : i.val < 58 := i.isLt
      rw [hs i.val hi]
      simp only [xVals, hi, ↓reduceDIte]
      exact cellVal_cellOf128 _
    · have hl : l.val < 16 := l.isLt
      rw [hp l.val hl]
      simp only [xSibs, hl, ↓reduceDIte]
      exact cellVal_cellOf128 _

end
end LeanVM.Guest.B1.Sig
