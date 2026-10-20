/-
  LeanVM.Guest.B1.Sig.Xmss

  `verify_lean_xmss` (G:2386-2442) holds of a claim exactly when some signature verifies it.
-/

module

public import LeanVM.Guest.B1.Sig.XmssLayerW
public import LeanVM.Guest.B1.Sig.XmssData
public import LeanVM.Spec.Node

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1.Sig

@[expose] public section

/-- A claim's four cells (`claim_cells`): the key's root and parameter, the message's two
halves. -/
def claimCells (root parameter : BitVec 128) (message : BitVec 256) : Fin 4 → E :=
  ![cellOf root, cellOf parameter, cellOf (message.extractLsb' 0 128), cellOf (message.extractLsb' 128 128)]

/-- The words at `p` are the cells `cs`. -/
def ClaimAt (rd : Reader) (p : E) (cs : Fin 4 → E) : Prop := ∀ k : Fin 4, LoadHolds rd p k.val (cs k)

/-- **`verify_lean_xmss(claim)`**: the claim at the pointer is a leanXMSS key and a message that
some signature verifies under BLAKE2s. -/
def Meaning_verify_lean_xmss (rd : Reader) (args rets : List E) : Prop :=
  ∃ p, args = [p] ∧ rets = [] ∧ ∃ (pk : LeanXmss.PublicKey) (m : LeanXmss.Message),
    ClaimAt rd p (claimCells pk.root pk.parameter m) ∧ ∃ σ, Node.xmssVerify pk m σ = true

namespace Sig

theorem cells_lt (c0 c1 : E) : cellNat c0 + 2 ^ 128 * cellNat c1 < 2 ^ 256 := by
  have h0 := cellNat_lt c0
  have h1 : 2 ^ 128 * cellNat c1 ≤ 2 ^ 128 * (2 ^ 128 - 1) :=
    Nat.mul_le_mul_left _ (by have := cellNat_lt c1; omega)
  omega

theorem lo_ofNat (c0 c1 : E) :
    (BitVec.ofNat 256 (cellNat c0 + 2 ^ 128 * cellNat c1)).extractLsb' 0 128 = cellVal c0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, toNat_cellVal, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt (cells_lt c0 c1), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (cellNat_lt c0)]

theorem hi_ofNat (c0 c1 : E) :
    (BitVec.ofNat 256 (cellNat c0 + 2 ^ 128 * cellNat c1)).extractLsb' 128 128 = cellVal c1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, toNat_cellVal, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (cells_lt c0 c1), Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (cellNat_lt c0),
    Nat.zero_add, Nat.mod_eq_of_lt (cellNat_lt c1)]

/-- A message's bytes are its halves'. -/
theorem bytesLE_message {m : BitVec 256} {c0 c1 : E} (h0 : m.extractLsb' 0 128 = cellVal c0)
    (h1 : m.extractLsb' 128 128 = cellVal c1) :
    LeanXmss.bytesLE 32 m = cellBytes c0 ++ cellBytes c1 := by
  have e0 := congrArg BitVec.toNat h0
  have e1 := congrArg BitVec.toNat h1
  rw [BitVec.extractLsb'_toNat, toNat_cellVal, Nat.shiftRight_zero] at e0
  rw [BitVec.extractLsb'_toNat, toNat_cellVal, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by have := m.isLt; norm_num at this ⊢; omega))] at e1
  have hm : m.toNat = cellNat c0 + 256 ^ 16 * cellNat c1 := by
    have := Nat.mod_add_div m.toNat (2 ^ 128)
    rw [show (256 : Nat) ^ 16 = 2 ^ 128 by norm_num]
    omega
  rw [bytesLE_eq, hm, show (32 : Nat) = 16 + 16 from rfl,
    leBytes_add_mul _ _ _ _ (by have := cellNat_lt c0; norm_num at this ⊢; omega),
    cellBytes_eq_leBytes, cellBytes_eq_leBytes]

/-- A claim's cells, from canonical ones. -/
theorem claimCells_of {r pp c0 c1 : E} (hr : IsCanonical128 r) (hp : IsCanonical128 pp) (h0 : IsCanonical128 c0)
    (h1 : IsCanonical128 c1) :
    claimCells (xv r) (xpp pp) (BitVec.ofNat 256 (cellNat c0 + 2 ^ 128 * cellNat c1)) = ![r, pp, c0, c1] := by
  funext k
  fin_cases k
  · exact cellOf_cellVal hr
  · exact cellOf_cellVal hp
  · show cellOf _ = c0; rw [lo_ofNat]; exact cellOf_cellVal h0
  · show cellOf _ = c1; rw [hi_ofNat]; exact cellOf_cellVal h1

/-- The leaf index as the scheme's. -/
def leafOf (L : Nat) (h : L < 2 ^ 32) : LeanXmss.LeafIndex := ⟨L, h⟩

theorem keyAt_bottom_val (i : LeanXmss.LeafIndex) : (LeanXmss.keyAt i LeanXmss.bottomLayer).val = i.val := by
  simp [LeanXmss.keyAt, LeanXmss.bottomLayer]

theorem keyAt_top_val (i : LeanXmss.LeafIndex) : (LeanXmss.keyAt i LeanXmss.topLayer).val = i.val / 2 ^ 16 := by
  simp [LeanXmss.keyAt, LeanXmss.topLayer, LeanXmss.layerHeight]

/-! ## The signature, the key and the message, from the valuation -/

/-- The leaf index `verify_lean_xmss` hints: the value of its bit cells `n(3 + j)`. -/
def xmssLeafOf (σ : Val) : LeanXmss.LeafIndex := ⟨xLeafNat σ, xLeafNat_lt σ⟩

/-- The layer signatures `verify_lean_xmss` hints: each layer's randomizer, chain values and
siblings. -/
def xmssPartOf (σ : Val) (lay : LeanXmss.Layer) : LeanXmss.LayerSignature :=
  if lay = LeanXmss.bottomLayer then xPart 0 (139 + 16) (.n 128) (.n (139 + 14)) (.n 139) (xLeafNat σ) σ
  else xPart 1 ((xLayer 0 139 (.n 0)).2.1 + 10) (.n ((xLayer 0 139 (.n 0)).2.1 + 1))
    (.n ((xLayer 0 139 (.n 0)).2.1 + 8)) (.n ((xLayer 0 139 (.n 0)).2.1 + 2)) (xLeafNat σ / 2 ^ 16) σ

/-- **The signature `verify_lean_xmss` checks**, of the values it hints. -/
def xmssSigOf (σ : Val) : LeanXmss.Signature := ⟨xmssLeafOf σ, xmssPartOf σ⟩

/-- The key `verify_lean_xmss` checks against: the top layer's computed root (asserted equal to the
claim's first cell) and the parameter it loads. -/
def xmssPkOf (σ : Val) : LeanXmss.PublicKey :=
  ⟨xv (σ (xLayer 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2).2.2), xpp (σ (.n 1))⟩

/-- The message `verify_lean_xmss` checks: the two cells it loads, the first low. -/
def xmssMsgOf (σ : Val) : LeanXmss.Message :=
  BitVec.ofNat 256 (cellNat (σ (.n (139 + 3))) + 2 ^ 128 * cellNat (σ (.n (139 + 4))))

/-- **`verify_lean_xmss` is sound**, for the key, message and signature of its valuation. -/
theorem verify_lean_xmss_sound_w {rd : Reader} {C : CallRel} {σ : Val} {rets : List E}
    (h : Stmt.HoldsList C rd σ xBody False (fun rs => rs = rets)) :
    rets = [] ∧ ClaimAt rd (σ (.n 0)) (claimCells (xmssPkOf σ).root (xmssPkOf σ).parameter (xmssMsgOf σ)) ∧
      Node.xmssVerify (xmssPkOf σ) (xmssMsgOf σ) (xmssSigOf σ) = true := by
  simp only [xBody, holdsList_append] at h
  obtain ⟨hl1, hpre, h⟩ := xPrologue_sound_w h
  obtain ⟨hl3, hl4, hpp, hm0, hm1, hr0, h⟩ :=
    xLayer0_sound_w (inst := ⟨Node.blake2sBits⟩) xq_blake2s hpre
      (keyAt_bottom_val (xmssLeafOf σ)) h
  obtain ⟨-, hrc, hr1, h⟩ :=
    xLayer1_sound_w (inst := ⟨Node.blake2sBits⟩) xq_blake2s hpre (keyAt_top_val (xmssLeafOf σ)) h
  obtain ⟨hl0, heq, hret⟩ := h
  have heq : _ = _ := e_add_eq_zero_iff.mp heq
  set r0 := σ (xLayer 0 139 (.n 0)).2.2
  set r1 := σ (xLayer 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2).2.2
  set c0 := σ (.n (139 + 3))
  set c1 := σ (.n (139 + 4))
  refine ⟨hret.symm, ?_, ?_⟩
  · show ClaimAt rd (σ (.n 0)) (claimCells (xv r1) (xpp (σ (.n 1)))
      (BitVec.ofNat 256 (cellNat c0 + 2 ^ 128 * cellNat c1)))
    rw [claimCells_of hrc hpp hm0 hm1]
    intro k
    fin_cases k
    · show LoadHolds rd _ 0 r1; rw [heq]; exact hl0
    · exact hl1
    · exact hl3
    · exact hl4
  · refine (xmssVerify_iff _ _ _).mpr ⟨xv r0, ?_, ?_⟩
    · show @LeanXmss.Concrete.layerRoot Id _ ⟨Node.blake2sBits⟩ (xpp (σ (.n 1))) LeanXmss.bottomLayer
        (LeanXmss.keyAt (xmssLeafOf σ) LeanXmss.bottomLayer)
        (LeanXmss.bytesLE 32 (BitVec.ofNat 256 (cellNat c0 + 2 ^ 128 * cellNat c1)))
        (xmssPartOf σ LeanXmss.bottomLayer) = some (xv r0)
      rw [bytesLE_message (lo_ofNat c0 c1) (hi_ofNat c0 c1)]
      simpa [xmssPartOf] using hr0
    · show @LeanXmss.Concrete.layerRoot Id _ ⟨Node.blake2sBits⟩ (xpp (σ (.n 1))) LeanXmss.topLayer
        (LeanXmss.keyAt (xmssLeafOf σ) LeanXmss.topLayer) (LeanXmss.bytesLE 16 (xv r0))
        (xmssPartOf σ LeanXmss.topLayer) = some (xv r1)
      rw [bytesLE_xv]
      simpa [xmssPartOf, show LeanXmss.topLayer ≠ LeanXmss.bottomLayer by decide] using hr1

/-- **`verify_lean_xmss` is sound.** -/
theorem verify_lean_xmss_sound {rd : Reader} {C : CallRel} {σ : Val} {rets : List E}
    (h : Stmt.HoldsList C rd σ xBody False (fun rs => rs = rets)) :
    rets = [] ∧ ∃ (pk : LeanXmss.PublicKey) (m : LeanXmss.Message),
      ClaimAt rd (σ (.n 0)) (claimCells pk.root pk.parameter m) ∧ ∃ sig, Node.xmssVerify pk m sig = true :=
  let ⟨hr, hc, hv⟩ := verify_lean_xmss_sound_w h
  ⟨hr, _, _, hc, _, hv⟩

end Sig

end
end LeanVM.Guest.B1
