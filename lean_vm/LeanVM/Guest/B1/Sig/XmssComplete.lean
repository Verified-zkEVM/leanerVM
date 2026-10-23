/-
  LeanVM.Guest.B1.Sig.XmssComplete

  `verify_lean_xmss` is complete: for a claim held in its canonical cells and a signature that
  verifies it, the body holds of a valuation whose argument is the claim's pointer
  (`verify_lean_xmss_complete_holds`).
-/

module

public import LeanVM.Guest.B1.Sig.XmssLayersComplete

/-!
# `verify_lean_xmss`, complete

The valuation: the claim's pointer, `P`, the leaf index's bits, the key's root at the end; the
prologue, then each layer with the signature's randomizer, chains' starts and siblings, its digits
those of its message digest, which decodes since the signature verifies (`layerRoot_decode`).
Each layer's root is then read off the valuation by soundness (`xmss_sound0`, `xmss_sound1`): the
frame holds the signature (`xPart_eq`), so the roots are the scheme's, the top one the key's, and
the final check holds.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

attribute [local irreducible] kMsg codewordT merkleT xLayer

variable {C : CallRel} {rd : Reader}

/-! ## The scheme's side -/

theorem cellPairVal_cellOf128 (m : LeanXmss.Message) :
    cellPairVal (cellOf128 (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128)) = m := by
  apply BitVec.eq_of_toNat_eq
  have hm : m.toNat < 2 ^ 256 := m.isLt
  rw [cellPairVal, BitVec.toNat_append, cellVal_cellOf128, cellVal_cellOf128, BitVec.extractLsb'_toNat,
    BitVec.extractLsb'_toNat, Nat.shiftLeft_eq, mul_comm, two_pow_mul_or (Nat.mod_lt _ (by positivity)),
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero, Nat.mod_eq_of_lt (a := m.toNat / 2 ^ 128) (by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa using hm)]
  exact Nat.div_add_mod _ _

/-- **A layer's root exists only when its message digest decodes.** -/
theorem layerRoot_decode {P : LeanXmss.PublicParameter} {lay : LeanXmss.Layer} {key : LeanXmss.KeyIndex}
    {M : LeanXmss.HashInput} {part : LeanXmss.LayerSignature} {r : LeanXmss.Digest}
    (h : @LeanXmss.Concrete.layerRoot Id _ ⟨Node.keccakBits⟩ P lay key M part = some r) :
    ∃ enc, LeanXmss.Codeword.decode
      (@LeanXmss.Concrete.messageDigest Id _ ⟨Node.keccakBits⟩ P lay key M part.randomness) = some enc := by
  rw [layerRoot_id, otsLeaf_id] at h
  cases hd : LeanXmss.Codeword.decode
      (@LeanXmss.Concrete.messageDigest Id _ ⟨Node.keccakBits⟩ P lay key M part.randomness) with
  | none => rw [hd] at h; simp at h
  | some enc => exact ⟨enc, rfl⟩

/-- A layer's chains' starts as cells. -/
def xVals (part : LeanXmss.LayerSignature) (i : Nat) : E :=
  if h : i < 58 then cellOf128 (part.chainValues ⟨i, h⟩) else 0

/-- A layer's siblings as cells. -/
def xSibs (part : LeanXmss.LayerSignature) (l : Nat) : E :=
  if h : l < 16 then cellOf128 (part.path ⟨l, h⟩) else 0

theorem xVals_canon (part : LeanXmss.LayerSignature) (i : Nat) : IsCanonical128 (xVals part i) := by
  unfold xVals; split
  · exact isCanonical128_cellOf128 _
  · exact canon_zero

theorem xSibs_canon (part : LeanXmss.LayerSignature) (l : Nat) : IsCanonical128 (xSibs part l) := by
  unfold xSibs; split
  · exact isCanonical128_cellOf128 _
  · exact canon_zero

/-- **The frame holds the layer's signature** when it holds its randomizer, its digits, its starts
and its siblings. -/
theorem xPart_eq {layer b : Nat} {σ : Val} {part : LeanXmss.LayerSignature} {K : Nat → Nat}
    (hK : ∀ q ≤ 19, K q < 4 ^ cwN 19 q) (hr : σ (xRho layer b) = cellOf128 part.randomness)
    (hd : ∀ q ≤ 19, σ (.n (cwState (xW layer b) (xA layer b + 6) q).2.2) = ofK (gpow (K q)))
    (hs : ∀ i < 58, σ (cwPos (xW layer b) 19 (xA layer b + 6) K i) = xVals part i)
    (hp : ∀ l < 16, mSib σ (xBitOf layer) l (mBase (xNodeOf layer) 0 l (xLeafK layer b).2.1) = xSibs part l) :
    xPart layer b σ = part := by
  cases part with
  | mk r cv pa =>
    simp only [xPart, LeanXmss.LayerSignature.mk.injEq]
    refine ⟨by rw [hr]; exact cellVal_cellOf128 _, funext fun i => ?_, funext fun l => ?_⟩
    · have hi : i.val < 58 := i.isLt
      rw [cwStart_eq_cwPos hK hd (show i.val < 3 * 19 + 1 by omega), hs i.val hi]
      simp only [xVals, hi, ↓reduceDIte]
      exact cellVal_cellOf128 _
    · have hl : l.val < 16 := l.isLt
      rw [hp l.val hl]
      simp only [xSibs, hl, ↓reduceDIte]
      exact cellVal_cellOf128 _

/-! ## The template's side -/

theorem merkleT_out (pad : Nat) (pp : V) (bitOf : Nat → V) (nodeOf : Nat → Option V) (addrOf : Nat → Nat) :
    ∀ (m l : Nat) (cur : V) (b : Nat), 0 < m → ∃ j, (merkleT pad pp bitOf nodeOf addrOf m l cur b).2.2 = .n j ∧
      j < (merkleT pad pp bitOf nodeOf addrOf m l cur b).2.1
  | 0, _, _, _, h => absurd h (by omega)
  | m + 1, l, cur, b, _ => by
      have key : ∀ c, ∃ j, (merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 14)).2.2 = .n j ∧
          j < (merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 14)).2.1 := by
        intro c
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · exact ⟨c + 1, by simp [merkleT], by simp [merkleT]⟩
        · exact merkleT_out pad pp bitOf nodeOf addrOf m (l + 1) _ _ hm
      simp only [merkleT]
      split
      · exact key _
      · exact key _

theorem xPreSeq_nb : NumBelow 196 (Stmt.valsList xPrologue) := by
  rw [xPrologue_split, valsList_append]
  exact (xPreChecks_nb.mono (by norm_num)).append xPreSeq_ok.numBelow

/-! ## The valuation -/

/-- **The valuation the proof starts from**: the claim's pointer, `P`, the leaf index's bits and,
at the end of the layers, the key's root. -/
def xInit2 (p P : E) : Val := Function.update (Function.update (fun _ => (0 : E)) (.n 0) p) (.n 1) P

def xInit (p P Rt : E) (L e : Nat) : Val :=
  Function.update (updRun (xInit2 p P) 2 32 (fun j => if L.testBit j then 1 else 0)) (.n e) Rt

theorem xInit_low {p P Rt : E} {L e : Nat} (he : 34 ≤ e) :
    xInit p P Rt L e (.n 0) = p ∧ xInit p P Rt L e (.n 1) = P ∧
      (∀ j < 32, xInit p P Rt L e (.n (2 + j)) = if L.testBit j then 1 else 0) ∧ xInit p P Rt L e (.n e) = Rt := by
  have hb : ∀ k < 2, updRun (xInit2 p P) 2 32 (fun j => if L.testBit j then 1 else 0) (.n k) =
      xInit2 p P (.n k) := fun k hk => updRun_below _ 2 32 _ ⟨k, hk, rfl⟩
  refine ⟨?_, ?_, fun j hj => ?_, Function.update_self ..⟩
  · rw [xInit, Function.update_of_ne (by simp; omega), hb 0 (by norm_num), xInit2,
      Function.update_of_ne (by simp), Function.update_self]
  · rw [xInit, Function.update_of_ne (by simp; omega), hb 1 (by norm_num), xInit2, Function.update_self]
  · rw [xInit, Function.update_of_ne (by simp; omega), updRun_at _ 2 32 _ hj]

/-! ## Completeness -/

/-- **`verify_lean_xmss` is complete.** -/
theorem verify_lean_xmss_complete_holds : verify_lean_xmss_complete_Spec := by
  intro C rd p pk m sig hm hat hv
  obtain ⟨r0, h0, h1⟩ := (xmssVerify_iff pk m sig).mp hv
  obtain ⟨hldR, hldP, hldLo, hldHi⟩ := hat
  have hL : sig.leafIndex.val < 2 ^ 32 := sig.leafIndex.isLt
  have hfin : ∀ σ : Val, xLeaf σ = sig.leafIndex.val →
      (⟨xLeaf σ, xLeaf_lt σ⟩ : LeanXmss.LeafIndex) = sig.leafIndex := fun σ h => Fin.ext h
  -- the layers' ends
  have hE0 : 230 < (xLayer 0 196 (.n 0)).2.1 := by
    rw [xLayer_snd]; exact xCore_end 0 196 (by decide)
  have hE1 : (xLayer 0 196 (.n 0)).2.1 + 25 < (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.1 := by
    rw [xLayer_snd (layer := 1)]; exact xCore_end 1 _ (by show 211 ≤ _ + 19; omega)
  obtain ⟨jR0, eR0, hR0⟩ : ∃ j, (xLayer 0 196 (.n 0)).2.2 = .n j ∧ j < (xLayer 0 196 (.n 0)).2.1 := by
    rw [xLayer_snd]; exact merkleT_out _ _ _ _ _ 16 0 _ _ (by norm_num)
  obtain ⟨jR1, eR1, hR1⟩ : ∃ j, (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.2 = .n j ∧
      j < (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.1 := by
    rw [xLayer_snd]; exact merkleT_out _ _ _ _ _ 16 0 _ _ (by norm_num)
  -- the valuation
  set E0 := (xLayer 0 196 (.n 0)).2.1 with hE0def
  set R0 := (xLayer 0 196 (.n 0)).2.2 with hR0def
  set E1 := (xLayer 1 E0 R0).2.1 with hE1def
  set R1 := (xLayer 1 E0 R0).2.2 with hR1def
  obtain ⟨i0, i1, ibits, iE1⟩ := xInit_low (p := p) (P := cellOf128 pk.parameter) (Rt := cellOf128 pk.root)
    (L := sig.leafIndex.val) (e := E1) (by omega)
  generalize xInit p (cellOf128 pk.parameter) (cellOf128 pk.root) sig.leafIndex.val E1 = σ0 at i0 i1 ibits iE1
  -- the prologue and the bottom layer
  have hA : Completes C rd 34 E0 (xPrologue ++ (xLayer 0 196 (.n 0)).1) σ0
      (fun σ' => IsCanonical128 (σ' R0) ∧ ∀ σ'', AgreeBelow E0 σ' σ'' →
        σ'' (.n 196) = cellOf128 (sig.layers LeanXmss.bottomLayer).randomness ∧
        σ'' (.n 199) = cellOf128 (m.extractLsb' 0 128) ∧ σ'' (.n 200) = cellOf128 (m.extractLsb' 128 128) ∧
        xPart 0 196 σ'' = sig.layers LeanXmss.bottomLayer) := by
    refine Completes.append (m := 196) (by norm_num) (by omega) xPreSeq_nb
      (xPrologue_complete (C := C) (rd := rd) σ0 (by rw [i0, i1]; exact hldP)
        (fun j hj => by rw [ibits j hj]; split <;> simp [IsBit])) (fun σ1 he1 hp1 => ?_)
    obtain ⟨-, hpre⟩ := xPrologue_sound hp1
    have hag1 : AgreeBelow 34 σ0 σ1 := he1.agree
    have hb1 : ∀ j < 32, σ1 (.n (2 + j)) = if sig.leafIndex.val.testBit j then 1 else 0 := fun j hj => by
      rw [hag1.apply ⟨2 + j, by omega, rfl⟩]; exact ibits j hj
    have hleaf1 : xLeaf σ1 = sig.leafIndex.val := xLeaf_eq hL hb1
    have hP1 : σ1 (.n 1) = cellOf128 pk.parameter := by rw [hag1.apply ⟨1, by norm_num, rfl⟩]; exact i1
    have hp01 : σ1 (.n 0) = p := by rw [hag1.apply ⟨0, by norm_num, rfl⟩]; exact i0
    have hn0 : σ1 (xNode 0) = eOfNat sig.leafIndex.val := by
      rw [hpre.nodes 0 (by norm_num), hleaf1]; rfl
    -- the digest decodes
    obtain ⟨enc, hdec⟩ := layerRoot_decode h0
    have hM : LeanXmss.bytesLE 32 m = [cellOf128 (m.extractLsb' 0 128), cellOf128 (m.extractLsb' 128 128)].flatMap
        cellBytes := by
      calc LeanXmss.bytesLE 32 m = LeanXmss.bytesLE 32 (cellPairVal (cellOf128 (m.extractLsb' 0 128))
            (cellOf128 (m.extractLsb' 128 128))) := by rw [cellPairVal_cellOf128]
        _ = _ := by rw [bytesLE_cellPairVal]; simp
    have ha : cellBytes (σ1 (xNode 0) + word (tw 12) 0 0) = LeanXmss.tweakBytes
        (.message LeanXmss.bottomLayer (LeanXmss.keyAt sig.leafIndex LeanXmss.bottomLayer)) := by
      rw [hn0, ← xIdxNat_zero sig.leafIndex.val]
      exact xMsgAdr_bytes hL (by norm_num)
    have hmd := messageDigest_cells xq_keccak (pp := cellOf128 pk.parameter)
      (rho := cellOf128 (sig.layers LeanXmss.bottomLayer).randomness) ha hM
    rw [show xpp (cellOf128 pk.parameter) = pk.parameter from cellVal_cellOf128 _,
      show xv (cellOf128 (sig.layers LeanXmss.bottomLayer).randomness) =
        (sig.layers LeanXmss.bottomLayer).randomness from cellVal_cellOf128 _] at hmd
    rw [hmd] at hdec
    have hl0 := xLayer0_complete (C := C) (rd := rd) hm σ1 hpre (by rw [hP1]; exact isCanonical128_cellOf128 _)
      (isCanonical128_cellOf128 _) (isCanonical128_cellOf128 _) (isCanonical128_cellOf128 _)
      (by rw [hp01]; exact hldLo) (by rw [hp01]; exact hldHi) (enc := enc) (by rw [hP1]; exact hdec)
      (xVals (sig.layers LeanXmss.bottomLayer)) (xVals_canon _)
      (bits := fun l => sig.leafIndex.val.testBit (16 * 0 + l))
      (fun l hl => by simpa [xBitOf, xBit] using hb1 l (by omega))
      (sibs := xSibs (sig.layers LeanXmss.bottomLayer)) (fun l _ => xSibs_canon _ l)
    refine hl0.mono le_rfl le_rfl (fun σ' ⟨hc', hk⟩ => ⟨hc', fun σ'' hag => ?_⟩)
    obtain ⟨k196, k199, k200, kd, ks, kp⟩ := hk σ'' hag
    exact ⟨k196, k199, k200, xPart_eq (fun q _ => nDigits_lt 19 _ q) k196 kd ks kp⟩
  -- the top layer, from the bottom root the scheme's
  have hB : Completes C rd 34 E1 ((xPrologue ++ (xLayer 0 196 (.n 0)).1) ++ (xLayer 1 E0 R0).1) σ0
      (fun σ' => σ' R1 = cellOf128 pk.root) := by
    have hnb : NumBelow E0 (Stmt.valsList (xPrologue ++ (xLayer 0 196 (.n 0)).1)) := by
      rw [valsList_append]
      refine (xPreSeq_nb.mono (by omega)).append ?_
      rw [hE0def, xLayer_split, xLayer_snd]
      simp only [↓reduceIte]
      rw [valsList_append]
      have hcore := xCore_nb (layer := 0) (b := 196) (by decide) ⟨127, by decide, rfl⟩ ⟨211, by decide, rfl⟩
        (fun l hl => ⟨2 + l, by show 2 + l < 224; omega, by simp [xBitOf, xBit]⟩)
        (fun l nd h => by
          simp only [xNodeOf] at h
          split at h
          · cases h
          · cases h
            exact ⟨34 + 3 * (31 - (16 * 0 + l + 1)), by show _ < 224; omega, rfl⟩)
      have := xCore_end 0 196 (by decide)
      have hA0 : xA 0 196 = 224 := rfl
      rw [hA0] at this
      exact (xDigest0_nb.mono (by omega)).append hcore
    refine Completes.append (m := E0) (by omega) (by omega) hnb hA.withHolds
      (fun σ2 he2 ⟨⟨hc2, hk2⟩, hh2⟩ => ?_)
    obtain ⟨k196, k199, k200, kpart⟩ := hk2 σ2 (fun _ _ => rfl)
    have s0 := xmss_sound0 (C := C) (rd := rd) (rest := []) (next := True) (kret := fun _ => True)
      (by rw [List.append_nil]; exact hh2)
    obtain ⟨-, hpre2, hpad2, hroot0⟩ := s0
    have hag2 : AgreeBelow 34 σ0 σ2 := fun k hk => he2.agree k (by omega)
    have hb2 : ∀ j < 32, σ2 (.n (2 + j)) = if sig.leafIndex.val.testBit j then 1 else 0 := fun j hj => by
      rw [hag2.apply ⟨2 + j, by omega, rfl⟩]; exact ibits j hj
    have hleaf2 : xLeaf σ2 = sig.leafIndex.val := xLeaf_eq hL hb2
    have hP2 : σ2 (.n 1) = cellOf128 pk.parameter := by rw [hag2.apply ⟨1, by norm_num, rfl⟩]; exact i1
    -- the bottom root is the scheme's
    have hxpp : xpp (cellOf128 pk.parameter) = pk.parameter := cellVal_cellOf128 _
    simp only [hP2, hfin σ2 hleaf2, k199, k200, cellPairVal_cellOf128, kpart, hxpp] at hroot0
    have hr0 : xv (σ2 R0) = r0 := Option.some.inj (hroot0.symm.trans h0)
    -- the top layer's digest decodes
    obtain ⟨enc, hdec⟩ := layerRoot_decode h1
    have hn16 : σ2 (xNode 16) = eOfNat (sig.leafIndex.val >>> 16) := by
      rw [hpre2.nodes 16 (by norm_num), hleaf2]
    have hM : LeanXmss.bytesLE 16 r0 = [σ2 R0].flatMap cellBytes := by
      rw [← hr0, bytesLE_xv]; simp
    have ha : cellBytes (σ2 (xNode 16) + word lxTop 0 0 + word (tw 12) 0 0) = LeanXmss.tweakBytes
        (.message LeanXmss.topLayer (LeanXmss.keyAt sig.leafIndex LeanXmss.topLayer)) := by
      rw [hn16, xIdxNat_one hL]
      exact xMsgAdr_bytes hL (by norm_num)
    have hmd := messageDigest_cells xq_keccak (pp := cellOf128 pk.parameter)
      (rho := cellOf128 (sig.layers LeanXmss.topLayer).randomness) ha hM
    rw [show xpp (cellOf128 pk.parameter) = pk.parameter from cellVal_cellOf128 _,
      show xv (cellOf128 (sig.layers LeanXmss.topLayer).randomness) =
        (sig.layers LeanXmss.topLayer).randomness from cellVal_cellOf128 _] at hmd
    rw [hmd] at hdec
    have hl1 := xLayer1_complete (C := C) (rd := rd) (b := E0) (root := R0) (by omega) ⟨jR0, hR0, eR0⟩ hm σ2
      hpre2 hpad2 (by rw [hP2]; exact isCanonical128_cellOf128 _) hc2 (isCanonical128_cellOf128 _)
      (enc := enc) (by rw [hP2]; exact hdec)
      (xVals (sig.layers LeanXmss.topLayer)) (xVals_canon _)
      (bits := fun l => sig.leafIndex.val.testBit (16 * 1 + l))
      (fun l hl => by simpa [xBitOf, xBit, Nat.add_assoc] using hb2 (16 + l) (by omega))
      (sibs := xSibs (sig.layers LeanXmss.topLayer)) (fun l _ => xSibs_canon _ l)
    obtain ⟨σ3, he3, ⟨⟨hc3, hk3⟩, hh3⟩, hhl3⟩ := hl1.withHolds
    refine ⟨σ3, he3, ?_, hhl3⟩
    obtain ⟨k2, kd, ks, kp⟩ := hk3 σ3 (fun _ _ => rfl)
    have hag3 : AgreeBelow E0 σ2 σ3 := he3.agree
    have hpre3 : XPre σ3 := hpre2.congr (hag3.mono (by omega))
    have hpad3 : PadOK σ3 xPad := hpad2.congr (by simp [xPad]; omega) hag3
    have hleaf3 : xLeaf σ3 = sig.leafIndex.val := by
      rw [← hleaf2]
      unfold xLeaf bitsOf
      exact bitsVal_congr fun i hi => by rw [hag3.apply ⟨2 + i, by omega, rfl⟩]
    have hP3 : σ3 (.n 1) = cellOf128 pk.parameter := by rw [hag3.apply ⟨1, by omega, rfl⟩]; exact hP2
    have hR03 : σ3 R0 = σ2 R0 := by rw [eR0]; exact hag3.apply ⟨jR0, hR0, rfl⟩
    obtain ⟨-, hroot1⟩ := xmss_sound1 (C := C) (rd := rd) (rest := []) (next := True) (kret := fun _ => True)
      hpre3 hpad3 (by rw [List.append_nil]; exact hh3)
    simp only [hP3, hfin σ3 hleaf3, hR03, hr0, xPart_eq (fun q _ => nDigits_lt 19 _ q) k2 kd ks kp,
      hxpp] at hroot1
    have hr1 : xv (σ3 R1) = pk.root := Option.some.inj (hroot1.symm.trans h1)
    refine cellVal_inj hc3 (isCanonical128_cellOf128 _) ?_
    show xv (σ3 R1) = _
    rw [hr1]
    exact (cellVal_cellOf128 _).symm
  -- the end
  obtain ⟨σf, hef, hpf, hhf⟩ := hB
  refine ⟨σf, by rw [hef.apply (Or.inl (by norm_num))]; exact i0, ?_⟩
  rw [xBody_eq, xBody_split]
  rw [show xPrologue ++ ((xLayer 0 196 (.n 0)).1 ++ ((xLayer 1 E0 R0).1 ++
      [loadS (.n E1) (.n 0) 0, .atom (.assertEq R1 (.n E1)), .ret []])) =
      ((xPrologue ++ (xLayer 0 196 (.n 0)).1) ++ (xLayer 1 E0 R0).1) ++
        ([loadS (.n E1) (.n 0) 0, .atom (.assertEq R1 (.n E1))] ++ [.ret []]) by simp]
  rw [holdsList_append]
  refine hhf _ _ ?_
  rw [holdsList_append]
  have hE1f : σf (.n E1) = cellOf128 pk.root := by rw [hef.apply (Or.inr le_rfl)]; exact iE1
  refine holdsList_of_atomsHold rfl (fun a ha => ?_) _ _ rfl
  simp only [loadS, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · show LoadHolds rd (σf (.n 0)) 0 (σf (.n E1))
    rw [hef.apply (Or.inl (by norm_num)), i0, hE1f]
    exact hldR
  · show σf R1 + σf (.n E1) = 0
    rw [hpf, hE1f]
    exact e_add_self _

end
end LeanVM.Guest.B1.Sig
