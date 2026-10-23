/-
  LeanVM.Guest.B1.Sig.XmssLayersComplete

  The layers of `verify_lean_xmss` complete: each from its digest, its digits those of the digest
  when it decodes, its randomizer, chains' starts and siblings loaded and kept.
-/

module

public import LeanVM.Guest.B1.Sig.XmssPieces
public import LeanVM.Guest.B1.Sig.XmssLayersSound

/-!
# The layers, complete

* `canon_lit`, `digest_digits`: a canonical digest that decodes is the literal of its digits, which
  sum to `106`;
* `xLayer0_complete`, `xLayer1_complete`: a layer completes from the prologue's facts, its digest
  decoding, its randomizer `rho`, starts `vals` and siblings `sibs` loaded: its root canonical
  and, under any agreement below its end, its randomizer, digits, starts and siblings kept.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

attribute [local irreducible] kMsg codewordT merkleT xLayer

variable {C : CallRel} {rd : Reader}

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

/-- The digits of a cell's digest. -/
noncomputable def dN (x : E) : Nat := (xv x).toNat

theorem xNode_nb (l : Nat) (hl : l < 32) : NBv 196 (xNode l) := ⟨34 + 3 * (31 - l), by omega, rfl⟩

theorem xCore_end (layer b : Nat) (hA : 211 ≤ xA layer b) : xA layer b + 6 < (xMk layer b).2.1 := by
  have b1 : xA layer b + 6 < (xCw layer b).2.1 := by
    rw [xCw_eq]
    exact cwBase_lt (xWc layer b) (q := 0) (G := 19) _ _ _ (by norm_num)
  have htips : (xCw layer b).2.2 = (List.range 58).map (cwTip (xW layer b) (xA layer b + 6)) :=
    codewordT_tips (xW layer b) (G := 19) (by norm_num) _ _ _
  have hcellNB : ∀ c ∈ (xLeafCells layer b).map KC.cell, KCb ((xCw layer b).2.1 + 2) c := by
    intro c hc
    simp only [xLeafCells, List.map_cons, List.mem_cons, htips, List.map_map, List.mem_map,
      List.mem_range, Function.comp_apply] at hc
    rcases hc with rfl | rfl | ⟨i, hi, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨_, by omega, rfl⟩
    · obtain ⟨j, ej, hj⟩ := cwTip_lt (xW layer b) (G := 19) xTarget (xD0 layer b) (xA layer b + 6)
        (by norm_num) (show i < 3 * 19 + 1 by omega)
      have hj' : j < (xCw layer b).2.1 := hj
      exact ⟨j, by omega, ej⟩
  have b2 : (xCw layer b).2.1 + 2 ≤ (xLeafK layer b).2.1 :=
    kMsg_le (show xPad + 5 ≤ (xCw layer b).2.1 + 2 by simp [xPad]; omega) hcellNB
  have b3 : (xLeafK layer b).2.1 ≤ (xMk layer b).2.1 := merkleT_snd_ge ..
  omega

/-- **The bottom layer completes.** -/
theorem xLayer0_complete (hm : MemOK rd 64) (σ : Val) (hpre : XPre σ) (hPc : IsCanonical128 (σ (.n 1)))
    {c d rho : E} (hc : IsCanonical128 c) (hd : IsCanonical128 d) (hrho : IsCanonical128 rho)
    (hld2 : LoadHolds rd (σ (.n 0)) 2 c) (hld3 : LoadHolds rd (σ (.n 0)) 3 d) {enc : LeanXmss.Encoding}
    (hdec : LeanXmss.Codeword.decode
      (xv (hcell [σ (.n 1), σ (xNode 0) + word (tw 12) 0 0, c, d, rho]).1) = some enc)
    (vals : Nat → E) (hv : ∀ i, IsCanonical128 (vals i)) {bits : Nat → Bool}
    (hbits : ∀ l < 16, σ (xBitOf 0 l) = if bits l then 1 else 0) {sibs : Nat → E}
    (hsc : ∀ l < 16, IsCanonical128 (sibs l)) :
    Completes C rd 196 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).1 σ
      (fun σ' => IsCanonical128 (σ' (xLayer 0 196 (.n 0)).2.2) ∧
        ∀ σ'', AgreeBelow (xLayer 0 196 (.n 0)).2.1 σ' σ'' → σ'' (.n 196) = rho ∧
          (∀ q ≤ 19, σ'' (.n (cwState (xW 0 196) (xA 0 196 + 6) q).2.2) =
            ofK (gpow (nDigits 19 (dN (hcell [σ (.n 1), σ (xNode 0) + word (tw 12) 0 0, c, d, rho]).1) q))) ∧
          (∀ i < 58, σ'' (cwPos (xW 0 196) 19 (xA 0 196 + 6)
            (nDigits 19 (dN (hcell [σ (.n 1), σ (xNode 0) + word (tw 12) 0 0, c, d, rho]).1)) i) = vals i) ∧
          ∀ l < 16, mSib σ'' (xBitOf 0) l (mBase (xNodeOf 0) 0 l (xLeafK 0 196).2.1) = sibs l) := by
  have hA : xA 0 196 = 224 := rfl
  have hidx : NBv (xA 0 196) (xIdx 0 196) := ⟨127, by rw [hA]; norm_num, rfl⟩
  have hd0 : NBv (xA 0 196) (xD0 0 196) := ⟨211, by rw [hA]; norm_num, rfl⟩
  have hbitNB : ∀ l < 16, NBv (xA 0 196) (xBitOf 0 l) := fun l hl => ⟨2 + l, by rw [hA]; omega, by
    simp [xBitOf, xBit]⟩
  have hnodeNB : ∀ l nd, xNodeOf 0 l = some nd → NBv (xA 0 196) nd := by
    intro l nd h
    simp only [xNodeOf] at h
    split at h
    · cases h
    · cases h
      exact ⟨34 + 3 * (31 - (16 * 0 + l + 1)), by rw [hA]; omega, rfl⟩
  have hcnb := xCore_nb (layer := 0) (b := 196) (by rw [hA]; norm_num) hidx hd0 hbitNB hnodeNB
  have hge : 224 ≤ (xMk 0 196).2.1 := by
    have := xCore_end 0 196 (by rw [hA]; norm_num)
    rw [hA] at this
    omega
  rw [xLayer_split, xLayer_snd]
  simp only [↓reduceIte]
  refine Completes.append (m := 224) (by norm_num) hge xDigest0_nb
    (xDigest0_complete (C := C) (rd := rd) σ hrho hc hd hld2 hld3 hPc
      (by rw [hpre.nodes 0 (by norm_num)]; exact canon_eOfNat _)).withHolds
    (fun σd hed ⟨⟨hr196, hr199, hr200⟩, hhd⟩ => ?_)
  have hagd : AgreeBelow 196 σ σd := hed.agree
  obtain ⟨-, -, hpad, h198, h211⟩ := xDigest0_sound (atomsHold_of_holdsList (xDigest0_atoms 196) hhd)
  have hP : σd (.n 1) = σ (.n 1) := hagd.apply ⟨1, by norm_num, rfl⟩
  have hn0 : σd (xNode 0) = σ (xNode 0) := hagd.apply (xNode_nb 0 (by norm_num))
  have hx : σd (.n 211) = (hcell [σ (.n 1), σ (xNode 0) + word (tw 12) 0 0, c, d, rho]).1 := by
    rw [h211, hP, h198, hn0, hr199, hr200, hr196]
  obtain ⟨hN, hs⟩ := digest_digits (canon_hcell _) hdec
  have hcore := xCore_complete (C := C) (rd := rd) (layer := 0) (b := 196) (by rw [hA]; norm_num) hm σd
    (hpre.congr hagd) hpad (by rw [hP]; exact hPc) hidx
    (by show IsCanonical128 (σd (xNode 0)); rw [hn0, hpre.nodes 0 (by norm_num)]; exact canon_eOfNat _)
    hd0 (N := dN (hcell [σ (.n 1), σ (xNode 0) + word (tw 12) 0 0, c, d, rho]).1)
    (by show σd (.n 211) = _; rw [hx]; exact hN) hs vals hv (bits := bits)
    (fun l hl => ⟨hbitNB l hl, by
      rw [hagd.apply (show NBv 196 (xBitOf 0 l) from ⟨2 + l, by omega, by simp [xBitOf, xBit]⟩)]
      exact hbits l hl⟩)
    (fun l nd h => by
      have hnb := hnodeNB l nd h
      simp only [xNodeOf] at h
      split at h
      · cases h
      · cases h
        refine ⟨hnb, ?_⟩
        rw [show xNode (16 * 0 + l + 1) = xNode (min (16 * 0 + l + 1) 31) by
          simp only [xNode, V.mk.injEq, true_and]; omega,
          hagd.apply (xNode_nb _ (by omega)), hpre.nodes _ (by omega)]
        exact canon_eOfNat _) hsc
  refine (hcore.keep (Q := fun σ' => σ' (.n 196) = rho) (Q' := fun σ' => σ' (.n 196) = rho) hr196
    (fun σ' he h => by rw [he.apply (Or.inl (by rw [hA]; norm_num))]; exact h)).mono le_rfl le_rfl
    (fun σ' ⟨⟨hc', hk⟩, h196⟩ => ⟨hc', fun σ'' hag => ?_⟩)
  obtain ⟨k1, k2, k3⟩ := hk σ'' hag
  exact ⟨by rw [hag.apply ⟨196, by omega, rfl⟩]; exact h196, k1, k2, k3⟩

/-- **The top layer completes**, over the bottom root `root`. -/
theorem xLayer1_complete {b : Nat} {root : V} (hb : 211 ≤ b) (hroot : NBv b root) (hm : MemOK rd 64)
    (σ : Val) (hpre : XPre σ) (hpad : PadOK σ xPad) (hPc : IsCanonical128 (σ (.n 1)))
    (hrc : IsCanonical128 (σ root)) {rho : E} (hrho : IsCanonical128 rho) {enc : LeanXmss.Encoding}
    (hdec : LeanXmss.Codeword.decode
      (xv (hcell [σ (.n 1), σ (xNode 16) + word lxTop 0 0 + word (tw 12) 0 0, σ root, rho]).1) = some enc)
    (vals : Nat → E) (hv : ∀ i, IsCanonical128 (vals i)) {bits : Nat → Bool}
    (hbits : ∀ l < 16, σ (xBitOf 1 l) = if bits l then 1 else 0) {sibs : Nat → E}
    (hsc : ∀ l < 16, IsCanonical128 (sibs l)) :
    Completes C rd b (xLayer 1 b root).2.1 (xLayer 1 b root).1 σ
      (fun σ' => IsCanonical128 (σ' (xLayer 1 b root).2.2) ∧
        ∀ σ'', AgreeBelow (xLayer 1 b root).2.1 σ' σ'' → σ'' (.n (b + 2)) = rho ∧
          (∀ q ≤ 19, σ'' (.n (cwState (xW 1 b) (xA 1 b + 6) q).2.2) = ofK (gpow (nDigits 19
            (dN (hcell [σ (.n 1), σ (xNode 16) + word lxTop 0 0 + word (tw 12) 0 0, σ root, rho]).1) q))) ∧
          (∀ i < 58, σ'' (cwPos (xW 1 b) 19 (xA 1 b + 6) (nDigits 19
            (dN (hcell [σ (.n 1), σ (xNode 16) + word lxTop 0 0 + word (tw 12) 0 0, σ root, rho]).1)) i) =
            vals i) ∧
          ∀ l < 16, mSib σ'' (xBitOf 1) l (mBase (xNodeOf 1) 0 l (xLeafK 1 b).2.1) = sibs l) := by
  have hA : xA 1 b = b + 19 := rfl
  have hidx : NBv (xA 1 b) (xIdx 1 b) := ⟨b + 1, by rw [hA]; omega, rfl⟩
  have hd0 : NBv (xA 1 b) (xD0 1 b) := ⟨b + 6, by rw [hA]; omega, rfl⟩
  have hbit196 : ∀ l < 16, NBv 196 (xBitOf 1 l) := fun l hl => ⟨2 + (16 + l), by omega, by
    simp [xBitOf, xBit]⟩
  have hbitNB : ∀ l < 16, NBv (xA 1 b) (xBitOf 1 l) := fun l hl =>
    (hbit196 l hl).mono' (by rw [hA]; omega)
  have hnode : ∀ l nd, xNodeOf 1 l = some nd → nd = xNode (min (16 * 1 + l + 1) 31) := by
    intro l nd h
    simp only [xNodeOf] at h
    split at h
    · cases h
    · cases h
      simp only [xNode, V.mk.injEq, true_and]
      omega
  have hnodeNB : ∀ l nd, xNodeOf 1 l = some nd → NBv (xA 1 b) nd := fun l nd h => by
    rw [hnode l nd h]
    exact (xNode_nb _ (by omega)).mono' (by rw [hA]; omega)
  have hge : b + 19 ≤ (xMk 1 b).2.1 := by
    have := xCore_end 1 b (by rw [hA]; omega)
    rw [hA] at this
    omega
  rw [xLayer_split, xLayer_snd]
  simp only [one_ne_zero, ↓reduceIte]
  refine Completes.append (m := b + 5 + 14) (by omega) hge (xDigest1_nb hb hroot)
    (xDigest1_complete (C := C) (rd := rd) σ hb hroot hrc hrho hPc
      (by rw [hpre.nodes 16 (by norm_num)]; exact canon_eOfNat _) hpad).withHolds
    (fun σd hed ⟨hr2, hhd⟩ => ?_)
  have hagd : AgreeBelow b σ σd := hed.agree
  have hpadd : PadOK σd xPad := hpad.congr (by simp [xPad]; omega) hagd
  obtain ⟨h1, h4, h6⟩ := xDigest1_sound hpadd (atomsHold_of_holdsList (xDigest1_atoms b root) hhd)
  have hP : σd (.n 1) = σ (.n 1) := hagd.apply ⟨1, by omega, rfl⟩
  have hn16 : σd (xNode 16) = σ (xNode 16) := hagd.apply ((xNode_nb 16 (by norm_num)).mono' (by omega))
  have hrt : σd root = σ root := hagd.apply hroot
  have hx : σd (.n (b + 6)) =
      (hcell [σ (.n 1), σ (xNode 16) + word lxTop 0 0 + word (tw 12) 0 0, σ root, rho]).1 := by
    rw [h6, hP, h4, h1, hn16, hrt, hr2]
  obtain ⟨hN, hs⟩ := digest_digits (canon_hcell _) hdec
  have hagd196 : AgreeBelow 196 σ σd := hagd.mono (by omega)
  have hcore := xCore_complete (C := C) (rd := rd) (layer := 1) (b := b) (by rw [hA]; omega) hm σd
    (hpre.congr hagd196) hpadd (by rw [hP]; exact hPc) hidx
    (by
      show IsCanonical128 (σd (.n (b + 1)))
      rw [h1, hn16, hpre.nodes 16 (by norm_num)]
      exact canon_add (canon_eOfNat _) (canon_word _ _))
    hd0 (N := dN (hcell [σ (.n 1), σ (xNode 16) + word lxTop 0 0 + word (tw 12) 0 0, σ root, rho]).1)
    (by show σd (.n (b + 6)) = _; rw [hx]; exact hN) hs vals hv (bits := bits)
    (fun l hl => ⟨hbitNB l hl, by rw [hagd196.apply (hbit196 l hl)]; exact hbits l hl⟩)
    (fun l nd h => ⟨hnodeNB l nd h, by
      rw [hnode l nd h, hagd196.apply (xNode_nb _ (by omega)), hpre.nodes _ (by omega)]
      exact canon_eOfNat _⟩) hsc
  refine (hcore.keep (Q := fun σ' => σ' (.n (b + 2)) = rho) (Q' := fun σ' => σ' (.n (b + 2)) = rho) hr2
    (fun σ' he h => by rw [he.apply (Or.inl (by rw [hA]; omega))]; exact h)).mono le_rfl le_rfl
    (fun σ' ⟨⟨hc', hk⟩, h2⟩ => ⟨hc', fun σ'' hag => ?_⟩)
  obtain ⟨k1, k2, k3⟩ := hk σ'' hag
  exact ⟨by rw [hag.apply ⟨b + 2, by omega, rfl⟩]; exact h2, k1, k2, k3⟩

end
end LeanVM.Guest.B1.Sig
