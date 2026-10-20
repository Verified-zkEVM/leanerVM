/-
  LeanVM.Guest.B1.Sig.XmssLayerW

  The parts of a leanXMSS signature `verify_lean_xmss` hints, as functions of the valuation: the
  leaf index of its bit cells, and each layer's randomizer, chain values and authentication path.
  The prologue and the layers are sound for these values.
-/

module

public import LeanVM.Guest.B1.Sig.XmssLayer
public import LeanVM.Guest.B1.Sig.XmssWots

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanXmss LeanXmss.Concrete

@[expose] public section

variable {C : CallRel} {rd : Reader} {inst : HasQuery LeanXmss.HashSpec Id}

/-! ## The leaf index -/

/-- The leaf index the prologue's hinted bits `n(3 + j)` spell. -/
def xLeafNat (σ : Val) : Nat := bitsVal (fun j => decide (σ (.n (3 + j)) = 1)) 32

theorem xLeafNat_lt (σ : Val) : xLeafNat σ < 2 ^ 32 := bitsVal_lt _ 32

/-- **The prologue is sound** for the leaf index of its bit cells. -/
theorem xPrologue_sound_w {σ : Val} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ xPrologue next kret) :
    LoadHolds rd (σ (.n 0)) 1 (σ (.n 1)) ∧ XPre σ (xLeafNat σ) ∧ next := by
  rw [xPrologue_eq, holdsList_cons_atom, cst, holdsList_cons_atom, hintW, holds_hint_cons, holdsList_append,
    booleans_iff, holdsList_append] at h
  obtain ⟨hl, hmd, hbool, h⟩ := h
  have hL : xLeafNat σ < 2 ^ 32 := xLeafNat_lt σ
  have hbits : ∀ j < 32, σ (.n (3 + j)) = bitE ((xLeafNat σ).testBit j) := fun j hj => by
    rw [xLeafNat, testBit_bitsVal, decide_eq_true hj, Bool.true_and]
    exact bitE_of_mul_self (hbool j hj)
  obtain ⟨hsh, h⟩ := shifts_sound (by omega) (by omega) hL hbits h
  obtain ⟨hpow, hn⟩ := (powers_iff 129).mp h
  exact ⟨hl, ⟨hmd, hL, hbits, nodes_of_shifts hsh, hpow⟩, hn⟩

/-! ## A layer's parts -/

/-- The chain values a layer's tail hints, from the address base `a`, over the index `idx`. -/
def xTailVals (a : Nat) (idx : V) (σ : Val) : Nat → E :=
  codeX (xW a idx) (fun s => .n (129 + s)) 19 (a + 6) σ

/-- The siblings a layer's tail hints, over the key `key`. -/
def xTailSibs (layer a : Nat) (idx d0 : V) (key : Nat) (σ : Val) : Nat → E :=
  mSibs (fun l => 16 * layer + l + 1 == 32) (fun l => key.testBit l) σ 16 0
    ((cCodeword (xW a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6)).2.1 + 2 + hashValuesSize 58)

/-- A layer's signature: the randomizer at `rho`, the tail's chain values and siblings. -/
def xPart (layer a : Nat) (idx d0 rho : V) (key : Nat) (σ : Val) : LayerSignature :=
  ⟨xv (σ rho), fun i => xv (xTailVals a idx σ i.val), fun l => xv (xTailSibs layer a idx d0 key σ l.val)⟩

/-- **The tail of a layer is sound** for its hinted chain values and siblings (`xTail_sound`, the
values named). -/
theorem xTail_sound_w (hq : XQ inst) {σ : Val} {L layer a : Nat} {idx d0 : V} (hl : layer < 2)
    (hpre : XPre σ L) {key : KeyIndex} (hkey : key.val = L / 2 ^ (16 * layer))
    (hidx : σ idx = eOfNat (xIdx layer L)) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (xTail layer a idx d0).1 next kret) :
    (∃ enc : Encoding, Codeword.decode (xv (σ d0)) = some enc ∧
      @treeFold Id _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key (fun l => xv (xTailSibs layer a idx d0 key.val σ l.val))
        layerHeight
        (@leafHash Id _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key fun i =>
          @recoverChain Id _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key i (enc i) (xv (xTailVals a idx σ i.val))) =
        xv (σ (xTail layer a idx d0).2.2)) ∧ IsCanonical128 (σ (xTail layer a idx d0).2.2) ∧ next := by
  set lay : Layer := ⟨layer, hl⟩
  simp only [xTail, holdsList_append] at h ⊢
  obtain ⟨hS, h⟩ := (xStepAddrs_iff idx a).mp h
  obtain ⟨⟨dig, hdig, htips, htarget, hd0⟩, h⟩ := cCodeword_sound_w (w := xW a idx) hpre.md hpre.pow (G := 19)
    (by norm_num) h
  obtain ⟨hc, hc1, h⟩ := h
  have hc : σ (.n _) = word (tw 2) 0 0 := hc
  have hc1 : σ (.n _) = σ idx + σ (.n _) := hc1
  obtain ⟨hleaf, h⟩ := hashValues_sound (Or.inr (by norm_num)) (by norm_num) h
  obtain ⟨hroot, hn⟩ := merkle_sound_w (β := fun l => key.val.testBit l) 16 0 _ _ (fun l' _ hl' => by
    rw [show 3 + 16 * layer + l' = 3 + (16 * layer + l') by omega, hpre.bits _ (by omega), hkey, Nat.testBit_div_two_pow, Nat.add_comm l']) h
  have hsum : ∑ i ∈ Finset.range numChains, dig i = targetSum := by
    rw [xTarget_eq] at htarget
    have := digit_sum_le hdig (3 * 19 + 1)
    exact (gen_pow_inj (by norm_num) (by omega) htarget).symm
  refine ⟨⟨fun i => ⟨dig i.val, hdig _⟩, ?_, ?_⟩,
    by rw [hroot]; exact mFold_canonical _ _ _ _ _ _ _ (Or.inl (by norm_num)), hn⟩
  · rw [hd0]
    exact decode_lit hdig hsum
  have hL := hpre.lt
  have hadr : ∀ s : ChainStep, cellBytes (σ (.n (a + 2 * s.val + 1))) = tweakBytes (.chain lay key s) := fun s => by
    have hs : s.val < 3 := s.isLt
    rw [(hS s.val hs).2, hidx, chain_addr hL hl hs, tweakBytes_chain, hkey]
  have hchains : (fun i : ChainIndex => @recoverChain Id _ inst (xpp (σ (.n 1))) lay key i ⟨dig i.val, hdig _⟩
      (xv (xTailVals a idx σ i.val))) = fun i => xv (σ (xTip a idx d0 i.val)) := by
    funext i
    rw [recoverChain_cells (adr := fun s => σ (.n (a + 2 * s + 1))) hq hadr]
    have := (htips i.val i.isLt).1
    simp only [xTip]
    rw [this]
    exact congrArg (fun t => xv t.1) (tipPair_lx _ _ _ _ _ _).symm
  have hleafAdr : cellBytes (σ (.n ((cCodeword (xW a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6)).2.1 + 1))) =
      tweakBytes (.leaf lay key) := by
    rw [hc1, hc, hidx, tag_addr hL hl (by norm_num), tweakBytes_leaf, hkey]
  have hA : ∀ l < layerHeight, cellBytes (mAddr σ (fun l => .n (128 - 3 * (16 * layer + l)))
      (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop) (fun l => 16 * layer + l + 1 == 32) l) =
      tweakBytes (.node lay (l + 1) (key.val / 2 ^ (l + 1))) := fun l hl16 => by
    simp only [layerHeight] at hl16
    rw [tweakBytes_node, hkey]
    simp only [mAddr]
    by_cases he : 16 * layer + l + 1 = 32
    · have h1 : layer = 1 := by omega
      subst h1
      simp only [he, beq_self_eq_true, ↓reduceIte]
      rw [node_addr_end hL (by omega)]
    · have he' : (16 * layer + l + 1 == 32) = false := by simpa using he
      simp only [he', Bool.false_eq_true, ↓reduceIte]
      rw [show 16 * layer + (l + 1) = 16 * layer + l + 1 by omega, hpre.nodes _ (by omega),
        show L / 2 ^ (16 * layer + l + 1) = L / 2 ^ (16 * layer) / 2 ^ (l + 1) by
          rw [Nat.div_div_eq_div_mul, ← pow_add]; ring_nf,
        node_addr hL hl hl16]
  rw [hchains, leafHash_cells hq (fun i => σ (xTip a idx d0 i)) hleafAdr]
  simp only [xTip] at hleaf ⊢
  rw [show numChains = 58 from rfl, ← hleaf,
    treeFold_cells hq hA (xTailSibs layer a idx d0 key.val σ) layerHeight le_rfl, hroot]
  rfl

/-- **The bottom layer is sound** for its hinted parts (`xLayer0_sound`, the part named). -/
theorem xLayer0_sound_w (hq : XQ inst) {σ : Val} {L b : Nat} {root : V} (hpre : XPre σ L) {key : KeyIndex}
    (hkey : key.val = L) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (xLayer 0 b root).1 next kret) :
    LoadHolds rd (σ (.n 0)) 2 (σ (.n (b + 3))) ∧ LoadHolds rd (σ (.n 0)) 3 (σ (.n (b + 4))) ∧
      IsCanonical128 (σ (.n 1)) ∧ IsCanonical128 (σ (.n (b + 3))) ∧ IsCanonical128 (σ (.n (b + 4))) ∧
      @layerRoot Id _ inst (xpp (σ (.n 1))) bottomLayer key
        (cellBytes (σ (.n (b + 3))) ++ cellBytes (σ (.n (b + 4))))
        (xPart 0 (b + 16) (.n 128) (.n (b + 14)) (.n b) L σ) = some (xv (σ (xLayer 0 b root).2.2)) ∧
      next := by
  rw [xLayer_zero] at h ⊢
  dsimp only at h ⊢
  rw [holdsList_append] at h
  obtain ⟨hl3, hl4, hpp, hm0, hm1, hadr, hd, h⟩ := xDigest0_sound h
  have hkey' : key.val = L / 2 ^ (16 * 0) := by rw [hkey]; simp
  have hidx : σ (.n 128) = eOfNat (xIdx 0 L) := by
    have := hpre.nodes 0 (by omega)
    simpa [xIdx] using this
  obtain ⟨⟨enc, hdec, hroot⟩, -, hn⟩ := xTail_sound_w hq (by omega) hpre hkey' hidx h
  rw [hkey] at hroot
  refine ⟨hl3, hl4, hpp, hm0, hm1, layerRoot_of_tail (rho := σ (.n b)) ?_ hdec hroot, hn⟩
  rw [messageDigest_cells hq (a := σ (.n (b + 2))) (cs := [σ (.n (b + 3)), σ (.n (b + 4))]) ?_ (by simp), hd]
  · simp only [List.cons_append, List.nil_append]
  · rw [hadr, hidx, tag_addr hpre.lt (by omega) (by omega), tweakBytes_message, hkey',
      show (bottomLayer : Layer).val = 0 from rfl]

/-- **The top layer is sound** for its hinted parts (`xLayer1_sound`, the part named). -/
theorem xLayer1_sound_w (hq : XQ inst) {σ : Val} {L b : Nat} {root : V} (hpre : XPre σ L) {key : KeyIndex}
    (hkey : key.val = L / 2 ^ 16) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (xLayer 1 b root).1 next kret) :
    IsCanonical128 (σ root) ∧ IsCanonical128 (σ (xLayer 1 b root).2.2) ∧
      @layerRoot Id _ inst (xpp (σ (.n 1))) topLayer key (cellBytes (σ root))
        (xPart 1 (b + 10) (.n (b + 1)) (.n (b + 8)) (.n (b + 2)) (L / 2 ^ 16) σ) =
        some (xv (σ (xLayer 1 b root).2.2)) ∧ next := by
  rw [xLayer_one] at h ⊢
  dsimp only at h ⊢
  rw [holdsList_append] at h
  obtain ⟨hcan, hidx, hadr, hd, h⟩ := xDigest1_sound h
  have hkey' : key.val = L / 2 ^ (16 * 1) := by rw [hkey]
  have hidx' : σ (.n (b + 1)) = eOfNat (xIdx 1 L) := by
    have := hpre.nodes 16 (by omega)
    rw [hidx, show 128 - 3 * 16 = 80 by omega] at *
    rw [this, xIdx, show lxTop = 2 ^ 55 * 1 by rfl, eOfNat_add_word (lt_of_le_of_lt (Nat.div_le_self _ _)
      (lt_trans hpre.lt (by norm_num)))]
    congr 1
    ring
  obtain ⟨⟨enc, hdec, hroot⟩, hrc, hn⟩ := xTail_sound_w hq (by omega) hpre hkey' hidx' h
  rw [hkey] at hroot
  refine ⟨hcan, hrc, layerRoot_of_tail (rho := σ (.n (b + 2))) ?_ hdec hroot, hn⟩
  rw [messageDigest_cells hq (a := σ (.n (b + 4))) (cs := [σ root]) ?_ (by simp), hd]
  · simp only [List.cons_append, List.nil_append]
  · rw [hadr, hidx', tag_addr hpre.lt (by omega) (by omega), tweakBytes_message, hkey',
      show (topLayer : Layer).val = 1 from rfl]

end
end LeanVM.Guest.B1.Sig
