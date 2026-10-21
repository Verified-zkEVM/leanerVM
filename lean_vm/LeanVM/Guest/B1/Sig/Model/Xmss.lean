/-
  LeanVM.Guest.B1.Sig.Model.Xmss

  `verify_lean_xmss` under a hash model: the prologue, the two layers and the body, concluding
  leanXMSS verification with the model's answered hash (`Node.xmssVerifyWith M.H … = some true`).
-/

module

public import LeanVM.Guest.B1.Sig.Xmss
public import LeanVM.Guest.B1.Sig.Model.XmssScheme

/-!
# `verify_lean_xmss` under a hash model

The deployed chain (`XmssLayer`, `XmssLayerW`, `Xmss`) read forward over `M.sem`, the scheme run
in `Option` with the oracle `digestBits <$> M.H`:

| deployed | here |
|---|---|
| `xPrologue_sound_w`, `xStepAddrs_iff` | the same, by `holdsListB_free` (no `BLAKE2S`) |
| `xDigest0_sound`, `xDigest1_sound` | `xDigest0_model`, `xDigest1_model` |
| `xTail_sound_w` | `xTail_model` |
| `xLayer0_sound_w`, `xLayer1_sound_w` | `xLayer0_model`, `xLayer1_model` |
| `verify_lean_xmss_sound_w`, `verify_lean_xmss_sound` | `verify_lean_xmss_model_w`, `verify_lean_xmss_model` |
| `verify_lean_xmss_meaning` | `verify_lean_xmss_meaning_model` |
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanXmss LeanXmss.Concrete

@[expose] public section

namespace Sig

variable {M : HashModel} {C : CallRel} {rd : Reader} {inst : HasQuery LeanXmss.HashSpec Option}

/-! ## Hash-free blocks -/

theorem xPrologue_free : Stmt.freeInList [] xPrologue = true := by decide

theorem xStepAddrs_free (idx : V) (a : Nat) : Stmt.freeInList [] (xStepAddrs idx a) = true := rfl

/-! ## Chains: the index does not enter a leanXMSS step -/

theorem chainFromWith_lx (H : List UInt8 → Option Protocol.Digest) (pp : E) (adr : Nat → E) (idx : E) (i : Nat) :
    ∀ m s v, chainFromWith H true pp adr idx i m s v = chainFromWith H true pp adr 0 i m s v
  | 0, _, _ => rfl
  | m + 1, s, v => by
      simp only [chainFromWith, stepCells, ↓reduceIte]
      congr 1
      funext h
      exact chainFromWith_lx H pp adr idx i m _ _

theorem tipPairWith_lx (H : List UInt8 → Option Protocol.Digest) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat)
    (x : E) : tipPairWith H true pp adr idx i d x = tipPairWith H true pp adr 0 i d x := by
  simp only [tipPairWith]; split <;> simp only [chainFromWith_lx]

/-! ## The digests -/

/-- **The bottom layer's message digest under a model** (`xDigest0_sound`). -/
theorem xDigest0_model {σ : Val} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (xDigest0 b) next kret) :
    LoadHolds rd (σ (.n 0)) 2 (σ (.n (b + 3))) ∧ LoadHolds rd (σ (.n 0)) 3 (σ (.n (b + 4))) ∧
      IsCanonical128 (σ (.n 1)) ∧ IsCanonical128 (σ (.n (b + 3))) ∧ IsCanonical128 (σ (.n (b + 4))) ∧
      σ (.n (b + 2)) = σ (.n 128) + word (tw 12) 0 0 ∧
      (∃ o, hcellWith M.H [σ (.n 1), σ (.n (b + 2)), σ (.n (b + 3)), σ (.n (b + 4)), σ (.n b)] = some o ∧
        σ (.n (b + 14)) = o.1) ∧ next := by
  simp only [xDigest0, ivs, cst, b2s, addS, hintW, List.cons_append, List.nil_append, holdsListB_cons_atom,
    holdsListB_nil, Atom.HoldsB, true_and] at h
  obtain ⟨h1, h2, hl3, hl4, h5, h6, h7, hc1, h10, h11, h12, h13, hc2, hn⟩ := h
  rw [h5, h6, h7] at hc1
  rw [h10, h11, h12, h13, word_zero] at hc2
  have hr : ([σ (.n b)].flatMap cellBytes).length = 16 := by rw [length_flatMap_cellBytes']; rfl
  have hc2' : M.sem.check ![σ (.n b), 0, 0, 0] (σ (.n (b + 8))) (σ (.n (b + 9))) (σ (.n (b + 14)))
      (σ (.n (b + 15))) (mdw (64 + ([σ (.n b)].flatMap cellBytes).length) true) := by rw [hr]; exact hc2
  obtain ⟨hb0, -, -, ho⟩ := compress_two_model (M := M) (blockBytes_one (σ (.n b))) (by rw [hr]; omega)
    (by rw [hr]; omega) hc1 hc2'
  rw [fin4_canonical] at hb0
  refine ⟨hl3, hl4, hb0.1, hb0.2.2.1, hb0.2.2.2, by rw [h2, h1], ⟨(σ (.n (b + 14)), σ (.n (b + 15))), ?_, rfl⟩, hn⟩
  rw [hcellWith, ← ho, blockBytes_four, ← List.flatMap_append]
  rfl

/-- **The top layer's message digest under a model** (`xDigest1_sound`). -/
theorem xDigest1_model {σ : Val} {b : Nat} {root : V} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (xDigest1 b root) next kret) :
    IsCanonical128 (σ root) ∧ σ (.n (b + 1)) = σ (.n 80) + word lxTop 0 0 ∧
      σ (.n (b + 4)) = σ (.n (b + 1)) + word (tw 12) 0 0 ∧
      (∃ o, hcellWith M.H [σ (.n 1), σ (.n (b + 4)), σ root, σ (.n (b + 2))] = some o ∧ σ (.n (b + 8)) = o.1) ∧
      next := by
  simp only [xDigest1, ivs, cst, b2s, addS, hintW, List.cons_append, List.nil_append, holdsListB_cons_atom,
    holdsListB_nil, Atom.HoldsB, true_and] at h
  obtain ⟨h0, h1, h3, h4, h5, h6, h7, hc, hn⟩ := h
  rw [h5, h6, h7] at hc
  obtain ⟨hcan, ho⟩ := compress4_model hc
  exact ⟨hcan.2.2.1, by rw [h1, h0], by rw [h4, h3], ⟨_, ho, rfl⟩, hn⟩

/-! ## The tail of a layer -/

/-- **The tail of a layer under a model** (`xTail_sound_w`): the digest decodes, the chains recover
their tips from the hinted values, and the leaf of the tips folds along the hinted siblings to the
root, every hash answered. -/
theorem xTail_model (hq : XQW M.H inst) {σ : Val} {L layer a : Nat} {idx d0 : V} (hl : layer < 2)
    (hpre : XPre σ L) {key : KeyIndex} (hkey : key.val = L / 2 ^ (16 * layer))
    (hidx : σ idx = eOfNat (xIdx layer L)) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (xTail layer a idx d0).1 next kret) :
    (∃ enc : Encoding, Codeword.decode (xv (σ d0)) = some enc ∧
      ∃ tips : ChainIndex → LeanXmss.Digest,
        (∀ i, @recoverChain Option _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key i (enc i)
          (xv (xTailVals a idx σ i.val)) = some (tips i)) ∧
        ∃ leaf, @leafHash Option _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key tips = some leaf ∧
          @treeFold Option _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key
            (fun l => xv (xTailSibs layer a idx d0 key.val σ l.val)) layerHeight leaf =
            some (xv (σ (xTail layer a idx d0).2.2))) ∧
      IsCanonical128 (σ (xTail layer a idx d0).2.2) ∧ next := by
  set lay : Layer := ⟨layer, hl⟩
  simp only [xTail, holdsListB_append] at h ⊢
  obtain ⟨hS, h⟩ := (xStepAddrs_iff idx a).mp ((holdsListB_free (xStepAddrs_free idx a) σ _ _).mp h)
  obtain ⟨⟨dig, hdig, htips, htarget, hd0⟩, h⟩ := cCodeword_model (w := xW a idx) hpre.md hpre.pow (G := 19)
    (by norm_num) h
  obtain ⟨hc, hc1, h⟩ := h
  have hc : σ (.n _) = word (tw 2) 0 0 := hc
  have hc1 : σ (.n _) = σ idx + σ (.n _) := hc1
  obtain ⟨⟨o, hleaf, hout⟩, h⟩ := hashValues_model (Or.inr (by norm_num)) (by norm_num) h
  obtain ⟨hroot, hn⟩ := merkle_model (β := fun l => key.val.testBit l) 16 0 _ _ (fun l' _ hl' => by
    rw [show 3 + 16 * layer + l' = 3 + (16 * layer + l') by omega, hpre.bits _ (by omega), hkey,
      Nat.testBit_div_two_pow, Nat.add_comm l']) h
  have hsum : ∑ i ∈ Finset.range numChains, dig i = targetSum := by
    rw [xTarget_eq] at htarget
    have := digit_sum_le hdig (3 * 19 + 1)
    exact (gen_pow_inj (by norm_num) (by omega) htarget).symm
  have hL := hpre.lt
  have hadr : ∀ s : ChainStep, cellBytes (σ (.n (a + 2 * s.val + 1))) = tweakBytes (.chain lay key s) := fun s => by
    have hs : s.val < 3 := s.isLt
    rw [(hS s.val hs).2, hidx, chain_addr hL hl hs, tweakBytes_chain, hkey]
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
  refine ⟨⟨fun i => ⟨dig i.val, hdig _⟩, by rw [hd0]; exact decode_lit hdig hsum,
    fun i => xv (σ (xTip a idx d0 i.val)), fun i => ?_, _,
    leafHash_cellsW hq (fun i => σ (xTip a idx d0 i)) hleafAdr (o := o) ?_, ?_⟩,
    mFoldWith_canonical (by norm_num) hroot, hn⟩
  · obtain ⟨p, hp, hp1, -⟩ := htips i.val i.isLt
    have hp : tipPairWith M.H true (σ (.n 1)) (fun s => σ (.n (a + 2 * s + 1))) (σ idx) i.val (dig i.val)
        (xTailVals a idx σ i.val) = some p := hp
    rw [tipPairWith_lx] at hp
    rw [recoverChain_cellsW (adr := fun s => σ (.n (a + 2 * s + 1))) hq hadr ⟨dig i.val, hdig _⟩ _ hp]
    simp only [xTip]
    rw [hp1]
  · simp only [xTip]
    exact hleaf
  · rw [hout] at hroot
    exact treeFold_cellsW hq hA (xTailSibs layer a idx d0 key.val σ) layerHeight le_rfl _ hroot

/-! ## The layers -/

/-- **The bottom layer under a model** (`xLayer0_sound_w`). -/
theorem xLayer0_model (hq : XQW M.H inst) {σ : Val} {L b : Nat} {root : V} (hpre : XPre σ L) {key : KeyIndex}
    (hkey : key.val = L) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (xLayer 0 b root).1 next kret) :
    LoadHolds rd (σ (.n 0)) 2 (σ (.n (b + 3))) ∧ LoadHolds rd (σ (.n 0)) 3 (σ (.n (b + 4))) ∧
      IsCanonical128 (σ (.n 1)) ∧ IsCanonical128 (σ (.n (b + 3))) ∧ IsCanonical128 (σ (.n (b + 4))) ∧
      @layerRoot Option _ inst (xpp (σ (.n 1))) bottomLayer key
        (cellBytes (σ (.n (b + 3))) ++ cellBytes (σ (.n (b + 4))))
        (xPart 0 (b + 16) (.n 128) (.n (b + 14)) (.n b) L σ) = some (some (xv (σ (xLayer 0 b root).2.2))) ∧
      next := by
  rw [xLayer_zero] at h ⊢
  dsimp only at h ⊢
  rw [holdsListB_append] at h
  obtain ⟨hl3, hl4, hpp, hm0, hm1, hadr, ⟨o, hd, hd14⟩, h⟩ := xDigest0_model h
  have hkey' : key.val = L / 2 ^ (16 * 0) := by rw [hkey]; simp
  have hidx : σ (.n 128) = eOfNat (xIdx 0 L) := by
    have := hpre.nodes 0 (by omega)
    simpa [xIdx] using this
  obtain ⟨⟨enc, hdec, tips, htips, leaf, hleaf, hroot⟩, -, hn⟩ := xTail_model hq (by omega) hpre hkey' hidx h
  rw [hkey] at hroot
  refine ⟨hl3, hl4, hpp, hm0, hm1, layerRoot_cellsW (d := xv (σ (.n (b + 14)))) ?_ hdec htips hleaf hroot, hn⟩
  rw [hd14]
  refine messageDigest_cellsW hq (a := σ (.n (b + 2))) (cs := [σ (.n (b + 3)), σ (.n (b + 4))]) ?_ (by simp) ?_
  · rw [hadr, hidx, tag_addr hpre.lt (by omega) (by omega), tweakBytes_message, hkey',
      show (bottomLayer : Layer).val = 0 from rfl]
  · simpa only [List.cons_append, List.nil_append] using hd

/-- **The top layer under a model** (`xLayer1_sound_w`). -/
theorem xLayer1_model (hq : XQW M.H inst) {σ : Val} {L b : Nat} {root : V} (hpre : XPre σ L) {key : KeyIndex}
    (hkey : key.val = L / 2 ^ 16) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (xLayer 1 b root).1 next kret) :
    IsCanonical128 (σ root) ∧ IsCanonical128 (σ (xLayer 1 b root).2.2) ∧
      @layerRoot Option _ inst (xpp (σ (.n 1))) topLayer key (cellBytes (σ root))
        (xPart 1 (b + 10) (.n (b + 1)) (.n (b + 8)) (.n (b + 2)) (L / 2 ^ 16) σ) =
        some (some (xv (σ (xLayer 1 b root).2.2))) ∧ next := by
  rw [xLayer_one] at h ⊢
  dsimp only at h ⊢
  rw [holdsListB_append] at h
  obtain ⟨hcan, hidx, hadr, ⟨o, hd, hd8⟩, h⟩ := xDigest1_model h
  have hkey' : key.val = L / 2 ^ (16 * 1) := by rw [hkey]
  have hidx' : σ (.n (b + 1)) = eOfNat (xIdx 1 L) := by
    have := hpre.nodes 16 (by omega)
    rw [hidx, show 128 - 3 * 16 = 80 by omega] at *
    rw [this, xIdx, show lxTop = 2 ^ 55 * 1 by rfl, eOfNat_add_word (lt_of_le_of_lt (Nat.div_le_self _ _)
      (lt_trans hpre.lt (by norm_num)))]
    congr 1
    ring
  obtain ⟨⟨enc, hdec, tips, htips, leaf, hleaf, hroot⟩, hrc, hn⟩ := xTail_model hq (by omega) hpre hkey' hidx' h
  rw [hkey] at hroot
  refine ⟨hcan, hrc, layerRoot_cellsW (d := xv (σ (.n (b + 8)))) ?_ hdec htips hleaf hroot, hn⟩
  rw [hd8]
  refine messageDigest_cellsW hq (a := σ (.n (b + 4))) (cs := [σ root]) ?_ (by simp) ?_
  · rw [hadr, hidx', tag_addr hpre.lt (by omega) (by omega), tweakBytes_message, hkey',
      show (topLayer : Layer).val = 1 from rfl]
  · simpa only [List.cons_append, List.nil_append] using hd

/-! ## The body -/

/-- **`verify_lean_xmss` under a model**, for the key, message and signature of its valuation: the
signature verifies with the model's answered hash. -/
theorem verify_lean_xmss_model_w {σ : Val} {rets : List E}
    (h : Stmt.HoldsListB M.sem C rd σ xBody False (fun rs => rs = rets)) :
    rets = [] ∧ ClaimAt rd (σ (.n 0)) (claimCells (xmssPkOf σ).root (xmssPkOf σ).parameter (xmssMsgOf σ)) ∧
      Node.xmssVerifyWith M.H (xmssPkOf σ) (xmssMsgOf σ) (xmssSigOf σ) = some true := by
  simp only [xBody, holdsListB_append] at h
  obtain ⟨hl1, hpre, h⟩ := xPrologue_sound_w ((holdsListB_free xPrologue_free σ _ _).mp h)
  obtain ⟨hl3, hl4, hpp, hm0, hm1, hr0, h⟩ :=
    xLayer0_model (inst := ⟨fun x ↦ Node.digestBits <$> M.H x⟩) (xqw_with M.H) hpre
      (keyAt_bottom_val (xmssLeafOf σ)) h
  obtain ⟨-, hrc, hr1, h⟩ :=
    xLayer1_model (inst := ⟨fun x ↦ Node.digestBits <$> M.H x⟩) (xqw_with M.H) hpre
      (keyAt_top_val (xmssLeafOf σ)) h
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
  · refine verify_of_roots (r0 := xv r0) ?_ ?_
    · show @LeanXmss.Concrete.layerRoot Option _ ⟨fun x ↦ Node.digestBits <$> M.H x⟩ (xpp (σ (.n 1)))
        LeanXmss.bottomLayer (LeanXmss.keyAt (xmssLeafOf σ) LeanXmss.bottomLayer)
        (LeanXmss.bytesLE 32 (BitVec.ofNat 256 (cellNat c0 + 2 ^ 128 * cellNat c1)))
        (xmssPartOf σ LeanXmss.bottomLayer) = some (some (xv r0))
      rw [bytesLE_message (lo_ofNat c0 c1) (hi_ofNat c0 c1)]
      simpa [xmssPartOf] using hr0
    · show @LeanXmss.Concrete.layerRoot Option _ ⟨fun x ↦ Node.digestBits <$> M.H x⟩ (xpp (σ (.n 1)))
        LeanXmss.topLayer (LeanXmss.keyAt (xmssLeafOf σ) LeanXmss.topLayer) (LeanXmss.bytesLE 16 (xv r0))
        (xmssPartOf σ LeanXmss.topLayer) = some (some (xv r1))
      rw [bytesLE_xv]
      simpa [xmssPartOf, show LeanXmss.topLayer ≠ LeanXmss.bottomLayer by decide] using hr1

/-- **`verify_lean_xmss` under a model** (`verify_lean_xmss_sound`). -/
theorem verify_lean_xmss_model {σ : Val} {rets : List E}
    (h : Stmt.HoldsListB M.sem C rd σ xBody False (fun rs => rs = rets)) :
    rets = [] ∧ ∃ (pk : LeanXmss.PublicKey) (m : LeanXmss.Message),
      ClaimAt rd (σ (.n 0)) (claimCells pk.root pk.parameter m) ∧
        ∃ sig, Node.xmssVerifyWith M.H pk m sig = some true :=
  let ⟨hr, hc, hv⟩ := verify_lean_xmss_model_w h
  ⟨hr, _, _, hc, _, hv⟩

end Sig

/-- **`verify_lean_xmss(claim)` with the hash `H`**: the claim at the pointer is a leanXMSS key and a
message that some signature verifies with `H`'s answers (`Meaning_verify_lean_xmss`). -/
def Meaning_verify_lean_xmssWith (H : List UInt8 → Option Protocol.Digest) (rd : Reader) (args rets : List E) : Prop :=
  ∃ p, args = [p] ∧ rets = [] ∧ ∃ (pk : LeanXmss.PublicKey) (m : LeanXmss.Message),
    ClaimAt rd p (claimCells pk.root pk.parameter m) ∧ ∃ σ, Node.xmssVerifyWith H pk m σ = some true

/-- **`verify_lean_xmss` is sound under a model** (`verify_lean_xmss_meaning`). -/
theorem verify_lean_xmss_meaning_model {M : HashModel} {rd : Reader} {args rets : List E}
    (h : coreProgram.RelB M.sem rd "verify_lean_xmss" args rets) :
    Meaning_verify_lean_xmssWith M.H rd args rets := by
  obtain ⟨σ, hp, hb⟩ := (relB_iff_sem Sig.find_verify_lean_xmss args rets).mp h
  obtain ⟨hr, pk, m, hc, sig, hv⟩ := Sig.verify_lean_xmss_model hb
  exact ⟨σ (.n 0), by rw [← hp]; rfl, hr, pk, m, hc, sig, hv⟩

end
end LeanVM.Guest.B1
