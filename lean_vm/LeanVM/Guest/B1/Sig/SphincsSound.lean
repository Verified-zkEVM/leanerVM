/-
  LeanVM.Guest.B1.Sig.SphincsSound

  `verify_sig_lean_sphincs` is sound: whenever its body holds on a memory image of at most `2^32`
  words, it returns no words, and with the byte table at its second argument the signature its
  frame holds verifies the claim at its first (`verify_sig_lean_sphincs_sound_holds`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsParts
public import LeanVM.Guest.B1.Sig.SphincsData

/-!
# `verify_sig_lean_sphincs`, sound

`sphincsSigOf σ`: the randomizer `n3`, each coordinate's opening (`coordOpening`), the counter
`sp_from_bytes` reads, the chain values the codeword's dispatches hint and the tree's siblings.

`verify_sig_lean_sphincs_sound_holds`: the body (`Data.core20.body = sBody`) holding, the prologue
gives the message digest's two cells `n17`, `n18`; the forest's coordinates sum their weights into
`n17` and their marks into `n18`, so the digest's index and marks are the dispatches'; the forest
key is the sixteen top nodes; the counter is below `2^32` (the byte table), so the 292-byte
encoding is the Spec's; the codeword's digits sum to `123`; the leaf and the tree reach the root
asserted to be the claim's first word.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat gen)
open Sphincs Sphincs.Concrete

@[expose] public section

attribute [local irreducible] sCoords kMsg codewordT merkleT fkArms foldArms

/-- **The leanSPHINCS signature `verify_sig_lean_sphincs` checks**, read off its valuation. -/
noncomputable def sphincsSigOf (σ : Val) : Sphincs.Signature :=
  ⟨sv (σ (.n 3)), fun c => coordOpening σ c.val (cSt c.val).1 (cSt c.val).2.1 (cSt c.val).2.2,
    BitVec.ofNat 32 (cellNat (σ (.n sFb.2.1))), fun i => sv (σ (cwStart sW 21 (sEnc.2.1 + 10) σ i.val)),
    fun l => sv (mSib σ sBit l.val (mBase sNodeOf 0 l.val sLeaf.2.1))⟩

/-- A message of two cells. -/
def smsg (c d : E) : Sphincs.Message := cellPairVal c d

theorem cellVal_zero : cellVal 0 = 0 := by
  rw [cellVal, limb_zero, limb_zero]
  rfl

/-- The bound's cell as an integer. -/
theorem bound_cell {σ : Val} (hS : ∀ c < 8, cS σ c < 16) (hA : ∀ w < 16, wA σ w < 8) {N : Nat}
    (hN : N < 2 ^ 22) :
    eOfNat (sIdx σ) + word 0 (N * 2 ^ 42) 0 + eOfNat192 (marksNat σ) =
      eOfNat192 (sIdx σ + marksNat σ + 2 ^ 106 * N) := by
  have hidx := sIdx_lt σ
  have hSl : ∑ c ∈ Finset.range 8, cS σ c * 2 ^ (4 * c) < 2 ^ 32 :=
    sum_digits_lt' (cS σ) 4 8 (fun k hk => by simpa using hS k hk)
  have hAl : ∑ w ∈ Finset.range 16, wA σ w * 2 ^ (3 * w) < 2 ^ 48 :=
    sum_digits_lt' (wA σ) 3 16 (fun k hk => by simpa using hA k hk)
  have hm : marksNat σ = 2 ^ 26 * (∑ c ∈ Finset.range 8, cS σ c * 2 ^ (4 * c) +
      2 ^ 32 * ∑ w ∈ Finset.range 16, wA σ w * 2 ^ (3 * w)) := by
    rw [marksNat]; ring
  rw [← eOfNat192_of_lt (by omega), word_hi_eq_eOfNat192 (by omega), add_right_comm, hm,
    eOfNat192_add_shift (by omega), ← hm, show 2 ^ 64 * (N * 2 ^ 42) = 2 ^ 106 * N by ring,
    eOfNat192_add_shift (by rw [hm]; omega)]

/-- **What leanSPHINCS's verification checks**: the tree reaching `root`. -/
def SRoot (pp : PublicParameter) (m : Sphincs.Message) (sig : Sphincs.Signature)
    (root : Sphincs.Digest) : Prop :=
  ∃ leaf, @otsLeaf Id _ ⟨Node.keccakBits⟩ pp
      (digestIndex (@messageDigest Id _ ⟨Node.keccakBits⟩ pp m sig.randomness))
      (@forestRecover Id _ ⟨Node.keccakBits⟩ pp
        (digestIndex (@messageDigest Id _ ⟨Node.keccakBits⟩ pp m sig.randomness))
        (digestMarks (@messageDigest Id _ ⟨Node.keccakBits⟩ pp m sig.randomness)) sig.forest)
      sig.counter sig.chainValues = some leaf ∧
    @treeFold Id _ ⟨Node.keccakBits⟩ pp
      (digestIndex (@messageDigest Id _ ⟨Node.keccakBits⟩ pp m sig.randomness))
      (signaturePath sig) totalHeight leaf = root

theorem sphincsVerify_SRoot (pk : PublicKey) (m : Sphincs.Message) (sig : Sphincs.Signature) :
    Node.sphincsVerify pk m sig = true ↔ SRoot pk.parameter m sig pk.root :=
  sphincsVerify_iff pk m sig

variable {C : CallRel} {rd : Reader} {kret : List E → Prop}

/-- **The root `verify_sig_lean_sphincs` reaches**: the statements up to the root's check holding,
the counter a word below `2^32` and the unused bytes a word below `2^22`, the signature its frame
holds reaches the tree's root `σ sMk.2.2`. -/
theorem sphincs_root {σ : Val} {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ (sPrologue ++ (sCs.1 ++ (sMid ++ (sCw.1 ++ (sEndPre ++ rest))))) next kret)
    {Nc Nu : Nat} (hx : σ (.n sFb.2.1) = eOfNat Nc) (hNc32 : Nc < 2 ^ 32) (hNu : Nu < 2 ^ 22)
    (h161 : σ (.n 161) = σ (sNode 0) + word 0 (Nu * 2 ^ 42) 0) :
    Stmt.HoldsList C rd σ rest next kret ∧ SPre rd σ ∧
      SRoot (spp (σ sPP)) (smsg (σ (.n 5)) (σ (.n 6))) (sphincsSigOf σ) (sv (σ sMk.2.2)) := by
  have s0 := holdsList_split_atoms sPrologue_atoms h
  have hpa := atomsHold_of_holdsList sPrologue_atoms s0.1
  have hpre := sPrologue_sound hpa
  obtain ⟨s2, hcf⟩ := sCoords_sound (C := C) (rd := rd) (σ := σ) hpre.pad hpre.tws 8 0 s0.2
  obtain ⟨hrest, hmid, hcw, hsum, hd0, hla, hleafA, hmkA⟩ := sTailPre_sound hpre.pad s2
  refine ⟨hrest, hpre, ?_⟩
  have hidx26 := sIdx_lt σ
  -- the coordinates
  have hf : ∀ c < 8, CoordFacts σ c (cSt c).1 (cSt c).2.1 (cSt c).2.2 := fun c hc => by
    simpa using hcf c hc
  have hS : ∀ c < 8, cS σ c < 16 := fun c hc => (hf c hc).s_lt
  have hA : ∀ w < 16, wA σ w < 8 := by
    intro w hw
    have f := hf (w / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one w with h0 | h1
    · simp only [wA, cA, subBase, h0, ↓reduceIte]
      exact f.sub0.a_lt
    · simp only [wA, cA, subBase, h1, one_ne_zero, ↓reduceIte]
      exact f.sub1.a_lt
  have hT : ∀ w < 16, wT σ w < 256 := by
    intro w hw
    have f := hf (w / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one w with h0 | h1
    · simp only [wT, cT, subBase, h0, ↓reduceIte]
      exact f.sub0.t_lt
    · simp only [wT, cT, subBase, h1, one_ne_zero, ↓reduceIte]
      exact f.sub1.t_lt
  obtain ⟨acc1, acc2⟩ := cSt_acc hf 8 le_rfl
  rw [cSt_eight.1, encSum_eq hT] at acc1
  rw [cSt_eight.2, h161, sNode0_eq hpre, boundSum_eq hS hA, bound_cell hS hA hNu] at acc2
  have h17 : σ (.n 17) = eOfNat192 (encNat σ) := acc1
  obtain ⟨hVb, hVidx, hVs, hVa⟩ := bound_digits hS hA hidx26 hNu
  obtain ⟨hEnc, hEw⟩ := enc_digits hT
  set Vb := sIdx σ + marksNat σ + 2 ^ 106 * Nu with hVbdef
  have c17 : cellNat (σ (.n 17)) = encNat σ := by rw [h17, cellNat_eOfNat192 hEnc]
  have c18 : cellNat (σ (.n 18)) = Vb := by rw [acc2, cellNat_eOfNat192 hVb]
  have hmd : @messageDigest Id _ ⟨Node.keccakBits⟩ (spp (σ sPP))
      (smsg (σ (.n 5)) (σ (.n 6))) (sv (σ (.n 3))) =
      BitVec.ofNat messageDigestBits (encNat σ + 2 ^ 128 * Vb) := by
    rw [sMessageDigest_cells sq_keccak (a := σ (.n 4)) (m := smsg (σ (.n 5)) (σ (.n 6)))
      (by rw [hpre.msgAdr]; exact msgAdr_bytes)
      (sphincs_bytesLE_cellPairVal (σ (.n 5)) (σ (.n 6)) :
        Sphincs.bytesLE 32 (smsg (σ (.n 5)) (σ (.n 6))) = _), ← hpre.digest]
    simp only
    rw [c17, c18]
  unfold SRoot
  show ∃ leaf, @otsLeaf Id _ ⟨Node.keccakBits⟩ (spp (σ sPP))
      (digestIndex (@messageDigest Id _ ⟨Node.keccakBits⟩ (spp (σ sPP)) (smsg (σ (.n 5)) (σ (.n 6))) (sv (σ (.n 3)))))
      (@forestRecover Id _ ⟨Node.keccakBits⟩ (spp (σ sPP))
        (digestIndex (@messageDigest Id _ ⟨Node.keccakBits⟩ (spp (σ sPP)) (smsg (σ (.n 5)) (σ (.n 6))) (sv (σ (.n 3)))))
        (digestMarks (@messageDigest Id _ ⟨Node.keccakBits⟩ (spp (σ sPP)) (smsg (σ (.n 5)) (σ (.n 6))) (sv (σ (.n 3)))))
        (sphincsSigOf σ).forest)
      (sphincsSigOf σ).counter (sphincsSigOf σ).chainValues =
        some leaf ∧
      @treeFold Id _ ⟨Node.keccakBits⟩ (spp (σ sPP))
        (digestIndex (@messageDigest Id _ ⟨Node.keccakBits⟩ (spp (σ sPP)) (smsg (σ (.n 5)) (σ (.n 6))) (sv (σ (.n 3)))))
        (signaturePath (sphincsSigOf σ)) totalHeight leaf = sv (σ sMk.2.2)
  rw [hmd]
  set D := BitVec.ofNat messageDigestBits (encNat σ + 2 ^ 128 * Vb) with hD
  have hDidx : (digestIndex D).val = sIdx σ := by rw [hD, digestIndex_ofNat hEnc]; exact hVidx
  have hleafI : (digestIndex D).val = sIdx σ := hDidx
  have hmk : ∀ (c : Coord) (j : SubIdx), ((digestMarks D c).super).val = cS σ c.val ∧
      ((digestMarks D c).child j).val = cA σ c.val j.val ∧
      ((digestMarks D c).word j).val = cT σ c.val j.val := by
    intro c j
    obtain ⟨m1, m2, m3⟩ := digestMarks_ofNat (c1 := Vb) hEnc c j
    have hc8 : c.val < 8 := c.isLt
    have hj2 : j.val < 2 := j.isLt
    refine ⟨by rw [m1]; exact hVs c.val hc8, ?_, ?_⟩
    · rw [m2, hVa _ (by omega)]
      simp only [wA, show (2 * c.val + j.val) / 2 = c.val by omega,
        show (2 * c.val + j.val) % 2 = j.val by omega]
    · rw [m3, hEw _ (by omega)]
      simp only [wT, show (2 * c.val + j.val) / 2 = c.val by omega,
        show (2 * c.val + j.val) % 2 = j.val by omega]
  -- the forest key
  have hK : @forestRecover Id _ ⟨Node.keccakBits⟩ (spp (σ sPP)) (digestIndex D) (digestMarks D)
      (sphincsSigOf σ).forest = fun c => (sv (sT σ (2 * c.val)), sv (sT σ (2 * c.val + 1))) := by
    rw [forestRecover_id]
    funext c
    have f := hf c.val c.isLt
    have hp := getD_pairs (fun k => (cCoord (0 + k)).2.2.2.2.1) (fun k => (cCoord (0 + k)).2.2.2.2.2)
      (.n 0) 8 c.val c.isLt
    have e := sCoords_tops 8 0
    have t1 : sT σ (2 * c.val) = σ (cCoord c.val).2.2.2.2.1 := by
      unfold sT
      rw [show sCs = sCoords 8 0 (cSt 0).1 (cSt 0).2.1 (cSt 0).2.2 from rfl, e, hp.1, Nat.zero_add]
    have t2 : sT σ (2 * c.val + 1) = σ (cCoord c.val).2.2.2.2.2 := by
      unfold sT
      rw [show sCs = sCoords 8 0 (cSt 0).1 (cSt 0).2.1 (cSt 0).2.2 from rfl, e, hp.2, Nat.zero_add]
    rw [t1, t2]
    exact coordKey_eq hpre f (hmk c 0).1 (hmk c 0).2.1 (hmk c 1).2.1 (hmk c 0).2.2 (hmk c 1).2.2 hDidx
  -- the encoding
  have hE : cellBytes (σ (.n 164)) =
      tweakBytes (.encoding (digestIndex D)) := by
    rw [hpre.top1, sNode0_eq hpre]
    show _ = Sphincs.fieldBytes (Sphincs.tweakFields 4 0 0 (digestIndex D).val)
    rw [hleafI]
    exact encAdr_bytes hidx26
  have hcnt : Sphincs.bytesLE 4 (sphincsSigOf σ).counter =
      (cellBytes (σ (.n sFb.2.1))).take 4 :=
    bytesLE_counter (by rw [hx, cellNat_eOfNat (by omega)]; exact hNc32)
  set dig := cwDigit sW 21 (sEnc.2.1 + 10) σ with hdig
  have hdig4 : ∀ j, dig j < 4 := fun j => Nat.mod_lt _ (by norm_num)
  have hsum123 : ∑ i ∈ Finset.range numChains, dig i = targetSum := by
    have hle : ∑ i ∈ Finset.range (3 * 21 + 1), dig i ≤ ∑ _i ∈ Finset.range (3 * 21 + 1), 3 :=
      Finset.sum_le_sum fun j _ => by have := hdig4 j; omega
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
    show ∑ i ∈ Finset.range (3 * 21 + 1), dig i = 123
    exact Value.gen_pow_inj (by omega) (by norm_num) (hsum.trans sTarget_eq)
  have henc : @encode Id _ ⟨Node.keccakBits⟩ (spp (σ sPP))
      (digestIndex D)
      (fun c => (sv (sT σ (2 * c.val)), sv (sT σ (2 * c.val + 1))))
      (sphincsSigOf σ).counter = some fun i => ⟨dig i.val, hdig4 _⟩ := by
    rw [sEncode_cells sq_keccak (sT σ) (fun c => rfl) hE hcnt, ← hpre.top0,
      ← sEnc_sound hpre.pad hmid.left.right hNc32 hx, hd0]
    exact sDecode_lit hdig4 hsum123
  rw [hK, sOtsLeaf_id, henc, Option.map_some]
  refine ⟨_, rfl, ?_⟩
  -- the chains and the leaf
  have hrc : (fun i : ChainIndex => @recoverChain Id _ ⟨Node.keccakBits⟩ (spp (σ sPP))
      (digestIndex D) i ⟨dig i.val, hdig4 _⟩
      ((sphincsSigOf σ).chainValues i)) =
      fun i => sv (σ (cwTip sW (sEnc.2.1 + 10) i.val)) := by
    funext i
    show @recoverChain Id _ ⟨Node.keccakBits⟩ (spp (σ sPP))
      (digestIndex D) i ⟨dig i.val, hdig4 _⟩
      (sv (σ (cwStart sW 21 (sEnc.2.1 + 10) σ i.val))) = _
    rw [sRecoverChain_cells sq_keccak (pp := σ sPP)
      (adr := fun st => σ (sNode 0) + word (tw 1 + i.val * hiMul + st * stepMul) 0 0) (fun st => by
        rw [sNode0_eq hpre]
        show _ = Sphincs.fieldBytes (Sphincs.tweakFields 1 st.val i.val
          (digestIndex D).val)
        rw [hleafI]
        exact chainAdr_bytes hidx26 i.isLt st.isLt)]
    rw [(hcw i.val i.isLt).2, chainT_eq_sChain (fun s y => rfl)]
  have haL : cellBytes (σ (.n (sCw.2.1 + 1))) =
      tweakBytes (.leaf (digestIndex D)) := by
    rw [hla, sNode0_eq hpre]
    show _ = Sphincs.fieldBytes (Sphincs.tweakFields 2 0 0 (digestIndex D).val)
    rw [hleafI]
    exact leafAdr_bytes hidx26
  rw [hrc, sLeafHash_cells sq_keccak (tips := fun i => σ (cwTip sW (sEnc.2.1 + 10) i)) haL,
    show (hcell (σ sPP :: σ (.n (sCw.2.1 + 1)) ::
      (List.range numChains).map (fun i => σ (cwTip sW (sEnc.2.1 + 10) i)))).1 = σ (.n sLeaf.2.2)
      from (sLeaf_sound hpre.pad hleafA).symm]
  -- the tree
  have hpath : signaturePath (sphincsSigOf σ) =
      fun l => sv (if l < 26 then mSib σ sBit l (mBase sNodeOf 0 l sLeaf.2.1) else 0) := by
    funext l
    unfold signaturePath
    by_cases hl : l < 26
    · simp only [show totalHeight = 26 from rfl, hl, ↓reduceDIte, ↓reduceIte]
      rfl
    · simp only [show totalHeight = 26 from rfl, hl, ↓reduceDIte, ↓reduceIte]
      exact cellVal_zero.symm
  have hA : ∀ l < totalHeight, cellBytes (σ (mAdr sNodeOf l (mBase sNodeOf 0 l sLeaf.2.1))) =
      tweakBytes (.node (l + 1) ((digestIndex D).val / 2 ^ (l + 1))) := by
    intro l hl
    have hl26 : l < 26 := hl
    rw [sTree_adr hpre hmkA hl26]
    show _ = Sphincs.fieldBytes (Sphincs.tweakFields 3 0 (l + 1)
      ((digestIndex D).val / 2 ^ (l + 1)))
    rw [hleafI]
    exact nodeAdr_bytes hidx26 hl26
  rw [hpath, sTreeFold_cells sq_keccak (pp := σ sPP) hA _ totalHeight le_rfl]
  rw [sTree_sound hpre hmkA]
  refine congrArg sv (xFold_congr 26 (fun l hl => ⟨rfl, ?_, ?_⟩) _)
  · rw [hleafI, sIdx, bitsOf, testBit_bitsVal]
    simp only [hl, decide_true, Bool.true_and, sBit]
    congr
  · simp [hl]


/-- **`verify_sig_lean_sphincs` is sound**, for the signature its frame holds. -/
theorem verify_sig_lean_sphincs_sound_holds : verify_sig_lean_sphincs_sound_Spec sphincsSigOf := by
  intro C κ L hκ σ rets h
  rw [sBody_eq, sBody_split] at h
  have s0 := holdsList_split_atoms sPrologue_atoms h
  have hpa := atomsHold_of_holdsList sPrologue_atoms s0.1
  have hpre := sPrologue_sound hpa
  obtain ⟨s2, -⟩ := sCoords_sound (C := C) (rd := L.read) (σ := σ) hpre.pad hpre.tws 8 0 s0.2
  obtain ⟨hrets, hmid, -, -, -, -, -, -, hld0, hroot⟩ := sTail_sound hpre.pad s2
  refine ⟨hrets, fun hbb => ?_⟩
  -- the counter and the unused bytes
  have hfb : AtomsHold L.read σ sFb.1 := hmid.left.left.left.right
  have hcp : σ (.n sFb.2.1) = σ sFb.2.2 :=
    hmid.left.left.right.atom (a := .copy (.n sFb.2.1) sFb.2.2) (by simp [copyS])
  obtain ⟨Nc, hNc, hNclt⟩ := sFromBytes_sound hκ hbb (K := 256) (by norm_num) (by norm_num) g255W_eq
    (by norm_num) hfb
  have hNc32 : Nc < 2 ^ 32 := by simpa using hNclt
  obtain ⟨Nu, hNu, h161⟩ := sPrologue_bound hκ hbb hpa
  rw [sEnd_split] at h
  obtain ⟨-, -, hR⟩ := sphincs_root h (hcp.trans hNc) hNc32 hNu h161
  refine ⟨σ (.n sMk.2.1), σ sPP, σ (.n 5), σ (.n 6), ⟨hld0, hpre.ldP, hpre.ld2, hpre.ld3⟩, ?_⟩
  show Node.sphincsVerify ⟨sv (σ (.n sMk.2.1)), spp (σ sPP)⟩ (smsg (σ (.n 5)) (σ (.n 6)))
    (sphincsSigOf σ) = true
  rw [sphincsVerify_SRoot]
  have hr : σ sMk.2.2 = σ (.n sMk.2.1) := e_add_eq_zero_iff.mp hroot
  rw [hr] at hR
  exact hR

end
end LeanVM.Guest.B1.Sig
