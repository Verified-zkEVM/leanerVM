/-
  LeanVM.Guest.B1.Sig.SphincsComplete

  `verify_sig_lean_sphincs` is complete: for a claim held at `p` in its canonical cells and a
  signature that verifies it, on a memory of at least `256` words with the byte table at `bb`, its
  body holds of a valuation whose arguments are `p` and `bb`
  (`verify_sig_lean_sphincs_complete_holds`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsGlueComplete

/-!
# `verify_sig_lean_sphincs`, complete

The valuation: the claim's pointer, the byte table and, at the tree's end, the key's root. The
prologue loads `P` and the message, hints the randomizer, the index's bits and the unused bytes
(`sP_stage`); the forest's hints are the signature's openings under the digest's marks (`sF_stage`);
the counter is the signature's, the encoding's digest decodes to the codeword the Spec's encoding
(`sKey_eq`, `enc_lit`); the chains' starts and the path are the signature's (`sMid_complete`,
`sEnd_complete`). The root the frame reaches is then the Spec's (`sphincs_root`, `SRoot_unique`):
the key's root, which the last check compares with the claim's first word.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat gen)
open Sphincs Sphincs.Concrete

@[expose] public section

attribute [local irreducible] sCoords kMsg codewordT merkleT fkArms foldArms sCoord

variable {C : CallRel} {rd : Reader}

/-- The chains' starts a signature hints. -/
def sVals (sig : Sphincs.Signature) (i : Nat) : E :=
  if h : i < 64 then cellOf128 ((sig.layers topLayer).chainValues ⟨i, h⟩) else 0

/-- The path a signature hints. -/
def sSibs (sig : Sphincs.Signature) (l : Nat) : E :=
  if h : l < 26 then cellOf128 ((sig.layers topLayer).path ⟨l, h⟩) else 0

/-- The statements before the root's check. -/
def sPre : List Stmt := sPrologue ++ (sCs.1 ++ (sMid ++ (sCw.1 ++ sEndPre)))

/-- **What the final valuation holds**: the prologue's facts, the coordinates' hints, the counter's
word, the codeword's digits and starts, the path and a canonical root. -/
def SFinal (rd : Reader) (σ : Val) (Pc m0 m1 rho : E) (sig : Sphincs.Signature) (N17 N18 ctr : Nat) :
    Prop :=
  SP1 rd σ Pc m0 m1 rho ∧
    (∀ k < 8, ∃ e1 e2, CoordPost e1 e2 k (cSt k).1 (cSt k).2.1 (cSt k).2.2 (sH sig N17 N18 k) σ) ∧
    σ (.n sFb.2.1) = eOfNat ctr ∧
    (∃ Ncw, (∀ q ≤ 21, σ (.n (cwState sW (sEnc.2.1 + 10) q).2.2) = ofK (gpow (nDigits 21 Ncw q))) ∧
      ∀ i < 64, σ (cwPos sW 21 (sEnc.2.1 + 10) (nDigits 21 Ncw) i) = sVals sig i) ∧
    (∀ l < 26, mSib σ sBit l (mBase sNodeOf 0 l sLeaf.2.1) = sSibs sig l) ∧
    IsCanonical128 (σ sMk.2.2) ∧
    ∀ j < 4, σ (.n (sB + j)) = ofK (gpow (ctrByte ctr j))

theorem sPre_bounds : 206 ≤ sB ∧ sB ≤ sEnc.2.1 + 10 ∧ sEnc.2.1 + 10 ≤ sMk.2.1 := by
  have := sB_ge
  obtain ⟨e1, -⟩ := sEnc_ge
  obtain ⟨b1, b2, b3⟩ := sEnd_bounds
  exact ⟨this, by omega, by omega⟩

/-- **After the forest, complete**: the middle and the end, the counter, the codeword and the path
the signature's. -/
theorem sBack_stage (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) (sig : Sphincs.Signature)
    {Pc m0 m1 rho : E} (hPc : IsCanonical128 Pc) (σ2 : Val) (hp : SP1 rd σ2 Pc m0 m1 rho)
    (h1 : σ2 (.n 1) = bb) {H : Nat → CoordH} {E1 E2 : Nat → E}
    (hpost : ∀ k < 8, CoordPost (E1 k) (E2 k) k (cSt k).1 (cSt k).2.1 (cSt k).2.2 (H k) σ2)
    {Ncw : Nat}
    (hd : (digestScalars (keccak256 ((cellsBytes (σ2 (.n 162) :: σ2 (.n 164) ::
      (List.range 16).map (sT σ2) ++ [eOfNat (sig.layers topLayer).counter.toNat])).take 292))).1 =
        lit (∑ i ∈ Finset.range 64, Ncw / 4 ^ i % 4 * 4 ^ i))
    (hs : ∑ i ∈ Finset.range 64, Ncw / 4 ^ i % 4 = 123) :
    Completes C rd sB sMk.2.1 (sMid ++ (sCw.1 ++ sEndPre)) σ2 (fun σ' =>
      σ' (.n sFb.2.1) = eOfNat (sig.layers topLayer).counter.toNat ∧
      (∀ q ≤ 21, σ' (.n (cwState sW (sEnc.2.1 + 10) q).2.2) = ofK (gpow (nDigits 21 Ncw q))) ∧
      (∀ i < 64, σ' (cwPos sW 21 (sEnc.2.1 + 10) (nDigits 21 Ncw) i) = sVals sig i) ∧
      (∀ l < 26, mSib σ' sBit l (mBase sNodeOf 0 l sLeaf.2.1) = sSibs sig l) ∧
      IsCanonical128 (σ' sMk.2.2) ∧
      ∀ j < 4, σ' (.n (sB + j)) = ofK (gpow (ctrByte (sig.layers topLayer).counter.toNat j))) := by
  obtain ⟨hB, hBE, hEM⟩ := sPre_bounds
  have hpre := sPrologue_sound hp.atoms
  have hn0 : IsCanonical128 (σ2 (sNode 0)) := by
    rw [sNode0_eq hpre, ← word_eq_eOfNat]; exact canon_word _ 0
  have hP : IsCanonical128 (σ2 sPP) := by rw [hp.pp]; exact hPc
  refine Completes.append (m := sEnc.2.1 + 10) hBE hEM sMid_nb
    (sMid_complete hm hbb σ2 h1 hP hn0 (by rw [hpre.top0]; exact hP)
      (by rw [hpre.top1]; exact canon_add hn0 (canon_word _ _)) (sT_canon hpost) hpre.pad
      (sig.layers topLayer).counter.isLt hd) (fun σ3 he3 hp3 => ?_)
  obtain ⟨m1', m2', m3', m4'⟩ := hp3
  have hag : AgreeBelow sB σ2 σ3 := he3.agree
  have hp3 := hp.frame (hag.mono hB)
  have hpre3 := sPrologue_sound hp3.atoms
  obtain ⟨σ4, he4, ⟨hc4, hk4⟩, hh4⟩ := sEnd_complete (C := C) hm σ3 m3' (N := Ncw) m2' hs (sVals sig)
    (fun _ => canon_dite) (bits := (cellNat (σ3 (.n 18))).testBit) (fun l hl => hp3.bits l hl)
    (fun l hl => by rw [hpre3.nodes l hl, ← word_eq_eOfNat]; exact canon_word _ 0)
    (sibs := sSibs sig) (fun _ _ => canon_dite)
  obtain ⟨k1, k2, k3⟩ := hk4 σ4 (fun _ _ => rfl)
  obtain ⟨b1, -, -⟩ := sEnd_bounds
  have hfb : sFb.2.1 < sEnc.2.1 + 10 := by
    obtain ⟨f1, -, -⟩ := sFb_shape; obtain ⟨e1, -⟩ := sEnc_ge; omega
  exact ⟨σ4, he4, ⟨by rw [he4.apply (Or.inl hfb)]; exact m1', k1, k2, k3, hc4,
    fun j hj => by
      rw [he4.apply (Or.inl (by obtain ⟨e1, -⟩ := sEnc_ge; omega))]; exact m4' j hj⟩, hh4⟩

theorem sCellPairVal_cellOf128 (m : Sphincs.Message) :
    cellPairVal (cellOf128 (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128)) = m := by
  apply BitVec.eq_of_toNat_eq
  have hm : m.toNat < 2 ^ 256 := m.isLt
  rw [cellPairVal, BitVec.toNat_append, cellVal_cellOf128, cellVal_cellOf128, BitVec.extractLsb'_toNat,
    BitVec.extractLsb'_toNat, Nat.shiftLeft_eq, mul_comm, two_pow_mul_or (Nat.mod_lt _ (by positivity)),
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero, Nat.mod_eq_of_lt (a := m.toNat / 2 ^ 128) (by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa using hm)]
  exact Nat.div_add_mod _ _

/-- The message's bytes, as its two cells'. -/
theorem sphincs_msg_bytes (m : Sphincs.Message) :
    Sphincs.bytesLE 32 m = cellBytes (cellOf128 (m.extractLsb' 0 128)) ++
      cellBytes (cellOf128 (m.extractLsb' 128 128)) := by
  rw [← sphincs_bytesLE_cellPairVal]
  congr 1
  exact (sCellPairVal_cellOf128 m).symm

/-- **The stages complete**, from a valuation holding the claim's pointer and the byte table. -/
theorem sStages (hm : MemOK rd 256) {p bb : E} (hbb : ByteBits rd bb) (pk : Sphincs.PublicKey)
    (m : Sphincs.Message) (sig : Sphincs.Signature) (hv : SRoot pk.parameter pk.root m sig pk.root)
    (σ0 : Val) (h0 : σ0 (.n 0) = p) (h1 : σ0 (.n 1) = bb)
    (hldP : LoadHolds rd p 1 (cellOf128 pk.parameter))
    (hld2 : LoadHolds rd p 2 (cellOf128 (m.extractLsb' 0 128)))
    (hld3 : LoadHolds rd p 3 (cellOf128 (m.extractLsb' 128 128))) :
    Completes C rd 2 sMk.2.1 sPre σ0 (fun σ' => SFinal rd σ' (cellOf128 pk.parameter)
      (cellOf128 (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128)) (cellOf128 sig.randomness) sig
      (cellNat (hcell [cellOf128 pk.parameter, word (tw 12) 0 0, cellOf128 (m.extractLsb' 0 128),
        cellOf128 (m.extractLsb' 128 128), cellOf128 sig.randomness]).1)
      (cellNat (hcell [cellOf128 pk.parameter, word (tw 12) 0 0, cellOf128 (m.extractLsb' 0 128),
        cellOf128 (m.extractLsb' 128 128), cellOf128 sig.randomness]).2)
      (sig.layers topLayer).counter.toNat) := by
  obtain ⟨hB, hBE, hEM⟩ := sPre_bounds
  set Pc := cellOf128 pk.parameter with hPc
  set m0 := cellOf128 (m.extractLsb' 0 128) with hm0
  set m1 := cellOf128 (m.extractLsb' 128 128) with hm1
  set rho := cellOf128 sig.randomness with hrho
  set dg := hcell [Pc, word (tw 12) 0 0, m0, m1, rho] with hdg
  set N17 := cellNat dg.1 with hN17
  set N18 := cellNat dg.2 with hN18
  set ctr := (sig.layers topLayer).counter.toNat with hctr
  have cPc : IsCanonical128 Pc := isCanonical128_cellOf128 _
  -- the digest
  have hmd : @messageDigest Id _ ⟨Node.keccakBits⟩ pk.parameter pk.root m sig.randomness =
      BitVec.ofNat messageDigestBits (N17 + 2 ^ 128 * N18) := by
    have := sMessageDigest_cells sq_keccak (pp := Pc) (a := word (tw 12) 0 0) (m0 := m0) (m1 := m1)
      (rho := rho) (root := pk.root) (m := m) msgAdr_bytes (sphincs_msg_bytes m)
    rwa [show spp Pc = pk.parameter from cellVal_cellOf128 _,
      show sv rho = sig.randomness from cellVal_cellOf128 _] at this
  unfold sPre
  -- the prologue
  refine Completes.append (m := 206) (by norm_num) (by omega) sPrologue_nb
    (sP_stage (rho := rho) hm hbb σ0 h0 h1 hldP hld2 hld3 cPc (isCanonical128_cellOf128 _)
      (isCanonical128_cellOf128 _) (isCanonical128_cellOf128 _)) (fun σ1 he1 hp1 => ?_)
  have e17 : cellNat (σ1 (.n 17)) = N17 := by rw [show σ1 (.n 17) = dg.1 from congrArg Prod.fst hp1.dg]
  have e18 : cellNat (σ1 (.n 18)) = N18 := by rw [show σ1 (.n 18) = dg.2 from congrArg Prod.snd hp1.dg]
  have hF := (sF_stage (C := C) hm sig σ1 hp1 cPc).withHolds
  rw [e17, e18] at hF
  -- the forest
  refine Completes.append (m := sB) hB (by omega) sCs_nb hF (fun σ2 he2 ⟨hp2, hh2⟩ => ?_)
  have hag2 : AgreeBelow 206 σ1 σ2 := he2.agree
  have hp12 := hp1.frame hag2
  have hpre2 := sPrologue_sound hp12.atoms
  have hpost2 := hp2 σ2 (fun _ _ => rfl)
  have e18' : cellNat (σ2 (.n 18)) = N18 := by rw [← hag2 18 (by norm_num)]; exact e18
  have hidx2 : sIdx σ2 = N18 % 2 ^ 26 := by rw [sIdx_eq hp12.bits, e18']
  obtain ⟨-, hcf⟩ := sCoords_sound (C := C) (rd := rd) (σ := σ2) (rest := []) hpre2.pad hpre2.tws 8 0
    (by rw [List.append_nil]; exact hh2)
  have hcf' : ∀ c < 8, CoordFacts σ2 c (cSt c).1 (cSt c).2.1 (cSt c).2.2 := fun c hc => by
    simpa using hcf c hc
  have hkey := sKey_eq hpre2 hcf' sig (N17 := N17) (N18 := N18) (cellNat_lt _) hidx2 _ _ hpost2
  rw [hp12.pp, show spp Pc = pk.parameter from cellVal_cellOf128 _] at hkey
  -- the Spec's encoding
  obtain ⟨leaf, hots, -⟩ := hv
  rw [hmd, hkey, sOtsLeaf_id] at hots
  obtain ⟨enc, henc, -⟩ := Option.map_eq_some_iff.mp hots
  have hidx26 := sIdx_lt σ2
  have hleafI : (leafIndexAt (digestIndex (BitVec.ofNat messageDigestBits (N17 + 2 ^ 128 * N18)))
      topLayer).val = sIdx σ2 := by
    rw [leafIndexAt_top, digestIndex_ofNat (cellNat_lt _), hidx2]
  have hE : cellBytes (σ2 (.n 164)) = tweakBytes (.encoding topLayer 0
      (leafIndexAt (digestIndex (BitVec.ofNat messageDigestBits (N17 + 2 ^ 128 * N18))) topLayer)) := by
    rw [hpre2.top1, sNode0_eq hpre2]
    show _ = Sphincs.fieldBytes (Sphincs.tweakFields 4 0 0 _)
    rw [hleafI]
    exact encAdr_bytes hidx26
  have hc : Sphincs.bytesLE 4 (sig.layers topLayer).counter = (cellBytes (eOfNat ctr)).take 4 := by
    have hc32 : ctr < 2 ^ 32 := (sig.layers topLayer).counter.isLt
    have e : BitVec.ofNat (8 * 4) (cellNat (eOfNat ctr)) = (sig.layers topLayer).counter := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, cellNat_eOfNat (by omega), Nat.mod_eq_of_lt (by norm_num; omega)]
      exact hctr
    rw [← e]
    exact bytesLE_counter (by rw [cellNat_eOfNat (by omega)]; exact hc32)
  rw [show pk.parameter = spp Pc from (cellVal_cellOf128 _).symm,
    sEncode_cells sq_keccak (pp := Pc) (aE := σ2 (.n 164)) (x := eOfNat ctr) (sT σ2) (fun _ => rfl) hE hc]
    at henc
  have hcanE : IsCanonical128 (digestScalars (keccak256 ((cellsBytes (Pc :: σ2 (.n 164) ::
      (List.range 16).map (sT σ2) ++ [eOfNat ctr])).take 292))).1 := by
    simp [IsCanonical128, digestScalars]
  obtain ⟨hlit, hs⟩ := enc_lit hcanE henc
  -- the middle and the end
  have hback := sBack_stage (C := C) hm hbb sig cPc σ2 hp12
    (by rw [← hag2 1 (by norm_num), he1.apply (Or.inl (by norm_num))]; exact h1) hpost2
    (by rw [hpre2.top0, hp12.pp]; exact hlit) hs
  refine (hback.keep (Q := fun _ => True) (Q' := fun σ' => AgreeBelow sB σ2 σ') trivial
    (fun σ' he _ => he.agree)).mono le_rfl le_rfl (fun σ4 ⟨⟨k0, k1, k2, k3, k4, k5⟩, hag4⟩ => ?_)
  exact ⟨hp12.frame (hag4.mono hB), fun k hk => ⟨_, _, hp2 σ4 hag4 k hk⟩, k0, ⟨_, k1, k2⟩, k3, k4, k5⟩

/-- **The root the final valuation reaches is the key's.** -/
theorem sRoot_final {pk : Sphincs.PublicKey} {m : Sphincs.Message} {sig : Sphincs.Signature}
    (hv : SRoot pk.parameter pk.root m sig pk.root) {σ : Val} {N17 N18 : Nat}
    (hf : SFinal rd σ (cellOf128 pk.parameter) (cellOf128 (m.extractLsb' 0 128))
      (cellOf128 (m.extractLsb' 128 128)) (cellOf128 sig.randomness) sig N17 N18
      (sig.layers topLayer).counter.toNat)
    (hh : Stmt.HoldsList C rd σ sPre True (fun _ => True)) :
    σ sMk.2.2 = cellOf128 pk.root := by
  obtain ⟨hsp, hcp, hfb, ⟨Ncw, hdg, hst⟩, hsb, hcan, -⟩ := hf
  have hpre := sPrologue_sound hsp.atoms
  have hNu : cellNat (σ (.n 18)) / 2 ^ 106 < 2 ^ 22 := by have := cellNat_lt (σ (.n 18)); omega
  have h161 : σ (.n 161) = σ (sNode 0) + word 0 (cellNat (σ (.n 18)) / 2 ^ 106 * 2 ^ 42) 0 := by
    rw [hpre.bound0, hsp.unused, word_hi_mul hNu]
  obtain ⟨-, -, hR⟩ := sphincs_root (C := C) (rd := rd) (rest := []) (next := True) (kret := fun _ => True)
    (by rw [List.append_nil]; exact hh) hfb (sig.layers topLayer).counter.isLt hNu h161 pk.root
  rw [hsp.pp, hsp.c5, hsp.c6, show spp (cellOf128 pk.parameter) = pk.parameter from cellVal_cellOf128 _,
    show smsg (cellOf128 (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128)) = m from
      sCellPairVal_cellOf128 m] at hR
  have hr := SRoot_unique hv hR (by
      show sv (σ (.n 3)) = _
      rw [hsp.r]; exact cellVal_cellOf128 _)
    (by
      funext c
      show coordOpening σ c.val (cSt c.val).1 (cSt c.val).2.1 (cSt c.val).2.2 = sig.forest c
      obtain ⟨e1, e2, hP⟩ := hcp c.val c.isLt
      rw [coordOpening_eq (dS_lt _ _) (dT_lt _ _) (dA_lt _ _) (dT_lt _ _) (dA_lt _ _) hP]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt c.isLt))
    (by
      show (⟨BitVec.ofNat counterBits (cellNat (σ (.n sFb.2.1))),
          fun i => sv (σ (cwStart sW 21 (sEnc.2.1 + 10) σ i.val)),
          fun l => sv (mSib σ sBit l.val (mBase sNodeOf 0 l.val sLeaf.2.1))⟩ : LayerSignature topLayer) =
        ⟨(sig.layers topLayer).counter, (sig.layers topLayer).chainValues, (sig.layers topLayer).path⟩
      simp only [LayerSignature.mk.injEq]
      refine ⟨?_, funext fun i => ?_, funext fun l => ?_⟩
      · apply BitVec.eq_of_toNat_eq
        rw [hfb, BitVec.toNat_ofNat, cellNat_eOfNat (by
          have : (sig.layers topLayer).counter.toNat < 2 ^ 32 := (sig.layers topLayer).counter.isLt; omega),
          Nat.mod_eq_of_lt (sig.layers topLayer).counter.isLt]
      · rw [cwStart_eq_cwPos (fun q _ => nDigits_lt 21 Ncw q) hdg (show i.val < 3 * 21 + 1 by
          have := i.isLt; simp only [numChains] at this; omega),
          hst i.val i.isLt]
        exact sv_dite i
      · rw [hsb l.val l.isLt]
        exact sv_dite l)
  rw [← hr]
  exact (cellOf128_cellVal hcan).symm

/-- **The valuation completeness builds**: its arguments, the body holding, and what the final
valuation holds (for the loads' addresses, `SphincsLoads`). -/
theorem sphincs_complete_val (C : CallRel) (rd : Reader) (p bb : E) (pk : Sphincs.PublicKey)
    (m : Sphincs.Message) (sig : Sphincs.Signature) (hm : MemOK rd 256) (hbb : ByteBits rd bb)
    (hat : ClaimAt rd p (cellOf128 pk.root) (cellOf128 pk.parameter) (cellOf128 (m.extractLsb' 0 128))
      (cellOf128 (m.extractLsb' 128 128)))
    (hv : Node.sphincsVerify pk m sig = true) :
    ∃ σf : Val, σf (.n 0) = p ∧ σf (.n 1) = bb ∧
      Stmt.HoldsList C rd σf Data.core20.body False (fun rs => rs = []) ∧
      SFinal rd σf (cellOf128 pk.parameter) (cellOf128 (m.extractLsb' 0 128))
        (cellOf128 (m.extractLsb' 128 128)) (cellOf128 sig.randomness) sig
        (cellNat (hcell [cellOf128 pk.parameter, word (tw 12) 0 0, cellOf128 (m.extractLsb' 0 128),
          cellOf128 (m.extractLsb' 128 128), cellOf128 sig.randomness]).1)
        (cellNat (hcell [cellOf128 pk.parameter, word (tw 12) 0 0, cellOf128 (m.extractLsb' 0 128),
          cellOf128 (m.extractLsb' 128 128), cellOf128 sig.randomness]).2)
        (sig.layers topLayer).counter.toNat ∧
      Stmt.HoldsList C rd σf sPre True (fun _ => True) := by
  obtain ⟨hldR, hldP, hldLo, hldHi⟩ := hat
  rw [sphincsVerify_SRoot] at hv
  obtain ⟨hB, hBE, hEM⟩ := sPre_bounds
  set σ0 : Val := Function.update (Function.update (Function.update (fun _ => (0 : E)) (.n 0) p)
    (.n 1) bb) (.n sMk.2.1) (cellOf128 pk.root) with hσ0
  have i0 : σ0 (.n 0) = p := by
    rw [hσ0, Function.update_of_ne (by simp; omega), Function.update_of_ne (by simp), Function.update_self]
  have i1 : σ0 (.n 1) = bb := by
    rw [hσ0, Function.update_of_ne (by simp; omega), Function.update_self]
  have iR : σ0 (.n sMk.2.1) = cellOf128 pk.root := Function.update_self ..
  obtain ⟨σf, hef, hpf, hhf⟩ := sStages (C := C) hm hbb pk m sig hv σ0 i0 i1 hldP hldLo hldHi
  have hroot := sRoot_final hv hpf (hhf True _ trivial)
  refine ⟨σf, by rw [hef.apply (Or.inl (by norm_num))]; exact i0,
    by rw [hef.apply (Or.inl (by norm_num))]; exact i1, ?_, hpf, hhf True _ trivial⟩
  rw [sBody_eq, sBody_split, sEnd_split]
  rw [show sPrologue ++ (sCs.1 ++ (sMid ++ (sCw.1 ++ (sEndPre ++ [loadS (.n sMk.2.1) (.n 0) 0,
      .atom (.assertEq sMk.2.2 (.n sMk.2.1)), .ret []])))) =
      sPre ++ ([loadS (.n sMk.2.1) (.n 0) 0, .atom (.assertEq sMk.2.2 (.n sMk.2.1))] ++ [.ret []]) by
    simp [sPre]]
  rw [holdsList_append]
  refine hhf _ _ ?_
  rw [holdsList_append]
  have hEf : σf (.n sMk.2.1) = cellOf128 pk.root := by rw [hef.apply (Or.inr le_rfl)]; exact iR
  refine holdsList_of_atomsHold rfl (fun a ha => ?_) _ _ rfl
  simp only [loadS, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · show LoadHolds rd (σf (.n 0)) 0 (σf (.n sMk.2.1))
    rw [hef.apply (Or.inl (by norm_num)), i0, hEf]
    exact hldR
  · show σf sMk.2.2 + σf (.n sMk.2.1) = 0
    rw [hroot, hEf]
    exact e_add_self _

/-- **`verify_sig_lean_sphincs` is complete.** -/
theorem verify_sig_lean_sphincs_complete_holds : verify_sig_lean_sphincs_complete_Spec := by
  intro C rd p bb pk m sig hm hbb hat hv
  obtain ⟨σf, h0, h1, hb, -⟩ := sphincs_complete_val C rd p bb pk m sig hm hbb hat hv
  exact ⟨σf, h0, h1, hb⟩

end
end LeanVM.Guest.B1.Sig
