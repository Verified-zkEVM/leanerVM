/-
  LeanVM.Guest.B1.Sig.SphincsComplete

  `verify_sig_lean_sphincs` (`lean_ethereum.py:3881-3968` at leanVM `9d8bce81`) is complete, loading
  only the claim and the byte table (`verify_sig_lean_sphincs_complete_loads`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBottomComplete
public import LeanVM.Guest.B1.Sig.SphincsBridge
public import LeanVM.Guest.B1.Sig.SphincsData
public import LeanVM.Guest.B1.Sig.SphincsLoads

/-!
# `verify_sig_lean_sphincs`, complete

The body splits into its stages (`sBody_stages`): the digest calls (`sDigests_complete`), the fields
(`sFields_complete`), the FORS trees (`sForsTrees_complete`, the signature's openings hinted), the
addresses and the bottom encoding (`sBotPre_complete`), the bottom layer's call and path
(`layerTail_complete`), the two layers above (`sUpper_complete`), and the root's check. The
statement's verification by stages (`verifyWithKeccak_iff_stages`) gives each layer's leaf and root,
and the bridges (`sphincsDigest_cells`, `forsRecover_cells`, `sTreeFold_cells`, `encTh_cells`) say
the guest's cells are their values. The loads are the claim's and the byte pointers'
(`listLoadsB`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (eOfNat kToNat)
open HashSig HashSig.OverPermutation

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The body's stages -/

/-- The root's check. -/
def sFinal : List Stmt := [loadS (.n 7654) (.n 0) 0, .atom (.assertEq (.n 7641) (.n 7654))]

theorem sPathB_eq : sPathB = sPath (.n 6821) 0 (7 + 1) 0 (.n 6997) (6997 + 1) := by
  rw [sPathB, sH_eq, sEncB_snd.1]

theorem sPathB_snd : sPathB.2.1 = 7165 ∧ sPathB.2.2 = .n 7152 := by decide +kernel

theorem sUpperM_upper : sUpperM = sUpper (.n 6827) (.n 7152) (.n 6825) 8 (7 + 1) 7165 := by
  rw [sUpperM, sH_eq, sPathB_snd.1, sPathB_snd.2]

theorem sUpperM_snd : sUpperM.2.1 = 7388 ∧ sUpperM.2.2 = .n 7375 := by decide +kernel

theorem sUpperT_upper : sUpperT = sUpper (.n 6829) (.n 7375) (.n 7388) 16 (9 + 1) 7389 := by
  rw [sUpperT, sH_eq, sUpperM_snd.1, sUpperM_snd.2]

theorem sUpperT_snd : sUpperT.2.1 = 7654 ∧ sUpperT.2.2 = .n 7641 := by decide +kernel

theorem sFors_eq : sFors.1 = (sForsTrees 24 0 1225).1 := rfl

theorem sBody_stages : sBody = sDigests ++ (sFieldsBlock ++ (sFors.1 ++ (sBotPre ++
    (([sWotsCall (.n 6826) (.n 6984) 6997] ++ sPathB.1) ++ (sUpperM.1 ++ ([cst 7388 (word 0 2 0)] ++
      (sUpperT.1 ++ (sFinal ++ [.ret []])))))))) := by
  have e1 := sEncB_snd
  have e2 := sUpperM_snd
  have e3 := sUpperT_snd
  simp only [sBody, sFieldsBlock, sBotPre, sFinal, List.append_assoc, List.cons_append, List.nil_append,
    sH_eq, e1.1, e1.2, e2.1, e3.1, e3.2]

theorem sDigests_nb : NumBelow 51 (Stmt.valsList sDigests) := numBelow_of_all (by decide +kernel)
theorem sFieldsBlock_nb : NumBelow 1225 (Stmt.valsList sFieldsBlock) := numBelow_of_all (by decide +kernel)
theorem sBotPre_nb : NumBelow 6997 (Stmt.valsList sBotPre) := numBelow_of_all (by decide +kernel)
theorem sTail0_nb : NumBelow 7165 (Stmt.valsList ([sWotsCall (.n 6826) (.n 6984) 6997] ++ sPathB.1)) :=
  numBelow_of_all (by decide +kernel)
theorem sUpperM_nb : NumBelow 7388 (Stmt.valsList sUpperM.1) := numBelow_of_all (by decide +kernel)
theorem sUpperT_nb : NumBelow 7654 (Stmt.valsList sUpperT.1) := numBelow_of_all (by decide +kernel)

/-! ## The scheme's side -/

theorem sCellPairVal_cellOf128 (m : HashSig.Message) :
    cellPairVal (cellOf128 (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128)) = m := by
  apply BitVec.eq_of_toNat_eq
  have hm : m.toNat < 2 ^ 256 := m.isLt
  rw [cellPairVal, BitVec.toNat_append, cellVal_cellOf128, cellVal_cellOf128, BitVec.extractLsb'_toNat,
    BitVec.extractLsb'_toNat, Nat.shiftLeft_eq, mul_comm, two_pow_mul_or (Nat.mod_lt _ (by positivity)),
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero, Nat.mod_eq_of_lt (a := m.toNat / 2 ^ 128) (by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa using hm)]
  exact Nat.div_add_mod _ _

/-- The digest's index and FORS leaves from its integer. -/
theorem digest_fields (Dn : Nat) :
    (Sphincs.digestIndex (BitVec.ofNat Sphincs.messageDigestBits Dn)).val = Dn % 2 ^ 26 ∧
      ∀ c : Sphincs.ForsTreeIndex,
        (Sphincs.digestForsLeaves (BitVec.ofNat Sphincs.messageDigestBits Dn) c).val = fieldNat Dn (3 + c.val) := by
  refine ⟨?_, fun c => ?_⟩
  · show (BitVec.extractLsb' 0 26 (BitVec.ofNat 266 Dn)).toNat = Dn % 2 ^ 26
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_mod_two_pow]
    by_cases hj : j < 26
    · have h266 : j < 266 := by omega
      simp only [hj, decide_true, Bool.true_and, h266]
    · simp only [hj, decide_false, Bool.false_and]
  · have hc : c.val < 24 := c.isLt
    show (BitVec.extractLsb' (26 + 10 * c.val) 10 (BitVec.ofNat 266 Dn)).toNat = fieldNat Dn (3 + c.val)
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, fieldNat, fOff_eq, fLen_eq, fOff, Nat.shiftRight_eq_div_pow]
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    by_cases hj : j < 10
    · have h266 : j + (26 + 10 * c.val) < 266 := by omega
      simp only [hj, decide_true, Bool.true_and, h266]
    · simp only [hj, decide_false, Bool.false_and]

theorem path_bits {σ : Val} {D f : Nat} (hb : BitsAt σ D) (hf : f < 27) :
    ∀ j < sFieldLen f, σ (sBit (sFieldOff f + j)) = if (fieldNat D f).testBit j then 1 else 0 := by
  intro j hj
  obtain ⟨-, -, -, h266⟩ := field_facts hf
  rw [hb _ (by omega), testBit_fieldNat D f j hj]

theorem path_vals {σ : Val} {D f : Nat} (hv : ValsAt σ D) (hf : f < 27) :
    ∀ j, j + 1 < sFieldLen f → σ (sVal (sFieldOff f + j + 1)) = eOfNat (fieldNat D f >>> (j + 1)) := by
  intro j hj
  rw [Nat.add_assoc]
  exact valsAt_field hv hf hj

/-- The statements before the root's check. -/
def sPre : List Stmt :=
  sDigests ++ (sFieldsBlock ++ (sFors.1 ++ (sBotPre ++ (([sWotsCall (.n 6826) (.n 6984) 6997] ++ sPathB.1) ++
    (sUpperM.1 ++ ([cst 7388 (word 0 2 0)] ++ sUpperT.1))))))

theorem sBody_split2 : sBody = sPre ++ (sFinal ++ [.ret []]) := by
  rw [sBody_stages, sPre]; simp only [List.append_assoc]

/-- The byte pointers: the unused bytes' and the three counters'. -/
def sPtrs : List Nat :=
  (List.range 7).map (fbPtr 1158) ++ (List.range 4).map (fbPtr 6836) ++ (List.range 4).map (fbPtr 7169) ++
    (List.range 4).map (fbPtr 7393)

theorem sBody_loads : listLoadsB sPtrs Data.core20.body = true := by
  rw [sBody_eq]; decide +kernel

/-- The valuation the proof starts from: the arguments and, past every stage, the key's root. -/
def sInit (p bb Rt : E) : Val :=
  Function.update (Function.update (Function.update (fun _ => (0 : E)) (.n 0) p) (.n 1) bb) (.n 7654) Rt

theorem sInit_vals (p bb Rt : E) : sInit p bb Rt (.n 0) = p ∧ sInit p bb Rt (.n 1) = bb ∧
    sInit p bb Rt (.n 7654) = Rt := by
  refine ⟨?_, ?_, Function.update_self ..⟩
  · rw [sInit, Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]
  · rw [sInit, Function.update_of_ne (by simp), Function.update_self]

/-- A FORS opening's secret. -/
def fSec (sig : Sphincs.Signature) (c : Nat) : HashSig.Digest :=
  if h : c < 24 then (sig.forsOpening ⟨c, h⟩).secret else 0

/-- A FORS opening's path. -/
def fPth (sig : Sphincs.Signature) (c l : Nat) : HashSig.Digest :=
  if h : c < 24 then (if hl : l < 10 then (sig.forsOpening ⟨c, h⟩).path ⟨l, hl⟩ else 0) else 0

theorem fSec_eq (sig : Sphincs.Signature) (c : Sphincs.ForsTreeIndex) : fSec sig c.val = (sig.forsOpening c).secret := by
  have hc : c.val < 24 := c.isLt
  simp [fSec, hc]

theorem fPth_eq (sig : Sphincs.Signature) (c : Sphincs.ForsTreeIndex) {l : Nat} (h : l < 10) :
    fPth sig c.val l = (sig.forsOpening c).path ⟨l, h⟩ := by
  have hc : c.val < 24 := c.isLt
  simp [fPth, hc, h]

/-- The FORS openings' secrets as cells. -/
def fSecretOf (sig : Sphincs.Signature) (c : Nat) : E := cellOf128 (fSec sig c)

/-- The FORS openings' paths as cells. -/
def fSibOf (sig : Sphincs.Signature) (c l : Nat) : E := cellOf128 (fPth sig c l)

/-- A layer's path as cells. -/
def lSib (sig : Sphincs.Signature) (layer : Sphincs.Layer) (l : Nat) : E :=
  cellOf128 (Sphincs.Verification.layerPath sig layer l)

/-- **The statement's stages over the guest's cells**: the digest's integer, the index, the FORS key
and each layer's leaf and root. -/
theorem stages_cells (pk : HashSig.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature)
    (hv : Sphincs.verifyWithKeccak pk m sig = true) :
    let Pc := cellOf128 pk.parameter
    let m0 := cellOf128 (m.extractLsb' 0 128)
    let m1 := cellOf128 (m.extractLsb' 128 128)
    let ρc := cellOf128 sig.randomizer
    let Dn := digestD (hcell [Pc, digestAdr 0, m0, m1, ρc]).1 (hcell [Pc, digestAdr 0, m0, m1, ρc]).2
      (hcell [Pc, digestAdr 1, m0, m1, ρc]).1
    let idx := Sphincs.digestIndex (sDigestOf pk m sig)
    let tops : Nat → E × E := fun k => fTops Pc (eOfNat (Dn % 2 ^ 26)) k (fieldNat Dn (3 + k)) (fSecretOf sig k)
      (fSibOf sig k)
    idx.val = Dn % 2 ^ 26 ∧ ∃ r0 r1 v0 v1 v2,
      Id.run (Sphincs.Verification.otsLeaf keccakF1600 pk.parameter 0 (Sphincs.treeOfIndex 0 idx)
        (Sphincs.leafOfIndex 0 idx) ((topsList tops).flatMap cellBytes) (sig.layers 0).counter
        (sig.layers 0).chainValues) = some v0 ∧
      Id.run (Sphincs.Verification.treeFold keccakF1600 pk.parameter 0 (Sphincs.treeOfIndex 0 idx)
        (Sphincs.leafOfIndex 0 idx) (Sphincs.Verification.layerPath sig 0) (7 + 1) v0) = r0 ∧
      (∀ x : E, cellVal x = r0 → Id.run (Sphincs.Verification.otsLeaf keccakF1600 pk.parameter 1
        (Sphincs.treeOfIndex 1 idx) (Sphincs.leafOfIndex 1 idx) ([x].flatMap cellBytes) (sig.layers 1).counter
        (sig.layers 1).chainValues) = some v1) ∧
      Id.run (Sphincs.Verification.treeFold keccakF1600 pk.parameter 1 (Sphincs.treeOfIndex 1 idx)
        (Sphincs.leafOfIndex 1 idx) (Sphincs.Verification.layerPath sig 1) (7 + 1) v1) = r1 ∧
      (∀ x : E, cellVal x = r1 → Id.run (Sphincs.Verification.otsLeaf keccakF1600 pk.parameter 2
        (Sphincs.treeOfIndex 2 idx) (Sphincs.leafOfIndex 2 idx) ([x].flatMap cellBytes) (sig.layers 2).counter
        (sig.layers 2).chainValues) = some v2) ∧
      Id.run (Sphincs.Verification.treeFold keccakF1600 pk.parameter 2 (Sphincs.treeOfIndex 2 idx)
        (Sphincs.leafOfIndex 2 idx) (Sphincs.Verification.layerPath sig 2) (9 + 1) v2) = pk.root := by
  intro Pc m0 m1 ρc Dn idx tops
  have hdig : sDigestOf pk m sig = BitVec.ofNat Sphincs.messageDigestBits Dn := by
    have := sphincsDigest_cells Pc m0 m1 ρc
    have e0 : cellVal Pc = pk.parameter := cellVal_cellOf128 _
    have e1 : cellVal ρc = sig.randomizer := cellVal_cellOf128 _
    have e2 : cellPairVal m0 m1 = m := sCellPairVal_cellOf128 m
    rw [e0, e1, e2] at this
    exact this
  obtain ⟨hidx, hleaves⟩ := digest_fields Dn
  rw [← hdig] at hidx hleaves
  have hK : sForsKeyOf pk m sig = fun c => (cellVal (tops c.val).1, cellVal (tops c.val).2) := by
    have := forsRecover_cells Pc idx (Sphincs.digestForsLeaves (sDigestOf pk m sig)) sig.forsOpening
      (secretOf := fSecretOf sig) (sibOf := fSibOf sig)
      (fun c => (cellVal_cellOf128 (fSec sig c.val)).trans (fSec_eq sig c))
      (fun c l h => (cellVal_cellOf128 (fPth sig c.val l)).trans (fPth_eq sig c h))
    have e0 : cellVal Pc = pk.parameter := cellVal_cellOf128 _
    rw [e0] at this
    unfold sForsKeyOf
    rw [this]
    funext c
    have hidx' : idx.val = Dn % 2 ^ 26 := hidx
    simp only [hidx', hleaves]
    rfl
  refine ⟨hidx, ?_⟩
  obtain ⟨r0, r1, h0, h1, h2⟩ := (verifyWithKeccak_iff_stages pk m sig).mp hv
  obtain ⟨v0, o0, f0⟩ := (layerReaches_iff _ _ _ _ _ _).mp h0
  obtain ⟨v1, o1, f1⟩ := (layerReaches_iff _ _ _ _ _ _).mp h1
  obtain ⟨v2, o2, f2⟩ := (layerReaches_iff _ _ _ _ _ _).mp h2
  rw [hK] at o0
  erw [forsKeyPayload_cells tops] at o0
  refine ⟨r0, r1, v0, v1, v2, o0, f0, fun x hx => ?_, f1, fun x hx => ?_, f2⟩
  · rw [← bytes16_cell, hx]; exact o1
  · rw [← bytes16_cell, hx]; exact o2

theorem sUpperM_end : (sUpper (.n 6827) (.n 7152) (.n 6825) 8 (7 + 1) 7165).2.1 = 7388 ∧
    (sUpper (.n 6827) (.n 7152) (.n 6825) 8 (7 + 1) 7165).2.2 = .n 7375 := by
  rw [← sUpperM_upper]; exact sUpperM_snd

theorem sUpperT_end : (sUpper (.n 6829) (.n 7375) (.n 7388) 16 (9 + 1) 7389).2.1 = 7654 ∧
    (sUpper (.n 6829) (.n 7375) (.n 7388) 16 (9 + 1) 7389).2.2 = .n 7641 := by
  rw [← sUpperT_upper]; exact sUpperT_snd

theorem sPathB_end : (sPath (.n 6821) 0 (7 + 1) 0 (.n 6997) (6997 + 1)).2.2 = .n 7152 := by
  rw [← sPathB_eq]; exact sPathB_snd.2

theorem mem_sPtrs {q : Nat} (h : q ∈ sPtrs) :
    (∃ k ≤ 6, q = fbPtr 1158 k) ∨ (∃ k ≤ 3, q = fbPtr 6836 k) ∨ (∃ k ≤ 3, q = fbPtr 7169 k) ∨
      ∃ k ≤ 3, q = fbPtr 7393 k := by
  simp only [sPtrs, List.mem_append, List.mem_map, List.mem_range] at h
  rcases h with ((⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩
  · exact Or.inl ⟨k, by omega, rfl⟩
  · exact Or.inr (Or.inl ⟨k, by omega, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨k, by omega, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨k, by omega, rfl⟩))

theorem fbPtr_lt {b k : Nat} (hk : k ≤ 6) : b ≤ fbPtr b k ∧ fbPtr b k < b + 56 := by
  simp only [fbPtr]; split <;> omega

/-- **`verify_sig_lean_sphincs` is complete, loading the claim and the byte table.** -/
theorem verify_sig_lean_sphincs_complete_loads : verify_sig_lean_sphincs_complete_loads_Spec := by
  intro C rd p bb pk m sig hC hm hbb hat hv
  obtain ⟨hldR, hldP, hld2, hld3⟩ := hat
  obtain ⟨hidx, r0, r1, v0, v1, v2, o0, f0, o1, f1, o2, f2⟩ := stages_cells pk m sig hv
  generalize hidxd : Sphincs.digestIndex (sDigestOf pk m sig) = idx at hidx o0 f0 o1 f1 o2 f2
  generalize hPc : cellOf128 pk.parameter = Pc at hidx o0 o1 o2 hldP
  have hPcc : IsCanonical128 Pc := hPc ▸ isCanonical128_cellOf128 _
  set m0 := cellOf128 (m.extractLsb' 0 128) with hm0
  set m1 := cellOf128 (m.extractLsb' 128 128) with hm1
  set ρc := cellOf128 sig.randomizer with hρc
  set Dn := digestD (hcell [Pc, digestAdr 0, m0, m1, ρc]).1 (hcell [Pc, digestAdr 0, m0, m1, ρc]).2
    (hcell [Pc, digestAdr 1, m0, m1, ρc]).1 with hDn
  set I := eOfNat (Dn % 2 ^ 26) with hI
  set tops : Nat → E × E := fun k => fTops Pc I k (fieldNat Dn (3 + k)) (fSecretOf sig k) (fSibOf sig k) with htopsd
  obtain ⟨fl0, fl1, fl2, ft0, ft1, ft2⟩ := idx_fields idx hidx
  have hσ0 := sInit_vals p bb (cellOf128 pk.root)
  -- the statements before the root's check
  have hPre : Completes C rd 2 7654 sPre (sInit p bb (cellOf128 pk.root)) (fun σ' =>
      σ' (.n 7641) = cellOf128 pk.root ∧ ∀ q ∈ sPtrs, BytePtr bb (σ' (.n q))) := by
    unfold sPre
    -- the digest calls
    refine Completes.append (m := 51) (by norm_num) (by norm_num) sDigests_nb
      (sDigests_complete (C := C) (rd := rd) (rho := ρc) _ hσ0.1 hldP hld2 hld3 hPcc (isCanonical128_cellOf128 _)
        (isCanonical128_cellOf128 _) (isCanonical128_cellOf128 _))
      (fun σA heA hA => ?_)
    obtain ⟨hA2, -, hApad, hA17, hA38⟩ := hA
    have hA1 : σA (.n 1) = bb := by rw [heA.apply (Or.inl (by norm_num))]; exact hσ0.2.1
    have e17 : σA (.n 17) = (hcell [Pc, digestAdr 0, m0, m1, ρc]).1 := congrArg Prod.fst hA17
    have e18 : σA (.n 18) = (hcell [Pc, digestAdr 0, m0, m1, ρc]).2 := congrArg Prod.snd hA17
    have e38 : σA (.n 38) = (hcell [Pc, digestAdr 1, m0, m1, ρc]).1 := congrArg Prod.fst hA38
    -- the fields
    refine Completes.append (m := 1225) (by norm_num) (by norm_num) sFieldsBlock_nb
      (sFields_complete (C := C) hm hbb σA hA1 (by rw [e17]; exact canon_hcell _)
        (by rw [e18]; exact canon_hcell_snd _) (by rw [e38]; exact canon_hcell _))
      (fun σB heB ⟨hB, hB1224⟩ => ?_)
    rw [e17, e18, e38, ← hDn] at hB
    obtain ⟨hBbits, hBvals, hBidx, hBptr⟩ := hB
    have tB : ∀ k < 51, σB (.n k) = σA (.n k) := fun k hk => heB.apply (Or.inl hk)
    have hB2 : σB sPP = Pc := by rw [show sPP = .n 2 from rfl, tB 2 (by norm_num)]; exact hA2
    have hBpad : PadOK σB sPad := hApad.congr (b := 51) (by unfold sPad; omega) (fun j hj => (tB j hj).symm)
    have hB1 : σB (.n 1) = bb := by rw [tB 1 (by norm_num)]; exact hA1
    -- the FORS trees
    have hsec : ∀ k, IsCanonical128 (fSecretOf sig k) := fun _ => isCanonical128_cellOf128 _
    have hsib : ∀ k l, IsCanonical128 (fSibOf sig k l) := fun _ _ => isCanonical128_cellOf128 _
    have hIc : IsCanonical128 I := canon_eOfNat _
    refine Completes.append (m := 6817) (by norm_num) (by norm_num)
      (by rw [sFors_eq]; exact sForsTrees_nb 24 0 1225 (by norm_num) le_rfl)
      (by rw [sFors_eq]
          exact (sForsTrees_complete (C := C) (rd := rd) hsec hsib hIc hPcc 24 0 1225 σB (by norm_num) le_rfl hBpad hB2
            hBidx hBbits hBvals).mono le_rfl (by norm_num) (fun _ h => h))
      (fun σC heC hCt => ?_)
    have tC : ∀ k < 1225, σC (.n k) = σB (.n k) := fun k hk => heC.apply (Or.inl hk)
    have htops : ∀ k < 24, σC (.n (1454 + 233 * k)) = (tops k).1 ∧ σC (.n (1455 + 233 * k)) = (tops k).2 := by
      intro k hk
      have := hCt k hk
      rw [show 1454 + 233 * k = 1225 + 233 * k + 229 by ring, show 1455 + 233 * k = 1225 + 233 * k + 230 by ring]
      refine ⟨(congrArg Prod.fst this).trans ?_, (congrArg Prod.snd this).trans ?_⟩ <;> simp [htopsd]
    have htc : ∀ k, IsCanonical128 (tops k).1 ∧ IsCanonical128 (tops k).2 := fun k => by
      simp only [htopsd, fTops, mPair]
      split
      · exact ⟨hsib k 9, canon_hcell _⟩
      · exact ⟨canon_hcell _, hsib k 9⟩
    have hCpad : PadOK σC sPad := hBpad.congr (b := 1225) (by unfold sPad; omega) (fun j hj => (tC j hj).symm)
    -- the addresses and the bottom encoding
    refine Completes.append (m := 6997) (by norm_num) (by norm_num) sBotPre_nb
      (sBotPre_complete (C := C) hm hbb (P := pk.parameter) idx hidx (sig.layers 0).counter tops htc σC hCpad
        (by rw [tC 1 (by norm_num)]; exact hB1) (by rw [tC 1224 (by norm_num), hB1224, hA2, ← hPc])
        (valsAt_congr hBvals (fun k hk => (tC k (by omega)).symm)) htops)
      (fun σD heD ⟨hDl0, hDl1, hDa0, hDa1, hDa2, hDenc, hDptr⟩ => ?_)
    have tD : ∀ k < 1225, σD (.n k) = σB (.n k) := fun k hk => by
      rw [heD.apply (Or.inl (by omega)), heC.apply (Or.inl hk)]
    have hDpad : PadOK σD sPad := hBpad.congr (b := 1225) (by unfold sPad; omega) (fun j hj => (tD j hj).symm)
    have hDpp : σD sPP = cellOf128 pk.parameter := by rw [show sPP = .n 2 from rfl, tD 2 (by norm_num), hPc]; exact hB2
    have hDbits := bitsAt_congr hBbits (fun k hk => (tD k (by omega)).symm)
    have hDvals := valsAt_congr hBvals (fun k hk => (tD k (by omega)).symm)
    have hD1 : σD (.n 1) = bb := by rw [tD 1 (by norm_num)]; exact hB1
    -- the bottom layer's call and path
    have hl0 : (Sphincs.leafOfIndex 0 idx).val < 2 ^ (7 + 1) := by rw [← fl0]; exact fieldNat_lt Dn 0
    refine Completes.append (m := 7165) (by norm_num) (by norm_num) sTail0_nb
      (by rw [sPathB_eq]
          exact layerTail_complete (C := C) (rd := rd) hC o0 (path := Sphincs.Verification.layerPath sig 0)
            (by norm_num) hl0 (adr := .n 6826) (lane := .n 6821) (off := 0) (o := 6984) (d := 6997) (by norm_num)
            (by norm_num) (by norm_num) ⟨6826, by norm_num, rfl⟩ ⟨6821, by norm_num, rfl⟩ σD hDpad hDpp hDa0
            (by rw [hDenc, hPc]) hDl0
            (fun j hj => by rw [← fl0]; exact path_bits hDbits (f := 0) (by norm_num) j hj)
            (fun j hj => by rw [← fl0]; exact path_vals hDvals (f := 0) (by norm_num) j hj))
      (fun σE heE hE => ?_)
    obtain ⟨hE0, hEc⟩ := hE
    rw [sPathB_end, f0] at hE0
    rw [sPathB_end] at hEc
    have tE : ∀ k < 6997, σE (.n k) = σD (.n k) := fun k hk => heE.apply (Or.inl hk)
    -- the middle layer
    have hl1 : (Sphincs.leafOfIndex 1 idx).val < 2 ^ (7 + 1) := by rw [← fl1]; exact fieldNat_lt Dn 1
    have hEpad : PadOK σE sPad := hDpad.congr (b := 6997) (by unfold sPad; omega) (fun j hj => (tE j hj).symm)
    refine Completes.append (m := 7388) (by norm_num) (by norm_num) sUpperM_nb
      (by rw [sUpperM_upper, ← sUpperM_end.1]
          exact (sUpper_complete (C := C) hm hbb hC (P := pk.parameter) (o1 _ hE0)
            (path := Sphincs.Verification.layerPath sig 1) (by norm_num) hl1 (adr := .n 6827) (below := .n 7152)
            (lane := .n 6825) (off := 8) (b := 7165) (by norm_num) (by norm_num) ⟨6827, by norm_num, rfl⟩
            ⟨7152, by norm_num, rfl⟩ ⟨6825, by norm_num, rfl⟩ σE hEpad (by rw [tE 1 (by norm_num)]; exact hD1)
            (by rw [show sPP = .n 2 from rfl, tE 2 (by norm_num)]; exact hDpp)
            (by rw [tE 6827 (by norm_num)]; exact hDa1) rfl hEc (by rw [tE 6825 (by norm_num)]; exact hDl1)
            (fun j hj => by
              rw [← fl1, show sBit (8 + j) = .n (51 + (8 + j)) from rfl, tE _ (by omega),
                ← show sBit (8 + j) = .n (51 + (8 + j)) from rfl]
              exact path_bits hDbits (f := 1) (by norm_num) j hj)
            (fun j hj => by
              obtain ⟨k, hk, ek⟩ := sVal_nb (i := 8 + j + 1) (by omega)
              rw [← fl1, ek, tE _ (by omega), ← ek]
              exact path_vals hDvals (f := 1) (by norm_num) j hj)))
      (fun σF heF hF => ?_)
    obtain ⟨hF0, hFc, hFptr⟩ := hF
    rw [sUpperM_end.2, f1] at hF0
    rw [sUpperM_end.2] at hFc
    have tF : ∀ k < 7165, σF (.n k) = σE (.n k) := fun k hk => heF.apply (Or.inl hk)
    -- the top layer's lane
    refine Completes.append (m := 7389) (by norm_num) (by norm_num) (nb_cst 7388 _) (cst_complete σF 7388 _)
      (fun σG heG hG => ?_)
    have tG : ∀ k < 7388, σG (.n k) = σF (.n k) := fun k hk => heG.apply (Or.inl hk)
    have hlane2 : σG (.n 7388) = laneCell 2 (Sphincs.treeOfIndex 2 idx) := by
      rw [hG, laneCell_val, word0_eq, ft2]; rfl
    -- the top layer
    have hl2 : (Sphincs.leafOfIndex 2 idx).val < 2 ^ (9 + 1) := by rw [← fl2]; exact fieldNat_lt Dn 2
    have tGE : ∀ k < 7165, σG (.n k) = σE (.n k) := fun k hk => by rw [tG k (by omega), tF k hk]
    have tGD : ∀ k < 6997, σG (.n k) = σD (.n k) := fun k hk => by rw [tGE k (by omega), tE k hk]
    have hlowG : (∀ k ≤ 6, BytePtr bb (σG (.n (fbPtr 1158 k)))) ∧ (∀ k ≤ 3, BytePtr bb (σG (.n (fbPtr 6836 k)))) ∧
        (∀ k ≤ 3, BytePtr bb (σG (.n (fbPtr 7169 k)))) := by
      refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
      · obtain ⟨b1, b2⟩ := fbPtr_lt (b := 1158) hk
        rw [tGD _ (by omega), tD _ (by omega)]; exact hBptr k hk
      · obtain ⟨b1, b2⟩ := fbPtr_lt (b := 6836) (k := k) (by omega)
        rw [tGD _ (by omega)]; exact hDptr k hk
      · obtain ⟨b1, b2⟩ := fbPtr_lt (b := 7169) (k := k) (by omega)
        rw [tG _ (by omega)]; exact hFptr k hk
    have hH := (sUpper_complete (C := C) hm hbb hC (P := pk.parameter) (o2 _ hF0)
                (path := Sphincs.Verification.layerPath sig 2) (by norm_num) hl2 (adr := .n 6829) (below := .n 7375)
                (lane := .n 7388) (off := 16) (b := 7389) (by norm_num) (by norm_num) ⟨6829, by norm_num, rfl⟩
                ⟨7375, by norm_num, rfl⟩ ⟨7388, by norm_num, rfl⟩ σG
                (hDpad.congr (b := 6997) (by unfold sPad; omega) (fun j hj => (tGD j hj).symm))
                (by rw [tGD 1 (by norm_num)]; exact hD1)
                (by rw [show sPP = .n 2 from rfl, tGD 2 (by norm_num)]; exact hDpp)
                (by rw [tGD 6829 (by norm_num)]; exact hDa2) (tG 7375 (by norm_num)) hFc hlane2
                (fun j hj => by
                  rw [← fl2, show sBit (16 + j) = .n (51 + (16 + j)) from rfl, tGD _ (by omega),
                    ← show sBit (16 + j) = .n (51 + (16 + j)) from rfl]
                  exact path_bits hDbits (f := 2) (by norm_num) j hj)
                (fun j hj => by
                  obtain ⟨k, hk, ek⟩ := sVal_nb (i := 16 + j + 1) (by omega)
                  rw [← fl2, ek, tGD _ (by omega), ← ek]
                  exact path_vals hDvals (f := 2) (by norm_num) j hj))
    rw [sUpperT_end.1, ← sUpperT_upper] at hH
    refine (hH.keep (Q := fun σ' => (∀ k ≤ 6, BytePtr bb (σ' (.n (fbPtr 1158 k)))) ∧
        (∀ k ≤ 3, BytePtr bb (σ' (.n (fbPtr 6836 k)))) ∧ (∀ k ≤ 3, BytePtr bb (σ' (.n (fbPtr 7169 k)))))
      (Q' := fun σ' => (∀ k ≤ 6, BytePtr bb (σ' (.n (fbPtr 1158 k)))) ∧
        (∀ k ≤ 3, BytePtr bb (σ' (.n (fbPtr 6836 k)))) ∧ (∀ k ≤ 3, BytePtr bb (σ' (.n (fbPtr 7169 k)))))
      hlowG (fun σ' he ⟨q1, q2, q3⟩ => ⟨fun k hk => by
          obtain ⟨b1, b2⟩ := fbPtr_lt (b := 1158) hk; rw [he.apply (Or.inl (by omega))]; exact q1 k hk,
        fun k hk => by
          obtain ⟨b1, b2⟩ := fbPtr_lt (b := 6836) (k := k) (by omega); rw [he.apply (Or.inl (by omega))]; exact q2 k hk,
        fun k hk => by
          obtain ⟨b1, b2⟩ := fbPtr_lt (b := 7169) (k := k) (by omega); rw [he.apply (Or.inl (by omega))]
          exact q3 k hk⟩)).mono le_rfl le_rfl (fun σH hH' => ?_)
    obtain ⟨⟨hH0, hHc, hHptr⟩, hl1', hl2', hl3'⟩ := hH'
    rw [sUpperT_snd.2, f2] at hH0
    rw [sUpperT_snd.2] at hHc
    refine ⟨by rw [← hH0, cellOf128_cellVal hHc], fun q hq => ?_⟩
    rcases mem_sPtrs hq with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact hl1' k hk
    · exact hl2' k hk
    · exact hl3' k hk
    · exact hHptr k hk
  -- the root's check and the loads
  obtain ⟨σf, hef, ⟨hroot, hptrs⟩, hhf⟩ := hPre
  have f0' : σf (.n 0) = p := by rw [hef.apply (Or.inl (by norm_num))]; exact hσ0.1
  have f1' : σf (.n 1) = bb := by rw [hef.apply (Or.inl (by norm_num))]; exact hσ0.2.1
  have f7654 : σf (.n 7654) = cellOf128 pk.root := by rw [hef.apply (Or.inr le_rfl)]; exact hσ0.2.2
  refine ⟨σf, f0', f1', ?_, ?_⟩
  · rw [sBody_eq, sBody_split2, holdsList_append]
    refine hhf _ _ ⟨?_, ?_, rfl⟩
    · show LoadHolds rd (σf (.n 0)) 0 (σf (.n 7654))
      rw [f0', f7654]; exact hldR
    · show σf (.n 7641) + σf (.n 7654) = 0
      rw [hroot, f7654]; exact e_add_self _
  · intro es vs hw A hA
    have hok := loads_of_walk sBody_loads hw
    rcases loadAddrs_of_loadOk hok A hA with ⟨k, hk, e⟩ | ⟨q, hq, e⟩
    · exact Or.inl ⟨k, hk, by rw [e, f0']⟩
    · obtain ⟨v, hv256, ev⟩ := hptrs q hq
      refine Or.inr ⟨v, hv256, ?_⟩
      rw [e, ev, limb_mul_ofK (hbb 0 (by norm_num)).1]

end
end LeanVM.Guest.B1.Sig
