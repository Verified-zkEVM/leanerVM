/-
  LeanVM.Guest.B1.Sig.SphincsComplete

  `verify_sig_lean_sphincs` (`lean_ethereum.py:3665-3752` at leanVM `542b0353`) is complete, loading
  only the claim and the byte table (`verify_sig_lean_sphincs_complete_loads`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBottomComplete
public import LeanVM.Guest.B1.Sig.SphincsBridge
public import LeanVM.Guest.B1.Sig.SphincsData
public import LeanVM.Guest.B1.Sig.SphincsLoads

/-!
# `verify_sig_lean_sphincs`, complete

The body splits into its stages (`sBody_split`): the digest calls (`sDigests_complete`), the fields
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

theorem sUpperM_eq : sUpperM = sUpper (.n 6827) (.n 7152) (.n 6825) 8 (7 + 1) 7165 := by
  rw [sUpperM, sH_eq, sPathB_snd.1, sPathB_snd.2]

theorem sUpperM_snd : sUpperM.2.1 = 7388 ∧ sUpperM.2.2 = .n 7375 := by decide +kernel

theorem sUpperT_eq : sUpperT = sUpper (.n 6829) (.n 7375) (.n 7388) 16 (9 + 1) 7389 := by
  rw [sUpperT, sH_eq, sUpperM_snd.1, sUpperM_snd.2]

theorem sUpperT_snd : sUpperT.2.1 = 7654 ∧ sUpperT.2.2 = .n 7641 := by decide +kernel

theorem sFors_eq : sFors.1 = (sForsTrees 24 0 1225).1 := rfl

theorem sBody_split : sBody = sDigests ++ (sFieldsBlock ++ (sFors.1 ++ (sBotPre ++
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
  rw [sBody_split, sPre]; simp only [List.append_assoc]

/-- The byte pointers: the unused bytes' and the three counters'. -/
def sPtrs : List Nat :=
  (List.range 7).map (fbPtr 1158) ++ (List.range 4).map (fbPtr 6836) ++ (List.range 4).map (fbPtr 7169) ++
    (List.range 4).map (fbPtr 7393)

theorem sBody_loads : listLoadsB sPtrs Data.core21.body = true := by
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

end
end LeanVM.Guest.B1.Sig
