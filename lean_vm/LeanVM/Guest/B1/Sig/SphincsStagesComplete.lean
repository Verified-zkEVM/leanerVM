/-
  LeanVM.Guest.B1.Sig.SphincsStagesComplete

  The prologue and the forest of `verify_sig_lean_sphincs` complete for a signature: the forest's
  hints its openings and the message digest's marks.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSpecComplete

/-!
# The prologue and the forest, complete

* `SP1`: what the prologue's valuation holds; `sP_stage`: the prologue completes to it;
* `sH`: the forest's hints of a signature, from the digest's cells' integers;
* `sF_stage`: the forest completes, its hints kept.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat gen)
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash

@[expose] public section

attribute [local irreducible] sCoords

variable {C : CallRel} {rd : Reader}

theorem canon_hcell2 (cs : List E) : IsCanonical128 (hcell cs).2 := by
  simp [IsCanonical128, hcell, digestScalars]

theorem sIdx_eq {σ : Val} {N : Nat} (h : ∀ l < 26, σ (.n (30 + l)) = if N.testBit l then 1 else 0) :
    sIdx σ = N % 2 ^ 26 := by
  unfold sIdx bitsOf
  rw [← bitsVal_testBit (Nat.mod_lt N (by positivity) : N % 2 ^ 26 < 2 ^ 26)]
  refine bitsVal_congr fun i hi => ?_
  rw [h i hi, Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and]
  cases N.testBit i <;> simp

/-- What the prologue's valuation holds: its atoms, `P`, the randomizer and the message where it
reads them, the digest's cells, the index's bits and the unused bytes' word. -/
structure SP1 (rd : Reader) (σ : Val) (Pc m0 m1 rho : E) : Prop where
  atoms : AtomsHold rd σ sPrologue
  pp : σ sPP = Pc
  r : σ (.n 3) = rho
  c5 : σ (.n 5) = m0
  c6 : σ (.n 6) = m1
  dg : (σ (.n 17), σ (.n 18)) = hcell [Pc, word (tw 12) 0 0, m0, m1, rho]
  bits : ∀ l < 26, σ (.n (30 + l)) = if (cellNat (σ (.n 18))).testBit l then 1 else 0
  unused : σ (.n 158) = eOfNat (cellNat (σ (.n 18)) / 2 ^ 106)

/-- **The prologue completes** to `SP1`. -/
theorem sP_stage (hm : MemOK rd 256) {bb p Pc m0 m1 rho : E} (hbb : ByteBits rd bb)
    (σ : Val) (h0 : σ (.n 0) = p) (h1 : σ (.n 1) = bb) (hldP : LoadHolds rd p 1 Pc)
    (hld2 : LoadHolds rd p 2 m0) (hld3 : LoadHolds rd p 3 m1) (hPc : IsCanonical128 Pc)
    (hc0 : IsCanonical128 m0) (hc1 : IsCanonical128 m1) (hrho : IsCanonical128 rho) :
    Completes C rd 2 206 sPrologue σ (fun σ' => SP1 rd σ' Pc m0 m1 rho) := by
  refine (sPrologue_complete (C := C) hm hbb σ h0 h1 hldP hld2 hld3 hPc hc0 hc1 hrho).withHolds.mono
    le_rfl le_rfl (fun σ' ⟨⟨e2, e3, e5, e6, eb, eu⟩, hh⟩ => ?_)
  have ha := atomsHold_of_holdsList sPrologue_atoms hh
  have hpre := sPrologue_sound ha
  refine ⟨ha, e2, e3, e5, e6, ?_, eb, eu⟩
  rw [hpre.digest, e2, hpre.msgAdr, e5, e6, e3]

theorem SP1.frame {σ σ' : Val} {Pc m0 m1 rho : E} (h : SP1 rd σ Pc m0 m1 rho) (hag : AgreeBelow 206 σ σ') :
    SP1 rd σ' Pc m0 m1 rho := by
  have a : ∀ k < 206, σ' (.n k) = σ (.n k) := fun k hk => (hag k hk).symm
  refine ⟨h.atoms.frame sPrologue_nb hag, by rw [show sPP = V.n 2 from rfl, a 2 (by norm_num)]; exact h.pp,
    by rw [a 3 (by norm_num)]; exact h.r, by rw [a 5 (by norm_num)]; exact h.c5,
    by rw [a 6 (by norm_num)]; exact h.c6, by rw [a 17 (by norm_num), a 18 (by norm_num)]; exact h.dg,
    fun l hl => by rw [a (30 + l) (by omega), a 18 (by norm_num)]; exact h.bits l hl,
    by rw [a 158 (by norm_num), a 18 (by norm_num)]; exact h.unused⟩

/-- **The forest's hints of a signature**, from the digest's cells' integers. -/
def sH (sig : Sphincs.Signature) (N17 N18 c : Nat) : CoordH :=
  coordHOf (sig.forest ⟨c % 8, Nat.mod_lt _ (by decide)⟩) (dS N18 c) (dT N17 (2 * c)) (dA N18 (2 * c))
    (dT N17 (2 * c + 1)) (dA N18 (2 * c + 1))

theorem sH_ok (sig : Sphincs.Signature) (N17 N18 c : Nat) : (sH sig N17 N18 c).OK :=
  coordHOf_ok _ (dS_lt _ _) (dT_lt _ _) (dA_lt _ _) (dT_lt _ _) (dA_lt _ _)

theorem hEnc_sH (sig : Sphincs.Signature) (N17 N18 k : Nat) : hEnc k (sH sig N17 N18 k) =
    fkWeight (dT N17 (2 * k)) (2 * k) + fkWeight (dT N17 (2 * k + 1)) (2 * k + 1) := rfl

theorem hBound_sH (sig : Sphincs.Signature) (N17 N18 k : Nat) : hBound k (sH sig N17 N18 k) =
    cbMul (dA N18 (2 * k)) (58 + 3 * (2 * k)) + cbMul (dA N18 (2 * k + 1)) (58 + 3 * (2 * k + 1)) +
      cbMul (dS N18 k) (26 + 4 * k) := rfl

theorem sum_hEnc_sH (sig : Sphincs.Signature) (N17 N18 : Nat) :
    ∑ k ∈ Finset.range 8, hEnc k (sH sig N17 N18 k) = eOfNat192 (∑ w ∈ Finset.range 16, dT N17 w * 2 ^ (8 * w)) := by
  rw [← encSumF (dT N17) (fun w _ => dT_lt _ _)]
  exact Finset.sum_congr rfl fun k _ => hEnc_sH sig N17 N18 k

theorem sum_hBound_sH (sig : Sphincs.Signature) (N17 N18 : Nat) :
    ∑ k ∈ Finset.range 8, hBound k (sH sig N17 N18 k) = eOfNat192 (marksF (dS N18) (dA N18)) := by
  rw [← boundSumF (dS N18) (dA N18) (fun c _ => dS_lt _ _) (fun w _ => dA_lt _ _)]
  exact Finset.sum_congr rfl fun k _ => hBound_sH sig N17 N18 k

theorem forestX_of {σ : Val} (hpre : SPre rd σ) (hP : IsCanonical128 (σ sPP)) : ForestX σ := by
  refine ⟨hP, hpre.pad, fun k hk => ?_⟩
  obtain ⟨t1, t2⟩ := hpre.tws
  by_cases h24 : k < 24
  · have := t1 (k / 4) (by omega) (k % 4) (by omega)
    rw [show sTws (4 * (k / 4) + k % 4) = V.n (165 + k) by simp only [sTws]; congr 1; omega] at this
    rw [this]; exact canon_word _ _
  · by_cases h25 : k = 24
    · subst h25; rw [show V.n (165 + 24) = sTws 24 from rfl, t2]; exact canon_word _ _
    · have := hpre.subTws ((k - 25) / 2) (by omega) ((k - 25) % 2) (by omega)
      rw [show sSubTws (2 * ((k - 25) / 2) + (k - 25) % 2) = V.n (165 + k) by
        simp only [sSubTws]; congr 1; omega] at this
      rw [this]; exact canon_word _ _

/-- **The forest completes** from the prologue's valuation, its hints the signature's openings and
the digest's marks. -/
theorem sF_stage (hm : MemOK rd 256) (sig : Sphincs.Signature) {Pc m0 m1 rho : E} (σ : Val)
    (hp : SP1 rd σ Pc m0 m1 rho) (hPc : IsCanonical128 Pc) :
    Completes C rd 206 sB sCs.1 σ (fun σ' => ∀ σ'', AgreeBelow sB σ' σ'' → ∀ k < 8,
      CoordPost (∑ i ∈ Finset.range k, hEnc i (sH sig (cellNat (σ (.n 17))) (cellNat (σ (.n 18))) i))
        (σ (.n 161) + ∑ i ∈ Finset.range k, hBound i (sH sig (cellNat (σ (.n 17))) (cellNat (σ (.n 18))) i))
        k (cSt k).1 (cSt k).2.1 (cSt k).2.2 (sH sig (cellNat (σ (.n 17))) (cellNat (σ (.n 18))) k) σ'') := by
  have hpre := sPrologue_sound hp.atoms
  set N17 := cellNat (σ (.n 17)) with hN17
  set N18 := cellNat (σ (.n 18)) with hN18
  have c17 : IsCanonical128 (σ (.n 17)) := by
    have := congrArg Prod.fst hp.dg; simp only at this; rw [this]; exact canon_hcell _
  have c18 : IsCanonical128 (σ (.n 18)) := by
    have := congrArg Prod.snd hp.dg; simp only at this; rw [this]; exact canon_hcell2 _
  have hidx : sIdx σ = N18 % 2 ^ 26 := sIdx_eq hp.bits
  have hNu : N18 / 2 ^ 106 < 2 ^ 22 := by have := cellNat_lt (σ (.n 18)); omega
  have h17 : σ (.n 17) = ∑ k ∈ Finset.range 8, hEnc k (sH sig N17 N18 k) := by
    rw [sum_hEnc_sH, cell17_eq (show N17 < 2 ^ 128 from cellNat_lt _), hN17]
    exact eq_eOfNat192_cellNat c17
  have h18 : σ (.n 18) = σ (.n 161) + ∑ k ∈ Finset.range 8, hBound k (sH sig N17 N18 k) := by
    have hb := sum_hBound_sH sig N17 N18
    rw [hb, hpre.bound0, sNode0_eq hpre, hp.unused, ← hN18, word_hi_mul hNu, hidx,
      bound_cellF (fun c _ => dS_lt _ _) (fun w _ => dA_lt _ _) (Nat.mod_lt _ (by positivity)) hNu,
      cell18_eq, hN18, ← eq_eOfNat192_cellNat c18]
  have hX : ForestX σ := forestX_of hpre (by rw [hp.pp]; exact hPc)
  have hn0 : IsCanonical128 (σ (sNode 0)) := by
    rw [sNode0_eq hpre, ← word_eq_eOfNat]; exact canon_word _ 0
  have hc := sCoords_complete (C := C) hm (sH sig N17 N18) (fun c _ => sH_ok sig N17 N18 c) σ hX hn0 h17 h18
    8 0 rfl σ (fun _ _ => rfl) (by simp [cSt, encVal]) (by simp [cSt])
  rw [Nat.zero_add] at hc
  rw [sB_eq]
  refine hc.mono le_rfl le_rfl (fun σ' h σ'' hag k hk => h σ'' hag k (Nat.zero_le _) hk)

end
end LeanVM.Guest.B1.Sig
