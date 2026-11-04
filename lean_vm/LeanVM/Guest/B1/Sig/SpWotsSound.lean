/-
  LeanVM.Guest.B1.Sig.SpWotsSound

  `sp_wots` is sound: whenever its body holds (under any call relation: it calls nothing), it
  returns one word, the WOTS+C leaf of the chain values its frame holds, at the key whose address
  is its second argument and the encoding digest that is its third, of digit sum `T = 128`.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsGroups
public import LeanVM.Guest.B1.Sig.SpWotsData
public import LeanVM.Guest.B1.Sig.XmssCore

/-!
# `sp_wots`, sound

`spValues σ`: the chain values `sp_wots`'s frame `σ` holds, chain `i`'s the hint its walk reads in
the arm its group's dispatch takes (`spStart σ i`, `SpWotsGroups`).

`sp_wots_sound`: the body (`Data.core19.body = spBody`) holding, the powers are `g^s`; each group's
dispatch takes the arm of its digit word (`spGroupsT_sound`, `spGroupT_sound`), whose walks reach
their tips from the starts (`spArmK_sound`); the product is `g` to the digits' sum, asserted to be
`g^128`, and the encoding their base-4 number, asserted to be the third argument, whose digits they
therefore are; the leaf is the `keccak_cells` of `P`, `at + TW_LEAF` and the tips (`kMsg_sound`,
over the padding run the first group sets). At an address `at = keyAddressCell layer tree leaf` this is
`wotsLeafOf` (`wotsLeafOf_cells`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.Verifier HashSig

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The chain values `sp_wots`'s frame holds**: chain `i`'s hinted start. -/
noncomputable def spValues (σ : Val) : Sphincs.ChainIndex → HashSig.Digest :=
  fun i => cellVal (σ (spStart σ i.val))

/-- The powers `g^s` at `n(3 + s)`. -/
def spPowers : List Stmt := (List.range 10).map fun s => cst (3 + s) (word (2 ^ s) 0 0)

/-- The checks after the codeword: the encoding, the target, the leaf's address. -/
def spChecks : List Stmt :=
  [.atom (.assertEq (.n (spEnc false 1 (spState 21).2.2)) (.n 2)), cst spC spTarget,
    .atom (.assertEq (.n (spProd false 1 (spState 21).2.2)) (.n spC)), cst (spC + 1) (word (tw 2) 0 0),
    addS (.n (spC + 2)) (.n 1) (.n (spC + 1))]

theorem spLast_eq : spLast = spGroupT 63 1 false (spState 21).1 (spState 21).2.1 (spState 21).2.2 := by
  rw [spLast, spGs_eq]

theorem spBody_split : spBody = spPowers ++ (spGs.1 ++ (spLast.1 ++ (spChecks ++ (spLeafK.1 ++
    [copyS (.n spLeafK.2.1) (.n spLeafK.2.2), .ret [.n spLeafK.2.1]])))) := by
  rw [spBody, spChecks, spGs_eq, spPowers]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem spLeafK_atoms : atomsOnly spLeafK.1 = true := kMsg_atoms _ _ _ _ _ _

/-- **The tips, the product and the encoding** of the codeword, its groups' atoms holding. -/
theorem spCodeword_sound (hpow : ∀ s < 10, σ (.n (3 + s)) = gen ^ s) (hpad : PadOK σ spPad)
    (hg : ∀ p < 22, SpGroupOK rd σ p) :
    (∀ i < 64, σ (spTip i) = chainT (spStepF (σ (.n 0)) (σ (.n 1))) i (3 - spDigit σ i) (spDigit σ i)
      (σ (spStart σ i))) ∧
    σ (.n (spProd false 1 (spState 21).2.2)) = gen ^ (∑ i ∈ Finset.range 64, spDigit σ i) ∧
    σ (.n (spEnc false 1 (spState 21).2.2)) = lit (∑ i ∈ Finset.range 64, spDigit σ i * 4 ^ i) := by
  have hN : ∀ p, 0 < spN p ∧ spN p ≤ 3 := fun p => by unfold spN; split <;> omega
  have harm : ∀ p < 22, spDigitWord σ p < 4 ^ spN p ∧
      SpArmOK σ (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 (spDigitWord σ p)
        (spStartOf (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1
          (spDigitWord σ p)
          (spArmB (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1
            (spDigitWord σ p))) := by
    intro p hp
    obtain ⟨k, hk, hx, ha⟩ := hg p hp
    rw [spDigitWord_eq hk hx]
    exact ⟨hk, spArmK_sound hpad ha⟩
  refine ⟨fun i hi => ?_, ?_⟩
  · have hp : i / 3 < 22 := by omega
    have hr : i % 3 < spN (i / 3) := by
      unfold spN; split
      · omega
      · omega
    have := (harm (i / 3) hp).2.tip (i % 3) hr
    rw [show 3 * (i / 3) + i % 3 = i by omega] at this
    exact this
  · have hcw := spCodeword_vals (G := 21) (σ := σ) (by norm_num) le_rfl (spDigitWord σ)
      (fun p hp => (harm p (by omega)).1) hpow
      (fun p => σ (.n (spProd (p == 0) (spN p) (spState p).2.2)))
      (fun p => σ (.n (spEnc (p == 0) (spN p) (spState p).2.2)))
      (by
        have := (harm 0 (by norm_num)).2.prod
        simp only [beq_self_eq_true, ↓reduceIte, one_mul] at this
        exact this)
      (fun p hp => by
        have := (harm (p + 1) (by omega)).2.prod
        have hb : (p + 1 == 0) = false := by simp
        rw [hb] at this
        simp only [Bool.false_eq_true, ↓reduceIte] at this
        rw [spState_succ] at this
        show σ (.n (spProd (p + 1 == 0) (spN (p + 1)) (spState (p + 1)).2.2)) =
          σ (.n (spProd (p == 0) (spN p) (spState p).2.2)) *
            σ (.n (3 + digitSum (spDigitWord σ (p + 1)) (spN (p + 1))))
        rw [hb, spState_succ, this, spN_of_lt hp])
      (by
        have := (harm 0 (by norm_num)).2.enc
        simp only [beq_self_eq_true, ↓reduceIte, zero_add] at this
        exact this)
      (fun p hp => by
        have := (harm (p + 1) (by omega)).2.enc
        have hb : (p + 1 == 0) = false := by simp
        rw [hb] at this
        simp only [Bool.false_eq_true, ↓reduceIte] at this
        rw [spState_succ] at this
        show σ (.n (spEnc (p + 1 == 0) (spN (p + 1)) (spState (p + 1)).2.2)) =
          σ (.n (spEnc (p == 0) (spN p) (spState p).2.2)) +
            lit (spDigitWord σ (p + 1) * 4 ^ (3 * (p + 1)))
        rw [hb, spState_succ, this, spN_of_lt hp])
    simpa [spN, spDigit] using hcw

/-- **`sp_wots` is sound**: whenever its body holds of `σ`, it returns one canonical word `leaf`,
and at an address cell `σ n1 = keyAddressCell layer tree lf` the encoding digest `σ n2` has digit sum `128`
and `leaf` is the WOTS+C leaf the chain values `spValues σ` recover at its digits. -/
theorem sp_wots_sound {rets : List E}
    (h : Stmt.HoldsList C rd σ Data.core19.body False (fun rs => rs = rets)) :
    ∃ leaf, rets = [leaf] ∧ IsCanonical128 leaf ∧ ∀ (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
      (lf : Sphincs.TreeLeafIndex), σ (.n 1) = keyAddressCell layer tree lf →
        Sphincs.TargetSum.Valid (digestDigits (cellVal (σ (.n 2)))) ∧
        cellVal leaf = wotsLeafOf (cellVal (σ (.n 0))) layer tree lf (cellVal (σ (.n 2))) (spValues σ) := by
  rw [spBody_eq, spBody_split] at h
  -- the powers
  have s0 := holdsList_split_atoms (xs := spPowers) rfl h
  have hpw := atomsHold_of_holdsList (ss := spPowers) rfl s0.1
  have hpow : ∀ s < 10, σ (.n (3 + s)) = gen ^ s := by
    intro s hs
    have e : σ (.n (3 + s)) = word (2 ^ s) 0 0 := hpw.atom (a := .const (.n (3 + s)) _) (by
      simp only [spPowers, cst, List.mem_map, List.mem_range]
      exact ⟨s, hs, rfl⟩)
    rw [e, word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]
  -- the groups
  have s1 := s0.2
  rw [spGs_fst] at s1
  obtain ⟨s2, hpad, hg⟩ := spGroupsT_sound (C := C) (rd := rd) (σ := σ) 21 0 (by norm_num) s1
  have hpad := hpad rfl (by norm_num)
  rw [spLast_eq] at s2
  obtain ⟨s3, -, kL, hkL, hxL, haL⟩ := spGroupT_sound s2
  have hgrp : ∀ p < 22, SpGroupOK rd σ p := by
    intro p hp
    by_cases hp21 : p < 21
    · simpa using hg p hp21
    · have : p = 21 := by omega
      subst this
      exact ⟨kL, by simpa [spN] using hkL, hxL, by simpa [spN] using haL⟩
  obtain ⟨htip, hprod, henc⟩ := spCodeword_sound hpow hpad hgrp
  -- the checks and the leaf
  have hca : atomsOnly (spChecks ++ spLeafK.1) = true := by
    rw [atomsOnly_append, spLeafK_atoms]; rfl
  rw [← List.append_assoc] at s3
  have s4 := holdsList_split_atoms hca s3
  have hc := atomsHold_of_holdsList hca s4.1
  have e2 : σ (.n (spEnc false 1 (spState 21).2.2)) + σ (.n 2) = 0 :=
    hc.atom (a := .assertEq (.n (spEnc false 1 (spState 21).2.2)) (.n 2)) (by simp [spChecks])
  have eC : σ (.n spC) = spTarget := hc.atom (a := .const (.n spC) _) (by simp [spChecks, cst])
  have eP : σ (.n (spProd false 1 (spState 21).2.2)) + σ (.n spC) = 0 :=
    hc.atom (a := .assertEq (.n (spProd false 1 (spState 21).2.2)) (.n spC)) (by simp [spChecks])
  have eL1 : σ (.n (spC + 1)) = word (tw 2) 0 0 :=
    hc.atom (a := .const (.n (spC + 1)) _) (by simp [spChecks, cst])
  have eL2 : σ (.n (spC + 2)) = σ (.n 1) + σ (.n (spC + 1)) :=
    hc.atom (a := .add (.n (spC + 2)) (.n 1) (.n (spC + 1))) (by simp [spChecks, addS])
  have henc2 : σ (.n 2) = lit (∑ i ∈ Finset.range 64, spDigit σ i * 4 ^ i) :=
    ((Value.e_add_eq_zero_iff).mp e2).symm.trans henc
  have hdlt0 : ∀ j, spDigit σ j < 4 := fun j => Nat.mod_lt _ (by norm_num)
  have hsum : ∑ i ∈ Finset.range 64, spDigit σ i = 128 := by
    have hle : ∑ i ∈ Finset.range 64, spDigit σ i ≤ ∑ _i ∈ Finset.range 64, 3 := by
      apply Finset.sum_le_sum
      intro j _
      have := hdlt0 j
      omega
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
    refine Value.gen_pow_inj (by omega) (by norm_num) ?_
    rw [← hprod, (Value.e_add_eq_zero_iff).mp eP, eC, spTarget_eq]
  -- the leaf's message
  have hl := hc.right
  have hlenC : spLeafCells.length = 66 := by decide +kernel
  have hk := kMsg_sound hpad (cells := spLeafCells.map KC.cell)
    (len := 1056) (tailRun := false) (out := none) (b := spC + 3) (fun h => absurd h (by simp))
    hl (by simp [hlenC]) (fun j hj => by
      rw [List.getD_eq_default _ _ (by rw [length_cellsBytes]; simp [hlenC]; omega)])
  have hcv : (spLeafCells.map KC.cell).map (KC.val σ) = spLeafCells.map σ := by
    rw [List.map_map]
    rfl
  have htake : (cellsBytes (spLeafCells.map σ)).take 1056 = cellsBytes (spLeafCells.map σ) := by
    rw [List.take_of_length_le (by rw [length_cellsBytes]; simp [hlenC])]
  rw [hcv, htake] at hk
  have hleaf : σ (.n spLeafK.2.2) = (hcell (spLeafCells.map σ)).1 := congrArg Prod.fst hk
  -- the return
  have s5 := s4.2
  simp only [Stmt.HoldsList, Stmt.Holds, copyS, Atom.Holds, List.map_cons, List.map_nil] at s5
  obtain ⟨hcp, hret⟩ := s5
  refine ⟨σ (.n spLeafK.2.1), hret.symm, by rw [hcp, hleaf]; exact canon_hcell _,
    fun layer tree lf hat => ?_⟩
  have hdlt : ∀ j, spDigit σ j < 4 := fun j => Nat.mod_lt _ (by norm_num)
  have hdig : ∀ i : Sphincs.ChainIndex, (digestDigits (cellVal (σ (.n 2))) i).val = spDigit σ i.val := by
    intro i
    rw [henc2, cellVal_lit, digit_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le (base4_lt hdlt 64) (by norm_num)),
      base4_digit hdlt 64 i.val i.isLt]
  refine ⟨?_, ?_⟩
  · show ∑ i : Sphincs.ChainIndex, (digestDigits (cellVal (σ (.n 2))) i).val = 128
    simp only [hdig]
    rw [Fin.sum_univ_eq_sum_range (fun i => spDigit σ i)]
    exact hsum
  · have hw : wotsLeafOf (cellVal (σ (.n 0))) layer tree lf (cellVal (σ (.n 2))) (spValues σ) = _ :=
      wotsLeafOf_cells hat _ (fun i => σ (spStart σ i)) (spDigit σ) hdig
    rw [hcp, hleaf, hw, spLeafCells_eq]
    simp only [List.map_cons, List.map_map]
    rw [eL2, eL1]
    have hm : List.map (σ ∘ spTip) (List.range 64) = List.map (fun i => chainT (spStepF (σ (.n 0))
        (σ (.n 1))) i (3 - spDigit σ i) (spDigit σ i) (σ (spStart σ i))) (List.range Sphincs.chainCount) :=
      List.map_congr_left (fun i hi => htip i (List.mem_range.mp hi))
    rw [hm]

end
end LeanVM.Guest.B1.Sig
