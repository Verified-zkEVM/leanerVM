/-
  LeanVM.Guest.B1.Sig.SphincsSoundDigest

  The message digest and its fields in `verify_sig_lean_sphincs` (`lean_ethereum.py:3665-3707` at
  leanVM `542b0353`) are sound: whatever bits are hinted, they are the low `266` bits of the two
  digest calls, and each field's values and the index are theirs.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBridge
public import LeanVM.Guest.B1.Sig.SphincsFieldsComplete
public import LeanVM.Guest.B1.Sig.SphincsDigestComplete
public import LeanVM.Guest.B1.Sig.SphincsBytes
public import LeanVM.Guest.B1.Sig.Digest80

/-!
# The digest and its fields, sound

* `sDigests_sound`: the claim's words loaded, the padding run, and the two calls' cells the
  `hcell`s of `P`, their addresses, the message and `ρ`;
* `sBits_bitsAt`: the bits pinned Boolean are those of the number they spell, `bitsOf σ 51 266`;
* `sCheck_digest`: the lanes rebuild the first call's cells and the second's low ten bits (its high
  lane checked into `K`, the unused bytes below `2^54` by the byte table), so the digest's number is
  the bits';
* `sFieldsDigest_sound`: the whole prologue: the statement's message digest is the bits' number,
  the index its low `26` bits.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The digest calls -/

theorem loadHolds_eq {p : E} {off : Nat} {a b : E} (ha : LoadHolds rd p off a) (hb : LoadHolds rd p off b) :
    a = b :=
  Option.some.inj (ha.2.symm.trans hb.2)

/-- **The digest calls, sound.** -/
theorem sDigests_sound (h : AtomsHold rd σ sDigests) :
    PadOK σ sPad ∧ LoadHolds rd (σ (.n 0)) 1 (σ sPP) ∧ LoadHolds rd (σ (.n 0)) 2 (σ (.n 5)) ∧
      LoadHolds rd (σ (.n 0)) 3 (σ (.n 6)) ∧
      (σ (.n 17), σ (.n 18)) = hcell [σ sPP, digestAdr 0, σ (.n 5), σ (.n 6), σ (.n 3)] ∧
      (σ (.n 38), σ (.n 39)) = hcell [σ sPP, digestAdr 1, σ (.n 5), σ (.n 6), σ (.n 3)] := by
  rw [sDigests_split] at h
  have c : ∀ (k : Nat) (w : E), Stmt.atom (.const (.n k) w) ∈ (loadS sPP (.n 0) 1 :: hintW "sp_rand" [.n 3] ::
      cst 4 (digestAdr 0) :: loadS (.n 5) (.n 0) 2 :: loadS (.n 6) (.n 0) 3 :: (dPre0 ++
      (kecS (digestIns 4) (runV 17 13) false false :: cst 30 (digestAdr 1) :: loadS (.n 31) (.n 0) 2 ::
      loadS (.n 32) (.n 0) 3 :: (dPre1 ++ [kecS (digestIns 30) (runV 38 13) false false])))) →
      σ (.n k) = w := fun k w hm => h.atom hm
  have p12 := c 12 (word 1 0 0) (by simp [dPre0, cst])
  have p13 := c 13 (word 0 0 0) (by simp [dPre0, cst])
  have p14 := c 14 (word 0 0 0) (by simp [dPre0, cst])
  have p15 := c 15 (word 0 0 0) (by simp [dPre0, cst])
  have p16 := c 16 (word 0 0 0) (by simp [dPre0, cst])
  rw [word_zero] at p13 p14 p15 p16
  have hp : PadOK σ sPad := ⟨p12, p13, p14, p15, p16⟩
  have lP : LoadHolds rd (σ (.n 0)) 1 (σ sPP) := h.atom (a := .load sPP (.n 0) 1) (by simp [loadS])
  have l5 : LoadHolds rd (σ (.n 0)) 2 (σ (.n 5)) := h.atom (a := .load (.n 5) (.n 0) 2) (by simp [loadS])
  have l6 : LoadHolds rd (σ (.n 0)) 3 (σ (.n 6)) := h.atom (a := .load (.n 6) (.n 0) 3) (by simp [loadS])
  have l31 : LoadHolds rd (σ (.n 0)) 2 (σ (.n 31)) := h.atom (a := .load (.n 31) (.n 0) 2) (by simp [loadS])
  have l32 : LoadHolds rd (σ (.n 0)) 3 (σ (.n 32)) := h.atom (a := .load (.n 32) (.n 0) 3) (by simp [loadS])
  have c7 : σ (.n 7) = σ (.n 3) := h.atom (a := .copy (.n 7) (.n 3)) (by simp [dPre0, copyS])
  have c33 : σ (.n 33) = σ (.n 3) := h.atom (a := .copy (.n 33) (.n 3)) (by simp [dPre1, copyS])
  refine ⟨hp, lP, l5, l6, ?_, ?_⟩
  · have k := kec80_sound (pp := sPP) (adr := .n 4) (m0 := .n 5) (m1 := .n 6) (r := .n 7) (t1 := .n 8) (t2 := .n 9) (t3 := .n 10) (t4 := .n 11) (z1 := .n 13) (z2 := .n 14)
      (z3 := .n 15) (z4 := .n 16) (o := 17) (h.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; simp [digestIns, sPad])
      (c 8 (word 1 0 0) (by simp [dPre0, cst])) ((c 9 (word 0 0 0) (by simp [dPre0, cst])).trans word_zero)
      ((c 10 (word 0 0 0) (by simp [dPre0, cst])).trans word_zero) (c 11 (word (2 ^ 63) 0 0) (by simp [dPre0, cst])) p13 p14 p15 p16
    rw [k, c 4 (digestAdr 0) (by simp [cst]), c7]
  · have k := kec80_sound (pp := sPP) (adr := .n 30) (m0 := .n 31) (m1 := .n 32) (r := .n 33) (t1 := .n 34) (t2 := .n 35) (t3 := .n 36) (t4 := .n 37) (z1 := .n 13) (z2 := .n 14)
      (z3 := .n 15) (z4 := .n 16) (o := 38) (h.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; simp [digestIns, sPad])
      (c 34 (word 1 0 0) (by simp [dPre1, cst])) ((c 35 (word 0 0 0) (by simp [dPre1, cst])).trans word_zero)
      ((c 36 (word 0 0 0) (by simp [dPre1, cst])).trans word_zero) (c 37 (word (2 ^ 63) 0 0) (by simp [dPre1, cst])) p13 p14 p15 p16
    rw [k, c 30 (digestAdr 1) (by simp [cst]), c33, loadHolds_eq l31 l5, loadHolds_eq l32 l6]

/-! ## The bits -/

/-- **The bits, pinned Boolean, are those of their number.** -/
theorem sBits_bitsAt (h : AtomsHold rd σ sBooleans) : BitsAt σ (bitsOf σ 51 266) := by
  intro i hi
  have hb : IsBit (σ (sBit i)) := by
    have hm : Stmt.atom (.mul (sBit i) (sBit i) (sBit i)) ∈ sBooleans := by
      unfold sBooleans
      by_cases h1 : i < 128
      · refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr h1, ?_⟩)
        exact List.mem_cons_self ..
      · by_cases h2 : i < 256
        · refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨i - 128, List.mem_range.mpr (by omega), ?_⟩)
          refine List.mem_cons_of_mem _ ?_
          obtain ⟨j, rfl⟩ : ∃ j, i = 128 + j := ⟨i - 128, by omega⟩
          rw [show 128 + j - 128 = j by omega]
          show Stmt.atom (.mul (.n (51 + (128 + j))) (.n (51 + (128 + j))) (.n (51 + (128 + j)))) ∈ _
          rw [show 51 + (128 + j) = 179 + j by omega]
          exact List.mem_cons_self ..
        · refine List.mem_append_right _ (List.mem_map.mpr ⟨i - 256, List.mem_range.mpr (by omega), ?_⟩)
          obtain ⟨j, rfl⟩ : ∃ j, i = 256 + j := ⟨i - 256, by omega⟩
          rw [show 256 + j - 256 = j by omega]
          show _ = Stmt.atom (.mul (.n (51 + (256 + j))) (.n (51 + (256 + j))) (.n (51 + (256 + j))))
          rw [show 51 + (256 + j) = 307 + j by omega]
          rfl
    exact (h.atom hm).symm
  rw [bitsOf, testBit_bitsVal]
  simp only [hi, decide_true, Bool.true_and, sBit] at hb ⊢
  rcases isBit_cases hb with h0 | h1
  · simp [h0, one_ne_zero_E.symm]
  · simp [h1]

theorem bitsOf_lt (σ : Val) : bitsOf σ 51 266 < 2 ^ 266 := bitsVal_lt _ _

/-! ## The check -/

/-- A word of two lanes: the low one plus `y` times the high one. -/
theorem cellNat_lanes {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    cellNat (eOfNat a + eOfNat b * word 0 1 0) = a + 2 ^ 64 * b := by
  rw [word_y, eOfNat_eq_ofLimbs, eOfNat_eq_ofLimbs, ofLimbs_mul_y, ofLimbs_add, cellNat]
  simp only [ofLimbs_limb0, ofLimbs_limb1, add_zero, zero_add, kToNat_ofBits, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]

/-- **The second call's low ten bits**: its cell, the field bits' lane `l` and the unused bits
`N` times `g^10` checked into `K` after `y⁻¹`. -/
theorem high_low_bits {x : E} {l N : Nat} (hl : l < 2 ^ 10) (hN : N < 2 ^ 54)
    (hK : IsInK ((x + eOfNat l + eOfNat N * word 1024 0 0) * word 1 0 1)) :
    cellNat x % 2 ^ 10 = l := by
  rw [show (1024 : Nat) = 2 ^ 10 by norm_num, word_eq_eOfNat, mul_comm (eOfNat N),
    eOfNat_two_pow_mul (by omega), word_yinv] at hK
  rw [eq_ofLimbs x, eOfNat_eq_ofLimbs, eOfNat_eq_ofLimbs, ofLimbs_add, ofLimbs_add, ofLimbs_mul_y_inv,
    isInK_ofLimbs_iff] at hK
  simp only [add_zero] at hK
  have h0 : x.limb 0 = K.ofBits l + K.ofBits (2 ^ 10 * N) := by
    have := hK.2
    rw [add_assoc] at this
    exact (add_eq_zero_iff_eq_neg.mp this).trans (CharTwo.neg_eq _)
  rw [cellNat, h0, ← ofBits_xor, Nat.xor_comm, two_pow_mul_xor hl, kToNat_ofBits]
  omega

/-- The digest's number from the lanes and the high check. -/
theorem digestD_eq {D : Nat} (hD : D < 2 ^ 266) {c17 c18 c38 : E}
    (h17 : cellNat c17 = D % 2 ^ 128) (h18 : cellNat c18 = D / 2 ^ 128 % 2 ^ 128)
    (h38 : cellNat c38 % 2 ^ 10 = D / 2 ^ 256 % 2 ^ 10) :
    digestD c17 c18 c38 % 2 ^ 266 = D := by
  unfold digestD
  rw [h17, h18]
  omega

/-- **The fields' check, sound**: the digest calls' cells rebuilt from the lanes of `D`, the
second call's high lane in `K` and the unused bytes read off the byte table, the digest's number is
`D`. -/
theorem sCheck_digest {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} (hbb : ByteBits L.read (σ (.n 1)))
    {D : Nat} (hD : D < 2 ^ 266) (hv : ValsAt σ D) (hpl : AtomsHold L.read σ sPl.1)
    (hc : AtomsHold L.read σ (sCheck sPl.2.1).1) :
    digestD (σ (.n 17)) (σ (.n 18)) (σ (.n 38)) % 2 ^ 266 = D := by
  obtain ⟨hlanes, -, hlast⟩ := sPl_sound hv hpl
  rw [sCheck_eq] at hc
  have a1147 : σ (.n 1147) = word 0 1 0 := hc.atom (a := .const (.n 1147) _) (by simp [fcA, cst])
  have a1148 : σ (.n 1148) = σ (sLane 1) * σ (.n 1147) := hc.atom (a := .mul (.n 1148) _ _) (by simp [fcA, mulS])
  have a17 : σ (.n 17) = σ (sLane 0) + σ (.n 1148) := hc.atom (a := .add (.n 17) _ _) (by simp [addS])
  have a1149 : σ (.n 1149) = word 0 1 0 := hc.atom (a := .const (.n 1149) _) (by simp [fcB, cst])
  have a1150 : σ (.n 1150) = σ (sLane 3) * σ (.n 1149) := hc.atom (a := .mul (.n 1150) _ _) (by simp [fcB, mulS])
  have a18 : σ (.n 18) = σ (sLane 2) + σ (.n 1150) := hc.atom (a := .add (.n 18) _ _) (by simp [addS])
  have hU : AtomsHold L.read σ fcU.1 := hc.sub fun x hx => by simp [hx]
  obtain ⟨N, hN, hNlt⟩ := sFromBytes_sound hκ hbb (K := 64) (by norm_num) (by norm_num) g63W_eq (by norm_num) hU
  have hN' : σ (.n 1217) = eOfNat N := by rw [← fcU_val]; exact hN
  have c1218 : σ (.n 1218) = σ (.n 38) + σ (.n 1060) := hc.atom (a := .add (.n 1218) _ _) (by simp [fcC, addS])
  have c1219 : σ (.n 1219) = word 1024 0 0 := hc.atom (a := .const (.n 1219) _) (by simp [fcC, cst])
  have c1220 : σ (.n 1220) = σ (.n 1217) * σ (.n 1219) := hc.atom (a := .mul (.n 1220) _ _) (by simp [fcC, mulS])
  have c1221 : σ (.n 1221) = σ (.n 1218) + σ (.n 1220) := hc.atom (a := .add (.n 1221) _ _) (by simp [fcC, addS])
  have c1222 : σ (.n 1222) = word 1 0 1 := hc.atom (a := .const (.n 1222) _) (by simp [fcC, cst])
  have c1223 : σ (.n 1223) = σ (.n 1221) * σ (.n 1222) := hc.atom (a := .mul (.n 1223) _ _) (by simp [fcC, mulS])
  have hK : IsInK (σ (.n 1223)) := (hc.atom (a := .assertInK (.n 1223) (.n 1217)) (by simp)).1
  have hl' : σ (.n 1060) = eOfNat (D / 2 ^ 256 % 2 ^ 10) := by rw [← sPl_lane]; exact hlast
  rw [c1223, c1222, c1221, c1220, c1219, c1218, hN', hl'] at hK
  have h38 := high_low_bits (Nat.mod_lt _ (by norm_num)) (by simpa using hNlt) hK
  have l0 := hlanes 0 (by norm_num)
  have l1 := hlanes 1 (by norm_num)
  have l2 := hlanes 2 (by norm_num)
  have l3 := hlanes 3 (by norm_num)
  have n17 : cellNat (σ (.n 17)) = D % 2 ^ 128 := by
    rw [a17, a1148, a1147, l0, l1, cellNat_lanes (show laneNat D 0 < 2 ^ 64 from Nat.mod_lt _ (by norm_num))
      (show laneNat D 1 < 2 ^ 64 from Nat.mod_lt _ (by norm_num)),
      laneNat, laneNat]
    omega
  have n18 : cellNat (σ (.n 18)) = D / 2 ^ 128 % 2 ^ 128 := by
    rw [a18, a1150, a1149, l2, l3, cellNat_lanes (show laneNat D 2 < 2 ^ 64 from Nat.mod_lt _ (by norm_num))
      (show laneNat D 3 < 2 ^ 64 from Nat.mod_lt _ (by norm_num)),
      laneNat, laneNat]
    omega
  exact digestD_eq hD n17 n18 h38

/-! ## The prologue -/

/-- **The prologue of `verify_sig_lean_sphincs`, sound**: the claim's words loaded, the padding
run, and a number `D < 2^266` whose bits and values the fields hold, its low `26` bits the index,
is the statement's message digest of the message and the randomizer. -/
theorem sFieldsDigest_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} (hbb : ByteBits L.read (σ (.n 1)))
    (hA : AtomsHold L.read σ (sDigests ++ sFieldsBlock)) :
    PadOK σ sPad ∧ LoadHolds L.read (σ (.n 0)) 1 (σ sPP) ∧ LoadHolds L.read (σ (.n 0)) 2 (σ (.n 5)) ∧
      LoadHolds L.read (σ (.n 0)) 3 (σ (.n 6)) ∧ σ (.n 1224) = σ sPP ∧
      ∃ D, D < 2 ^ 266 ∧ BitsAt σ D ∧ ValsAt σ D ∧ σ sIdx = eOfNat (D % 2 ^ 26) ∧
        Id.run (Sphincs.Verification.messageDigest (m := Id) keccakF1600 (cellVal (σ sPP))
          (cellPairVal (σ (.n 5)) (σ (.n 6))) (cellVal (σ (.n 3)))) = BitVec.ofNat Sphincs.messageDigestBits D := by
  obtain ⟨hp, lP, l5, l6, d0, d1⟩ := sDigests_sound hA.left
  have hF := hA.right
  rw [sFieldsBlock_eq] at hF
  have hbits : BitsAt σ (bitsOf σ 51 266) := sBits_bitsAt (hF.left.sub fun x hx => List.mem_append_right _ hx)
  have hR := hF.right
  have hsh : AtomsHold L.read σ sShifts := hR.left.left.left
  have hvals : ValsAt σ (bitsOf σ 51 266) := sShifts_vals hbits hsh
  have hpl : AtomsHold L.read σ sPl.1 := hR.left.right
  obtain ⟨-, hidx, -⟩ := sPl_sound hvals hpl
  have hcheck : AtomsHold L.read σ (sCheck sPl.2.1).1 := by
    rw [sCheck_eq]
    exact hR.right.sub fun x hx => by
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      tauto
  have hD := sCheck_digest hκ hbb (bitsOf_lt σ) hvals hpl hcheck
  have hcp : σ (.n 1224) = σ sPP := hR.right.atom (a := .copy (.n 1224) sPP) (by simp [copyS])
  refine ⟨hp, lP, l5, l6, hcp, bitsOf σ 51 266, bitsOf_lt σ, hbits, hvals, hidx, ?_⟩
  rw [sphincsDigest_cells, ← congrArg Prod.fst d0, ← congrArg Prod.snd d0, ← congrArg Prod.fst d1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, show Sphincs.messageDigestBits = 266 from rfl]
  dsimp only
  have := bitsOf_lt σ
  omega

end
end LeanVM.Guest.B1.Sig
