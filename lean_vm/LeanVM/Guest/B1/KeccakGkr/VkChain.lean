/-
  LeanVM.Guest.B1.KeccakGkr.VkChain

  `verify_keccak`'s twelve steps (G:2846-2879): the layers, one after the other, on the claim
  chain at `claims`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkStep

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The returns of a step, split: the capacity and the cursor. -/
theorem split6 {B : ℕ} (hB : 6 ≤ B) {cap : List E} {x : E}
    (h : ((List.range 6).map fun j ↦ σ (.n (B - 6 + j))) = cap ++ [x]) :
    cap = [σ (.n (B - 6)), σ (.n (B - 5)), σ (.n (B - 4)), σ (.n (B - 3)), σ (.n (B - 2))] ∧
      σ (.n (B - 1)) = x := by
  have e : ((List.range 6).map fun j ↦ σ (.n (B - 6 + j))) =
      [σ (.n (B - 6)), σ (.n (B - 5)), σ (.n (B - 4)), σ (.n (B - 3)), σ (.n (B - 2))] ++
        [σ (.n (B - 1))] := by
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append]
    rw [show B - 6 + 0 = B - 6 by omega, show B - 6 + 1 = B - 5 by omega,
      show B - 6 + 2 = B - 4 by omega, show B - 6 + 3 = B - 3 by omega,
      show B - 6 + 4 = B - 2 by omega, show B - 6 + 5 = B - 1 by omega]
  rw [e] at h
  have := List.append_inj' h rfl
  simp only [List.cons.injEq, and_true] at this
  exact ⟨this.1.symm, this.2⟩

theorem stepEnd_0 : stepEnd 0 488 = 531 := by decide +kernel
theorem stepEnd_1 : stepEnd 1 531 = 746 := by decide +kernel
theorem stepEnd_2 : stepEnd 2 746 = 960 := by decide +kernel
theorem stepEnd_3 : stepEnd 3 960 = 1315 := by decide +kernel
theorem stepEnd_4 : stepEnd 4 1315 = 1624 := by decide +kernel
theorem stepEnd_5 : stepEnd 5 1624 = 1979 := by decide +kernel
theorem stepEnd_6 : stepEnd 6 1979 = 2192 := by decide +kernel
theorem stepEnd_7 : stepEnd 7 2192 = 2501 := by decide +kernel
theorem stepEnd_8 : stepEnd 8 2501 = 2763 := by decide +kernel
theorem stepEnd_9 : stepEnd 9 2763 = 3074 := by decide +kernel
theorem stepEnd_10 : stepEnd 10 3074 = 3383 := by decide +kernel
theorem stepEnd_11 : stepEnd 11 3383 = 3691 := by decide +kernel

/-- **The twelve steps** (G:2846-2879). -/
theorem vkStepsT_holds {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (h17 : σ (.n 17) = gen ^ (τ - 4))
    (h43 : σ (.n 43) = gen ^ ((τ - 3) / 2)) (h47 : σ (.n 47) = gen ^ ((τ - 3) % 2))
    (h48 : σ (.n 48) = gen ^ ((τ - 3) / 2 + (τ - 3) % 2)) {c : KeccakClaim} {L0 : E}
    (hcr : ClaimRec rd ((1 : ℕ) = 1) (σ (.n 201)) c (τ - 3))
    (hL0 : ∀ v, LoadHolds rd (σ (.n 274)) 30 v → v = L0)
    (hw0 : ∀ z < 64, c.weights.getD z 0 = L0 * gen ^ z)
    (hpk : FsPackOk σ (.n 191) (191 + 1) dsObserve)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ vkStepsT next kret) :
    ∃ (xs : List E) (c' : KeccakClaim), ReadsAt rd (σ (.n 5) * gen) xs ∧
      RunsTo (keccakLayers τ (List.range keccakDepth) c)
        ⟨[σ (.n 179), σ (.n 180), σ (.n 181), σ (.n 182), σ (.n 183)], [(σ (.n 191), dsObserve)]⟩
        xs c' ⟨[σ (.n 3685), σ (.n 3686), σ (.n 3687), σ (.n 3688), σ (.n 3689)], []⟩ ∧
      ClaimRec rd ((0 : ℕ) = 1) (σ (.n 201) * gen ^ (22 * 12)) c' (τ - 3) ∧
      σ (.n 3690) = σ (.n 5) * gen * gen ^ xs.length ∧ next := by
  rw [vkStepsT] at h
  simp only [List.append_assoc] at h
  rw [holdsList_append] at h
  obtain ⟨xs0, c1, cap1, hx0, r0, hc1, e0, h⟩ := stepT_holds0 hτ1 hτ2 h17 h43 h47 h48 hcr hL0 hw0 hpk h
  rw [stepEnd_0] at e0
  obtain ⟨k1, u1⟩ := split6 (by norm_num) e0
  rw [holdsList_append] at h
  obtain ⟨xs1, c2, cap2, hx1, r1, hc2, e1, h⟩ := stepT_holdsL (s := 1) (b := 531) (by norm_num) (by norm_num) hτ1 hτ2 h17 h43 h47 h48 hc1 h
  rw [stepEnd_1] at e1
  obtain ⟨k2, u2⟩ := split6 (by norm_num) e1
  simp only [Nat.reduceSub] at k1 u1
  rw [← k1] at r1
  rw [holdsList_append] at h
  obtain ⟨xs2, c3, cap3, hx2, r2, hc3, e2, h⟩ := stepT_holdsL (s := 2) (b := 746) (by norm_num) (by norm_num) hτ1 hτ2 h17 h43 h47 h48 hc2 h
  rw [stepEnd_2] at e2
  obtain ⟨k3, u3⟩ := split6 (by norm_num) e2
  simp only [Nat.reduceSub] at k2 u2
  rw [← k2] at r2
  rw [holdsList_append] at h
  obtain ⟨xs3, c4, cap4, hx3, r3, hc4, e3, h⟩ := stepT_holdsL (s := 3) (b := 960) (by norm_num) (by norm_num) hτ1 hτ2 h17 h43 h47 h48 hc3 h
  rw [stepEnd_3] at e3
  obtain ⟨k4, u4⟩ := split6 (by norm_num) e3
  simp only [Nat.reduceSub] at k3 u3
  rw [← k3] at r3
  rw [holdsList_append] at h
  obtain ⟨xs4, c5, cap5, hx4, r4, hc5, e4, h⟩ := stepT_holdsL (s := 4) (b := 1315) (by norm_num) (by norm_num) hτ1 hτ2 h17 h43 h47 h48 hc4 h
  rw [stepEnd_4] at e4
  obtain ⟨k5, u5⟩ := split6 (by norm_num) e4
  simp only [Nat.reduceSub] at k4 u4
  rw [← k4] at r4
  rw [holdsList_append] at h
  obtain ⟨xs5, c6, cap6, hx5, r5, hc6, e5, h⟩ := stepT_holdsL (s := 5) (b := 1624) (by norm_num) (by norm_num) hτ1 hτ2 h17 h43 h47 h48 hc5 h
  rw [stepEnd_5] at e5
  obtain ⟨k6, u6⟩ := split6 (by norm_num) e5
  simp only [Nat.reduceSub] at k5 u5
  rw [← k5] at r5
  rw [holdsList_append] at h
  obtain ⟨xs6, c7, cap7, hx6, r6, hc7, e6, h⟩ := stepT_holdsL (s := 6) (b := 1979) (by norm_num) (by norm_num) hτ1 hτ2 h17 h43 h47 h48 hc6 h
  rw [stepEnd_6] at e6
  obtain ⟨k7, u7⟩ := split6 (by norm_num) e6
  simp only [Nat.reduceSub] at k6 u6
  rw [← k6] at r6
  rw [holdsList_append] at h
  obtain ⟨xs7, c8, cap8, hx7, r7, hc8, e7, h⟩ := stepT_holdsL (s := 7) (b := 2192) (by norm_num) (by norm_num) hτ1 hτ2 h17 h43 h47 h48 hc7 h
  rw [stepEnd_7] at e7
  obtain ⟨k8, u8⟩ := split6 (by norm_num) e7
  simp only [Nat.reduceSub] at k7 u7
  rw [← k7] at r7
  rw [holdsList_append] at h
  obtain ⟨xs8, c9, cap9, hx8, r8, hc9, e8, h⟩ := stepT_holdsL (s := 8) (b := 2501) (by norm_num) (by norm_num) hτ1 hτ2 h17 h43 h47 h48 hc8 h
  rw [stepEnd_8] at e8
  obtain ⟨k9, u9⟩ := split6 (by norm_num) e8
  simp only [Nat.reduceSub] at k8 u8
  rw [← k8] at r8
  rw [holdsList_append] at h
  obtain ⟨xs9, c10, cap10, hx9, r9, hc10, e9, h⟩ := stepT_holdsL (s := 9) (b := 2763) (by norm_num) (by norm_num) hτ1 hτ2 h17 h43 h47 h48 hc9 h
  rw [stepEnd_9] at e9
  obtain ⟨k10, u10⟩ := split6 (by norm_num) e9
  simp only [Nat.reduceSub] at k9 u9
  rw [← k9] at r9
  rw [holdsList_append] at h
  obtain ⟨xs10, c11, cap11, hx10, r10, hc11, e10, h⟩ := stepT_holdsL (s := 10) (b := 3074) (by norm_num) (by norm_num) hτ1 hτ2 h17 h43 h47 h48 hc10 h
  rw [stepEnd_10] at e10
  obtain ⟨k11, u11⟩ := split6 (by norm_num) e10
  simp only [Nat.reduceSub] at k10 u10
  rw [← k10] at r10
  obtain ⟨xs11, c12, cap12, hx11, r11, hc12, e11, h⟩ := stepT_holdsL (s := 11) (b := 3383) (by norm_num) (by norm_num) hτ1 hτ2 h17 h43 h47 h48 hc11 h
  rw [stepEnd_11] at e11
  obtain ⟨k12, u12⟩ := split6 (by norm_num) e11
  simp only [Nat.reduceSub] at k11 u11
  rw [← k11] at r11
  simp only [Nat.reduceSub] at k12 u12
  have run := runsTo_keccakLayers_cons r0 (runsTo_keccakLayers_cons r1 (runsTo_keccakLayers_cons r2
    (runsTo_keccakLayers_cons r3 (runsTo_keccakLayers_cons r4 (runsTo_keccakLayers_cons r5
    (runsTo_keccakLayers_cons r6 (runsTo_keccakLayers_cons r7 (runsTo_keccakLayers_cons r8
    (runsTo_keccakLayers_cons r9 (runsTo_keccakLayers_cons r10 (runsTo_keccakLayers_cons r11
    (runsTo_keccakLayers_nil τ c12 _))))))))))))
  have R11 : ReadsAt rd (σ (.n 3382)) (xs11 ++ []) := by simpa using hx11
  have R10 : ReadsAt rd (σ (.n 3073)) (xs10 ++ (xs11 ++ [])) :=
    readsAt_append.2 ⟨hx10, by rw [← u11]; exact R11⟩
  have R9 : ReadsAt rd (σ (.n 2762)) (xs9 ++ (xs10 ++ (xs11 ++ []))) :=
    readsAt_append.2 ⟨hx9, by rw [← u10]; exact R10⟩
  have R8 : ReadsAt rd (σ (.n 2500)) (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ [])))) :=
    readsAt_append.2 ⟨hx8, by rw [← u9]; exact R9⟩
  have R7 : ReadsAt rd (σ (.n 2191)) (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ []))))) :=
    readsAt_append.2 ⟨hx7, by rw [← u8]; exact R8⟩
  have R6 : ReadsAt rd (σ (.n 1978)) (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ [])))))) :=
    readsAt_append.2 ⟨hx6, by rw [← u7]; exact R7⟩
  have R5 : ReadsAt rd (σ (.n 1623)) (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ []))))))) :=
    readsAt_append.2 ⟨hx5, by rw [← u6]; exact R6⟩
  have R4 : ReadsAt rd (σ (.n 1314)) (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ [])))))))) :=
    readsAt_append.2 ⟨hx4, by rw [← u5]; exact R5⟩
  have R3 : ReadsAt rd (σ (.n 959)) (xs3 ++ (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ []))))))))) :=
    readsAt_append.2 ⟨hx3, by rw [← u4]; exact R4⟩
  have R2 : ReadsAt rd (σ (.n 745)) (xs2 ++ (xs3 ++ (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ [])))))))))) :=
    readsAt_append.2 ⟨hx2, by rw [← u3]; exact R3⟩
  have R1 : ReadsAt rd (σ (.n 530)) (xs1 ++ (xs2 ++ (xs3 ++ (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ []))))))))))) :=
    readsAt_append.2 ⟨hx1, by rw [← u2]; exact R2⟩
  have R0 : ReadsAt rd (σ (.n 5) * gen) (xs0 ++ (xs1 ++ (xs2 ++ (xs3 ++ (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ [])))))))))))) :=
    readsAt_append.2 ⟨hx0, by rw [← u1]; exact R1⟩
  refine ⟨xs0 ++ (xs1 ++ (xs2 ++ (xs3 ++ (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ []))))))))))), c12, R0, ?_, hc12, ?_, h⟩
  · rw [k12] at run
    exact run
  · rw [u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1]
    simp only [List.length_append, List.length_nil, Nat.add_zero, pow_add, mul_assoc]

end
end LeanVM.Guest.B1.VerifySub
