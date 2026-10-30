/-
  LeanVM.Guest.B1.KeccakGkr.VkIn

  `verify_keccak`'s inputs' opening up to the slices (G:2873-2925).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkOut
public import LeanVM.Guest.B1.KeccakGkr.VkSlices
public import LeanVM.Guest.B1.KeccakGkr.VkOpenMath

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {rd : Reader} {σ : Val}

theorem word_2p39 : word 549755813888 0 0 = gen ^ 39 := by
  rw [show (549755813888 : ℕ) = 2 ^ 39 from rfl]; exact word_two_pow (by decide)

/-- **The inputs' opening up to the slices** (G:2873-2925). -/
theorem vkInT_holds {τ : ℕ} (h6 : σ (.n 6) = gen ^ τ)
    {c : KeccakClaim} (hc : ClaimRec rd ((0 : ℕ) = 1) (σ (.n 201) * gen ^ (22 * 12)) c (τ - 3))
    (hw : FsPackOk σ (.n 3701) (3701 + 1) dsObserve)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ vkInT next kret) :
    ∃ (mI mS : List (E × E)) (low slotI : List E), mI.length = 4 ∧
      ReadsAt rd (σ (.n 3699) * gen) (mI.flatMap fun c ↦ [c.1, c.2]) ∧
      plainRun mI c.value
        ((⟨[σ (.n 3694), σ (.n 3695), σ (.n 3696), σ (.n 3697), σ (.n 3698)], []⟩ : Fs).absorb
          (σ (.n 3701)) dsObserve) =
        (low, σ (.n 3986), ⟨[σ (.n 3980), σ (.n 3981), σ (.n 3982), σ (.n 3983), σ (.n 3984)], []⟩) ∧
      ReadsAt rd (σ (.n 9) * gen ^ 39) low ∧ σ (.n 3985) = σ (.n 3699) * gen * gen ^ 8 ∧
      σ (.n 4104) = multilinearEval c.mu low ∧
      mS.length = 6 ∧ ReadsAt rd (σ (.n 3985)) (mS.flatMap fun c ↦ [c.1, c.2]) ∧
      plainRun mS (σ (.n 3986))
        ⟨[σ (.n 3980), σ (.n 3981), σ (.n 3982), σ (.n 3983), σ (.n 3984)], []⟩ =
        (slotI, σ (.n 4116),
          ⟨[σ (.n 4110), σ (.n 4111), σ (.n 4112), σ (.n 4113), σ (.n 4114)], []⟩) ∧
      ReadsAt rd (σ (.n 4107)) slotI ∧ σ (.n 4107) = σ (.n 9) * gen ^ 39 * gen ^ τ ∧
      σ (.n 4115) = σ (.n 3985) * gen ^ 12 ∧
      ReadsAt rd (σ (.n 4115)) ((List.range 64).map fun z ↦ σ (.n (slB 4122 z))) ∧
      (∀ z < 64, LoadHolds rd (σ (.n 10)) z (σ (.n (slB 4122 z)))) ∧
      ((⟨[σ (.n 4110), σ (.n 4111), σ (.n 4112), σ (.n 4113), σ (.n 4114)], []⟩ : Fs).absorbAll
        ((List.range 64).map fun z ↦ σ (.n (slB 4122 z))) dsObserve).squeeze =
        (σ (.n 4976), ⟨[σ (.n 4965), σ (.n 4966), σ (.n 4967), σ (.n 4968), σ (.n 4969)], []⟩) ∧
      next := by
  obtain ⟨hmuL, hptL, hval, -, hmus, -⟩ := hc
  rw [vkInT] at h
  generalize hEQ : eqtreeT (.n 9) (.n 3987) 39 3988 4 = EQ at h
  generalize hPD : pairsDotT (.n 3987) (.n 201) (consecOffs 14 270 16) 4042 = PD at h
  generalize hSL : slicesT (.n 4115) 4117 4122 = SL at h
  generalize hCP : (List.range 5).map (fun j ↦ Stmt.atom (.copy (.n (4117 + j)) (.n (4110 + j)))) = CP at h
  simp only [holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil] at h
  obtain ⟨e75, e76, l77, e78, e79, hcall1, -, h⟩ := h
  -- the pack's rounds
  obtain ⟨mI, hmL, hmR, hrun⟩ := plain_call (k0 := 1) (n := 4) (by omega) rfl
    (cap := [σ (.n 3694), σ (.n 3695), σ (.n 3696), σ (.n 3697), σ (.n 3698)]) rfl
    (by simpa [List.range_succ, plainName] using hcall1)
  obtain ⟨hpt1, hrets1⟩ := hrun (σ (.n 3701)) (fun _ hc ↦ fsPackT_cells hw hc)
  simp only [plainStart, ↓reduceIte] at hpt1 hrets1
  have hval' : σ (.n 3977) = c.value := by
    have := (loadHolds_mul_gen_pow rd _ _ _ _).1 hval
    exact loadHolds_unique l77 (by simpa using this)
  rw [hval'] at hpt1 hrets1
  have hpend1 := plainRun_pend mI c.value
    ⟨[σ (.n 3694), σ (.n 3695), σ (.n 3696), σ (.n 3697), σ (.n 3698)], [(σ (.n 3701), dsObserve)]⟩
    (by rintro rfl; simp at hmL)
  set R1 := plainRun mI c.value
    ⟨[σ (.n 3694), σ (.n 3695), σ (.n 3696), σ (.n 3697), σ (.n 3698)], [(σ (.n 3701), dsObserve)]⟩
    with hR1
  rw [show [σ (.n 3980), σ (.n 3981), σ (.n 3982), σ (.n 3983), σ (.n 3984), σ (.n 3985),
      σ (.n 3986)] = [σ (.n 3980), σ (.n 3981), σ (.n 3982), σ (.n 3983), σ (.n 3984)] ++
      [σ (.n 3985), σ (.n 3986)] from rfl] at hrets1
  obtain ⟨hcap1, hlast1⟩ := List.append_inj' hrets1 rfl
  simp only [List.cons.injEq, and_true] at hlast1
  obtain ⟨h3985, h3986⟩ := hlast1
  have hR1s : R1 = (R1.1, σ (.n 3986),
      ⟨[σ (.n 3980), σ (.n 3981), σ (.n 3982), σ (.n 3983), σ (.n 3984)], []⟩) := by
    rw [h3986, hcap1, ← hpend1]
  have hlowL : R1.1.length = 4 := by rw [hR1, plainRun_length, hmL]
  have h3979 : σ (.n 3979) = σ (.n 9) * gen ^ 39 := by rw [e79, e78, word_2p39]
  -- the low tree and μ at the low point
  rw [← hEQ] at h
  obtain ⟨hlt, h⟩ := eqtreeT_last (rs := R1.1) (n := 4) (by omega) hlowL (fun t ht ↦ by
    have := hpt1 t (by omega)
    rw [h3979, loadHolds_mul_gen_pow] at this
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact this) h
  rw [← hPD] at h
  obtain ⟨hmu, h⟩ := pairsDotT_holds (P := fun i ↦ (eqKernel R1.1).getD i 0)
    (Q := fun i ↦ c.mu.getD i 0) (fun k hk v hv ↦ by
      simp only [consecOffs, List.length_map, List.length_range] at hk
      simp only [consecOffs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some] at hv
      have := hlt k (by norm_num; omega)
      simp only [show 2 ^ 4 - 2 = 14 from rfl] at this
      exact loadHolds_unique hv (by simpa [List.getD_eq_getElem?_getD] using this))
    (fun k hk v hv ↦ by
      simp only [consecOffs, List.length_map, List.length_range] at hk
      simp only [consecOffs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some] at hv
      have := (loadHolds_mul_gen_pow rd _ _ _ _).1 (hmus k (by simp [pack]; omega))
      exact loadHolds_unique hv (by
        rw [List.getD_eq_getElem?_getD] at this ⊢
        simpa [show 22 * 12 + (6 + k) = 270 + k by omega] using this))
    (by simp [consecOffs]) h
  simp only [consecOffs, List.length_map, List.length_range, pairsDotV] at hmu
  have hmle : σ (.n 4104) = multilinearEval c.mu R1.1 := by
    rw [show (4104 : ℕ) = 4042 + 4 * (16 - 1) + 2 from rfl, hmu,
      multilinearEval_eqAt c.mu R1.1 (by simpa [pack] using hmuL) hlowL]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < 16 := Finset.mem_range.1 hi
    rw [eqKernel_getD]
    simp [hlowL, hi']
  -- the slot's rounds
  obtain ⟨e05, e06, e07, -, -, hcall2, h⟩ := h
  obtain ⟨mS, hsL, hsR, hrun2⟩ := plain_call (k0 := 0) (n := 6) (by omega) rfl
    (cap := [σ (.n 3980), σ (.n 3981), σ (.n 3982), σ (.n 3983), σ (.n 3984)]) rfl
    (by simpa [List.range_succ, plainName] using hcall2)
  obtain ⟨hpt2, hrets2⟩ := hrun2 0 (fun h ↦ absurd h (by decide))
  simp only [plainStart, show ¬ ((0 : ℕ) = 1) by decide, ↓reduceIte] at hpt2 hrets2
  have hpend2 := plainRun_pend mS (σ (.n 3986))
    ⟨[σ (.n 3980), σ (.n 3981), σ (.n 3982), σ (.n 3983), σ (.n 3984)], []⟩
    (by rintro rfl; simp at hsL)
  set R2 := plainRun mS (σ (.n 3986))
    ⟨[σ (.n 3980), σ (.n 3981), σ (.n 3982), σ (.n 3983), σ (.n 3984)], []⟩ with hR2
  rw [show [σ (.n 4110), σ (.n 4111), σ (.n 4112), σ (.n 4113), σ (.n 4114), σ (.n 4115),
      σ (.n 4116)] = [σ (.n 4110), σ (.n 4111), σ (.n 4112), σ (.n 4113), σ (.n 4114)] ++
      [σ (.n 4115), σ (.n 4116)] from rfl] at hrets2
  obtain ⟨hcap2, hlast2⟩ := List.append_inj' hrets2 rfl
  simp only [List.cons.injEq, and_true] at hlast2
  obtain ⟨h4115, h4116⟩ := hlast2
  have hR2s : R2 = (R2.1, σ (.n 4116),
      ⟨[σ (.n 4110), σ (.n 4111), σ (.n 4112), σ (.n 4113), σ (.n 4114)], []⟩) := by
    rw [h4116, hcap2, ← hpend2]
  -- the copies and the slices
  rw [← hCP, holdsList_map_atoms] at h
  obtain ⟨hcp, h⟩ := h
  simp only [Atom.Holds] at hcp
  rw [← hSL] at h
  obtain ⟨hrs, hst, hsq, hn⟩ := slicesT_holds h
  have hc5 : (cap5 4117).map σ = [σ (.n 4110), σ (.n 4111), σ (.n 4112), σ (.n 4113), σ (.n 4114)] := by
    simp only [cap5, List.map_cons, List.map_nil]
    rw [hcp 0 (by omega), hcp 1 (by omega), hcp 2 (by omega), hcp 3 (by omega), hcp 4 (by omega)]
  rw [hc5, show (4122 : ℕ) + 854 = 4976 from rfl, show (4122 : ℕ) + 843 = 4965 from rfl] at hsq
  refine ⟨mI, mS, R1.1, R2.1, hmL, ?_, ?_, ?_, ?_, hmle, hsL, ?_, hR2s, hpt2, ?_, h4115.trans
    (by norm_num), hrs, hst, by simpa [cap5] using hsq, hn⟩
  · rw [e76, e75, word_gen] at hmR; exact hmR
  · rw [show (⟨[σ (.n 3694), σ (.n 3695), σ (.n 3696), σ (.n 3697), σ (.n 3698)], []⟩ : Fs).absorb
      (σ (.n 3701)) dsObserve = ⟨[σ (.n 3694), σ (.n 3695), σ (.n 3696), σ (.n 3697), σ (.n 3698)],
        [(σ (.n 3701), dsObserve)]⟩ from rfl]
    exact hR1s
  · rw [← h3979]; exact hpt1
  · rw [h3985, e76, e75, word_gen]
  · exact hsR
  · rw [e07, e06, e05, word_2p39, h6]

end
end LeanVM.Guest.B1.VerifySub
