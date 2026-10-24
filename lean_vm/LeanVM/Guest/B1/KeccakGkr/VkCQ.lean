/-
  LeanVM.Guest.B1.KeccakGkr.VkCQ

  The pointers `verify_keccak` loads through, on its layout.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCP

/-!
# The pointers, on the layout

`step_ptrs`: step `s` loads its claim's point at `stepB s + 2` and, for a later claim, its lanes
and slices at each flip's first two values; `fin_ptrs`: the inputs' check loads the last claim's
point, local point and lanes through `4978`, `5212`, `6363`. Each is a pointer into the claim's
buffers (`CL`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

namespace VkData

variable {D : VkData} {rd : Reader} {B curE chiE olE zvE slE : ℕ} {ls : ℕ → ℕ}

/-- Word `k` of claim `s`'s record, through the claim records' pointer. -/
theorem rec_word (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE ls) {σ : Val}
    (h201 : σ (.n 201) = ptr (B + D.o201)) {s : ℕ} (hs : s < 12) {k : ℕ} (hk : k < 22) :
    LoadHolds rd (σ (.n 201)) (22 * s + k) ((D.CL B ls s).cw.getD k 0) := by
  have hcw := memL_entry (CL_mem h hm hs) (b := (D.CL B ls s).bclaim) (ws := (D.CL B ls s).cw)
    (by simp [ClaimLay.L])
  have hbc : (D.CL B ls s).bclaim = B + D.o201 + 22 * s := by cases s <;> rfl
  rw [hbc, ← ptr_mul_gen, ← h201] at hcw
  have := ClaimLay.getD_load hcw (k := k) (by rw [(D.CL_ok h B ls hs.le).1]; exact hk)
  exact (loadHolds_mul_gen_pow rd _ _ _ _).1 this

set_option maxHeartbeats 4000000 in
/-- **Step `s`'s pointers.** -/
theorem step_ptrs (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE) {s : ℕ} (hs : s < 12)
    (h17 : σ (.n 17) = gen ^ (D.τ - 4)) (h201 : σ (.n 201) = ptr (B + D.o201)) :
    σ (.n (stepB s + 2)) = ptr (D.CL B ls s).bpp * gen ^ (D.τ - 4) ∧
    (s ≠ 0 → ∀ j < (iotaUsed s).length, σ (.n (stepB s + 6 + 46 * j)) = ptr (D.CL B ls s).blp ∧
      σ (.n (stepB s + 6 + 46 * j + 1)) = ptr (D.CL B ls s).bsl) := by
  have hg : ∀ st ∈ stepCore s (stepB s), GoodS rd vkSt (D.w B curE) σ st := fun st hst ↦ by
    subst hσd
    refine val_good' h (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (mem_steps s hs st ?_)))))
    rw [stepT_split]; exact List.mem_append_left _ hst
  have gA : ∀ a, Stmt.atom a ∈ stepCore s (stepB s) → Good rd vkSt (D.w B curE) σ a :=
    fun a h ↦ hg _ h
  obtain ⟨k1, -, -, -, -, k6, -⟩ := step_ker s hs
  obtain ⟨-, -, -, -, -, h2, h3, -, -, hw⟩ := D.CL_ok h B ls hs.le
  obtain ⟨-, hbB⟩ := step_bounds s hs
  have e0 : σ (.n (stepB s)) = ptr (D.CL B ls s).bpp := by
    have := rec_word h hm h201 hs (k := 2) (by norm_num)
    rw [h2] at this
    exact load_val (gA (.load (.n (stepB s)) (.n 201) (22 * s + 2)) (mem_stepCoreA (by simp)))
      (not_mem_of_noneIn k1 _ (by simp)) this
  have m2 := mulG (by omega) (by omega)
    (gA (.mul (.n (stepB s + 2)) (.n (stepB s)) (.n 17)) (mem_stepCoreA (by simp)))
  refine ⟨by rw [m2, e0, h17], fun hs0 j hj ↦ ?_⟩
  have hf0 : firstOf s = 0 := by unfold firstOf; split <;> omega
  simp only [hf0, show (0 : ℕ) = 1 ↔ False by decide, ↓reduceIte] at hw
  obtain ⟨h4, h5, -, -⟩ := hw
  have hm' : ∀ a ∈ [Atom.load (.n (stepB s + 6 + 46 * j)) (.n 201) (22 * s + 3),
      .load (.n (stepB s + 6 + 46 * j + 1)) (.n 201) (22 * s + 5)],
      Stmt.atom a ∈ flipsT s (stepB s + 6) := by
    intro a ha
    simp only [flipsT, List.mem_flatten, List.mem_map, List.mem_range]
    refine ⟨_, ⟨j, hj, rfl⟩, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp [flipT, hs0, flipSz]
  have m0 := hm' (.load (.n (stepB s + 6 + 46 * j)) (.n 201) (22 * s + 3)) (by simp)
  have m1 := hm' (.load (.n (stepB s + 6 + 46 * j + 1)) (.n 201) (22 * s + 5)) (by simp)
  have l3 := rec_word h hm h201 hs (k := 3) (by norm_num)
  have l5 := rec_word h hm h201 hs (k := 5) (by norm_num)
  rw [h3] at l3
  rw [h5] at l5
  exact ⟨load_val (w := D.w B curE) (hg _ (mem_stepCoreF m0))
      (not_mem_of_noneIn k6 _ (load_mem_resid m0)) l3,
    load_val (w := D.w B curE) (hg _ (mem_stepCoreF m1))
      (not_mem_of_noneIn k6 _ (load_mem_resid m1)) l5⟩

/-- **The inputs' check's pointers.** -/
theorem fin_ptrs (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE) (h17 : σ (.n 17) = gen ^ (D.τ - 4))
    (h201 : σ (.n 201) = ptr (B + D.o201)) :
    σ (.n 4978) = ptr (ls 11) * gen ^ (D.τ - 4) ∧
      σ (.n 5212) = ptr (ls 11 + (D.layer 11).y + 128) ∧
      σ (.n 6363) = ptr (ls 11 + (D.layer 11).y + 139) := by
  have hg : ∀ st ∈ vkFinT, GoodS rd vkSt (D.w B curE) σ st := fun st hst ↦ by
    subst hσd
    exact val_good' h (List.mem_append_right _ hst)
  have gA : ∀ a, Stmt.atom a ∈ vkFinT → Good rd vkSt (D.w B curE) σ a := fun a h ↦ hg _ h
  have k1 := vkFin_ker.1
  have hrec := last_rec h hm
  rw [outWs_last h, ← h201] at hrec
  have e4977 : σ (.n 4977) = ptr (ls 11) :=
    load_val (gA (.load (.n 4977) (.n 201) 266) (by simp [vkFinT])) (not_mem_of_noneIn k1 _ (by simp))
      (by simpa using hrec 2 (by norm_num))
  have m4978 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 4978) (.n 4977) (.n 17)) (by simp [vkFinT]))
  refine ⟨by rw [m4978, e4977, h17], ?_, ?_⟩
  · exact load_val (gA (.load (.n 5212) (.n 201) 268) (by simp [vkFinT]))
      (not_mem_of_noneIn k1 _ (by simp)) (by simpa using hrec 4 (by norm_num))
  · exact load_val (gA (.load (.n 6363) (.n 201) 267) (by simp [vkFinT]))
      (not_mem_of_noneIn k1 _ (by simp)) (by simpa using hrec 3 (by norm_num))

end VkData

end
end LeanVM.Guest.B1.VerifySub
