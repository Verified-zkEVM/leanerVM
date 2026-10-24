/-
  LeanVM.Guest.B1.KeccakGkr.VkCN

  `verify_keccak`'s steps on its layout: the claim records in memory, each step holding.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCM

/-!
# The steps, on the layout

`CL_mem`: on a memory holding the layout, claim `s`'s record and buffers (`CL`) are in memory:
the first in `verify_keccak`'s buffers, the later ones in its claim records and the previous
layer's buffers. `mem_steps`: step `s`'s statements are the body's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

theorem mem_steps : ∀ s < 12, ∀ st ∈ stepT s (stepB s) (stepCap s) (stepCur s) vkGw,
    st ∈ vkStepsT := by
  intro s hs st hst
  rw [vkStepsT]
  interval_cases s
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hst)))))))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))))))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst))))))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst))))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))
  · exact (List.mem_append_left _ (List.mem_append_right _ hst))
  · exact (List.mem_append_right _ hst)

namespace VkData

variable {D : VkData} {rd : Reader} {B curE chiE olE zvE slE : ℕ} {ls : ℕ → ℕ}

theorem outWs_length (s : ℕ) : (D.outWs ls s).length = 22 := by
  simp [outWs, LayerData.outW, LayerData.next, layerClaim, keccakInstanceWeights_length]

theorem cw0_length (h : D.Ok) : (D.cw0 B).length = 22 := by simp [cw0, c0_mu h]

/-- Claim `s + 1`'s record, in the claim records. -/
theorem claims_slice (h : D.Ok) {k : ℕ} (hk : k < 12)
    (hc : ReadsAt rd (ptr (B + D.o201)) (D.claims B ls)) :
    ReadsAt rd (ptr (B + D.o201 + 22 * (k + 1))) (D.outWs ls k) := by
  rw [claims, flatMap_range_split _ hk] at hc
  have := readsAt_mid (A := D.cw0 B ++ (List.range k).flatMap (D.outWs ls))
    (by simpa only [List.append_assoc] using hc)
  rw [ptr_mul_gen, List.length_append, cw0_length h,
    flatMap_range_length _ (fun j _ ↦ outWs_length j)] at this
  rwa [show B + D.o201 + (22 + k * 22) = B + D.o201 + 22 * (k + 1) by ring] at this

/-- The first claim's record, in the claim records. -/
theorem claims_first (hc : ReadsAt rd (ptr (B + D.o201)) (D.claims B ls)) :
    ReadsAt rd (ptr (B + D.o201 + 22 * 0)) (D.cw0 B) :=
  (Digest.readsAt_append.1 hc).1

/-- The first claim's lanes, in the lane coordinates' tree. -/
theorem lanes_first (ht : ReadsAt rd (ptr (B + D.o274)) (eqLevels D.rl 5)) :
    ReadsAt rd (ptr (B + D.o274 + 30)) ((eqKernel D.rl).take 25) := by
  rw [eqLevels_succ] at ht
  have := (Digest.readsAt_append.1 ht).2
  rw [ptr_mul_gen, eqLevels_length (by rw [rl_length]; norm_num),
    show D.rl.take (4 + 1) = D.rl from List.take_of_length_le (by rw [rl_length])] at this
  intro k hk
  simp only [List.length_take, eqKernel_length, rl_length] at hk
  rw [List.getElem_take]
  exact this k (by simp [eqKernel_length, rl_length]; omega)

/-- **Claim `s`'s record and buffers, in memory.** -/
theorem CL_mem (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE ls) {s : ℕ} (hs : s < 12) :
    MemL rd ((D.CL B ls s).L (firstOf s) (D.layer s).c) := by
  obtain ⟨m58, -, m201, -, m274, -, -, -⟩ := own_mem (by have := h.1; omega) hm.own
  rcases s with _ | k
  · intro q hq
    simp only [CL, ClaimLay.L, firstOf, ↓reduceIte, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact claims_first m201
    · exact m58
    · exact lanes_first m274
  · have hk : k < 12 := by omega
    have hL := hm.lay k hk
    rw [layerBufs_eq] at hL
    have hc : (D.layer (k + 1)).c = (D.layer k).next (firstOf k) := by
      show (D.chain (k + 1)).1 = _
      rw [D.layer_succ h hk]
    intro q hq
    simp only [CL, ClaimLay.L, show firstOf (k + 1) = 0 from rfl, show (0 : ℕ) ≠ 1 by decide,
      ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl) | rfl | rfl
    · exact claims_slice h hk m201
    · rw [hc, show ((D.layer k).next (firstOf k)).point = (D.layer k).chs (firstOf k) from rfl]
      exact hL _ (by simp)
    · exact hL _ (by simp)
    · exact hL _ (by simp)
    · exact hL _ (by simp)

end VkData

end
end LeanVM.Guest.B1.VerifySub
