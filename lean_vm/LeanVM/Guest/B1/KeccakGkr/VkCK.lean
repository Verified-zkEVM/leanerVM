/-
  LeanVM.Guest.B1.KeccakGkr.VkCK

  `verify_keccak`'s honest oracle: the bits of `y`, the buffers' bases, the callees' returns; and
  the buffers' words in memory.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCJ
public import LeanVM.Guest.B1.KeccakGkr.FlatGI

/-!
# The oracle

`D.w B curE`: the values `Fwd.ev` takes from its oracle, honestly: the bits of `y = τ - 3`, the
nineteen buffers' bases from `B`, the layers' and the openings' rounds' returns (the cursors from
`curE`). `own_mem`: a memory holding the buffers holds each of them.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public noncomputable section

/-- Where step `s` ends. -/
def stepE (s : ℕ) : ℕ :=
  [531, 746, 960, 1315, 1624, 1979, 2192, 2501, 2763, 3074, 3383, 3691].getD s 0

theorem stepE_eq : ∀ s < 12, stepT0 s (stepB s) + stepTailSz s = stepE s := by decide +kernel

namespace VkData

variable (D : VkData)

/-- **The oracle.** -/
def w (B curE : ℕ) (i : ℕ) : E :=
  if 20 ≤ i ∧ i < 25 then Value.bitE ((D.τ - 3).testBit (i - 20))
  else if i = 58 then ptr B
  else if i = 90 then ptr (B + (D.τ - 3))
  else if i = 201 then ptr (B + D.o201)
  else if i = 203 then ptr (B + D.τ + 288)
  else if i = 274 then ptr (B + D.o274)
  else if i = 382 then ptr (B + D.τ + 380)
  else if i = 3987 then ptr (B + D.τ + 406)
  else if 3694 ≤ i ∧ i < 3701 then (D.oRets curE).getD (i - 3694) 0
  else if 3980 ≤ i ∧ i < 3987 then (D.iRets curE).getD (i - 3980) 0
  else if 4110 ≤ i ∧ i < 4117 then (D.sRets curE).getD (i - 4110) 0
  else match (List.range 12).find? (fun s ↦ i == stepB s + 1) with
    | some s => ptr (B + D.τ + 382 + 2 * s)
    | none => match (List.range 12).find? (fun s ↦ stepE s - 6 ≤ i && i < stepE s) with
      | some s => ((D.layer s).rets (firstOf s) (ptr (curE + D.lcur s))).getD (i - (stepE s - 6)) 0
      | none => 0

variable {D} {B curE : ℕ}

theorem w_bits {j : ℕ} (hj : j < 5) : D.w B curE (20 + j) = Value.bitE ((D.τ - 3).testBit j) := by
  simp only [w, Nat.le_add_right, true_and, show 20 + j < 25 by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]


theorem w_o {j : ℕ} (hj : j < 7) : D.w B curE (3694 + j) = (D.oRets curE).getD j 0 := by
  interval_cases j <;> rfl

theorem w_i {j : ℕ} (hj : j < 7) : D.w B curE (3980 + j) = (D.iRets curE).getD j 0 := by
  interval_cases j <;> rfl

theorem w_s {j : ℕ} (hj : j < 7) : D.w B curE (4110 + j) = (D.sRets curE).getD j 0 := by
  interval_cases j <;> rfl

theorem w_step {s : ℕ} (hs : s < 12) : D.w B curE (stepB s + 1) = ptr (B + D.τ + 382 + 2 * s) := by
  interval_cases s <;> rfl

theorem w_layer {s : ℕ} (hs : s < 12) {j : ℕ} (hj : j < 6) :
    D.w B curE (stepE s - 6 + j) =
      ((D.layer s).rets (firstOf s) (ptr (curE + D.lcur s))).getD j 0 := by
  interval_cases s <;> interval_cases j <;> rfl

theorem bufL_eq (h3 : 3 ≤ D.τ) (B : ℕ) (ls : ℕ → ℕ) :
    bufL B D.sizes (D.own B ls) =
      [(B, D.c0.point), (B + (D.τ - 3), D.rl), (B + D.o201, D.claims B ls),
        (B + D.τ + 288, eqLevels (D.chis.take 4) 4), (B + D.o274, eqLevels D.rl 5),
        (B + D.τ + 380, eqKernel D.seg)] ++
      (List.range 12).map (fun s ↦ (B + D.τ + 382 + 2 * s, D.segW s)) ++
      [(B + D.τ + 406, eqLevels D.I.1 4)] := by
  rw [bufL, bases_eq D B h3, own]
  rw [List.zip_append (by simp), List.zip_append (by simp)]
  simp [List.range_succ]

/-- **The buffers, each in memory.** -/
theorem own_mem (h3 : 3 ≤ D.τ) {rd : Reader} {B : ℕ} {ls : ℕ → ℕ}
    (hm : MemL rd (bufL B D.sizes (D.own B ls))) :
    ReadsAt rd (ptr B) D.c0.point ∧ ReadsAt rd (ptr (B + (D.τ - 3))) D.rl ∧
      ReadsAt rd (ptr (B + D.o201)) (D.claims B ls) ∧
      ReadsAt rd (ptr (B + D.τ + 288)) (eqLevels (D.chis.take 4) 4) ∧
      ReadsAt rd (ptr (B + D.o274)) (eqLevels D.rl 5) ∧
      ReadsAt rd (ptr (B + D.τ + 380)) (eqKernel D.seg) ∧
      (∀ s < 12, ReadsAt rd (ptr (B + D.τ + 382 + 2 * s)) (D.segW s)) ∧
      ReadsAt rd (ptr (B + D.τ + 406)) (eqLevels D.I.1 4) := by
  rw [bufL_eq h3] at hm
  refine ⟨memL_entry hm (by simp), memL_entry hm (by simp), memL_entry hm (by simp),
    memL_entry hm (by simp), memL_entry hm (by simp), memL_entry hm (by simp),
    fun s hs ↦ memL_entry hm (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩))),
    memL_entry hm (by simp)⟩

end VkData

end
end LeanVM.Guest.B1.VerifySub
