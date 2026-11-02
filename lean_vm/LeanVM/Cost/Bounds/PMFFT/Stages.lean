module

public import LeanVM.Cost.Bounds.PMFFT.Lib

/-!
# Bounds of the PM decoder's FFT: the butterflies

`planFwd` and `planInv` by the plan of size `N = 2^j`: `j` stages, each `fwdStageFast` (the
products `t·hi` in one pass, the outputs in another) or `invStageFast` (one pass); every entry
bounded uniformly (`fwdStage_cost`: `390·N + 100`, `invStage_cost`: `330·N + 80`).
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction.Fast
open Auto.LeanVM.Extraction.Fast.FFT

public section

variable (P : MachineProgram)

/-- `Nat.testBit` (`testBit.c225`): `13` on words. -/
theorem testBit_cost' (hP : Includes P Auto.Nat.testBit.c225.costDeps) (a b : ℕ) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) : machineCost P Auto.Nat.testBit.c225.costIdx [encodeValue a, encodeValue b] ≤ 13 := by
  rw [Auto.Nat.testBit.c225.costEq P hP, limbs_of_lt ha, limbs_of_lt hb,
    limbs_of_lt (lt_of_le_of_lt (Nat.shiftRight_le a b) ha),
    limbs_of_lt (lt_of_le_of_lt (Nat.and_le_left (n := 1) (m := a >>> b)) (by norm_num))]

/-- **A forward stage** over `2^m` (`fwdStageFast.c511`): at most `390·2^m + 100`. -/
theorem fwdStage_cost (hP : Includes P fwdStageFast.c511.costDeps) {m i : ℕ} (hi : i < m)
    (hm : m ≤ 40) (tw b : Array K) :
    machineCost P fwdStageFast.c511.costIdx [encodeValue m, encodeValue i, encodeValue tw,
      encodeValue b] ≤ 390 * 2 ^ m + 100 := by
  rw [fwdStageFast.c511.costEq P hP]
  have hN : 2 ^ m ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hm
  have hHi : 2 ^ (i + 1) ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hH : 2 ^ i ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h0 := ofFnFrom_cost P (by includes) (n := 2 ^ m) (by omega) _
    (.closure fwdStageFast.c511.lam0.costIdx [encodeValue m, encodeValue i, encodeValue tw,
      encodeValue b, encodeValue (2 ^ i), encodeValue (2 ^ (i + 1))])
    (fun p ↦ RunsApp.of_spec (fwdStageFast.c511.lam0.costSpec P (by includes) m i tw b _ _ p)) 300
    (fun p ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      have hp : p.val < 2 ^ 40 := by have := p.isLt; omega
      have := testBit_cost' P (by includes) p.val i (by omega) (by omega)
      rw [fwdStageFast.c511.lam0.costEq P (by includes)]
      cost_simp
      split_ifs <;> omega) 0 (Nat.zero_le _)
  have h1 := ofFnFrom_cost P (by includes) (n := 2 ^ m) (by omega) _
    (.closure fwdStageFast.c511.lam1.costIdx [encodeValue m, encodeValue i, encodeValue b,
      encodeValue (Array.ofFn fun p : Fin (2 ^ m) ↦
        if p.val.testBit i = true then 0 else tw.getD (p.val / 2 ^ (i + 1)) 0 * b.getD (p.val + 2 ^ i) 0),
      encodeValue (2 ^ i), encodeValue (2 ^ (i + 1))])
    (fun p ↦ RunsApp.of_spec (fwdStageFast.c511.lam1.costSpec P (by includes) m i b _ _ _ p)) 50
    (fun p ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      have hp : p.val < 2 ^ 40 := by have := p.isLt; omega
      have := testBit_cost' P (by includes) p.val i (by omega) (by omega)
      rw [fwdStageFast.c511.lam1.costEq P (by includes)]
      cost_simp
      split_ifs <;> omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, ofFnFrom_length, limbs_shift (by omega), limbs_shift (by omega),
    limbs_shift (by omega)]
  cost_simp
  simp only [Nat.sub_zero] at h0 h1
  omega

/-- **An inverse stage** over `2^m` (`invStageFast.c516`): at most `330·2^m + 80`. -/
theorem invStage_cost (hP : Includes P invStageFast.c516.costDeps) {m i : ℕ} (hi : i < m)
    (hm : m ≤ 40) (tw b : Array K) :
    machineCost P invStageFast.c516.costIdx [encodeValue m, encodeValue i, encodeValue tw,
      encodeValue b] ≤ 330 * 2 ^ m + 80 := by
  rw [invStageFast.c516.costEq P hP]
  have hN : 2 ^ m ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hm
  have hHi : 2 ^ (i + 1) ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hH : 2 ^ i ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h0 := ofFnFrom_cost P (by includes) (n := 2 ^ m) (by omega) _
    (.closure invStageFast.c516.lam0.costIdx [encodeValue m, encodeValue i, encodeValue tw,
      encodeValue b, encodeValue (2 ^ i), encodeValue (2 ^ (i + 1))])
    (fun p ↦ RunsApp.of_spec (invStageFast.c516.lam0.costSpec P (by includes) m i tw b _ _ p)) 310
    (fun p ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      have hp : p.val < 2 ^ 40 := by have := p.isLt; omega
      have := testBit_cost' P (by includes) p.val i (by omega) (by omega)
      rw [invStageFast.c516.lam0.costEq P (by includes)]
      cost_simp
      split_ifs <;> omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, limbs_shift (by omega), limbs_shift (by omega), limbs_shift (by omega)]
  cost_simp
  simp only [Nat.sub_zero] at h0
  omega

/-- **The forward transform by the plan of size `N = 2^j`** (`planFwdC`): at most
`390·N·j + 30·N + 140·j + 60`. -/
theorem planFwdC_cost (hP : Includes P planFwdC.costDeps) {j : ℕ} (hj : j ≤ 40) (c : Array K) :
    machineCost P planFwdC.costIdx [encodeValue (FFT.mkPlan j), encodeValue c] ≤
      390 * (2 ^ j * j) + 30 * 2 ^ j + 140 * j + 60 := by
  rw [planFwdC.costEq P hP, FFT.mkPlan_log]
  have hNle : 2 ^ j ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hj
  have hof := ofFnFrom_cost P (by includes) (n := 2 ^ j) (by omega) _
    (.closure toNovelFastC.lam0.costIdx [encodeValue (FFT.mkPlan j), encodeValue c])
    (fun p ↦ RunsApp.of_spec (by
      have := toNovelFastC.lam0.costSpec P (by includes) (FFT.mkPlan j) c
      rw [FFT.mkPlan_log] at this
      exact this p)) 4
    (fun p ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      have := toNovelFastC.lam0.costEq P (by includes) (FFT.mkPlan j) c
      rw [FFT.mkPlan_log] at this
      rw [this p]) 0 (Nat.zero_le _)
  have hr := rangeLoop_cost P (by includes) j [] (by omega)
  have hf := foldr_cost P (by includes) _
    (.closure planFwdC.lam0.costIdx [encodeValue (FFT.mkPlan j)])
    (fun i b ↦ RunsApp.of_spec (by
      have := planFwdC.lam0.costSpec P (by includes) (FFT.mkPlan j) i b
      rw [FFT.mkPlan_log] at this
      exact this)) (390 * 2 ^ j + 111) (Array.ofFn fun p : Fin (2 ^ j) ↦ c.getD p 0) (List.range j)
    (fun i hi b ↦ by
      have hi := List.mem_range.mp hi
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [planFwdC.lam0.costEq P (by includes), FFT.mkPlan_log]
      have := fwdStage_cost P (by includes) hi hj ((FFT.mkPlan j).twiddles.getD i #[]) b
      omega)
  rw [ofFnFrom_length, limbs_shift (by omega), limbs_of_lt (by omega : j < 2 ^ 64),
    List.length_range] at *
  simp only [Nat.sub_zero] at hof
  have : (390 * 2 ^ j + 111 + 9) * j = 390 * (2 ^ j * j) + 120 * j := by ring
  omega

/-- **The inverse transform by the plan of size `N = 2^j`** (`planInvC`): at most
`330·N·j + 120·j + 40`. -/
theorem planInvC_cost (hP : Includes P planInvC.costDeps) {j : ℕ} (hj : j ≤ 40) (y : Array K) :
    machineCost P planInvC.costIdx [encodeValue (FFT.mkPlan j), encodeValue y] ≤
      330 * (2 ^ j * j) + 120 * j + 40 := by
  rw [planInvC.costEq P hP, FFT.mkPlan_log]
  have hr := rangeLoop_cost P (by includes) j [] (by omega)
  have hf := listFoldl_le P (by includes) _
    (.closure planInvC.lam0.costIdx [encodeValue (FFT.mkPlan j)])
    (fun b i ↦ RunsApp.of_spec (by
      have := planInvC.lam0.costSpec P (by includes) (FFT.mkPlan j) b i
      rw [FFT.mkPlan_log] at this
      exact this)) (330 * 2 ^ j + 91) (fun _ ↦ True) (List.range j) y trivial
    (fun acc _ i hi ↦ ⟨trivial, by
      have hi := List.mem_range.mp hi
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [planInvC.lam0.costEq P (by includes), FFT.mkPlan_log]
      have := invStage_cost P (by includes) hi hj ((FFT.mkPlan j).twiddles.getD i #[]) acc
      omega⟩)
  rw [List.length_range] at hf
  have : (330 * 2 ^ j + 91 + 9) * j = 330 * (2 ^ j * j) + 100 * j := by ring
  omega

end

end LeanVM.Cost.Bounds.PMFFT
