/-
  LeanVM.Guest.B1.Sig.SphincsCompleteConv

  FORS's roots and key in the forms `SphincsSoundFors` computes them (`fRootE` at `key + FORS_TREE`)
  are the statement-shaped cells of `SphincsBridgeCells` (`forsRootCell`), at leanVM 834e6614.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBridgeCells
public import LeanVM.Guest.B1.Sig.SphincsSoundFors

/-!
# FORS's cells, two ways

The FORS block's soundness and completeness compute a tree's nodes at `fAdrE A1 c z s`, `A1` the
key pair's cell plus `FORS_TREE` (`3·2^24`); the statement's bridge reads them at
`forsAdrCell kp c z s`, `adrsCell1 3 kp z (c·2^(10-z) + s >>> z)`. At `A1 = adrsCell1 3 kp 0 0`
they agree (`fAdrE_eq`), so do the roots (`fRootE_eq`) and the FORS key's hash (`forsKey_eq`, its
roots listed over `List.range 24` or `List.ofFn`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **A FORS node's address**, two ways. -/
theorem fAdrE_eq {kp c z s : Nat} (hc : c < 24) (hz : z ≤ 10) (hs : s < 2 ^ 10) :
    fAdrE (adrsCell1 3 kp 0 0) c z s = forsAdrCell kp c z s := by
  have hi := fIdx_lt hc hz hs
  have hh := a1Hi_lt (h := z) (by omega) hi
  rw [fAdrE, forsAdrCell, show c * 2 ^ (10 - z) + s >>> z = fIdx c z s by unfold fIdx; ring,
    ← adrsCell1_add_words23 3 kp z (fIdx c z s)]
  congr 1
  rw [lit, beWordAt_two_of_lt (by omega), beWordAt_three_of_lt_pow16 hi]
  unfold a1Hi at hh ⊢
  congr 1 <;> omega

/-- **A FORS tree's root**, two ways. -/
theorem fRootE_eq (pp a0 : E) {kp c s : Nat} (hc : c < 24) (hs : s < 2 ^ 10) (secret : E)
    (sib : Nat → E) :
    fRootE pp a0 (adrsCell1 3 kp 0 0) c s secret sib = forsRootCell pp a0 kp c s secret sib := by
  unfold fRootE forsRootCell
  rw [show fLeafE pp a0 (adrsCell1 3 kp 0 0) c s secret = forsLeafCell pp a0 kp c s secret by
    rw [fLeafE, forsLeafCell, fAdrE_eq hc (by norm_num) hs]]
  refine pFold_congr _ _ 10 _ fun z hz => funext fun v => ?_
  rw [fNodeE, forsNodeCell, fAdrE_eq hc (by omega) hs]

/-- **The FORS key's hash**, two ways: at the key pair's cell `adrsCell1 0 kp 0 0`, `FORS_TREE` and
`FORS_ROOTS` added. -/
theorem forsKey_eq (pp a0 : E) (kp : Nat) (s : Nat → Nat) (hs : ∀ c < 24, s c < 2 ^ 10)
    (secret : Nat → E) (sib : Nat → Nat → E) :
    (hcell ([pp, a0, adrsCell1 0 kp 0 0 + lit (4 * 2 ^ 24)] ++ (List.range 24).map fun c =>
      fRootE pp a0 (adrsCell1 0 kp 0 0 + lit (3 * 2 ^ 24)) c (s c) (secret c) (sib c))).1 =
    (hcell ([pp, a0, adrsCell1 4 kp 0 0] ++ List.ofFn fun c : Sphincs.ForsTreeIndex =>
      forsRootCell pp a0 kp c.val (s c.val) (secret c.val) (sib c.val))).1 := by
  have e4 : adrsCell1 0 kp 0 0 + lit (4 * 2 ^ 24) = adrsCell1 4 kp 0 0 := by
    rw [lit_of_lt (by norm_num)]; exact adrsCell1_add_type (by norm_num)
  have e3 : adrsCell1 0 kp 0 0 + lit (3 * 2 ^ 24) = adrsCell1 3 kp 0 0 := by
    rw [lit_of_lt (by norm_num)]; exact adrsCell1_add_type (by norm_num)
  have hl : ((List.range 24).map fun c =>
      fRootE pp a0 (adrsCell1 3 kp 0 0) c (s c) (secret c) (sib c)) =
      List.ofFn fun c : Sphincs.ForsTreeIndex =>
        forsRootCell pp a0 kp c.val (s c.val) (secret c.val) (sib c.val) := by
    show ((List.range Sphincs.forsTreeCount).map fun c =>
      fRootE pp a0 (adrsCell1 3 kp 0 0) c (s c) (secret c) (sib c)) = _
    rw [← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
    refine List.map_congr_left fun c _ => ?_
    exact fRootE_eq pp a0 c.isLt (hs c c.isLt) _ _
  rw [e4, e3, hl]

end
end LeanVM.Guest.B1.Sig
