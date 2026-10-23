/-
  LeanVM.Guest.B1.Place.OsInj

  Distinct buffers of one frame have distinct pointers.
-/

module

public import LeanVM.Guest.B1.Place.OsLay
public import LeanVM.Guest.B1.Place.OsPlace

/-!
# Distinct buffers, distinct pointers

`gpow_ne_window`: two exponents less than `2^64 - 1` apart are distinct addresses.
`osPtrAt_inj`: the frame's buffers, all of positive size and in total fewer than `2^64 - 1`
words, have distinct pointers.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

theorem gpow_ne_window {e e' : ℕ} (h : e < e') (h' : e' - e < 2 ^ 64 - 1) : gpow e ≠ gpow e' := by
  intro heq
  have hadd := gpow_add' e (e' - e)
  rw [Nat.add_sub_cancel' h.le, ← heq] at hadd
  have h1 : gpow (e' - e) = gpow 0 := by
    have hne := gpow_ne_zero e
    have : gpow e * gpow (e' - e) = gpow e * 1 := by rw [hadd, mul_one]
    rw [mul_left_cancel₀ hne this]; rfl
  have := gpow_injOn (show e' - e ∈ Set.Iio (2 ^ 64 - 1) from h')
    (show (0 : ℕ) ∈ Set.Iio (2 ^ 64 - 1) by simp) h1
  omega

theorem take_sum_lt {l : List ℕ} {j j' : ℕ} (hjj : j < j') (hj' : j' ≤ l.length)
    (hpos : 0 < l.getD j 0) : (l.take j).sum < (l.take j').sum := by
  have e : l.take j' = l.take (j + 1) ++ (l.drop (j + 1)).take (j' - (j + 1)) := by
    rw [← List.take_add, show j + 1 + (j' - (j + 1)) = j' by omega]
  have hj : j < l.length := by omega
  rw [e, List.sum_append, List.sum_take_succ _ _ hj]
  rw [List.getD_eq_getElem _ _ hj] at hpos
  omega

theorem take_sum_le_sum (l : List ℕ) (j : ℕ) : (l.take j).sum ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop j l]
  rw [List.sum_append]; omega

/-- **The frame's buffers have distinct pointers.** -/
theorem osPtrAt_inj {c : OsCfg} {b j j' : ℕ} (hj : j < (osSizesL c).length)
    (hj' : j' < (osSizesL c).length) (hpos : ∀ x ∈ osSizesL c, 0 < x)
    (htot : (osSizesL c).sum < 2 ^ 64 - 1) (h : osPtrAt c b j = osPtrAt c b j') : j = j' := by
  unfold osPtrAt osBase at h
  rw [os_bases_getD _ _ _ hj, os_bases_getD _ _ _ hj'] at h
  have h' := ofK_injective h
  by_contra hne
  have hp : ∀ i < (osSizesL c).length, 0 < (osSizesL c).getD i 0 := fun i hi ↦ by
    rw [List.getD_eq_getElem _ _ hi]; exact hpos _ (List.getElem_mem hi)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := take_sum_lt hlt hj'.le (hp j hj)
    have h2 := take_sum_le_sum (osSizesL c) j'
    exact gpow_ne_window (e := b + ((osSizesL c).take j).sum) (e' := b + ((osSizesL c).take j').sum)
      (by omega) (by omega) h'
  · have h1 := take_sum_lt hlt hj.le (hp j' hj')
    have h2 := take_sum_le_sum (osSizesL c) j
    exact gpow_ne_window (e := b + ((osSizesL c).take j').sum) (e' := b + ((osSizesL c).take j).sum)
      (by omega) (by omega) h'.symm

end
end LeanVM.Guest.B1
