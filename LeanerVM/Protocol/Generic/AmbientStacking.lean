/-
Copyright (c) 2026 leanerVM Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic)

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
-/

/-
  LeanerVM.Protocol.Generic.AmbientStacking

  Ambient evaluation of aligned stacks with arbitrary padding.
-/

module

public import LeanerVM.Protocol.Stacking

/-!
# Ambient stack evaluation

The ambient evaluation is the sum of the selected block evaluations plus the uncovered
padding weight. The pad is arbitrary: witness stacks use zero and product trees use one.
The proof works over a commutative ring, including characteristic two.

Category A: the leaf decomposition in leanVM specification §5.4, equation (5.4)
(`doc/leanvm/body/05-arithmetization.tex:97-109`) at
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. The source's pad-one formula is the
characteristic-two instance of the arbitrary-pad identity below. The pinned
`crates/lean_vm/src/leaf.rs:400-460` and `python-verifier/verifier.py:578-590`
include the same uncovered padding weight.

Derived from Verified-zkEVM/leanth at 23929f8c922cd4461ab22dbfaa6520f3ad23a3b2,
`Leanth/LeanVM/Protocol.lean:9818-9850` (`eval_MLE_stack_ambient`), by Aristotle (Harmonic),
Stefano Rocca and Elias Judin. The zero-padding source statement is extended to arbitrary
padding and coefficient maps using the current little-endian cube split. The named consumer
is protocol-blueprint Layer 6's `leaf_decomposition`, following Layer 5's product trees.

Upstream ownership: [ArkLib #900](https://github.com/Verified-zkEVM/ArkLib/issues/900).
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

omit [CommRing R] in
/-- Place a table at one high-coordinate selector and fill the other slices with zero. -/
def placeSlice [Zero R] {k m : ℕ} (t : CMlPolynomialEval R k) (j : Fin (2 ^ m)) :
    CMlPolynomialEval R (k + m) :=
  Vector.ofFn fun x ↦ if x.val / 2 ^ k = j.val then
    t[x.val % 2 ^ k]'(Nat.mod_lt _ (Nat.two_pow_pos k)) else 0

omit [CommRing R] in
/-- Slicing a placed table gives the table at its selector and zero at every other selector. -/
theorem slice_placeSlice [Zero R] {k m : ℕ} (t : CMlPolynomialEval R k) (j h : Fin (2 ^ m)) :
    slice (placeSlice t j) h = if h = j then t else Vector.replicate (2 ^ k) 0 := by
  apply Vector.ext
  intro i hi
  have hdiv := cubeIndex_div (⟨i, hi⟩ : Fin (2 ^ k)) h
  simp only [cubeIndex_val] at hdiv
  by_cases hh : h = j
  · subst h
    simp [slice, placeSlice, hdiv, Nat.mod_eq_of_lt hi]
  · have hn : h.val ≠ j.val := fun he ↦ hh (Fin.ext he)
    simp [slice, placeSlice, hdiv, hh, hn]

/-- Placing a table multiplies its extension by the selector's high-coordinate weight. -/
theorem evalMle_placeSlice {k m : ℕ} (t : CMlPolynomialEval R k) (j : Fin (2 ^ m))
    (z : Vector R k) (s : Vector R m) :
    evalMle (placeSlice t j) (z ++ s) = (eqTable s)[j] * evalMle t z := by
  rw [evalMle_split, Finset.sum_eq_single j]
  · simp [slice_placeSlice]
  · intro h _ hh
    simp [slice_placeSlice, hh, evalMle_replicate_zero]
  · simp

private theorem evalMle_const_aux {n : ℕ} (a : R) (z : Vector R n) :
    evalMle (Vector.replicate (2 ^ n) a) z = a := by
  rw [evalMle_eq_sum]
  simp only [Fin.getElem_fin, Vector.getElem_replicate]
  rw [← Finset.mul_sum]
  have hs := sumCube_eqTable z
  change (∑ i : Fin (2 ^ n), (lagrangeBasis z)[i]) = 1 at hs
  simp only [Fin.getElem_fin] at hs
  rw [hs, mul_one]

private theorem evalMle_sub_const_aux {n : ℕ} (t : CMlPolynomialEval R n) (a : R)
    (z : Vector R n) :
    evalMle (Vector.map (fun x ↦ x - a) t) z = evalMle t z - a := by
  rw [evalMle_eq_sum]
  simp only [Fin.getElem_fin, Vector.getElem_map, sub_mul, Finset.sum_sub_distrib]
  have hc : (∑ i : Fin (2 ^ n), a * (lagrangeBasis z)[i.val]) = a := by
    simpa only [evalMle_eq_sum, Fin.getElem_fin, Vector.getElem_replicate] using evalMle_const_aux a z
  rw [hc]
  congr 1
  exact (evalMle_eq_sum t z).symm

namespace Blocks

variable (B : Blocks R)

omit [CommRing R] in
/-- Every index below the total belongs to a block window: there are no internal gaps. -/
theorem exists_inWindow {x : ℕ} (hx : x < B.total) : ∃ b, B.InWindow b x := by
  by_contra h
  have hno : ∀ b : Fin B.n, ¬ B.InWindow b x := by simpa using h
  have hprefix : ∀ k, k ≤ B.n → B.offsetNat k ≤ x := by
    intro k hk
    induction k with
    | zero => simp [offsetNat]
    | succ k ih =>
      have hk' : k < B.n := by omega
      have hp := ih (by omega)
      rw [B.offsetNat_succ k hk']
      have hn := hno ⟨k, hk'⟩
      change ¬ (B.offsetNat k ≤ x ∧ x < B.offsetNat k + 2 ^ B.size ⟨k, hk'⟩) at hn
      omega
  have := hprefix B.n le_rfl
  exact (not_lt_of_ge this) hx

omit [CommRing R] in
/-- Alignment identifies window membership with the quotient selecting the high slice. -/
theorem inWindow_iff_div (b : Fin B.n) (x : ℕ) :
    B.InWindow b x ↔ x / 2 ^ B.size b = B.offset b / 2 ^ B.size b := by
  have ha := Nat.mul_div_cancel' (B.pow_size_dvd_offset b)
  rw [Nat.div_eq_iff (Nat.two_pow_pos (B.size b))]
  rw [Nat.mul_comm (B.offset b / 2 ^ B.size b), ha]
  have hp := Nat.two_pow_pos (B.size b)
  change (B.offset b ≤ x ∧ x < B.offset b + 2 ^ B.size b) ↔ _
  omega

/-- Read the low coordinates for block `b` from an ambient point. -/
def lowPoint {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (z : Vector R μ) :
    Vector R (B.size b) :=
  lowVec (Vector.cast (Nat.add_sub_cancel' (B.size_le hμ b)).symm z)

/-- Read the high coordinates on which block `b`'s selector is tested. -/
def highPoint {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (z : Vector R μ) :
    Vector R (μ - B.size b) :=
  highVec (Vector.cast (Nat.add_sub_cancel' (B.size_le hμ b)).symm z)

/-- The ambient equality-selector weight of one block. -/
def selectorWeight {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (z : Vector R μ) : R :=
  (eqTable (B.highPoint hμ b z))[B.selector hμ b]

omit [CommRing R] in
/-- Place arbitrary values in a block's window and zero outside it. -/
def windowTable [Zero R] {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (t : CMlPolynomialEval R (B.size b)) : CMlPolynomialEval R μ :=
  Vector.cast (congrArg (2 ^ ·) (Nat.add_sub_cancel' (B.size_le hμ b)))
    (placeSlice t (B.selector hμ b))

omit [CommRing R] in
/-- A window table reads the local value inside its window and vanishes outside it. -/
theorem windowTable_getElem [Zero R] {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (t : CMlPolynomialEval R (B.size b)) (x : Fin (2 ^ μ)) :
    (B.windowTable hμ b t)[x] = if h : B.InWindow b x.val then
      t[x.val - B.offset b]'(by have := h.2; omega) else 0 := by
  simp only [windowTable, Fin.getElem_fin, Vector.getElem_cast, placeSlice,
    Vector.getElem_ofFn, selector_val]
  by_cases hx : B.InWindow b x.val
  · have hd := (B.inWindow_iff_div b x.val).mp hx
    have hm := Nat.mod_add_div x.val (2 ^ B.size b)
    rw [hd, Nat.mul_div_cancel' (B.pow_size_dvd_offset b)] at hm
    have he : x.val % 2 ^ B.size b = x.val - B.offset b := by omega
    simp [hx, hd, he]
  · simp [hx, (B.inWindow_iff_div b x.val).not.mp hx]

/-- A block contribution evaluates to its local extension times its selector weight. -/
theorem evalMle_windowTable {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (t : CMlPolynomialEval R (B.size b)) (z : Vector R μ) :
    evalMle (B.windowTable hμ b t) z =
      B.selectorWeight hμ b z * evalMle t (B.lowPoint hμ b z) := by
  have hz : z = Vector.cast (Nat.add_sub_cancel' (B.size_le hμ b))
      (B.lowPoint hμ b z ++ B.highPoint hμ b z) := by
    apply Vector.ext
    intro i hi
    simp only [lowPoint, highPoint, lowVec, highVec, Vector.getElem_cast]
    rw [Vector.getElem_append]
    split
    · simp_all
    · simp only [Vector.getElem_ofFn]
      congr 1
      omega
  conv_lhs => rw [hz]
  rw [windowTable, evalMle_cast, evalMle_placeSlice]
  rfl

/-- Subtract the padding on each occupied window, then add the constant padding everywhere. -/
theorem stackAt_decomposition {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R) :
    B.stackAt μ pad = Vector.ofFn (fun x ↦ pad +
      ∑ b : Fin B.n, (B.windowTable hμ b (Vector.map (fun v ↦ v - pad) (B.values b)))[x]) := by
  apply Vector.ext
  intro x hx
  simp only [Vector.getElem_ofFn]
  by_cases hp : B.total ≤ x
  · rw [B.stackAt_getElem_of_total_le pad hx hp]
    have hn : ∀ b : Fin B.n, ¬ B.InWindow b x := by
      intro b hb
      have := B.offset_add_pow_le_total b
      omega
    simp [B.windowTable_getElem, hn]
  · obtain ⟨b, hb⟩ := B.exists_inWindow (Nat.lt_of_not_ge hp)
    rw [B.stackAt_getElem_of_inWindow (b := b) pad hx hb, Finset.sum_eq_single b]
    · rw [B.windowTable_getElem, dif_pos hb]
      simp
    · intro c _ hc
      rw [B.windowTable_getElem, dif_neg (fun hh ↦ hc (B.inWindow_unique hh hb))]
    · simp

/-- Ambient evaluation includes the entire uncovered padding weight. -/
theorem stack_eval_ambient {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R) (z : Vector R μ) :
    evalMle (B.stackAt μ pad) z =
      (∑ b : Fin B.n, B.selectorWeight hμ b z * evalMle (B.values b) (B.lowPoint hμ b z)) +
        pad * (1 - ∑ b : Fin B.n, B.selectorWeight hμ b z) := by
  rw [B.stackAt_decomposition hμ pad, evalMle_eq_sum]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hc : (∑ i : Fin (2 ^ μ), pad * (lagrangeBasis z)[i.val]) = pad := by
    simpa only [evalMle_eq_sum, Fin.getElem_fin, Vector.getElem_replicate] using evalMle_const_aux pad z
  rw [hc]
  have ht (b : Fin B.n) :
      (∑ i : Fin (2 ^ μ), (B.windowTable hμ b (Vector.map (fun v ↦ v - pad) (B.values b)))[i.val] *
        (lagrangeBasis z)[i.val]) =
        B.selectorWeight hμ b z * (evalMle (B.values b) (B.lowPoint hμ b z) - pad) := by
    simpa only [evalMle_eq_sum, Fin.getElem_fin] using
      (B.evalMle_windowTable hμ b (Vector.map (fun v ↦ v - pad) (B.values b)) z).trans
        (congrArg (B.selectorWeight hμ b z * ·)
          (evalMle_sub_const_aux (B.values b) pad (B.lowPoint hμ b z)))
  simp_rw [ht, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  ring

/-- Witness stacks have no padding contribution. -/
theorem stack_eval_ambient_zero {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (z : Vector R μ) :
    evalMle (B.stackAt μ 0) z =
      ∑ b : Fin B.n, B.selectorWeight hμ b z * evalMle (B.values b) (B.lowPoint hμ b z) := by
  simpa using B.stack_eval_ambient hμ 0 z

/-- Product-tree stacks retain the uncovered selector weight. -/
theorem stack_eval_ambient_one {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (z : Vector R μ) :
    evalMle (B.stackAt μ 1) z =
      (∑ b : Fin B.n, B.selectorWeight hμ b z * evalMle (B.values b) (B.lowPoint hμ b z)) +
        (1 - ∑ b : Fin B.n, B.selectorWeight hμ b z) := by
  simpa using B.stack_eval_ambient hμ 1 z

/-- A fully occupied table is independent of its unused padding parameter. -/
theorem stackAt_eq_of_total_eq {μ : ℕ} (h : B.total = 2 ^ μ) (pad pad' : R) :
    B.stackAt μ pad = B.stackAt μ pad' := by
  apply Vector.ext
  intro i hi
  simp [stackAt, h, Nat.not_le.mpr hi]

/-- Fully packed layouts have selector weights summing to one at every ambient point. -/
theorem sum_selectorWeight_of_total_eq {μ : ℕ} (h : B.total = 2 ^ μ) (z : Vector R μ) :
    (∑ b : Fin B.n, B.selectorWeight h.le b z) = 1 := by
  have hz := B.stack_eval_ambient_zero h.le z
  have ho := B.stack_eval_ambient_one h.le z
  rw [← B.stackAt_eq_of_total_eq h 0 1, hz] at ho
  have hc : 0 = 1 - ∑ b : Fin B.n, B.selectorWeight h.le b z :=
    add_left_cancel (by simpa only [add_zero] using ho)
  exact (sub_eq_zero.mp hc.symm).symm

/-- The ambient formula after mapping coefficients to a possibly larger ring. -/
theorem stack_eval₂_ambient {S : Type*} [CommRing S] (φ : R →+* S) {μ : ℕ}
    (hμ : B.total ≤ 2 ^ μ) (pad : R) (z : Vector S μ) :
    eval₂Mle (B.stackAt μ pad) φ z =
      (∑ b : Fin B.n, (B.map φ).selectorWeight hμ b z *
        eval₂Mle (B.values b) φ ((B.map φ).lowPoint hμ b z)) +
      φ pad * (1 - ∑ b : Fin B.n, (B.map φ).selectorWeight hμ b z) := by
  rw [eval₂Mle, B.map_stackAt]
  exact (B.map φ).stack_eval_ambient hμ (φ pad) z

end Blocks

end
end LeanerVM.Protocol
