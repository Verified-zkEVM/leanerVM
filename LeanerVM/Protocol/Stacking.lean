/-
  LeanerVM.Protocol.Stacking

  Aligned stacking of hypercube tables of different heights into one table, and the
  selection identity: evaluating the stack at a point whose high coordinates are a block's
  selector bits evaluates that block. Protocol roadmap Layer 1, generic half.
-/

module

public import LeanerVM.Protocol.Multilinear

/-!
# Aligned stacking

Protocol roadmap Layer 1 (`docs/roadmap/protocol-blueprint.md`, convention *Stacks*): blocks are
ordered largest first, each block sits at an offset that is a multiple of its size, the selector
of block `b` is `offset_b >> κ_b`, and the stack is padded past the last block. Category A:
nothing here transcribes a source; the leanVM stack and leaf layouts are Layer 3's.

Derived from Verified-zkEVM/leanth `leanth-project` at 23929f8c, by Aristotle (Harmonic),
Stefano Rocca and Elias Judin (`docs/roadmap/leanth-reuse.md`): `Blocks` is
`ProofSystem/Stacking.lean:48` (`AlignedLayout`, minus the two unused fields), `offset` its
`offset` (:71), `pow_size_dvd_offset` is `pow_height_dvd_offset` (:388), the window lemmas are
`offset_add_pow_height_le` and `offset_add_pow_height_le_offset` (:397, :409), and `stack_eval`
is `eval_MLE_stack_block` (:603) restated little-endian as on the explore branch
(`Stacking/MLE.lean`, `eval_stackPoly_sel`, by this repository's maintainer). The proof here is
new: it is the generic selection identity `evalMle_append_boolVec` of `Multilinear.lean` applied
to the slice of the stack at the selector index, which alignment identifies with the block.

## Wrong readings excluded

* Alignment is a theorem of the descending order (`pow_size_dvd_offset`), not a hypothesis:
  blocks of sizes 4, 2, 1 in that order are aligned, in any other order they are not
  (acceptance test 15 of the roadmap).
* The pad value is a parameter: the witness stack pads with `0` and the bus trees with `1`
  (acceptance test 2); nothing in `stack_eval` depends on it.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-- Blocks to stack: `n` tables, block `b` on `size b` variables, largest first. -/
structure Blocks (R : Type*) where
  /-- The number of blocks. -/
  n : ℕ
  /-- The number of variables of each block; its height is `2 ^ size b`. -/
  size : Fin n → ℕ
  /-- The tables. -/
  values : (b : Fin n) → CMlPolynomialEval R (size b)
  /-- Largest first. -/
  descending : Antitone size

namespace Blocks

variable (B : Blocks R)

/-! ## Offsets -/

/-- The sum of the heights of the first `k` blocks. -/
def offsetNat (k : ℕ) : ℕ :=
  ∑ c ∈ Finset.range k, if h : c < B.n then 2 ^ B.size ⟨c, h⟩ else 0

/-- The offset of block `b`: the sum of the heights of the blocks before it. -/
def offset (b : Fin B.n) : ℕ := B.offsetNat b.val

/-- The total height of the blocks. -/
def total : ℕ := B.offsetNat B.n

omit [CommRing R] in
theorem offsetNat_succ (k : ℕ) (hk : k < B.n) :
    B.offsetNat (k + 1) = B.offsetNat k + 2 ^ B.size ⟨k, hk⟩ := by
  simp [offsetNat, Finset.sum_range_succ, hk]

omit [CommRing R] in
theorem offsetNat_mono : Monotone B.offsetNat := fun _ _ hab ↦
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

omit [CommRing R] in
/-- Windows of distinct blocks are disjoint and in order. -/
theorem offset_add_pow_le_offset {b c : Fin B.n} (hbc : b < c) :
    B.offset b + 2 ^ B.size b ≤ B.offset c := by
  rw [offset, offset, ← B.offsetNat_succ b.val b.isLt]
  exact B.offsetNat_mono hbc

omit [CommRing R] in
/-- Every window fits below the total. -/
theorem offset_add_pow_le_total (b : Fin B.n) : B.offset b + 2 ^ B.size b ≤ B.total := by
  rw [offset, total, ← B.offsetNat_succ b.val b.isLt]
  exact B.offsetNat_mono b.isLt

omit [CommRing R] in
/-- Alignment: the offset of a block is a multiple of its height, because every earlier block
is at least as large. -/
theorem pow_size_dvd_offset (b : Fin B.n) : 2 ^ B.size b ∣ B.offset b := by
  unfold offset offsetNat
  refine Finset.dvd_sum fun c hc ↦ ?_
  rw [Finset.mem_range] at hc
  have hcn : c < B.n := lt_trans hc b.isLt
  rw [dif_pos hcn]
  exact Nat.pow_dvd_pow 2 (B.descending (Fin.le_def.mpr (Nat.le_of_lt hc)))

/-- Index `x` lies in the window of block `b`. -/
abbrev InWindow (b : Fin B.n) (x : ℕ) : Prop :=
  B.offset b ≤ x ∧ x < B.offset b + 2 ^ B.size b

omit [CommRing R] in
theorem inWindow_unique {b c : Fin B.n} {x : ℕ} (hb : B.InWindow b x) (hc : B.InWindow c x) :
    b = c := by
  rcases lt_trichotomy b c with h | h | h
  · exact absurd (lt_of_lt_of_le hb.2 (B.offset_add_pow_le_offset h)) (not_lt.mpr hc.1)
  · exact h
  · exact absurd (lt_of_lt_of_le hc.2 (B.offset_add_pow_le_offset h)) (not_lt.mpr hb.1)

/-! ## The stack -/

/-- The stack on `μ` variables: block `b`'s entries at its window, `pad` past the total. -/
def stackAt (μ : ℕ) (pad : R) : CMlPolynomialEval R μ :=
  Vector.ofFn fun x ↦
    if B.total ≤ x.val then pad
    else ∑ b : Fin B.n,
      if B.InWindow b x.val then ((B.values b)[x.val - B.offset b]?).getD 0 else 0

theorem stackAt_getElem_of_inWindow {μ : ℕ} (pad : R) {b : Fin B.n} {x : ℕ} (hx : x < 2 ^ μ)
    (h : B.InWindow b x) :
    (B.stackAt μ pad)[x] = (B.values b)[x - B.offset b]'(by have := h.2; omega) := by
  simp only [stackAt, Vector.getElem_ofFn]
  rw [if_neg (by have := B.offset_add_pow_le_total b; omega), Finset.sum_eq_single b]
  · rw [if_pos h, Vector.getElem?_eq_getElem (by have := h.2; omega), Option.getD_some]
  · intro c _ hc
    rw [if_neg fun h' ↦ hc (B.inWindow_unique h' h)]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem stackAt_getElem_of_total_le {μ : ℕ} (pad : R) {x : ℕ} (hx : x < 2 ^ μ)
    (h : B.total ≤ x) : (B.stackAt μ pad)[x] = pad := by
  simp [stackAt, h]

/-! ## Selectors -/

omit [CommRing R] in
/-- Every block fits in a stack of `μ` variables. -/
theorem size_le {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) : B.size b ≤ μ := by
  have h1 : 2 ^ B.size b ≤ 2 ^ μ :=
    le_trans (by have := B.offset_add_pow_le_total b; omega) hμ
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

/-- The selector of block `b` in a stack of `μ` variables: the index `offset_b >> size_b` of
the high `μ - size_b` coordinates. -/
def selector {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) : Fin (2 ^ (μ - B.size b)) :=
  ⟨B.offset b / 2 ^ B.size b, by
    have h1 := B.offset_add_pow_le_total b
    have h2 : B.offset b < 2 ^ B.size b * 2 ^ (μ - B.size b) := by
      rw [← pow_add, Nat.add_sub_cancel' (B.size_le hμ b)]
      have h3 := Nat.two_pow_pos (B.size b)
      omega
    exact Nat.div_lt_of_lt_mul h2⟩

omit [CommRing R] in
@[simp] theorem selector_val {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) :
    (B.selector hμ b).val = B.offset b / 2 ^ B.size b := rfl

/-- The slice of the stack at a block's selector is the block. -/
theorem slice_stackAt {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R) (b : Fin B.n) :
    slice (Vector.cast (congrArg (2 ^ ·) (Nat.add_sub_cancel' (B.size_le hμ b)).symm)
        (B.stackAt μ pad)) (B.selector hμ b) = B.values b := by
  apply Vector.ext
  intro i hi
  rw [slice_getElem_nat _ _ hi]
  simp only [Vector.getElem_cast, selector_val, Nat.mul_div_cancel' (B.pow_size_dvd_offset b)]
  have hx : i + B.offset b < 2 ^ μ := by
    have := B.offset_add_pow_le_total b
    omega
  rw [B.stackAt_getElem_of_inWindow (b := b) pad hx ⟨by omega, by omega⟩]
  simp

/-- The selection identity: the stack, at a point whose low coordinates are `z` and whose high
coordinates are block `b`'s selector bits, evaluates to block `b` at `z`. -/
theorem stack_eval {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R) (b : Fin B.n)
    (z : Vector R (B.size b)) :
    evalMle (B.stackAt μ pad)
      (Vector.cast (Nat.add_sub_cancel' (B.size_le hμ b))
        (z ++ (boolVec (B.selector hμ b) : Vector R (μ - B.size b)))) =
    evalMle (B.values b) z := by
  have hk : B.size b + (μ - B.size b) = μ := Nat.add_sub_cancel' (B.size_le hμ b)
  have hS : B.stackAt μ pad =
      Vector.cast (congrArg (2 ^ ·) hk)
        (Vector.cast (congrArg (2 ^ ·) hk.symm) (B.stackAt μ pad)) := by
    simp
  rw [hS, evalMle_cast hk, evalMle_append_boolVec, slice_stackAt]

end Blocks

end
end LeanerVM.Protocol
