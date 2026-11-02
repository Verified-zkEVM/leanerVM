module

public import LeanVM.Cost.Bounds.PMBasis.Defs
public import Mathlib.Order.MinMax
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# PM-basis's price: the divide-and-conquer recursion, solved

For a price `T` on the recursion's states `x` (fuel, problem, shift) whose maximal order is
`ord x`:

* **`le_pmTree`**: a leaf (maximal order `≤ c` or `≤ 1`) priced at most `L`, an inner node at
  most `N (ord x)` and its two children's prices, the children at the maximal orders
  `ord x / 2` and `ord x − ord x / 2` (exactly), give `T x ≤ pmTree c L N (ord x)`;
* **`pmTree_le_levels`**: for a monotone `N` and `1 ≤ o ≤ 2^K`,
  `pmTree c L N o ≤ pmLevels N K o + L·o` (`o` leaves at most, a level `k` at most
  `2^k·N(⌈o/2^k⌉)`), and **`pmLevels_eq_sum`**: `pmLevels N K o = Σ_{k<K} 2^k·N(⌈o/2^k⌉)`;
* **`pmTreePair_eq`**: `pmTreePair c L N f q = (pmTree c L N q, pmTree c L N (q + 1))` for
  `q + 1 ≤ 2^f` (the evaluation in `f` steps);
* **`le_two_pow_clog2`**, **`two_pow_clog2_le`**: `x ≤ 2^(clog2 x) < 2·x` (`x ≥ 1`).
-/

namespace LeanVM.Cost.Bounds.PMBasis

public section

theorem pmTree_eq (c L : ℕ) (N : ℕ → ℕ) (o : ℕ) :
    pmTree c L N o = if o ≤ c ∨ o ≤ 1 then L
      else N o + pmTree c L N (o / 2) + pmTree c L N (o - o / 2) := by
  rw [pmTree]

theorem pmTree_leaf {c L : ℕ} {N : ℕ → ℕ} {o : ℕ} (h : o ≤ c ∨ o ≤ 1) : pmTree c L N o = L := by
  rw [pmTree_eq]
  split_ifs
  rfl

theorem pmTree_node {c L : ℕ} {N : ℕ → ℕ} {o : ℕ} (hc : c < o) (h1 : 1 < o) :
    pmTree c L N o = N o + pmTree c L N (o / 2) + pmTree c L N (o - o / 2) := by
  rw [pmTree_eq]
  split_ifs with h'
  · omega
  · rfl

/-! ## The recursion's price -/

/-- **The divide-and-conquer price**: on states `x` of an invariant `I`, a leaf (`ord x ≤ c` or
`ord x ≤ 1`) at most `L`; an inner node (`c < ord x`, `1 < ord x`) at most `N (ord x)` and the
prices of two children of `I` at the maximal orders `ord x / 2` and `ord x − ord x / 2`. Then
`T x ≤ pmTree c L N (ord x)`. -/
theorem le_pmTree {α : Type*} (I : α → Prop) (ord T : α → ℕ) (c L : ℕ) (N : ℕ → ℕ)
    (hleaf : ∀ x, I x → (ord x ≤ c ∨ ord x ≤ 1) → T x ≤ L)
    (hnode : ∀ x, I x → c < ord x → 1 < ord x → ∃ y z, I y ∧ I z ∧ ord y = ord x / 2 ∧
      ord z = ord x - ord x / 2 ∧ T x ≤ N (ord x) + T y + T z) :
    ∀ x, I x → T x ≤ pmTree c L N (ord x) := by
  intro x hx
  induction hm : ord x using Nat.strong_induction_on generalizing x with
  | _ o ih =>
    subst hm
    by_cases h : ord x ≤ c ∨ ord x ≤ 1
    · rw [pmTree_leaf h]; exact hleaf x hx h
    · obtain ⟨y, z, hy, hz, hoy, hoz, hT⟩ := hnode x hx (by omega) (by omega)
      rw [pmTree_node (by omega) (by omega)]
      have := ih (ord y) (by omega) y hy rfl
      have := ih (ord z) (by omega) z hz rfl
      rw [hoy] at *; rw [hoz] at *
      omega

/-! ## The closed form by levels -/

theorem pmLevels_mono {N : ℕ → ℕ} (hN : Monotone N) :
    ∀ K {a b : ℕ}, a ≤ b → pmLevels N K a ≤ pmLevels N K b := by
  intro K
  induction K with
  | zero => intro a b _; simp [pmLevels]
  | succ K ih =>
    intro a b hab
    simp only [pmLevels]
    have := hN hab
    have := ih (show (a + 1) / 2 ≤ (b + 1) / 2 by omega)
    omega

/-- **The per-level closed form**: for a monotone node price and `1 ≤ o ≤ 2^K` (`K` levels),
`pmTree c L N o ≤ pmLevels N K o + L·o`: at most `o` leaves, and level `k` at most `2^k` nodes of
maximal order at most `⌈o/2^k⌉`. -/
theorem pmTree_le_levels (c L : ℕ) {N : ℕ → ℕ} (hN : Monotone N) :
    ∀ K o, 1 ≤ o → o ≤ 2 ^ K → pmTree c L N o ≤ pmLevels N K o + L * o := by
  intro K
  induction K with
  | zero =>
    intro o h1 hK
    rw [pmTree_leaf (by simp at hK; omega)]
    simp [pmLevels]; nlinarith
  | succ K ih =>
    intro o h1 hK
    by_cases h : o ≤ c ∨ o ≤ 1
    · rw [pmTree_leaf h]; nlinarith
    · rw [pmTree_node (by omega) (by omega)]
      have hp : 2 ^ (K + 1) = 2 * 2 ^ K := by ring
      have e : o - o / 2 = (o + 1) / 2 := by omega
      rw [e]
      have h2 := ih (o / 2) (by omega) (by omega)
      have h3 := ih ((o + 1) / 2) (by omega) (by omega)
      have h4 := pmLevels_mono hN K (show o / 2 ≤ (o + 1) / 2 by omega)
      have h5 : L * (o / 2) + L * ((o + 1) / 2) = L * o := by
        rw [← Nat.mul_add]; congr 1; omega
      simp only [pmLevels]
      omega

theorem ceil_half_div (o P : ℕ) (hP : 0 < P) :
    ((o + 1) / 2 + P - 1) / P = (o + 2 * P - 1) / (2 * P) := by
  rw [← Nat.div_div_eq_div_mul]
  congr 1
  omega

/-- **`pmLevels` as a sum**: `Σ_{k<K} 2^k·N(⌈o/2^k⌉)`. -/
theorem pmLevels_eq_sum (N : ℕ → ℕ) :
    ∀ K o, pmLevels N K o =
      ∑ k ∈ Finset.range K, 2 ^ k * N ((o + 2 ^ k - 1) / 2 ^ k) := by
  intro K
  induction K with
  | zero => intro o; simp [pmLevels]
  | succ K ih =>
    intro o
    rw [Finset.sum_range_succ', pmLevels, ih, Finset.mul_sum]
    simp only [pow_zero, one_mul, Nat.add_sub_cancel, Nat.div_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [ceil_half_div o (2 ^ k) (Nat.two_pow_pos k), pow_succ]
    ring_nf

/-! ## The evaluation in `log₂ o` steps -/

theorem pmTreeStep_eq (c L : ℕ) (N : ℕ → ℕ) (h x : ℕ) (hx : x / 2 = h ∨ x / 2 = h + 1)
    (hx' : x - x / 2 = h ∨ x - x / 2 = h + 1) :
    pmTreeStep c L N h (pmTree c L N h) (pmTree c L N (h + 1)) x = pmTree c L N x := by
  have sel : ∀ y, (y = h ∨ y = h + 1) →
      (if y = h then pmTree c L N h else pmTree c L N (h + 1)) = pmTree c L N y := by
    intro y hy
    rcases hy with rfl | rfl
    · simp
    · simp
  unfold pmTreeStep
  rw [pmTree_eq c L N x, sel _ hx, sel _ hx']

/-- **The evaluation**: `pmTreePair c L N f q = (pmTree c L N q, pmTree c L N (q + 1))` when
`q + 1 ≤ 2^f`. -/
theorem pmTreePair_eq (c L : ℕ) (N : ℕ → ℕ) :
    ∀ f q, q + 1 ≤ 2 ^ f → pmTreePair c L N f q = (pmTree c L N q, pmTree c L N (q + 1)) := by
  intro f
  induction f with
  | zero =>
    intro q hq
    simp at hq
    subst hq
    simp only [pmTreePair, pmTree_leaf (show (0 : ℕ) ≤ c ∨ 0 ≤ 1 by omega),
      pmTree_leaf (show (0 + 1 : ℕ) ≤ c ∨ 0 + 1 ≤ 1 by omega)]
  | succ f ih =>
    intro q hq
    have hp : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
    rw [pmTreePair, ih (q / 2) (by omega)]
    simp only
    rw [pmTreeStep_eq c L N _ q (by omega) (by omega),
      pmTreeStep_eq c L N _ (q + 1) (by omega) (by omega)]

/-! ## `clog2` -/

theorem le_two_pow_clog2Aux : ∀ f x, x ≤ 2 ^ f → x ≤ 2 ^ clog2Aux f x := by
  intro f
  induction f with
  | zero => intro x hx; simpa [clog2Aux] using hx
  | succ f ih =>
    intro x hx
    unfold clog2Aux
    split_ifs with h
    · simp; omega
    · have hp : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
      have := ih ((x + 1) / 2) (by omega)
      rw [pow_succ]
      omega

theorem two_pow_clog2Aux_le : ∀ f x, 1 ≤ x → 2 ^ clog2Aux f x + 1 ≤ 2 * x := by
  intro f
  induction f with
  | zero => intro x hx; simp [clog2Aux]; omega
  | succ f ih =>
    intro x hx
    unfold clog2Aux
    split_ifs with h
    · simp; omega
    · have := ih ((x + 1) / 2) (by omega)
      generalize clog2Aux f ((x + 1) / 2) = e at this ⊢
      rcases e with _ | e
      · simp; omega
      · rw [pow_succ, pow_succ] at *
        omega

theorem le_two_pow_clog2 (x : ℕ) : x ≤ 2 ^ clog2 x :=
  le_two_pow_clog2Aux x x (Nat.lt_two_pow_self).le

theorem two_pow_clog2_le {x : ℕ} (hx : 1 ≤ x) : 2 ^ clog2 x < 2 * x := by
  have := two_pow_clog2Aux_le x x hx
  unfold clog2
  omega

end

end LeanVM.Cost.Bounds.PMBasis
