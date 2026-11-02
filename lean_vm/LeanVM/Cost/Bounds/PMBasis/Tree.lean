module

public import LeanVM.Cost.Bounds.PMBasis.Defs
public import Mathlib.Order.MinMax
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr

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
* **`pmTree_mono`**: monotone in the order for a monotone `N`;
* **`pmTreePair_eq`**: `pmTreePair c L N f q = (pmTree c L N q, pmTree c L N (q + 1))` for
  `q + 1 ≤ 2^f` (the evaluation in `f` steps);
* **`le_two_pow_clog2`**, **`clog2_le`**, **`two_pow_clog2_lt`**: `clog2 e` is the least `j` with
  `e ≤ 2^j`, and `2^(clog2 e) < 2·e` (`e ≥ 1`); `clog2_mono`.
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

theorem le_two_pow_clog2Loop (e : ℕ) :
    ∀ fuel j, e ≤ j + fuel → e ≤ 2 ^ clog2Loop e fuel j
  | 0, j, h => by
    rw [clog2Loop]
    exact (Nat.le_of_lt_succ (by omega : e < j + 1)).trans (Nat.lt_two_pow_self).le
  | fuel + 1, j, h => by
    rw [clog2Loop]
    split
    · assumption
    · exact le_two_pow_clog2Loop e fuel (j + 1) (by omega)

theorem le_two_pow_clog2 (e : ℕ) : e ≤ 2 ^ clog2 e :=
  le_two_pow_clog2Loop e e 0 (by omega)

theorem clog2Loop_le (e : ℕ) {j : ℕ} (hj : e ≤ 2 ^ j) :
    ∀ fuel j₀, j₀ ≤ j → clog2Loop e fuel j₀ ≤ j
  | 0, _, h => h
  | fuel + 1, j₀, h => by
    rw [clog2Loop]
    split
    · exact h
    · rename_i hlt
      have : j₀ < j := by
        by_contra hc
        exact hlt (hj.trans (Nat.pow_le_pow_right (by omega) (by omega)))
      exact clog2Loop_le e hj fuel (j₀ + 1) this

/-- `clog2 e` is the least: `e ≤ 2^j` gives `clog2 e ≤ j`. -/
theorem clog2_le {e j : ℕ} (hj : e ≤ 2 ^ j) : clog2 e ≤ j :=
  clog2Loop_le e hj e 0 (Nat.zero_le _)

theorem clog2_mono {a b : ℕ} (h : a ≤ b) : clog2 a ≤ clog2 b :=
  clog2_le (h.trans (le_two_pow_clog2 b))

/-- The transform size is below twice the degree bound: `2^clog2 e < 2·e` (`e ≥ 1`). -/
theorem two_pow_clog2_lt {e : ℕ} (he : 1 ≤ e) : 2 ^ clog2 e < 2 * e := by
  rcases Nat.eq_zero_or_pos (clog2 e) with h0 | hpos
  · rw [h0]; omega
  · obtain ⟨k, hk⟩ : ∃ k, clog2 e = k + 1 := ⟨clog2 e - 1, by omega⟩
    have : ¬ e ≤ 2 ^ k := fun h ↦ by have := clog2_le h; omega
    rw [hk, pow_succ]
    omega

/-- **`pmTreeEval` is `pmTree`.** -/
theorem pmTreeEval_eq (c L : ℕ) (N : ℕ → ℕ) (o : ℕ) : pmTreeEval c L N o = pmTree c L N o := by
  rw [pmTreeEval, pmTreePair_eq c L N _ o (le_two_pow_clog2 (o + 1))]

/-! ## Monotone in the order -/

theorem le_pmTree_self (c L : ℕ) (N : ℕ → ℕ) (o : ℕ) : L ≤ pmTree c L N o := by
  rcases Nat.lt_or_ge 1 o with h1 | h1
  · by_cases hc : o ≤ c
    · rw [pmTree_leaf (Or.inl hc)]
    · rw [pmTree_node (by omega) h1]
      have := le_pmTree_self c L N (o - o / 2)
      omega
  · rw [pmTree_leaf (Or.inr h1)]
termination_by o
decreasing_by omega

/-- **`pmTree` is monotone in the order** for a monotone node price. -/
theorem pmTree_mono (c L : ℕ) {N : ℕ → ℕ} (hN : Monotone N) :
    ∀ b a, a ≤ b → pmTree c L N a ≤ pmTree c L N b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hab
    by_cases ha : a ≤ c ∨ a ≤ 1
    · rw [pmTree_leaf ha]; exact le_pmTree_self c L N b
    · rw [pmTree_node (c := c) (L := L) (N := N) (o := a) (by omega) (by omega),
        pmTree_node (c := c) (L := L) (N := N) (o := b) (by omega) (by omega)]
      have := hN hab
      have := ih (b / 2) (by omega) (a / 2) (by omega)
      have := ih (b - b / 2) (by omega) (a - a / 2) (by omega)
      omega

/-- **`pmTree` is monotone in the leaf price.** -/
theorem pmTree_mono_leaf (c : ℕ) {L L' : ℕ} (N : ℕ → ℕ) (hL : L ≤ L') :
    ∀ o, pmTree c L N o ≤ pmTree c L' N o := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
    by_cases h : o ≤ c ∨ o ≤ 1
    · rw [pmTree_leaf h, pmTree_leaf h]; exact hL
    · rw [pmTree_node (L := L) (by omega) (by omega), pmTree_node (L := L') (by omega) (by omega)]
      have := ih (o / 2) (by omega)
      have := ih (o - o / 2) (by omega)
      omega

/-! ## The model is monotone -/

theorem fwdPrice_mono (p : PMPrices) {j j' : ℕ} (h : j ≤ j') : fwdPrice p j ≤ fwdPrice p j' := by
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
  unfold fwdPrice; gcongr

theorem invPrice_mono (p : PMPrices) {j j' : ℕ} (h : j ≤ j') : invPrice p j ≤ invPrice p j' := by
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
  unfold invPrice; gcongr

/-- A product of larger degrees costs no less (its transform size `clog2` is monotone). -/
theorem evalMatPrice_mono (p : PMPrices) (R S T : ℕ) {dA dB dA' dB' : ℕ} (hA : dA ≤ dA')
    (hB : dB ≤ dB') : evalMatPrice p R S T dA dB ≤ evalMatPrice p R S T dA' dB' := by
  have hj := clog2_mono (show dA + dB + 1 ≤ dA' + dB' + 1 by omega)
  have := fwdPrice_mono p hj
  have := invPrice_mono p hj
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj
  unfold evalMatPrice; gcongr

/-- **The model's node price is monotone in the order**, so `pmTree_le_levels` applies to it. -/
theorem pmNodePrice_mono (p : PMPrices) (r m : ℕ) : Monotone (pmNodePrice p r m) := by
  intro a b h
  have := evalMatPrice_mono p r r r (show a - a / 2 ≤ b - b / 2 by omega)
    (show a / 2 ≤ b / 2 by omega)
  have := evalMatPrice_mono p r r m (show a / 2 ≤ b / 2 by omega) (show a - 1 ≤ b - 1 by omega)
  unfold pmNodePrice; gcongr

end

end LeanVM.Cost.Bounds.PMBasis
