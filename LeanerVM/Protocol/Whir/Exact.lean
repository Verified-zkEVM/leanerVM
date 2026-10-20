/-
  LeanerVM.Protocol.Whir.Exact

  The interfaces of the soundness proof at exact agreement: the list bound and mutual correlated
  agreement hold with `L = 1` and `N = 1`.
-/

module

public import LeanerVM.Protocol.Whir.Lanes

/-!
# The interfaces at exact agreement

`ListBound` and `McaBound` (`LeanerVM.Protocol.Whir.Lanes`) are the two theorems of
coding theory the soundness of WHIR's opening consumes, per level, as parameters. They are not
vacuous: at the threshold `a = 2 ^ (κ + R)`, agreement on every position (radius `γ = 0`), both
hold with the constants `1`, from the encoder alone.

* `listBound_exact`: a word is exactly the codeword of at most one interleaved codeword: the
  encoder is injective on every lane;
* `mcaBound_exact`: for a two-lane word at most one fold `c` makes the fold a codeword while the
  lanes are not: two such folds `c₁ ≠ c₂` give two codewords from which both lanes are recovered
  by linear combination.

With them the opening's soundness theorem applies at the extreme parameters of the unique-decoding
regime; the Johnson-bound regime is the coding theory's.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

namespace Whir

/-- Agreement on `2 ^ b` positions out of `2 ^ b` is agreement on all of them. -/
private theorem eq_univ_of_card_ge {b : ℕ} {A : Finset (Fin (2 ^ b))} (h : 2 ^ b ≤ A.card) :
    A = Finset.univ := by
  have h1 : A.card ≤ Fintype.card (Fin (2 ^ b)) := Finset.card_le_univ A
  have h2 : Fintype.card (Fin (2 ^ b)) = 2 ^ b := Fintype.card_fin _
  exact Finset.eq_univ_of_card A (by omega)

/-- **The list bound at exact agreement.** A word has at most one interleaved codeword that agrees
with it everywhere. -/
theorem listBound_exact {κ R : ℕ} (m : ℕ) (hb : κ + R ≤ 64) :
    ListBound κ R (2 ^ (κ + R)) m 1 := by
  intro F
  refine Finite.card_le_one_iff_subsingleton.mpr ?_
  refine ⟨fun V V' ↦ Subtype.ext (funext fun u ↦ ?_)⟩
  have hV := eq_univ_of_card_ge V.2
  have hV' := eq_univ_of_card_ge V'.2
  refine encode_injective (algebraMap K E) (by omega) (algebraMap K E).injective (R := R)
    (funext fun y ↦ ?_)
  have h1 := (Finset.mem_filter.mp (Finset.eq_univ_iff_forall.mp hV y)).2 u
  have h2 := (Finset.mem_filter.mp (Finset.eq_univ_iff_forall.mp hV' y)).2 u
  exact h1.trans h2.symm

/-- **The list bound at unique decoding.** If the threshold is more than half of the sum of the
positions and the message length, `2 a ≥ 2 ^ κ + 2 ^ (κ + R)`, a word has at most one interleaved
codeword within it: two such codewords agree with each other on at least `2 a - 2 ^ (κ + R) ≥ 2 ^ κ`
positions, hence are equal. This is a list bound below exact agreement. -/
theorem listBound_unique {κ R : ℕ} (m : ℕ) (hb : κ + R ≤ 64) {a : ℕ}
    (ha : 2 ^ κ + 2 ^ (κ + R) ≤ 2 * a) : ListBound κ R a m 1 := by
  classical
  intro F
  refine Finite.card_le_one_iff_subsingleton.mpr ?_
  refine ⟨fun V V' ↦ Subtype.ext (funext fun u ↦ ?_)⟩
  set A := Finset.univ.filter fun y : Fin (2 ^ (κ + R)) ↦
    ∀ u : Fin (2 ^ m), encode (algebraMap K E) κ R (V.1 u) y = F y u with hA
  set A' := Finset.univ.filter fun y : Fin (2 ^ (κ + R)) ↦
    ∀ u : Fin (2 ^ m), encode (algebraMap K E) κ R (V'.1 u) y = F y u with hA'
  have h1 : a ≤ A.card := V.2
  have h2 : a ≤ A'.card := V'.2
  have hn : (A ∪ A').card ≤ 2 ^ (κ + R) := by
    have := Finset.card_le_univ (A ∪ A')
    rwa [Fintype.card_fin] at this
  have hinter : 2 ^ κ ≤ (A ∩ A').card := by
    have := Finset.card_union_add_card_inter A A'
    omega
  exact encode_eq_of_agree (algebraMap K E) hb (algebraMap K E).injective (A ∩ A') hinter
    fun y hy ↦ by
      have e1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).1).2 u
      have e2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2 u
      exact e1.trans e2.symm

/-- **Mutual correlated agreement at exact agreement.** For a two-lane word at most one fold is
bad: two folds `c₁ ≠ c₂` that are codewords give both lanes as codewords. -/
theorem mcaBound_exact {κ R : ℕ} : McaBound κ R (2 ^ (κ + R)) 1 := by
  intro F
  refine Finite.card_le_one_iff_subsingleton.mpr ?_
  refine ⟨fun c₁ c₂ ↦ Subtype.ext ?_⟩
  by_contra hne
  obtain ⟨A₁, hA₁, ⟨w₁, hw₁⟩, hn₁⟩ := c₁.2
  obtain ⟨A₂, hA₂, ⟨w₂, hw₂⟩, -⟩ := c₂.2
  have e₁ := eq_univ_of_card_ge hA₁
  have e₂ := eq_univ_of_card_ge hA₂
  have hd : c₂.1 - c₁.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  refine hn₁ ⟨comb (c₂.1 / (c₂.1 - c₁.1)) (-c₁.1 / (c₂.1 - c₁.1)) w₁ w₂,
    comb (-(1 - c₂.1) / (c₂.1 - c₁.1)) ((1 - c₁.1) / (c₂.1 - c₁.1)) w₁ w₂, fun y hy ↦ ?_⟩
  have h1 := hw₁ y (Finset.eq_univ_iff_forall.mp e₁ y)
  have h2 := hw₂ y (Finset.eq_univ_iff_forall.mp e₂ y)
  rw [encode_comb, encode_comb, h1, h2]
  constructor <;> field_simp <;> ring

end Whir

end

end LeanerVM.Protocol
