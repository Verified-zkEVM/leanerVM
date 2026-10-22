/-
  LeanerVM.Protocol.ToCompPoly.PlainSum

  The unweighted sum of a function over the cube with its first coordinates fixed: the running
  claim of a plain sumcheck that binds the lowest variable first. Candidate for CompPoly.
-/

module

public import LeanerVM.Protocol.ToCompPoly.PartialSum

/-!
# Plain partial sums over the cube

For a function `g` on `m` coordinates and the first `j` coordinates fixed to `c`,
`plainSum g j c` is `Σ_{x ∈ {0,1}^(m - j)} g(c, x)`. It is the claim a sumcheck on `Σ_x g(x)`
carries after `j` rounds when the rounds bind the lowest variable first and weigh the points
`0` and `1` equally. `PartialSum` has the same for the claim of a sumcheck on `Σ_x eq(r, x) g(x)`.

* `plainSum_zero`: with nothing fixed it is the sum of `g` over the cube;
* `plainSum_split`: fixing one more coordinate splits it into the two sums with that coordinate
  `0` and `1`;
* `plainSum_self`: with everything fixed it is `g c`.

Over an arbitrary commutative ring. Candidate for CompPoly, beside `PartialSum`. Nothing here
transcribes a source.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-- The unweighted partial sum `Σ_x g(c, x)`; zero when more than `m` coordinates are fixed. -/
def plainSum {m : ℕ} (g : Vector R m → R) (j : ℕ) (c : Vector R j) : R :=
  if hj : j ≤ m then ∑ x : Fin (2 ^ (m - j)), g (fixLow hj c (boolVec x)) else 0

omit [CommRing R] in
private theorem fixLow_zero' {m : ℕ} (x : Vector R (m - 0)) :
    fixLow (Nat.zero_le m) (#v[] : Vector R 0) x = x := by
  apply Vector.ext
  intro i hi
  simp [fixLow]

/-- With nothing fixed, the partial sum is the sum over the cube. -/
theorem plainSum_zero {m : ℕ} (g : Vector R m → R) :
    plainSum g 0 #v[] = ∑ x : Fin (2 ^ m), g (boolVec x) := by
  rw [plainSum, dite_eq_left (Nat.zero_le m)]
  simp only [fixLow_zero']
  rfl

omit [CommRing R] in
private theorem fixLow_self' {m : ℕ} (c : Vector R m) (x : Vector R (m - m)) :
    fixLow le_rfl c x = c := by
  apply Vector.ext
  intro i hi
  simp [fixLow, hi]

/-- With everything fixed, the partial sum is the value at the fixed point. -/
theorem plainSum_self {m : ℕ} (g : Vector R m → R) (c : Vector R m) : plainSum g m c = g c := by
  rw [plainSum, dite_eq_left le_rfl]
  have hone : 2 ^ (m - m) = 1 := by simp
  have : Unique (Fin (2 ^ (m - m))) :=
    ⟨⟨⟨0, by omega⟩⟩, fun x ↦ Fin.ext (by have := x.isLt; omega)⟩
  rw [Fintype.sum_unique]
  simp only [fixLow_self']

/-- Extending `c` by `0` and then by `x'` is extending `c` by the point `2x'`. -/
private theorem fixLow_push_zero' {m j : ℕ} (hj : j < m) (c : Vector R j)
    (x' : Fin (2 ^ (m - (j + 1)))) (hb : 2 * x'.val < 2 ^ (m - j)) (z : R) (hz : z = 0) :
    fixLow hj (c.push z) (boolVec x') =
      fixLow hj.le c (boolVec (⟨2 * x'.val, hb⟩ : Fin (2 ^ (m - j)))) := by
  subst hz
  apply Vector.ext
  intro i hi
  simp only [fixLow, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_push, boolVec,
    Vector.getElem_ofFn]
  by_cases h1 : i < j
  · simp [h1, show i < j + 1 by omega]
  · by_cases h2 : i < j + 1
    · have hij : i = j := by omega
      subst hij
      simp [Nat.testBit_zero]
    · have hs : i - j = (i - (j + 1)) + 1 := by omega
      simp only [h1, h2, dite_false, hs, Nat.testBit_succ, Nat.mul_div_cancel_left _ two_pos]

/-- Extending `c` by `1` and then by `x'` is extending `c` by the point `2x' + 1`. -/
private theorem fixLow_push_one' {m j : ℕ} (hj : j < m) (c : Vector R j)
    (x' : Fin (2 ^ (m - (j + 1)))) (hb : 2 * x'.val + 1 < 2 ^ (m - j)) (z : R) (hz : z = 1) :
    fixLow hj (c.push z) (boolVec x') =
      fixLow hj.le c (boolVec (⟨2 * x'.val + 1, hb⟩ : Fin (2 ^ (m - j)))) := by
  subst hz
  apply Vector.ext
  intro i hi
  simp only [fixLow, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_push, boolVec,
    Vector.getElem_ofFn]
  by_cases h1 : i < j
  · simp [h1, show i < j + 1 by omega]
  · by_cases h2 : i < j + 1
    · have hij : i = j := by omega
      subst hij
      simp [Nat.testBit_zero]
    · have hs : i - j = (i - (j + 1)) + 1 := by omega
      simp only [h1, h2, dite_false, hs, Nat.testBit_succ,
        show (2 * x'.val + 1) / 2 = x'.val by omega]

/-- A sum over `2 n` terms is the sum over the pairs of an even and the next odd term. -/
private theorem sum_even_odd {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i =
      ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

/-- Fixing one more coordinate: the partial sum at `j` is the sum of the partial sums at `j + 1`
with the coordinate fixed to `0` and to `1`. -/
theorem plainSum_split {m : ℕ} (g : Vector R m → R) {j : ℕ} (hj : j < m) (c : Vector R j) :
    plainSum g j c = plainSum g (j + 1) (c.push 0) + plainSum g (j + 1) (c.push 1) := by
  have hm : 2 ^ (m - j) = 2 * 2 ^ (m - (j + 1)) := by
    rw [show m - j = (m - (j + 1)) + 1 by omega, pow_succ]; ring
  rw [plainSum, plainSum, plainSum, dite_eq_left hj.le, dite_eq_left (Nat.succ_le_of_lt hj),
    dite_eq_left (Nat.succ_le_of_lt hj)]
  rw [← Finset.sum_add_distrib]
  let G : ℕ → R := fun i ↦
    if h : i < 2 ^ (m - j) then g (fixLow hj.le c (boolVec (⟨i, h⟩ : Fin (2 ^ (m - j))))) else 0
  have h1 : ∑ x : Fin (2 ^ (m - j)), g (fixLow hj.le c (boolVec x)) =
      ∑ i ∈ Finset.range (2 ^ (m - j)), G i := by
    rw [← Fin.sum_univ_eq_sum_range G]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp [G, x.isLt]
  rw [h1, hm, sum_even_odd,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ G (2 * i) + G (2 * i + 1)) (2 ^ (m - (j + 1)))]
  refine Finset.sum_congr rfl fun x' _ ↦ ?_
  have hx := x'.isLt
  rw [fixLow_push_zero' hj c x' (by omega) 0 rfl, fixLow_push_one' hj c x' (by omega) 1 rfl]
  simp only [G, show 2 * x'.val < 2 ^ (m - j) by omega,
    show 2 * x'.val + 1 < 2 ^ (m - j) by omega, dite_true]

end
end LeanerVM.Protocol
