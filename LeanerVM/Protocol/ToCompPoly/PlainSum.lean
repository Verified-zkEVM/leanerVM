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

/-- With nothing fixed, the partial sum is the sum over the cube. -/
theorem plainSum_zero {m : ℕ} (g : Vector R m → R) :
    plainSum g 0 #v[] = ∑ x : Fin (2 ^ m), g (boolVec x) := by
  rw [plainSum, dite_eq_left (Nat.zero_le m)]
  simp only [fixLow_zero]
  rfl

/-- With everything fixed, the partial sum is the value at the fixed point. -/
theorem plainSum_self {m : ℕ} (g : Vector R m → R) (c : Vector R m) : plainSum g m c = g c := by
  rw [plainSum, dite_eq_left le_rfl]
  have hone : 2 ^ (m - m) = 1 := by simp
  have : Unique (Fin (2 ^ (m - m))) :=
    ⟨⟨⟨0, by omega⟩⟩, fun x ↦ Fin.ext (by have := x.isLt; omega)⟩
  rw [Fintype.sum_unique]
  simp only [fixLow_self]

/-- Fixing one more coordinate: the partial sum at `j` is the sum of the partial sums at `j + 1`
with the coordinate fixed to `0` and to `1`. -/
theorem plainSum_split {m : ℕ} (g : Vector R m → R) {j : ℕ} (hj : j < m) (c : Vector R j) :
    plainSum g j c = plainSum g (j + 1) (c.push 0) + plainSum g (j + 1) (c.push 1) := by
  have hm : 2 * 2 ^ (m - (j + 1)) = 2 ^ (m - j) := by
    rw [show m - j = (m - (j + 1)) + 1 by omega, pow_succ]; ring
  rw [plainSum, plainSum, plainSum, dite_eq_left hj.le, dite_eq_left (Nat.succ_le_of_lt hj),
    dite_eq_left (Nat.succ_le_of_lt hj), ← Fin.sum_congr' _ hm, Fin.sum_univ_split_even_add_odd]
  congr 1 <;> refine Finset.sum_congr rfl fun x' _ ↦ ?_
  · rw [fixLow_push_zero hj c x' (by omega)]; rfl
  · rw [fixLow_push_one hj c x' (by omega)]; rfl

end
end LeanerVM.Protocol
