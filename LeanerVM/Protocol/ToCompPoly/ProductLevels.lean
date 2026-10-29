/-
  LeanerVM.Protocol.ToCompPoly.ProductLevels

  Every level of a product tree, built once from the leaves up: the data a grand-product prover
  reads layer after layer, each level equal to `layerTable`. Candidate for CompPoly.
-/

module

public import LeanerVM.Protocol.ToCompPoly.ProductTree

/-!
# The levels of a product tree, built once

`layerTable t m` is the level of the tree of `t` on `m` variables, computed from the leaves:
reading it for every `m` contracts the leaves `μ - m` times each. `levelsOf t` contracts once per
level and keeps every level (`Levels R μ`: the leaves, then the levels above, down to the root),
and `Levels.get` reads one off; the level read is `layerTable`'s (`get_levelsOf`), a table of
ones past the leaves as there. Over an arbitrary commutative ring; nothing here transcribes a
source.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

universe u

/-- The levels of a product tree of `2 ^ μ` leaves: the leaves, then the tree of the level
above. -/
def Levels (R : Type u) : ℕ → Type u
  | 0 => CMlPolynomialEval R 0
  | μ + 1 => CMlPolynomialEval R (μ + 1) × Levels R μ

/-- The level on `m` variables, a table of ones past the leaves. -/
def Levels.get {R : Type u} [One R] : {μ : ℕ} → Levels R μ → (m : ℕ) → CMlPolynomialEval R m
  | 0, L, m =>
    if h : m = 0 then Vector.cast (congrArg (2 ^ ·) h.symm) (show CMlPolynomialEval R 0 from L)
    else Vector.replicate (2 ^ m) 1
  | μ + 1, L, m =>
    if h : m = μ + 1 then
      Vector.cast (congrArg (2 ^ ·) h.symm)
        (show CMlPolynomialEval R (μ + 1) × Levels R μ from L).1
    else Levels.get (show CMlPolynomialEval R (μ + 1) × Levels R μ from L).2 m

variable {R : Type u} [CommRing R]

/-- The levels of the tree of `t`, each contracted once from the one below. -/
def levelsOf : {μ : ℕ} → CMlPolynomialEval R μ → Levels R μ
  | 0, t => t
  | μ + 1, t => (show CMlPolynomialEval R (μ + 1) × Levels R μ from (t, levelsOf (contract t)))

/-- The level read off the built levels is the tree's level. -/
theorem get_levelsOf : {μ : ℕ} → (t : CMlPolynomialEval R μ) → (m : ℕ) →
    (levelsOf t).get m = layerTable t m
  | 0, _, _ => rfl
  | μ + 1, t, m => by
    simp only [levelsOf, Levels.get, layerTable, get_levelsOf (contract t) m]

end
end LeanerVM.Protocol
