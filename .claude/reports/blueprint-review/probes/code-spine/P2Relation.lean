import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose

/-!
Probe P2 (code-spine): `M3Holds` on variants of the toy instance.

* multiplicity: a tuple pushed twice and pulled once, a tuple pushed twice and never pulled;
* the side filter: the same instance with the two sides exchanged;
* the layout's freedom: every column read from the same two cells.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

namespace Probe

/-! ## Multiplicity -/

/-- A boundary block of height one (`κ = 0`): pulls the single tuple `(1, 0, …)`. -/
def boundaryOnce : BoundaryBlock shape where
  κ := 0
  side := .pull
  coords := Vector.ofFn fun k ↦ if k.val = 0 then .const 1 else .const 0

/-- The toy whose boundary pulls `(1, 0, …)` once, where the table pushes it twice. -/
abbrev toyOnce : M3Instance := { toy with boundary := [boundaryOnce] }

/-- The toy with no boundary: the table pushes `(1, 0, …)` twice and nothing is pulled. -/
abbrev toyNever : M3Instance := { toy with boundary := [] }

-- Pushed twice, pulled once: the two sides are the same *set* and differ as multisets.
#guard (toyOnce.tuples honest .push).length = 2
#guard (toyOnce.tuples honest .pull).length = 1
#guard (toyOnce.tuples honest .push).map (fun t ↦ t.get 0) = [1, 1]
#guard (toyOnce.tuples honest .pull).map (fun t ↦ t.get 0) = [1]
#guard (toyOnce.tuples honest .push).all fun t ↦ (toyOnce.tuples honest .pull).any fun u ↦
  t.toList == u.toList
#guard (toyOnce.tuples honest .pull).all fun t ↦ (toyOnce.tuples honest .push).any fun u ↦
  t.toList == u.toList
-- Only the balance clause fails.
#guard toyOnce.ConstraintsVanish honest
#guard ¬ toyOnce.Balanced honest
#guard toyOnce.CountsNonzero honest
#guard toyOnce.PublicLinesHold (1 : K) honest
#guard ¬ M3Holds toyOnce (1 : K) honest

-- Pushed twice, never pulled: every coordinate sums to zero in `K` on both sides (the sum of
-- the empty side is zero), so a balance summed in the field accepts; the multiset balance
-- rejects, and only it fails.
#guard (toyNever.tuples honest .push).length = 2
#guard (toyNever.tuples honest .pull).length = 0
#guard (List.finRange 16).all fun k ↦
  ((toyNever.tuples honest .push).map fun t ↦ t.get k).sum =
    ((toyNever.tuples honest .pull).map fun t ↦ t.get k).sum
#guard toyNever.ConstraintsVanish honest
#guard ¬ toyNever.Balanced honest
#guard toyNever.CountsNonzero honest
#guard toyNever.PublicLinesHold (1 : K) honest
#guard ¬ M3Holds toyNever (1 : K) honest

/-! ## The side filter -/

/-- The toy's flush, pulled instead of pushed. -/
def flushPull : Side × Vector (CMvPolynomial 3 K) 16 := (.pull, Toy.flush.2)

/-- The toy's boundary block, pushed instead of pulled. -/
def boundaryPush : BoundaryBlock shape := { Toy.boundary with side := .push }

/-- The toy with the two sides exchanged. -/
abbrev toySwap : M3Instance :=
  { toy with
    flushes := fun _ ↦ [flushPull]
    flushes_degree := fun _ f h k ↦ by
      rw [List.mem_singleton.mp h]
      exact toy.flushes_degree 0 Toy.flush (List.mem_singleton_self _) k
    boundary := [boundaryPush] }

#guard (toySwap.tuples honest .push).length = 2
#guard (toySwap.tuples honest .pull).length = 2
#guard (toySwap.flushTuples honest .push).length = 0
#guard (toySwap.flushTuples honest .pull).length = 2
#guard (toySwap.boundaryTuples honest .push).length = 2
#guard (toySwap.boundaryTuples honest .pull).length = 0
#guard M3Holds toySwap (1 : K) honest
#guard ¬ toySwap.Balanced (⟨#v[1, 0, 1, 1, 1, 0, 0, 0]⟩ : Column 3)

/-! ## The row ranges -/

-- One pushed tuple per row of the table (2 rows), one pulled tuple per row of the block
-- (2 rows); a block of height one contributes one.
#guard (toy.flushTuples honest .push).length = 2 ^ toy.τ 0
#guard (toy.boundaryTuples honest .pull).length = 2 ^ Toy.boundary.κ
#guard (toyOnce.boundaryTuples honest .pull).length = 2 ^ boundaryOnce.κ

-- The count clause ranges over every row of the count column and over nothing else: a zero
-- in the padding (cells 6, 7) or in another column's cell does not fail it.
#guard toy.CountsNonzero honest
#guard toy.CountsNonzero (⟨#v[0, 0, 1, 1, 0, 0, 0, 0]⟩ : Column 3)
#guard ¬ toy.CountsNonzero (⟨#v[1, 1, 0, 1, 1, 0, 1, 1]⟩ : Column 3)
#guard ¬ toy.CountsNonzero (⟨#v[1, 1, 1, 0, 1, 0, 1, 1]⟩ : Column 3)

/-! ## The layout's freedom: every column read from the same cells -/

/-- Every column is the slice at cells `0, 1`. -/
def aliasSlice (q : Column 3) (_ : Col) : Column 1 :=
  ⟨#v[q.values.get ⟨0, by decide⟩, q.values.get ⟨1, by decide⟩]⟩

/-- Every column's selector is `(0, 0)`. -/
def aliasExtend (_ : Col) (z : Vector E 1) : Vector E 3 := #v[z.head, 0, 0]

/-- The reading law holds of the aliased layout. -/
theorem alias_read_eval (q : Column 3) (c : Col) (z : Vector E 1) :
    CMlPolynomialEval.eval₂Mle (aliasSlice q c).values (algebraMap K E) z =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) (aliasExtend c z) := by
  simp [CMlPolynomialEval.eval₂Mle, CMlPolynomialEval.evalMle,
    CMlPolynomialEval.evalMleValues, CMlPolynomialEval.evalMleStep, CMlPolynomialEval.map,
    Vector.head, Vector.tail, aliasExtend, aliasSlice]

/-- The aliased layout: a `Layout`, since the law is a reading law. -/
def aliasLayout : Layout 3 Col (fun _ ↦ 1) where
  read := aliasSlice
  extend := aliasExtend
  read_eval := alias_read_eval

/-- The toy with every column read from cells `0, 1`. -/
abbrev toyAlias : M3Instance := { toy with layout := aliasLayout }

#guard (toyAlias.column honest ⟨0, 0⟩).values.toList = (toyAlias.column honest ⟨0, 2⟩).values.toList
#guard ¬ M3Holds toyAlias (1 : K) honest
-- Balance needs cells `0, 1` to be `1, 1`; the public line needs cell `1` to be `0`.
#guard toyAlias.Balanced honest
#guard ¬ toyAlias.PublicLinesHold (1 : K) honest
#guard toyAlias.PublicLinesHold (1 : K) (⟨#v[1, 0, 1, 1, 1, 0, 0, 0]⟩ : Column 3)
#guard ¬ toyAlias.Balanced (⟨#v[1, 0, 1, 1, 1, 0, 0, 0]⟩ : Column 3)

-- Evidence (not a proof) that the relation of the aliased toy is empty: no stack with cells
-- `0, 1` in `{0, 1, 2}` satisfies it at a statement in `{0, 1, 2}`. On paper: balance forces
-- cells `0, 1` to be `1, 1`, and the public line on column 2, now cells `0, 1`, forces cell 1
-- to be `0`.
#guard ([0, 1, 2] : List K).all fun a ↦ ([0, 1, 2] : List K).all fun b ↦
  ([0, 1, 2] : List K).all fun s ↦
    decide (¬ M3Holds toyAlias s (⟨#v[a, b, 1, 1, 1, 0, 0, 0]⟩ : Column 3))

end Probe
