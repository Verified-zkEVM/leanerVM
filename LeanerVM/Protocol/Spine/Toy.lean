/-
  LeanerVM.Protocol.Spine.Toy

  The toy instance: one table of width three and height two on a stack of height eight, with one
  constraint, one push, one boundary pull, one count column and one public cell. Every phase is
  tested on it.
-/

module

public import LeanerVM.Protocol.Spine.Instance

/-!
# The toy instance

Protocol roadmap, section *The spine*, item 7 of *What the spine fixes*, and acceptance test 27.
The instance is small enough that `M3Holds` is decided by evaluation (`#guard` in
`tests/LeanerVMTests/Protocol/Spine.lean`), and rich enough that every clause of `M3Holds` can be
made to fail alone:

* the one table has three columns of height two, at stack cells `0–1`, `2–3`, `4–5` (cells `6–7`
  are padding);
* column 2 must be Boolean (`X₂² − X₂ = 0`), and its cell `0` is the public statement;
* the table pushes `(X₀, 0, …)` on every row, and one boundary block pulls the public column
  `[1, 1]`, so the bus balances exactly when column 0 is `[1, 1]` in some order;
* column 1 is a count column, so its cells must be nonzero;
* the auxiliary predicate is `True`.

The layout is the spine's own `Layout` with the selector law proved by hand for the three
slices: column `i` at cells `2i, 2i + 1` has selector bits `(i mod 2, i div 2)`, so its extension
at `z` is the stack's extension at `(z, i mod 2, i div 2)`.
-/

namespace LeanerVM.Protocol.Toy

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CPoly

@[expose] public section

/-- The columns of the toy: one table, three columns. -/
abbrev Col : Type := ColumnId 1 fun _ ↦ 3

/-- Column `i` is the slice at cells `2i, 2i + 1`. -/
def slice (q : Column 3) (c : Col) : Column 1 :=
  ⟨#v[q.values.get ⟨2 * c.2.val, by have h : c.2.val < 3 := c.2.isLt; omega⟩,
      q.values.get ⟨2 * c.2.val + 1, by have h : c.2.val < 3 := c.2.isLt; omega⟩]⟩

/-- The selector of column `i` is the pair of bits `(i mod 2, i div 2)`. -/
def extend (c : Col) (z : Vector E 1) : Vector E 3 :=
  #v[z.head, if c.2.val % 2 = 1 then 1 else 0, if c.2.val / 2 = 1 then 1 else 0]

/-- Three interpolation layers evaluate a three-variable table at a literal point. -/
private theorem evalMle_three (p : CMlPolynomialEval E 3) (a b c : E) :
    CMlPolynomialEval.evalMle p #v[a, b, c] =
      (CMlPolynomialEval.evalMleLayer (CMlPolynomialEval.evalMleLayer
        (CMlPolynomialEval.evalMleLayer p a) b) c).get ⟨0, by norm_num⟩ := rfl

/-- One interpolation layer evaluates a one-variable table. -/
private theorem evalMle_one (p : CMlPolynomialEval E 1) (x : Vector E 1) :
    CMlPolynomialEval.evalMle p x =
      (CMlPolynomialEval.evalMleLayer p x.head).get ⟨0, by norm_num⟩ := rfl

/-- The selector law for the three slices: reading the slice then extending at `z` is extending
the stack at `(z, i mod 2, i div 2)`. -/
theorem read_eval (q : Column 3) (c : Col) (z : Vector E 1) :
    CMlPolynomialEval.eval₂Mle (slice q c).values (algebraMap K E) z =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) (extend c z) := by
  obtain ⟨j, i⟩ := c
  fin_cases i <;>
  · simp only [CMlPolynomialEval.eval₂Mle, extend, slice]
    simp only [evalMle_three, evalMle_one, CMlPolynomialEval.evalMleLayer_get,
      CMlPolynomialEval.map]
    simp

/-- The layout of the toy. -/
def layout : Layout 3 Col (fun _ ↦ 1) where
  read := slice
  extend := extend
  read_eval := read_eval

/-- The one flush: `(X₀, 0, …)`, pushed. -/
def flush : Side × Vector (CMvPolynomial 3 K) 16 :=
  (.push, Vector.ofFn fun k ↦ if k.val = 0 then CMvPolynomial.X 0 else 0)

/-- The one boundary block: pulls `([1, 1], 0, …)`. -/
def boundary : BoundaryBlock 1 (fun _ ↦ 3) (fun _ ↦ 1) where
  κ := 1
  side := .pull
  coords := Vector.ofFn fun k ↦ if k.val = 0 then .known ⟨#v[1, 1]⟩ else .const 0

/-- The toy instance. An `abbrev`, so that its fields reduce wherever a test names it. -/
abbrev toy : M3Instance where
  Stmt := K
  ntab := 1
  τ := fun _ ↦ 1
  width := fun _ ↦ 3
  constraints := fun _ ↦ [CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2]
  flushes := fun _ ↦ [flush]
  counts := fun _ ↦ [1]
  boundary := [boundary]
  μ := 3
  layout := layout
  publicCells := fun v ↦ [⟨⟨0, 2⟩, 0, v⟩]
  aux := fun _ ↦ True
  decAux := fun _ ↦ inferInstance

/-- The honest stack: columns `[1, 1]`, `[1, 1]`, `[1, 0]`, then padding. -/
def honest : Column 3 := ⟨#v[1, 1, 1, 1, 1, 0, 0, 0]⟩

end
end LeanerVM.Protocol.Toy
