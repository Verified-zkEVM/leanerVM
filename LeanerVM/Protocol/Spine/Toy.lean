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

One table of width 3 and height 2 on a stack of height 8: column `i` at cells `2i, 2i + 1`,
cells 6 and 7 padding. Column 2 must be Boolean and its cell 0 is the public statement; the
table pushes `(X₀, 0, …)` on every row and one boundary block pulls the known column `[1, 1]`,
so the bus balances exactly when column 0 is `[1, 1]` in some order; column 1 is a count
column; the auxiliary predicate is `True`. `M3Holds` on it is decided by evaluation, and each
of its clauses can be made to fail alone (`tests/LeanerVMTests/Protocol/Spine.lean`).
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

/-- The layout law for the three slices: the slice's extension at `z` is the stack's at
`(z, i mod 2, i div 2)`. -/
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
