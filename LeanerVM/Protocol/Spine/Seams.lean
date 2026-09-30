/-
  LeanerVM.Protocol.Spine.Seams

  The claims that travel between the phases, and the seam relations: the output relation of
  each phase, which is the input relation of the next by definition.
-/

module

public import LeanerVM.Protocol.Spine.Instance

/-!
# Claims and seams

The oracle protocol is six phases, `commit ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫ opening`, each a
reduction from a statement to a statement over the one committed stack `q`. The statement
types between phases and the relations on them are fixed here, so a phase is built and proved
knowing only its two seams.

Three kinds of claim, each a statement about an extension read off `q` at a point of `E`:

* a `ColumnClaim`: one column's extension at a point equals a value;
* a `LinearClaim`: an `E`-weighted sum of virtual tables' extensions equals a value, a virtual
  table being a `K`-polynomial of the row evaluated on every row of a table (§5.5's summand). A
  zerocheck claim is one term, of weight 1, with the constraint; a bus form is the list of terms
  of weight `eq(sel_b, ζ_hi)·eq(α, i)` with the coordinate polynomials `c_{b,i}`, plus one
  constant term of weight `eq(sel_b, ζ_hi)·β`. The bus seam bounds the total degree of every
  term's polynomial by the instance's `d`, the degree the table sumcheck is built for;
* a `WeightedClaim`: `Σ_x W(x)·q(x)` over the stack equals a value, with `W` a weight of the
  stack's oracle interface (`LeanerVM.Protocol.Field`): its cube values and an evaluator the
  verifier can run (§3, Definition 3.13).

| Seam | Statement | Holds |
| --- | --- | --- |
| `commit` | the public input | `M3Holds` of the oracle itself |
| `bus` | linear and column claims | every claim; terms of degree `≤ d`; public lines; `aux` |
| `table` | column claims | every claim; the public lines; `aux` |
| `pub` | column claims | every claim; `aux` |
| `flock` | column and weighted claims | every claim |
| `done` | nothing | nothing |

A seam says which claims hold, not which claims a phase emits: that is fixed by the phase's
knowledge soundness (a bus phase emitting no claim typechecks and cannot be proved knowledge
sound). Seams carry no challenge; the zerocheck point `ζ` reaches the table sumcheck inside the
claims' points, and the escape "violated on the cube, zero at `ζ`" is charged to the bus phase
where `ζ` is drawn (§5.5).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CPoly

@[expose] public section

/-! ## Claims -/

/-- A claim on one column of the stack: its extension at a point equals a value. -/
structure ColumnClaim (I : M3Instance) where
  /-- The column. -/
  col : I.ColumnId
  /-- The point, in `E`. -/
  point : Vector E (I.κ col)
  /-- The claimed value. -/
  value : E

/-- The claim holds of the stack `q`. -/
def ColumnClaim.Holds {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I) : Prop :=
  CMlPolynomialEval.eval₂Mle (I.column q c.col).values (algebraMap K E) c.point = c.value

/-- One term of a linear claim: a weight in `E`, a table, a polynomial of its row with
coefficients in `K`, and the point the table's extension is taken at. -/
structure VirtualTerm (I : M3Instance) where
  /-- The weight of the term in the sum. -/
  weight : E
  /-- The table. -/
  j : Fin I.ntab
  /-- The polynomial of the row. -/
  poly : CMvPolynomial (I.width j) K
  /-- The point the virtual table is extended to. -/
  point : Vector E (I.τ j)

/-- The virtual table of a term: its polynomial on every row of its table, lifted to `E`. -/
def VirtualTerm.table {I : M3Instance} (q : Column I.μ) (t : VirtualTerm I) :
    CMlPolynomialEval E (I.τ t.j) :=
  Vector.ofFn fun x ↦ ofK (t.poly.eval (I.row q t.j x))

/-- The value of a term: its weight times its virtual table's extension at its point. -/
def VirtualTerm.eval {I : M3Instance} (q : Column I.μ) (t : VirtualTerm I) : E :=
  t.weight * CMlPolynomialEval.evalMle (t.table q) t.point

/-- A linear claim: a weighted sum of virtual-table extensions equals a value. -/
structure LinearClaim (I : M3Instance) where
  /-- The terms. -/
  terms : List (VirtualTerm I)
  /-- The claimed value. -/
  value : E

/-- The claim holds of the stack `q`. -/
def LinearClaim.Holds {I : M3Instance} (q : Column I.μ) (c : LinearClaim I) : Prop :=
  (c.terms.map fun t ↦ t.eval q).sum = c.value

/-- A weighted claim on the stack: the inner product of a weight with the stack, the stack's
oracle answer to that weight, equals a value. -/
structure WeightedClaim (I : M3Instance) where
  /-- The weight. -/
  weight : Weight E I.μ
  /-- The claimed value. -/
  value : E

/-- The claim holds of the stack `q`. -/
def WeightedClaim.Holds {I : M3Instance} (q : Column I.μ) (c : WeightedClaim I) : Prop :=
  c.weight.pair (algebraMap K E) q.values = c.value

/-! ## Seam statements -/

/-- What the bus phase hands on: the zerocheck claims at `ζ` and the bus forms, as linear claims,
and the boundary blocks' column claims. -/
structure BusOut (I : M3Instance) where
  /-- The linear claims. -/
  linear : List (LinearClaim I)
  /-- The column claims. -/
  columns : List (ColumnClaim I)

/-- What the table sumcheck hands on: column claims only. -/
structure TableOut (I : M3Instance) where
  /-- The column claims. -/
  columns : List (ColumnClaim I)

/-- What the public-input phase hands on: column claims, now with the public words' claims. -/
structure PubOut (I : M3Instance) where
  /-- The column claims. -/
  columns : List (ColumnClaim I)

/-- What the Flock phase hands on: the claim pool the opening phase batches. -/
structure FlockOut (I : M3Instance) where
  /-- The column claims, to be weighted through the layout. -/
  columns : List (ColumnClaim I)
  /-- The weighted claims, ring switched. -/
  weighted : List (WeightedClaim I)

/-! ## Seam relations

Each is a set of `((statement, oracle), witness)` with the one oracle the stack and the witness
trivial: after the commit phase the oracle is the witness. -/

/-- The stack behind the one oracle. -/
abbrev theStack {I : M3Instance} (o : ∀ i, TheOracle I i) : Column I.μ := o 0

namespace Seam

variable (I : M3Instance)

/-- The seam of a predicate of the statement and the stack behind the one oracle. -/
def of {S : Type} (P : S → Column I.μ → Prop) : Set ((S × ∀ i, TheOracle I i) × Unit) :=
  {p | P p.1.1 (theStack p.1.2)}

/-- After the commit phase: `M3Holds` of the oracle itself, which pins the oracle to the witness
of record. -/
def commit := of I (M3Holds I)

/-- After the bus phase: every claim holds, every term has degree at most `d`, and what the bus
did not touch. -/
def bus := of I fun (s : I.Stmt × BusOut I) q ↦ (∀ c ∈ s.2.linear, c.Holds q) ∧
  (∀ c ∈ s.2.linear, ∀ t ∈ c.terms, t.poly.totalDegree ≤ I.d) ∧
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q

/-- After the table sumcheck: every column claim holds, and what it did not touch. -/
def table := of I fun (s : I.Stmt × TableOut I) q ↦
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q

/-- After the public-input phase: every column claim holds, and the auxiliary predicate. -/
def pub := of I fun (s : I.Stmt × PubOut I) q ↦ (∀ c ∈ s.2.columns, c.Holds q) ∧ I.aux q

/-- After the Flock phase: every pooled claim holds. -/
def flock := of I fun (s : I.Stmt × FlockOut I) q ↦
  (∀ c ∈ s.2.columns, c.Holds q) ∧ ∀ c ∈ s.2.weighted, c.Holds q

/-- After the opening phase: nothing is left to check. -/
def done := of I fun (_ : Unit) _ ↦ True

end Seam

end
end LeanerVM.Protocol
