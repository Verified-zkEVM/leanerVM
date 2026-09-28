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
* a `LinearClaim`: a weighted sum of virtual tables' extensions equals a value, a virtual table
  being a polynomial of the row evaluated on every row of a table (§5.5's summand: a constraint,
  or a bus form `β − π_α(t)` with the fingerprint folded into the coefficients);
* a `WeightedClaim`: `Σ_x W(x)·q(x)` over the stack equals a value, with `W` given by its cube
  values and an evaluator the verifier can run (§3, Definition 3.13).

| Seam | Statement | Holds of `q` |
| --- | --- | --- |
| `commit` | the public input | `M3Holds` of the oracle itself |
| `bus` | linear and column claims | every claim; the public cells; `aux` |
| `table` | column claims | every claim; the public cells; `aux` |
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

/-- One term of a linear claim: a weight, a table, a polynomial of its row with coefficients in
`E`, and a point of the table's cube. -/
structure VirtualTerm (I : M3Instance) where
  /-- The weight of the term in the sum. -/
  weight : E
  /-- The table. -/
  j : Fin I.ntab
  /-- The polynomial of the row. -/
  poly : CMvPolynomial (I.width j) E
  /-- The point the virtual table is extended to. -/
  point : Vector E (I.τ j)

/-- The virtual table of a term: its polynomial on every row of its table, lifted to `E`. -/
def VirtualTerm.table {I : M3Instance} (q : Column I.μ) (t : VirtualTerm I) :
    CMlPolynomialEval E (I.τ t.j) :=
  Vector.ofFn fun x ↦ t.poly.eval fun i ↦ ofK (I.row q t.j x i)

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

/-- A weight on the stack (Definition 3.13): its cube values, and an evaluator for its extension
the verifier can run, with the proof that they agree. -/
structure Weight (μ : ℕ) where
  /-- The values on the cube. -/
  onCube : CMlPolynomialEval E μ
  /-- The extension, as the verifier evaluates it. -/
  mle : Vector E μ → E
  /-- The evaluator computes the extension of the cube values. -/
  mle_eq : ∀ r, mle r = CMlPolynomialEval.evalMle onCube r

/-- The pairing `Σ_x W(x)·q(x)` of a weight with a column, over the cube. -/
def Weight.pair {μ : ℕ} (W : Weight μ) (q : Column μ) : E :=
  ∑ i : Fin (2 ^ μ), W.onCube.get i * ofK (q.values.get i)

/-- A weighted claim on the stack: its pairing with a weight equals a value. -/
structure WeightedClaim (I : M3Instance) where
  /-- The weight. -/
  weight : Weight I.μ
  /-- The claimed value. -/
  value : E

/-- The claim holds of the stack `q`. -/
def WeightedClaim.Holds {I : M3Instance} (q : Column I.μ) (c : WeightedClaim I) : Prop :=
  c.weight.pair q = c.value

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

/-- After the commit phase: `M3Holds` of the oracle itself, which pins the oracle to the witness
of record. -/
def commit : Set ((I.Stmt × ∀ i, TheOracle I i) × Unit) :=
  {p | M3Holds I p.1.1 (theStack p.1.2)}

/-- After the bus phase: every claim holds, and what the bus did not touch. -/
def bus : Set (((I.Stmt × BusOut I) × ∀ i, TheOracle I i) × Unit) :=
  {p | (∀ c ∈ p.1.1.2.linear, c.Holds (theStack p.1.2)) ∧
    (∀ c ∈ p.1.1.2.columns, c.Holds (theStack p.1.2)) ∧
    I.PublicCellsHold p.1.1.1 (theStack p.1.2) ∧ I.aux (theStack p.1.2)}

/-- After the table sumcheck: every column claim holds, and what it did not touch. -/
def table : Set (((I.Stmt × TableOut I) × ∀ i, TheOracle I i) × Unit) :=
  {p | (∀ c ∈ p.1.1.2.columns, c.Holds (theStack p.1.2)) ∧
    I.PublicCellsHold p.1.1.1 (theStack p.1.2) ∧ I.aux (theStack p.1.2)}

/-- After the public-input phase: every column claim holds, and the auxiliary predicate. -/
def pub : Set (((I.Stmt × PubOut I) × ∀ i, TheOracle I i) × Unit) :=
  {p | (∀ c ∈ p.1.1.2.columns, c.Holds (theStack p.1.2)) ∧ I.aux (theStack p.1.2)}

/-- After the Flock phase: every pooled claim holds. -/
def flock : Set (((I.Stmt × FlockOut I) × ∀ i, TheOracle I i) × Unit) :=
  {p | (∀ c ∈ p.1.1.2.columns, c.Holds (theStack p.1.2)) ∧
    (∀ c ∈ p.1.1.2.weighted, c.Holds (theStack p.1.2))}

/-- After the opening phase: nothing is left to check. -/
def done : Set ((Unit × ∀ i, TheOracle I i) × Unit) := Set.univ

end Seam

end
end LeanerVM.Protocol
