/-
  LeanerVM.Protocol.Spine.Seams

  The claims that travel between the phases of the oracle protocol, and the seam relations: the
  output relation of each phase, which is the input relation of the next by definition.
-/

module

public import LeanerVM.Protocol.Spine.Instance

/-!
# Claims and seams

Protocol roadmap, section *The spine*, convention *Seams*. The oracle protocol is six phases,

```text
commit ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫ opening
```

and every phase is a reduction over the one committed oracle `q : Column I.μ` from a statement
to a statement. The statement types between the phases (`BusOut`, `TableOut`, `PubOut`,
`FlockOut`) and the relations on them (`Seam.commit` to `Seam.done`) are fixed here, so that a
phase can be built and proved knowing only its two seams. Whatever a seam does not carry, the
phase before it must have established, and the round-by-round knowledge soundness of that phase
is exactly the proof that it did.

## Three kinds of claim

Every claim is a statement about the extension of some table read off `q` at a point of `E`.

* A `ColumnClaim`: one column's extension at a point equals a value. Produced by the bus phase
  (the boundary blocks), the table sumcheck (its final evaluations) and the public-input phase.
* A `LinearClaim`: a weighted sum of *virtual* tables' extensions equals a value, where a
  virtual table is a polynomial of the row evaluated on every row of a table (specification
  §5.5's summand: a constraint, or a bus form `β − π_α(t)` with the fingerprint folded into
  the polynomial's coefficients). Produced by the bus phase: the zerocheck claims at the reused
  point `ζ` (value `0`) and the three bus forms (values the tables owe, §5.4 "Settling it").
  Consumed by the table sumcheck, which needs nothing else about where they came from.
* A `WeightedClaim`: `Σ_x W(x)·q(x)` over the stack equals a value, with `W` given by its cube
  values and an evaluator for its extension (Definition 3.13, an MLE-friendly weight). The
  currency of the opening phase and of WHIR; a column claim becomes one through the layout's
  `extend` (`eq(extend c z, ·)` as the weight), the ring-switched Flock claim is born one.

## What each seam carries

| Seam | Statement | Holds of `q` |
| --- | --- | --- |
| `commit` | the public input | `M3Holds` on the oracle itself: the oracle *is* the witness |
| `bus` | `BusOut`: linear claims, column claims | every claim; the public cells; `aux` |
| `table` | `TableOut`: column claims | every claim; the public cells; `aux` |
| `pub` | `PubOut`: column claims | every claim; `aux` |
| `flock` | `FlockOut`: column claims, weighted claims | every claim |
| `done` | nothing | nothing |

The zerocheck point is recycled from the bus (§5.5): the bus phase draws `ζ` inside its GKR and
emits the zerocheck claims at it, so the escape "a constraint violated on the cube whose
extension vanishes at `ζ`" is charged in the bus phase, coordinate by coordinate as `ζ` is drawn
(decision 3 of the roadmap, settled). There is no separate zerocheck phase.

Category A: written from the specification's phase structure (§5, §8.5); nothing here transcribes
Rust. Target: T4, the intermediate relations of the oracle protocol.

## Wrong readings excluded

* A seam relation does not say *which* claims a phase emits; its knowledge soundness does. A
  bus phase emitting no claims typechecks and cannot be proved knowledge sound.
* The seams carry no challenge and no message: a phase that needs an earlier phase's challenge
  (the table sumcheck needs `ζ`) reads it inside the claims it receives.
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

/-- A weight on the stack (Definition 3.13): its values on the cube, and an evaluator for its
extension that the verifier can run, with the proof that the two agree. -/
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

/-- What the bus phase hands to the table sumcheck: the zerocheck claims at the reused point and
the bus forms, as linear claims, and the boundary blocks' column claims. -/
structure BusOut (I : M3Instance) where
  /-- The linear claims. -/
  linear : List (LinearClaim I)
  /-- The column claims. -/
  columns : List (ColumnClaim I)

/-- What the table sumcheck hands to the public-input phase: column claims only. -/
structure TableOut (I : M3Instance) where
  /-- The column claims. -/
  columns : List (ColumnClaim I)

/-- What the public-input phase hands to the Flock phase: column claims, now including the
public words' claims. -/
structure PubOut (I : M3Instance) where
  /-- The column claims. -/
  columns : List (ColumnClaim I)

/-- What the Flock phase hands to the opening phase: the claim pool. -/
structure FlockOut (I : M3Instance) where
  /-- The column claims, to be weighted through the layout. -/
  columns : List (ColumnClaim I)
  /-- The weighted claims, ring switched. -/
  weighted : List (WeightedClaim I)

/-! ## Seam relations

Each is a set of `((statement × oracle) × witness)` in ArkLib's shape, with the one oracle
`TheOracle I` and the trivial witness: after the commit phase the oracle is the witness. -/

/-- The stack behind the one oracle. -/
abbrev theStack {I : M3Instance} (o : ∀ i, TheOracle I i) : Column I.μ := o 0

namespace Seam

variable (I : M3Instance)

/-- After the commit phase: `M3Holds` of the oracle itself. The strengthened intermediate
relation of the leanth pattern, pinning the oracle to the witness of record. -/
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
