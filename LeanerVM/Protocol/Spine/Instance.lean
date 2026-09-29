/-
  LeanerVM.Protocol.Spine.Instance

  The abstract instance the proof system is stated over, and the relation it proves knowledge of.
-/

module

public import LeanerVM.Protocol.Field
public import LeanerVM.Protocol.ToArkLib.Oracles
public import CompPoly.Multivariate.Basic

/-!
# The M3 instance and the relation `M3Holds`

An `M3Instance` is everything the verifier reads about an arithmetization: the tables with their
log-heights and widths; per table, the constraint polynomials that must vanish on every row
(§5.5) and the bus flushes, each a side and sixteen coordinate polynomials with the domain
separator first (§5.1); a bound `d` on the total degree of both (leanVM's is 2); the count
columns whose cells must be nonzero (§6.2); the boundary blocks, tuples the verifier's side of
the bus provides or consumes, with constant, publicly known or committed coordinates (§5.4); the
layout of every column inside the one committed stack `q`; the columns whose first two cells the
public statement fixes (§8.2); and an auxiliary predicate for what the Flock phase proves of
the committed region it owns (for leanISA, that Flock's R1CS holds of the bits packed into
`q_flock`, §4.2 and Annex C; that the eighteen limb slots then compress is a consequence, not
the predicate, since the wires must already be in `q` for the honest prover to convince).
Nothing here knows leanISA: leanISA is one instance, built by the adaptor.

`M3Holds I input q` is the relation: constraints vanish, pushed and pulled tuples are one
multiset (a permutation, counted in the integers: in characteristic two a tuple pushed twice and
never pulled would sum to zero), count cells are nonzero, the public lines hold, the auxiliary
predicate holds. It is decidable, and every value is read from `q` through `I.layout`, so
knowledge of `q` is exactly as strong as the layout is. Polynomials are CompPoly's computable
`CMvPolynomial` and degrees its `totalDegree`; `fromCMvPolynomial` bridges to Mathlib's, whose
degree lemmas prove a concrete instance's bound. The announced sizes are not a clause: the
compiled verifier rejects inadmissible sizes before the protocol starts, so the protocol is a
family over admissible instances.

Written from the specification; nothing here transcribes Rust.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CPoly

@[expose] public section

/-! ## Columns of an instance -/

/-- A side of the bus: a tuple is provided (`push`) or consumed (`pull`). -/
inductive Side
  | push
  | pull
  deriving DecidableEq, Repr

/-- The tables of an instance: how many, and each one's log-height and width. -/
structure Shape where
  /-- Number of tables. -/
  ntab : ℕ
  /-- Log-height of each table: the announced sizes. -/
  τ : Fin ntab → ℕ
  /-- Width of each table. -/
  width : Fin ntab → ℕ

/-- A column: table `j`, column `i`. -/
abbrev Shape.ColumnId (S : Shape) : Type := Σ j : Fin S.ntab, Fin (S.width j)

/-- How each column of height `2 ^ κ c` is read off the stack of height `2 ^ μ`, and how a point
of the column lifts to a point of the stack, with the law that reading then evaluating equals
evaluating the stack at the lifted point (§4.1, the stacking identity, and §5.4, equation (2);
for an aligned block at selector bits `sel`, `extend c z = (z, sel)`). It is a reading law, not a
stacking law: it does not say the columns are disjoint slices of `q`. -/
structure Layout (μ : ℕ) (ι : Type) (κ : ι → ℕ) where
  /-- Read column `c` off the stack. -/
  read : Column μ → (c : ι) → Column (κ c)
  /-- Lift a point of column `c` to the point of the stack that reads the same value. -/
  extend : (c : ι) → Vector E (κ c) → Vector E μ
  /-- The selector law: reading then extending is extending then reading. -/
  read_eval : ∀ (q : Column μ) (c : ι) (z : Vector E (κ c)),
    CMlPolynomialEval.eval₂Mle (read q c).values (algebraMap K E) z =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) (extend c z)

/-- One coordinate of a boundary tuple on a block of height `2 ^ κ`: a constant, a column both
parties know (the index column `g^i`, the bytecode column), or a committed column of the same
height. -/
inductive Coord (S : Shape) (κ : ℕ)
  | const (c : K)
  | known (col : Column κ)
  | committed (c : S.ColumnId) (h : S.τ c.1 = κ)

/-- A boundary block (§5.4): `2 ^ κ` tuples on one side of the bus, coordinate by coordinate. -/
structure BoundaryBlock (S : Shape) where
  /-- Log-height of the block. -/
  κ : ℕ
  /-- The side its tuples are on. -/
  side : Side
  /-- The sixteen coordinates, the separator first. -/
  coords : Vector (Coord S κ) 16

/-- A column whose first two cells the public statement fixes (§8.2: the two public words are
the first two memory cells). -/
structure PublicLine (S : Shape) where
  /-- The column. -/
  col : S.ColumnId
  /-- The value cell 0 must hold. -/
  cell0 : K
  /-- The value cell 1 must hold. -/
  cell1 : K
  /-- Whether the proof carries the value claimed for this column on the line through its two
  cells (§8.2: it does for the two low limbs of the memory, and not for the top limb, whose
  value is known to be zero). It fixes the transcript, not the relation. -/
  sent : Bool
  /-- The column has a cell 1. -/
  pos : 0 < S.τ col.1

/-! ## The instance -/

/-- Everything the verifier reads about an arithmetization. -/
structure M3Instance extends Shape where
  /-- The public statement type (leanISA: `PublicInput`). -/
  Stmt : Type
  /-- The constraint polynomials of each table, in the row's variables. -/
  constraints : (j : Fin ntab) → List (CMvPolynomial (width j) K)
  /-- The flush tuples of each table: a side and sixteen coordinate polynomials, separator first. -/
  flushes : (j : Fin ntab) → List (Side × Vector (CMvPolynomial (width j) K) 16)
  /-- The degree bound: every constraint and every flush coordinate has total degree at most
  `d`; leanVM's is 2. -/
  d : ℕ
  /-- Every constraint has total degree at most `d`. -/
  constraints_degree : ∀ j, ∀ C ∈ constraints j, C.totalDegree ≤ d
  /-- Every flush coordinate has total degree at most `d`. -/
  flushes_degree : ∀ j, ∀ f ∈ flushes j, ∀ k, (f.2.get k).totalDegree ≤ d
  /-- The count columns of each table. -/
  counts : (j : Fin ntab) → List (Fin (width j))
  /-- The boundary blocks. -/
  boundary : List (BoundaryBlock toShape)
  /-- Log-height of the committed stack. -/
  μ : ℕ
  /-- The stack layout. -/
  layout : Layout μ toShape.ColumnId (fun c ↦ τ c.1)
  /-- The columns whose first two cells the statement fixes. -/
  publicLines : Stmt → List (PublicLine toShape)
  /-- What the Flock phase proves of the committed region it owns, beyond the polynomial
  checks: the statement its honest prover can convince the verifier of, so it names the
  committed witness (Flock's R1CS on `q_flock`), never only a consequence of it. -/
  aux : Column μ → Prop
  /-- The auxiliary predicate is decidable, so that the relation is. -/
  decAux : DecidablePred aux

attribute [instance] M3Instance.decAux

namespace M3Instance

variable (I : M3Instance)

/-- Log-height of a column: its table's. -/
abbrev κ (c : I.ColumnId) : ℕ := I.τ c.1

/-- Read one column off the stack. -/
def column (q : Column I.μ) (c : I.ColumnId) : Column (I.κ c) := I.layout.read q c

/-- Row `x` of table `j`, read off the stack. -/
def row (q : Column I.μ) (j : Fin I.ntab) (x : Fin (2 ^ I.τ j)) : Fin (I.width j) → K :=
  fun i ↦ (I.column q ⟨j, i⟩).values.get x

/-- The value of a boundary coordinate at row `x` of its block. -/
def coordCell (q : Column I.μ) {κ : ℕ} : Coord I.toShape κ → Fin (2 ^ κ) → K
  | .const c, _ => c
  | .known col, x => col.values.get x
  | .committed c h, x => (I.column q c).values.get (Fin.cast (congrArg (2 ^ ·) h.symm) x)

/-- The tuples of one side flushed by the tables: every table, every flush of that side, every
row. -/
def flushTuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  (List.finRange I.ntab).flatMap fun j ↦
    ((I.flushes j).filter fun f ↦ decide (f.1 = s)).flatMap fun f ↦
      (List.finRange (2 ^ I.τ j)).map fun x ↦ f.2.map fun P ↦ P.eval (I.row q j x)

/-- The tuples of one side on the boundary blocks. -/
def boundaryTuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  (I.boundary.filter fun b ↦ decide (b.side = s)).flatMap fun b ↦
    (List.finRange (2 ^ b.κ)).map fun x ↦ b.coords.map fun co ↦ I.coordCell q co x

/-- Every tuple of one side of the bus. -/
def tuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  I.flushTuples q s ++ I.boundaryTuples q s

end M3Instance

/-! ## The relation, clause by clause -/

namespace M3Instance

variable (I : M3Instance)

/-- Every constraint vanishes on every row of its table (the zerocheck, §5.5). -/
def ConstraintsVanish (q : Column I.μ) : Prop :=
  ∀ j, ∀ C ∈ I.constraints j, ∀ x, C.eval (I.row q j x) = 0

/-- The pushed tuples are one multiset with the pulled tuples (the bus, §5.2), counted in `ℕ`. -/
def Balanced (q : Column I.μ) : Prop := (I.tuples q .push).Perm (I.tuples q .pull)

/-- Every cell of every count column is nonzero (the count product `R_c ≠ 0`, §6.2). -/
def CountsNonzero (q : Column I.μ) : Prop :=
  ∀ j, ∀ i ∈ I.counts j, ∀ x, (I.column q ⟨j, i⟩).values.get x ≠ 0

/-- Cells 0 and 1 of every column the statement fixes hold their values (§8.2). -/
def PublicLinesHold (input : I.Stmt) (q : Column I.μ) : Prop :=
  ∀ l ∈ I.publicLines input,
    (I.column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩ = l.cell0 ∧
      (I.column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩ = l.cell1

deriving instance Decidable for ConstraintsVanish, Balanced, CountsNonzero, PublicLinesHold

end M3Instance

/-- The relation the oracle protocol proves knowledge of: what the verifier establishes about
the committed stack `q`. -/
def M3Holds (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Prop :=
  I.ConstraintsVanish q ∧ I.Balanced q ∧ I.CountsNonzero q ∧ I.PublicLinesHold input q ∧ I.aux q

-- The relation is decidable: every clause is a finite check over computable data.
deriving instance Decidable for M3Holds

/-- The one oracle of the protocol from the commit phase on: the stack. -/
abbrev TheOracle (I : M3Instance) : Fin 1 → Type := OneOracle (Column I.μ)

/-- `M3Holds` as ArkLib states relations: the statement is the public input with no oracle, the
witness is the stack. -/
def M3Rel (I : M3Instance) : Set ((I.Stmt × (∀ i, NoOracle i)) × Column I.μ) :=
  {p | M3Holds I p.1.1 p.2}

end
end LeanerVM.Protocol
