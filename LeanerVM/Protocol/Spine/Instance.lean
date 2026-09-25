/-
  LeanerVM.Protocol.Spine.Instance

  The abstract M3 instance and the relation the oracle protocol proves knowledge of. Nothing
  here knows leanISA: the instance is the polynomial view of *an* arithmetization, and leanISA
  is one instance of it (the adaptor, roadmap Layer 3).
-/

module

public import LeanerVM.Protocol.Field
public import CompPoly.Multivariate.CMvPolynomial

/-!
# The M3 instance and the relation `M3Holds`

Protocol roadmap, section *The spine* (`docs/roadmap/protocol-blueprint.md`, hole S). This module
is the top of the wall (convention *The wall*): every phase of the proof system is written over a
variable `I : M3Instance` and imports this file, never `LeanerVM.Arithmetization`.

## What an instance is

An `M3Instance` is what the verifier of leanVM's proof system reads about an arithmetization
and nothing more:

* `ntab` tables, each with an announced log-height `τ j` (its column height is `2 ^ τ j`) and a
  width `width j` (its number of columns);
* per table, the constraint polynomials, in the row's `width j` variables, that must vanish on
  every row (specification §5.5, the zerocheck), and the flush tuples: a side (`push` or
  `pull`) and sixteen coordinate polynomials, the separator first (§5.2, the bus);
* per table, which columns are count columns, whose cells must all be nonzero (§6.2, the count
  product `R_c ≠ 0`);
* the boundary blocks (§5.4, the framework blocks): tuples pushed or pulled by the verifier's
  side of the bus, whose coordinates are constants, public columns the verifier evaluates
  itself, or committed columns of the stack;
* the stack layout: every column of every table lives inside the one committed column
  `q : Column μ`, and `layout` says how to read it back and how a point of a column lifts to a
  point of the stack (the selector law, specification §5.4 equation (2) and the `Stacks`
  convention);
* the public cells: which cells of which columns the public statement fixes (§8.2, the two
  public words), as a function of the statement;
* an auxiliary predicate on the stack, the fact the Flock phase (roadmap Layer 9) establishes
  beyond the polynomial checks: for leanISA, that the BLAKE2S rows are valid compressions; for
  the toy instance, `True`.

Polynomials are CompPoly's computable `CPoly.CMvPolynomial`, so that the relation below is
decidable and the executable verifier of Layer 12 can evaluate them; the bridge to Mathlib's
`MvPolynomial` is CompPoly's `fromCMvPolynomial` (with `eval_equiv` and `totalDegree_equiv`),
which the security proofs of the phases use for Schwartz–Zippel.

## The relation

`M3Holds I input q` is the checklist the verifier establishes about the committed stack `q`:
every constraint vanishes on every row of its table, the pushed tuples are a permutation of the
pulled tuples (one multiset, counted in `ℕ`, never a field sum: leanISA finding #16), every
count cell is nonzero, the public cells carry the statement, and the auxiliary predicate holds.
Everything is read through `I.layout`: knowledge of a stack `q` with `M3Holds I input q` is
exactly as strong as the layout that reads it (a layout reading every column off one cell
satisfies the `Layout` law), and it is the adaptor's `witnessOf_stackOf` (Layer 3) that pins the
leanISA layout to the stacking of `witness.rs:85-101`.
`M3Rel I` is the same relation in ArkLib's shape, the shape the master theorems of the spine are
stated over. The witness is the stack itself, in `Type 0`; the adaptor (`witnessOf`, Layer 3)
turns it into leanISA's `EnsembleWitness`, which lives in `Type 1` and could not be the witness
of an ArkLib reduction.

Category A: written from the specification; nothing here transcribes Rust. Target: T4, the
relation whose knowledge the oracle protocol proves.

## Wrong readings excluded

* The sizes are instance data, not a clause: an inadmissible size (the caps of §6.2) is
  rejected by the compiled verifier before the oracle protocol starts (Layer 12), so the oracle
  protocol is a family indexed by admissible instances and `M3Holds` never mentions caps.
* Balance is `List.Perm` of the two tuple lists, so a tuple pushed twice and never pulled does
  not balance; over `K` (characteristic two) a field-summed balance would accept it.
* `Coord.known` is a column both parties know; it is data of the instance, never read off `q`.
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

/-- A column of an instance with `ntab` tables of the given widths: table `j`, column `i`. -/
abbrev ColumnId (ntab : ℕ) (width : Fin ntab → ℕ) : Type := Σ j : Fin ntab, Fin (width j)

/-- The stack layout: how every column of height `2 ^ κ c` is read off the committed column of
height `2 ^ μ`, and how a point of the column lifts to a point of the stack, with the one law
every phase reads a column through: the extension of the column at `z` is the extension of the
stack at `extend c z` (specification §5.4 equation (2); for an aligned block at selector `sel`,
`extend c z = z ++ sel`, roadmap Layer 1's `stack_eval`). Any concrete layout (the `Blocks` of
Layer 1, the toy's three slices) is an inhabitant. It is a *reading* law, not a stacking law: it
does not say the columns are disjoint slices of the stack, and a relation stated through it is as
strong as the layout is; the adaptor's `witnessOf_stackOf` is where the leanISA layout is pinned. -/
structure Layout (μ : ℕ) (ι : Type) (κ : ι → ℕ) where
  /-- Read column `c` off the stack. -/
  read : Column μ → (c : ι) → Column (κ c)
  /-- Lift a point of column `c` to the point of the stack that reads the same value. -/
  extend : (c : ι) → Vector E (κ c) → Vector E μ
  /-- The selector law: reading then extending is extending then reading. -/
  read_eval : ∀ (q : Column μ) (c : ι) (z : Vector E (κ c)),
    CMlPolynomialEval.eval₂Mle (read q c).values (algebraMap K E) z =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) (extend c z)

/-- One coordinate of a boundary tuple on a block of height `2 ^ κ`: a constant, a public column
the verifier evaluates itself (the index column `g^i`, the bytecode column), or a committed
column of the stack of the same height. -/
inductive Coord (ntab : ℕ) (width : Fin ntab → ℕ) (τ : Fin ntab → ℕ) (κ : ℕ)
  | const (c : K)
  | known (col : Column κ)
  | committed (c : ColumnId ntab width) (h : τ c.1 = κ)

/-- A boundary block (specification §5.4, the framework blocks): `2 ^ κ` tuples on one side of
the bus, coordinate by coordinate. -/
structure BoundaryBlock (ntab : ℕ) (width : Fin ntab → ℕ) (τ : Fin ntab → ℕ) where
  /-- Log-height of the block. -/
  κ : ℕ
  /-- The side its tuples are on. -/
  side : Side
  /-- The sixteen coordinates, the separator first. -/
  coords : Vector (Coord ntab width τ κ) 16

/-- A cell of a column fixed by the public statement. -/
structure PublicCell (ntab : ℕ) (width : Fin ntab → ℕ) (τ : Fin ntab → ℕ) where
  /-- The column. -/
  col : ColumnId ntab width
  /-- The row. -/
  idx : Fin (2 ^ τ col.1)
  /-- The value the cell must hold. -/
  val : K

/-! ## The instance -/

/-- The polynomial view of an arithmetization: what every phase reads, and nothing more. -/
structure M3Instance where
  /-- The public statement type (leanISA: `PublicInput`). -/
  Stmt : Type
  /-- Number of tables. -/
  ntab : ℕ
  /-- Log-height of each table: the announced sizes. -/
  τ : Fin ntab → ℕ
  /-- Width of each table. -/
  width : Fin ntab → ℕ
  /-- The constraint polynomials of each table, in the row's variables. -/
  constraints : (j : Fin ntab) → List (CMvPolynomial (width j) K)
  /-- The flush tuples of each table: a side and sixteen coordinate polynomials, separator first. -/
  flushes : (j : Fin ntab) → List (Side × Vector (CMvPolynomial (width j) K) 16)
  /-- The count columns of each table. -/
  counts : (j : Fin ntab) → List (Fin (width j))
  /-- The boundary blocks. -/
  boundary : List (BoundaryBlock ntab width τ)
  /-- Log-height of the committed stack. -/
  μ : ℕ
  /-- The stack layout. -/
  layout : Layout μ (ColumnId ntab width) (fun c ↦ τ c.1)
  /-- The cells the statement fixes. -/
  publicCells : Stmt → List (PublicCell ntab width τ)
  /-- What the auxiliary (Flock) phase establishes about the stack. -/
  aux : Column μ → Prop
  /-- The auxiliary predicate is decidable, so that the relation is. -/
  decAux : DecidablePred aux

attribute [instance] M3Instance.decAux

namespace M3Instance

variable (I : M3Instance)

/-- The columns of the instance. -/
abbrev ColumnId : Type := LeanerVM.Protocol.ColumnId I.ntab I.width

/-- Log-height of a column: its table's. -/
abbrev κ (c : I.ColumnId) : ℕ := I.τ c.1

/-- Read one column off the stack. -/
def column (q : Column I.μ) (c : I.ColumnId) : Column (I.κ c) := I.layout.read q c

/-- Row `x` of table `j`, read off the stack. -/
def row (q : Column I.μ) (j : Fin I.ntab) (x : Fin (2 ^ I.τ j)) : Fin (I.width j) → K :=
  fun i ↦ (I.column q ⟨j, i⟩).values.get x

/-- The value of a boundary coordinate at row `x` of its block. -/
def coordCell (q : Column I.μ) {κ : ℕ} : Coord I.ntab I.width I.τ κ → Fin (2 ^ κ) → K
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

/-- The cells the statement fixes hold their values (§8.2). -/
def PublicCellsHold (input : I.Stmt) (q : Column I.μ) : Prop :=
  ∀ c ∈ I.publicCells input, (I.column q c.col).values.get c.idx = c.val

instance (q : Column I.μ) : Decidable (I.ConstraintsVanish q) := by
  unfold ConstraintsVanish; infer_instance
instance (q : Column I.μ) : Decidable (I.Balanced q) := by
  unfold Balanced; infer_instance
instance (q : Column I.μ) : Decidable (I.CountsNonzero q) := by
  unfold CountsNonzero; infer_instance
instance (input : I.Stmt) (q : Column I.μ) : Decidable (I.PublicCellsHold input q) := by
  unfold PublicCellsHold; infer_instance

end M3Instance

/-- The relation the oracle protocol proves knowledge of: what the verifier establishes about
the committed stack `q`. In the order the phases consume them: every constraint vanishes on
every row of its table and the bus balances (reduced by the bus phase and the table sumcheck),
every count cell is nonzero (the bus phase's `R_c ≠ 0`), the public cells carry the statement
(the public-input phase), and the auxiliary predicate holds (the Flock phase). -/
def M3Holds (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Prop :=
  I.ConstraintsVanish q ∧ I.Balanced q ∧ I.CountsNonzero q ∧ I.PublicCellsHold input q ∧ I.aux q

/-- The relation is decidable: every clause is a finite check over computable data. -/
instance (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Decidable (M3Holds I input q) := by
  unfold M3Holds
  infer_instance

/-- The empty oracle-statement family: before the commit phase there is no oracle. -/
abbrev NoOracle : Fin 0 → Type := fun i ↦ i.elim0

/-- The one oracle of the protocol: the committed stack, from the commit phase on. -/
abbrev TheOracle (I : M3Instance) : Fin 1 → Type := fun _ ↦ Column I.μ

/-- `M3Holds` in ArkLib's shape: the statement is the public input and no oracle, the witness
is the stack. -/
def M3Rel (I : M3Instance) : Set ((I.Stmt × (∀ i, NoOracle i)) × Column I.μ) :=
  {p | M3Holds I p.1.1 p.2}

end
end LeanerVM.Protocol
