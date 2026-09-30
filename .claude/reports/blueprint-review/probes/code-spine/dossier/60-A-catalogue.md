## A. Catalogue

Every public declaration of the modules in scope, in file order, with its class: **load-bearing** (the statement of a master theorem unfolds to it; "named form" marks those reached only through `piop_rbrKnowledgeSoundness`'s named extractor and state function, section B), **interface** (a phase author must meet or use it), **helper** (used only inside proofs; those a master statement unfolds to are marked), **test fixture**. Snippets are extracted from `git show b435631:<file>` by `probes/code-spine/catalogue.py`: structures and inductives in full, definitions with their data body and without proof fields, theorems and instances as their statement. Helpers that are pure proof lemmas (`passThrough_materializeOutput`, `passThroughVerifier_toVerifier_run`, `passThroughPure`, `passThroughProver`, `passThroughVerifier`, `passThroughExtractor`, `passThroughStateFunction`, `passThrough_rbr`, `sendSpec`, `sendProver`, `sendEmbedding`, `sendVerifier`, `sendOracle_outputPure`, `send_materializeOutput`, `sendVerifier_toVerifier_run`, `sendVerifierPure`, `sendOracle_complete`, `sendWitMid`, `sendOracle_rbr`, `Refinement.id`, `Refinement.comp`, `noOracle_eq`, and the seventeen lemmas of `KnowledgeAppend` other than its two named declarations) are named here and not listed one by one; the send-oracle ones are counted in section B where the named statement reaches them.

Library objects (all at the pins ArkLib `dca90385`, CompPoly `3468b38c`, VCVio `f9dc47d9`) are introduced where first used in sections C and D; the catalogue names them in the "depends on" column.

### `LeanerVM/Protocol/Field.lean`

**`Column`** (`Field.lean:67-69`) — *load-bearing*. A table of `2^n` values of `K`, indexed by the cube `{0,1}^n` low bit first: what is committed. Wrapped in a structure so that its oracle interface is the evaluation one, not ArkLib's position query on `Vector`. Depends on: CompPoly `CMlPolynomialEval`.

```lean
structure Column (n : ℕ) where
  values : CMlPolynomialEval K n
```

**`evalOracle`** (`Field.lean:102-106`) — *load-bearing*. How the verifier queries a committed column: a query is a point `r ∈ E^n`, the answer is the multilinear extension `q̃(r)` with the entries lifted from `K` to `E`. Every seam is read through it. Depends on: `Column`, CompPoly `eval₂Mle`, ArkLib `OracleInterface`.

```lean
instance evalOracle (n : ℕ) : OracleInterface (Column n) where
  Query := Vector E n
  toOC :=
    { spec := (Vector E n) →ₒ E
      impl := fun r ↦ do return CMlPolynomialEval.eval₂Mle (← read).values (algebraMap K E) r }
```

**`instSampleableTypeE`** (`Field.lean:93-93`) — *load-bearing*. Uniform sampling of a challenge in `E` as three independent uniform limbs (VCVio needs a sampler for every challenge type). Depends on: `limbsEquiv`, VCVio `SampleableType`.

```lean
instance instSampleableTypeE : SampleableType E := SampleableType.ofEquiv limbsEquiv
```

### `LeanerVM/Protocol/ToArkLib/Oracles.lean`

**`NoOracle`** (`Oracles.lean:26-26`) — *load-bearing*. The oracle family with no oracle (before the commit). Depends on: —.

```lean
abbrev NoOracle : Fin 0 → Type := fun i ↦ i.elim0
```

**`OneOracle`** (`Oracles.lean:29-29`) — *load-bearing*. The oracle family with exactly one oracle of type `M` (the stack, from the commit on). Depends on: —.

```lean
abbrev OneOracle (M : Type) : Fin 1 → Type := fun _ ↦ M
```

**`noOracle_eq`** (`Oracles.lean:32-32`) — *helper*. Any two empty oracle families are equal. Depends on: —.

```lean
theorem noOracle_eq (o o' : ∀ i, NoOracle i) : o = o' :=
```

### `LeanerVM/Protocol/Spine/Instance.lean`

**`Side`** (`Instance.lean:51-54`) — *load-bearing*. Which side of the bus a tuple is on: provided (`push`) or consumed (`pull`). Depends on: —.

```lean
inductive Side
  | push
  | pull
  deriving DecidableEq, Repr
```

**`Shape`** (`Instance.lean:57-63`) — *load-bearing*. The tables: how many, each one's log-height (the announced sizes) and width. Depends on: —.

```lean
structure Shape where
  ntab : ℕ
  τ : Fin ntab → ℕ
  width : Fin ntab → ℕ
```

**`Shape.ColumnId`** (`Instance.lean:66-66`) — *load-bearing*. A column: a table and a column index in it. Depends on: `Shape`.

```lean
abbrev Shape.ColumnId (S : Shape) : Type := Σ j : Fin S.ntab, Fin (S.width j)
```

**`Layout`** (`Instance.lean:73-81`) — *load-bearing*. How a column is read off the stack (`read`) and how a point of the column lifts to a point of the stack (`extend`), with the one law: the column's extension at `z` is the stack's at `extend c z`. A reading law: it does not say the columns are disjoint slices (C.2, D.4). Depends on: `Column`, CompPoly `eval₂Mle`.

```lean
structure Layout (μ : ℕ) (ι : Type) (κ : ι → ℕ) where
  read : Column μ → (c : ι) → Column (κ c)
  extend : (c : ι) → Vector E (κ c) → Vector E μ
  read_eval : ∀ (q : Column μ) (c : ι) (z : Vector E (κ c)),
    CMlPolynomialEval.eval₂Mle (read q c).values (algebraMap K E) z =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) (extend c z)
```

**`Coord`** (`Instance.lean:86-89`) — *load-bearing*. One coordinate of a boundary tuple: a constant, a column both parties know (index, bytecode), or a committed column of the block's height. Depends on: `Shape`, `Column`.

```lean
inductive Coord (S : Shape) (κ : ℕ)
  | const (c : K)
  | known (col : Column κ)
  | committed (c : S.ColumnId) (h : S.τ c.1 = κ)
```

**`BoundaryBlock`** (`Instance.lean:92-98`) — *load-bearing*. `2^κ` boundary tuples on one side of the bus, given coordinate by coordinate (sixteen, separator first). Depends on: `Coord`, `Side`.

```lean
structure BoundaryBlock (S : Shape) where
  κ : ℕ
  side : Side
  coords : Vector (Coord S κ) 16
```

**`PublicLine`** (`Instance.lean:102-114`) — *load-bearing*. A column whose cells 0 and 1 the public statement fixes; `sent` says whether the proof carries its value (transcript only, not the relation); `pos` says the column has a cell 1. Depends on: `Shape`.

```lean
structure PublicLine (S : Shape) where
  col : S.ColumnId
  cell0 : K
  cell1 : K
  sent : Bool
  pos : 0 < S.τ col.1
```

**`M3Instance`** (`Instance.lean:119-148`) — *load-bearing*. Everything the verifier reads about an arithmetization: the statement type, per table its constraints and flushes (polynomials over `K` of the row), a degree bound `d` with the two proofs, the count columns, the boundary blocks, the stack height `μ` and layout, the public lines of a statement, and the auxiliary predicate `aux` with its decision procedure. Trusted data (section F). Depends on: `Shape`, `Layout`, `BoundaryBlock`, `PublicLine`, CompPoly `CMvPolynomial`, `totalDegree`.

```lean
structure M3Instance extends Shape where
  Stmt : Type
  constraints : (j : Fin ntab) → List (CMvPolynomial (width j) K)
  flushes : (j : Fin ntab) → List (Side × Vector (CMvPolynomial (width j) K) 16)
  d : ℕ
  constraints_degree : ∀ j, ∀ C ∈ constraints j, C.totalDegree ≤ d
  flushes_degree : ∀ j, ∀ f ∈ flushes j, ∀ k, (f.2.get k).totalDegree ≤ d
  counts : (j : Fin ntab) → List (Fin (width j))
  boundary : List (BoundaryBlock toShape)
  μ : ℕ
  layout : Layout μ toShape.ColumnId (fun c ↦ τ c.1)
  publicLines : Stmt → List (PublicLine toShape)
  aux : Column μ → Prop
  decAux : DecidablePred aux
```

**`κ`** (`Instance.lean:157-157`) — *load-bearing*. Log-height of a column: its table's. Depends on: `M3Instance`.

```lean
abbrev κ (c : I.ColumnId) : ℕ := I.τ c.1
```

**`column`** (`Instance.lean:160-160`) — *load-bearing*. One column of the stack, through the layout. Depends on: `Layout.read`.

```lean
def column (q : Column I.μ) (c : I.ColumnId) : Column (I.κ c) := I.layout.read q c
```

**`row`** (`Instance.lean:163-164`) — *load-bearing*. Row `x` of table `j`: the function giving each column's cell `x`. Depends on: `column`.

```lean
def row (q : Column I.μ) (j : Fin I.ntab) (x : Fin (2 ^ I.τ j)) : Fin (I.width j) → K :=
  fun i ↦ (I.column q ⟨j, i⟩).values.get x
```

**`coordCell`** (`Instance.lean:167-170`) — *load-bearing*. The value of a boundary coordinate at row `x` of its block. Depends on: `Coord`, `column`.

```lean
def coordCell (q : Column I.μ) {κ : ℕ} : Coord I.toShape κ → Fin (2 ^ κ) → K
  | .const c, _ => c
  | .known col, x => col.values.get x
  | .committed c h, x => (I.column q c).values.get (Fin.cast (congrArg (2 ^ ·) h.symm) x)
```

**`flushTuples`** (`Instance.lean:174-177`) — *load-bearing*. The tuples of one side flushed by the tables: for every table, every flush of that side, every row, the sixteen coordinate polynomials evaluated on the row. Depends on: `row`, CompPoly `CMvPolynomial.eval`.

```lean
def flushTuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  (List.finRange I.ntab).flatMap fun j ↦
    ((I.flushes j).filter fun f ↦ decide (f.1 = s)).flatMap fun f ↦
      (List.finRange (2 ^ I.τ j)).map fun x ↦ f.2.map fun P ↦ P.eval (I.row q j x)
```

**`boundaryTuples`** (`Instance.lean:180-182`) — *load-bearing*. The tuples of one side on the boundary blocks: for every block of that side, every row. Depends on: `coordCell`.

```lean
def boundaryTuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  (I.boundary.filter fun b ↦ decide (b.side = s)).flatMap fun b ↦
    (List.finRange (2 ^ b.κ)).map fun x ↦ b.coords.map fun co ↦ I.coordCell q co x
```

**`tuples`** (`Instance.lean:185-186`) — *load-bearing*. Every tuple of one side: the tables' then the boundary's. Depends on: `flushTuples`, `boundaryTuples`.

```lean
def tuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  I.flushTuples q s ++ I.boundaryTuples q s
```

**`ConstraintsVanish`** (`Instance.lean:197-198`) — *load-bearing*. Every constraint of every table is zero on every row (the zerocheck target). Depends on: `row`.

```lean
def ConstraintsVanish (q : Column I.μ) : Prop :=
  ∀ j, ∀ C ∈ I.constraints j, ∀ x, C.eval (I.row q j x) = 0
```

**`Balanced`** (`Instance.lean:201-201`) — *load-bearing*. The pushed tuples are a permutation of the pulled tuples: the same multiset, counted in `ℕ`. Depends on: `tuples`, Mathlib `List.Perm`.

```lean
def Balanced (q : Column I.μ) : Prop := (I.tuples q .push).Perm (I.tuples q .pull)
```

**`CountsNonzero`** (`Instance.lean:204-205`) — *load-bearing*. Every cell of every count column is nonzero (the count product). Depends on: `column`.

```lean
def CountsNonzero (q : Column I.μ) : Prop :=
  ∀ j, ∀ i ∈ I.counts j, ∀ x, (I.column q ⟨j, i⟩).values.get x ≠ 0
```

**`PublicLinesHold`** (`Instance.lean:208-211`) — *load-bearing*. Cells 0 and 1 of every line the statement names hold the line's values. Depends on: `column`, `PublicLine`.

```lean
def PublicLinesHold (input : I.Stmt) (q : Column I.μ) : Prop :=
  ∀ l ∈ I.publicLines input,
    (I.column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩ = l.cell0 ∧
      (I.column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩ = l.cell1
```

**`M3Holds`** (`Instance.lean:219-220`) — *load-bearing*. The relation: the five clauses. What the verifier establishes about the committed stack. Depends on: the five clauses.

```lean
def M3Holds (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Prop :=
  I.ConstraintsVanish q ∧ I.Balanced q ∧ I.CountsNonzero q ∧ I.PublicLinesHold input q ∧ I.aux q
```

**`TheOracle`** (`Instance.lean:226-226`) — *load-bearing*. The one oracle from the commit on: the stack. Depends on: `OneOracle`, `Column`.

```lean
abbrev TheOracle (I : M3Instance) : Fin 1 → Type := OneOracle (Column I.μ)
```

**`M3Rel`** (`Instance.lean:230-231`) — *load-bearing*. `M3Holds` as ArkLib states relations: statement = public input with no oracle, witness = the stack. Depends on: `M3Holds`, `NoOracle`.

```lean
def M3Rel (I : M3Instance) : Set ((I.Stmt × (∀ i, NoOracle i)) × Column I.μ) :=
  {p | M3Holds I p.1.1 p.2}
```

### `LeanerVM/Protocol/Spine/Seams.lean`

**`ColumnClaim`** (`Seams.lean:57-63`) — *load-bearing*. One column's extension at a point of `E^κ` equals a value. Depends on: `M3Instance`.

```lean
structure ColumnClaim (I : M3Instance) where
  col : I.ColumnId
  point : Vector E (I.κ col)
  value : E
```

**`ColumnClaim.Holds`** (`Seams.lean:66-67`) — *load-bearing*. The claim is true of the stack, reading the column through the layout. Depends on: `column`, `eval₂Mle`.

```lean
def ColumnClaim.Holds {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I) : Prop :=
  CMlPolynomialEval.eval₂Mle (I.column q c.col).values (algebraMap K E) c.point = c.value
```

**`VirtualTerm`** (`Seams.lean:71-79`) — *load-bearing*. One term of a linear claim: a weight in `E`, a table, a polynomial of its row over `K`, and the point the virtual table (the polynomial on every row) is extended to. Depends on: `M3Instance`.

```lean
structure VirtualTerm (I : M3Instance) where
  weight : E
  j : Fin I.ntab
  poly : CMvPolynomial (I.width j) K
  point : Vector E (I.τ j)
```

**`VirtualTerm.table`** (`Seams.lean:82-84`) — *load-bearing*. The virtual table of a term: its polynomial evaluated on every row of its table, lifted to `E`. Depends on: `row`.

```lean
def VirtualTerm.table {I : M3Instance} (q : Column I.μ) (t : VirtualTerm I) :
    CMlPolynomialEval E (I.τ t.j) :=
  Vector.ofFn fun x ↦ ofK (t.poly.eval (I.row q t.j x))
```

**`VirtualTerm.eval`** (`Seams.lean:87-88`) — *load-bearing*. The term's value: weight times the virtual table's extension at the point. Depends on: `table`, CompPoly `evalMle`.

```lean
def VirtualTerm.eval {I : M3Instance} (q : Column I.μ) (t : VirtualTerm I) : E :=
  t.weight * CMlPolynomialEval.evalMle (t.table q) t.point
```

**`LinearClaim`** (`Seams.lean:91-95`) — *load-bearing*. A weighted sum of virtual-table extensions equals a value (a zerocheck claim is one term of weight 1 and value 0; a bus form is a list of terms). Depends on: `VirtualTerm`.

```lean
structure LinearClaim (I : M3Instance) where
  terms : List (VirtualTerm I)
  value : E
```

**`LinearClaim.Holds`** (`Seams.lean:98-99`) — *load-bearing*. The sum of the terms' values is the claimed value. Depends on: `VirtualTerm.eval`.

```lean
def LinearClaim.Holds {I : M3Instance} (q : Column I.μ) (c : LinearClaim I) : Prop :=
  (c.terms.map fun t ↦ t.eval q).sum = c.value
```

**`Weight`** (`Seams.lean:103-109`) — *load-bearing*. A weight on the stack (specification Definition 3.13): its values on the cube, an evaluator for its extension, and their agreement. Depends on: CompPoly `evalMle`.

```lean
structure Weight (μ : ℕ) where
  onCube : CMlPolynomialEval E μ
  mle : Vector E μ → E
  mle_eq : ∀ r, mle r = CMlPolynomialEval.evalMle onCube r
```

**`Weight.pair`** (`Seams.lean:112-113`) — *load-bearing*. `Σ_x W(x)·q(x)` over the cube. Depends on: `Weight`, `Column`.

```lean
def Weight.pair {μ : ℕ} (W : Weight μ) (q : Column μ) : E :=
  ∑ i : Fin (2 ^ μ), W.onCube.get i * ofK (q.values.get i)
```

**`WeightedClaim`** (`Seams.lean:116-120`) — *load-bearing*. The pairing of a weight with the stack equals a value. Depends on: `Weight`.

```lean
structure WeightedClaim (I : M3Instance) where
  weight : Weight I.μ
  value : E
```

**`WeightedClaim.Holds`** (`Seams.lean:123-124`) — *load-bearing*. True of the stack when the pairing is the value. Depends on: `Weight.pair`.

```lean
def WeightedClaim.Holds {I : M3Instance} (q : Column I.μ) (c : WeightedClaim I) : Prop :=
  c.weight.pair q = c.value
```

**`BusOut`** (`Seams.lean:130-134`) — *load-bearing*. What the bus phase hands on: linear claims and column claims. Depends on: `LinearClaim`, `ColumnClaim`.

```lean
structure BusOut (I : M3Instance) where
  linear : List (LinearClaim I)
  columns : List (ColumnClaim I)
```

**`TableOut`** (`Seams.lean:137-139`) — *load-bearing*. What the table sumcheck hands on: column claims. Depends on: `ColumnClaim`.

```lean
structure TableOut (I : M3Instance) where
  columns : List (ColumnClaim I)
```

**`PubOut`** (`Seams.lean:142-144`) — *load-bearing*. What the public-input phase hands on: column claims (the same type as `TableOut`). Depends on: `ColumnClaim`.

```lean
structure PubOut (I : M3Instance) where
  columns : List (ColumnClaim I)
```

**`FlockOut`** (`Seams.lean:147-151`) — *load-bearing*. What the Flock phase hands on: column claims and weighted claims. Depends on: `ColumnClaim`, `WeightedClaim`.

```lean
structure FlockOut (I : M3Instance) where
  columns : List (ColumnClaim I)
  weighted : List (WeightedClaim I)
```

**`theStack`** (`Seams.lean:159-159`) — *load-bearing*. The stack behind the one oracle. Depends on: `TheOracle`.

```lean
abbrev theStack {I : M3Instance} (o : ∀ i, TheOracle I i) : Column I.μ := o 0
```

**`of`** (`Seams.lean:166-167`) — *load-bearing*. A seam from a predicate on the statement and the stack: the set of `((statement, oracles), ())` where it holds of the one oracle. Depends on: `theStack`.

```lean
def of {S : Type} (P : S → Column I.μ → Prop) : Set ((S × ∀ i, TheOracle I i) × Unit) :=
  {p | P p.1.1 (theStack p.1.2)}
```

**`commit`** (`Seams.lean:171-171`) — *load-bearing*. After the commit: `M3Holds` of the oracle itself. Depends on: `of`, `M3Holds`.

```lean
def commit := of I (M3Holds I)
```

**`bus`** (`Seams.lean:175-177`) — *load-bearing*. After the bus phase: every linear claim holds, every term is within the degree bound, every column claim holds, the lines hold, `aux` holds. Depends on: `of`, the claims, `PublicLinesHold`.

```lean
def bus := of I fun (s : I.Stmt × BusOut I) q ↦ (∀ c ∈ s.2.linear, c.Holds q) ∧
  (∀ c ∈ s.2.linear, ∀ t ∈ c.terms, t.poly.totalDegree ≤ I.d) ∧
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q
```

**`table`** (`Seams.lean:180-181`) — *load-bearing*. After the table sumcheck: column claims, lines, `aux`. Depends on: `of`.

```lean
def table := of I fun (s : I.Stmt × TableOut I) q ↦
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q
```

**`pub`** (`Seams.lean:184-184`) — *load-bearing*. After the public-input phase: column claims and `aux`. Depends on: `of`.

```lean
def pub := of I fun (s : I.Stmt × PubOut I) q ↦ (∀ c ∈ s.2.columns, c.Holds q) ∧ I.aux q
```

**`flock`** (`Seams.lean:187-188`) — *load-bearing*. After the Flock phase: column claims and weighted claims. Depends on: `of`.

```lean
def flock := of I fun (s : I.Stmt × FlockOut I) q ↦
  (∀ c ∈ s.2.columns, c.Holds q) ∧ ∀ c ∈ s.2.weighted, c.Holds q
```

**`done`** (`Seams.lean:191-191`) — *load-bearing*. After the opening: nothing (the whole set). Depends on: `of`.

```lean
def done := of I fun (_ : Unit) _ ↦ True
```

### `LeanerVM/Protocol/ToArkLib/Component.lean`

**`Def`** (`Component.lean:52-66`) — *interface*. A component: its number of rounds, its schedule (who speaks, what type), the instances that every message can be queried and every challenge sampled, the honest prover with the verifier (an ArkLib `OracleReduction` over the empty shared oracle), and the knowledge error it declares per challenge. Depends on: ArkLib `ProtocolSpec`, `OracleReduction`, `OracleInterface`, VCVio `SampleableType`.

```lean
structure Def (StmtIn : Type) {ιi : Type} (OStmtIn : ιi → Type) (WitIn : Type)
    (StmtOut : Type) {ιo : Type} (OStmtOut : ιo → Type) (WitOut : Type)
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)] where
  n : ℕ
  pSpec : ProtocolSpec n
  [msgOracle : ∀ i, OracleInterface (pSpec.Message i)]
  [chalSample : ∀ i, SampleableType (pSpec.Challenge i)]
  red : OracleReduction []ₒ StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec
  err : pSpec.ChallengeIdx → ℝ≥0
```

**`Complete`** (`Component.lean:76-85`) — *interface*. The completeness half a phase must supply: the prover's output is pure (redundant, D.7), the verifier is a check followed by a verdict (data), and perfect completeness from any shared state. Depends on: `Def`, ArkLib `OutputIsPure`, `GuardedForm`, `perfectCompleteness`.

```lean
structure Complete (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)) where
  outputPure : D.red.prover.OutputIsPure
  guarded : D.red.toReduction.verifier.GuardedForm
  complete : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.perfectCompleteness init impl relIn relOut
```

**`Security`** (`Component.lean:90-106`) — *interface*. The security half: completeness, the intermediate witness types, a round-by-round extractor, its knowledge state function from any shared state, and worst-case round-by-round knowledge soundness for them at the declared error. Depends on: `Complete`, ArkLib `Extractor.RoundByRound`, `KnowledgeStateFunction`, `rbrKnowledgeSoundnessWorstCaseWith`.

```lean
structure Security (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    extends Complete D relIn relOut where
  witMid : Fin (D.n + 1) → Type
  extractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (StmtIn × ∀ i, OStmtIn i)
    WitIn WitOut D.pSpec witMid
  kSF : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.verifier.toVerifier.KnowledgeStateFunction init impl relIn relOut extractor
  rbr : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut witMid
      extractor (kSF init impl) D.err
```

**`stateFunctionOfEq`** (`Component.lean:110-120`) — *helper (in the named statement)*. Transport a knowledge state function along an equality of verifiers (needed because ArkLib's appended oracle verifier is only propositionally the appended ordinary verifier). Depends on: ArkLib `KnowledgeStateFunction`.

```lean
def stateFunctionOfEq {ι : Type} {oSpec : OracleSpec ι} {S T WitIn WitOut : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec S WitIn WitOut pSpec W} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {relIn : Set (S × WitIn)}
    {relOut : Set (T × WitOut)} {V V' : Verifier oSpec S T pSpec} (h : V' = V)
    (K : V.KnowledgeStateFunction init impl relIn relOut E) :
    V'.KnowledgeStateFunction init impl relIn relOut E where
  toFun := K.toFun
```

**`rbrKnowledgeSoundnessWorstCaseWith_of_eq`** (`Component.lean:124-135`) — *helper*. The same transport for the bound. Depends on: `stateFunctionOfEq`.

```lean
theorem rbrKnowledgeSoundnessWorstCaseWith_of_eq {ι : Type} {oSpec : OracleSpec ι}
    {S T WitIn WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec S WitIn WitOut pSpec W} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {relIn : Set (S × WitIn)}
    {relOut : Set (T × WitOut)} {V V' : Verifier oSpec S T pSpec} (h : V' = V)
    {K : V.KnowledgeStateFunction init impl relIn relOut E} {ε : pSpec.ChallengeIdx → ℝ≥0}
    (hK : V.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut W E K ε) :
    V'.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut W E (stateFunctionOfEq h K)
      ε :=
```

**`Def.append`** (`Component.lean:143-148`) — *load-bearing*. Two components in sequence: rounds add, schedules concatenate, reductions append (ArkLib), each challenge keeps its component's error. Depends on: ArkLib `OracleReduction.append`, `ChallengeIdx.sumEquiv`.

```lean
def Def.append (D₁ : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂)
    (D₂ : Def Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃) : Def Stmt₁ OStmt₁ Wit₁ Stmt₃ OStmt₃ Wit₃ where
  n := D₁.n + D₂.n
  pSpec := D₁.pSpec ++ₚ D₂.pSpec
  red := D₁.red.append D₂.red
  err := Sum.elim D₁.err D₂.err ∘ ChallengeIdx.sumEquiv.symm
```

**`guardedAppend`** (`Component.lean:156-159`) — *helper (in the named statement)*. The guarded form of an appended verifier from those of its parts (ArkLib's `GuardedForm.append`, cast along the append equation). Depends on: ArkLib `GuardedForm.append`.

```lean
def guardedAppend (G₁ : D₁.red.toReduction.verifier.GuardedForm)
    (G₂ : D₂.red.toReduction.verifier.GuardedForm) :
    (D₁.append D₂).red.toReduction.verifier.GuardedForm :=
  cast (congrArg _ (OracleVerifier.append_toVerifier _ _).symm) (G₁.append G₂)
```

**`Complete.append`** (`Component.lean:162-169`) — *helper (in the named statement)*. Completeness composes: purity, guarded form, and ArkLib's guarded-append completeness theorem. Depends on: ArkLib `append_perfectCompleteness_of_guarded_verifiers`.

```lean
def Complete.append (C₁ : Complete D₁ rel₁ rel₂) (C₂ : Complete D₂ rel₂ rel₃) :
    Complete (D₁.append D₂) rel₁ rel₃ where
  outputPure := Prover.OutputIsPure.append _ _ C₁.outputPure C₂.outputPure
  guarded := guardedAppend C₁.guarded C₂.guarded
```

**`Security.append`** (`Component.lean:174-184`) — *helper (in the named statement)*. Security composes: extractors appended through the first verdict (ArkLib), state functions by the ported `appendGuarded`, the bound by the ported theorem. Depends on: ArkLib `Extractor.RoundByRound.append`; `appendGuarded`; `append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`.

```lean
def Security.append (S₁ : Security D₁ rel₁ rel₂) (S₂ : Security D₂ rel₂ rel₃) :
    Security (D₁.append D₂) rel₁ rel₃ where
  toComplete := S₁.toComplete.append S₂.toComplete
  witMid := _
  extractor := S₁.extractor.append S₂.extractor S₁.guarded.out
  kSF := fun init impl ↦ stateFunctionOfEq (OracleVerifier.append_toVerifier _ _)
    (Verifier.KnowledgeStateFunction.appendGuarded S₁.guarded (S₁.kSF init impl)
      (S₂.kSF init impl))
```

### `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean`

**`appendGuarded`** (`KnowledgeAppend.lean:474-488`) — *helper (in the named statement)*. The knowledge state function of two appended verifiers, the first guarded: the first's state up to the seam, then the first check together with the second's state on the first verdict (ported from ArkLib #615). Depends on: `state`.

```lean
def appendGuarded (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂) :
    (V₁.append V₂).KnowledgeStateFunction init impl R₁ R₃ (E₁.append E₂ G.out) where
  toFun := state G K₁ K₂
```

**`append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`** (`KnowledgeAppend.lean:510-582`) — *helper*. Round-by-round knowledge soundness composes across an append whose first verifier is guarded, each challenge keeping its error (ported from ArkLib #615; admitted upstream at the pin). Depends on: `appendGuarded`, ArkLib `Extractor.RoundByRound.append`.

```lean
theorem append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundnessWorstCaseWith init impl R₁ R₂ W₁ E₁ K₁ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundnessWorstCaseWith init impl R₂ R₃ W₂ E₂ K₂ ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundnessWorstCaseWith init impl R₁ R₃
      (Witness W₁ W₂) (E₁.append E₂ G.out) (KnowledgeStateFunction.appendGuarded G K₁ K₂)
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) :=
```

### `LeanerVM/Protocol/ToArkLib/PassThrough.lean`

**`passThrough`** (`PassThrough.lean:53-57`) — *interface*. The component with no round that maps the statement and keeps the oracles and the witness: the shape of bookkeeping steps. Depends on: `passThroughProver`, `passThroughVerifier`, `keepOracles`.

```lean
def passThrough (f : StmtIn → StmtOut) : Def StmtIn OStmt W StmtOut OStmt W where
  n := 0
  pSpec := !p[]
  red := ⟨passThroughProver OStmt f, passThroughVerifier OStmt f⟩
  err := fun i ↦ Fin.elim0 i.1
```

**`passThroughComplete`** (`PassThrough.lean:81-95`) — *interface*. Its completeness, whenever the map carries the input relation into the output relation. Depends on: `passThrough`, `GuardedVerdict`.

```lean
def passThroughComplete (f : StmtIn → StmtOut)
    {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)} {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ((f s, o), w) ∈ relOut) :
    Complete (passThrough OStmt f) relIn relOut where
  outputPure := ⟨_, fun _ ↦ rfl⟩
  guarded := (passThroughPure OStmt f).toGuardedForm
```

**`passThroughSecurity`** (`PassThrough.lean:132-138`) — *interface*. Its security at error zero, with the extractor that keeps the witness, whenever the map also reflects the output relation into the input relation. Depends on: `passThroughExtractor`, `passThroughStateFunction`, `passThrough_rbr`.

```lean
def passThroughSecurity (hc : ∀ s o w, ((s, o), w) ∈ relIn → ((f s, o), w) ∈ relOut) :
    Security (passThrough OStmt f) relIn relOut where
  toComplete := passThroughComplete OStmt f hc
  witMid := fun _ ↦ W
  extractor := passThroughExtractor OStmt
  kSF := passThroughStateFunction OStmt f h
```

### `LeanerVM/Protocol/ToArkLib/SendOracle.lean`

**`sendOracle`** (`SendOracle.lean:61-65`) — *load-bearing*. The component whose one message becomes the one oracle: the prover sends the witness, the verifier keeps the statement and exposes the message; no challenge, error zero. Depends on: `sendSpec`, `sendProver`, `sendVerifier`, `sendEmbedding`.

```lean
def sendOracle : Def S NoOracle M S (OneOracle M) Unit where
  n := 1
  pSpec := sendSpec M
  red := ⟨sendProver S M, sendVerifier S M⟩
  err := fun _ ↦ 0
```

**`sendOracle_relOut`** (`SendOracle.lean:71-73`) — *load-bearing (named form)*. The input relation read on the oracle instead of the witness (definitionally `Seam.commit` at `M3Rel`). Depends on: —.

```lean
def sendOracle_relOut (rel : Set ((S × ∀ i, NoOracle i) × M)) :
    Set ((S × ∀ i, OneOracle M i) × Unit) :=
  {p | ((p.1.1, fun i ↦ i.elim0), p.1.2 0) ∈ rel}
```

**`sendOracleComplete`** (`SendOracle.lean:121-125`) — *load-bearing (named form)*. Its completeness half. Depends on: `sendVerifierPure`, `sendOracle_complete`.

```lean
def sendOracleComplete (rel : Set ((S × ∀ i, NoOracle i) × M)) :
    Complete (sendOracle S M) rel (sendOracle_relOut rel) where
  outputPure := sendOracle_outputPure
  guarded := (sendVerifierPure (S := S) (M := M)).toGuardedForm
```

**`sendExtractor`** (`SendOracle.lean:134-138`) — *load-bearing (named form)*. Its extractor: read the message, at every round. Depends on: ArkLib `Extractor.RoundByRound`.

```lean
def sendExtractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (S × ∀ i, NoOracle i) M
    Unit (sendSpec M) (sendWitMid M) where
  extractMid := fun m _ tr _ ↦ tr ⟨0, Nat.succ_pos m.val⟩
  extractOut := fun _ tr _ ↦ tr 0
```

**`sendStateFunction`** (`SendOracle.lean:145-161`) — *load-bearing (named form)*. Its knowledge state function: before the message, the relation of the candidate witness; after it, the relation of the message. Depends on: `sendExtractor`, `GuardedVerdict`.

```lean
def sendStateFunction :
    (sendVerifier S M).toVerifier.KnowledgeStateFunction init impl rel (sendOracle_relOut rel)
      (sendExtractor (S := S) (M := M)) where
  toFun := fun m stmt tr w ↦
    if h : m.val = 0 then (stmt, w) ∈ rel else (stmt, tr ⟨0, Nat.pos_of_ne_zero h⟩) ∈ rel
```

**`sendOracleSecurity`** (`SendOracle.lean:172-177`) — *load-bearing (named form)*. Its security half at error zero. Depends on: `sendOracleComplete`, `sendExtractor`, `sendStateFunction`, `sendOracle_rbr`.

```lean
def sendOracleSecurity : Security (sendOracle S M) rel (sendOracle_relOut rel) where
  toComplete := sendOracleComplete rel
  witMid := sendWitMid M
  extractor := sendExtractor
  kSF := sendStateFunction rel
```

### `LeanerVM/Protocol/ToArkLib/Refinement.lean`

**`Refinement`** (`Refinement.lean:31-36`) — *interface (the adaptor)*. A map on witnesses between two relations over the same statements, sending valid witnesses to valid witnesses; the two witness types may live in different universes (D.7). Depends on: —.

```lean
structure Refinement {Stmt : Type} {W₁ W₂ : Type _} (R : Set (Stmt × W₁))
    (S : Set (Stmt × W₂)) where
  map : Stmt → W₁ → W₂
  map_valid : ∀ x w, (x, w) ∈ R → (x, map x w) ∈ S
```

**`map_option_valid`** (`Refinement.lean:55-60`) — *interface (the adaptor)*. On an extractor's output slot: if every witness the slot may hold is valid for `R`, every witness of the mapped slot is valid for `S`. Pointwise; the probabilistic form is D.7. Depends on: `Refinement`.

```lean
theorem map_option_valid {R : Set (Stmt × W₁)} {S : Set (Stmt × W₂)} (f : Refinement R S)
    (x : Stmt) (w? : Option W₁) (h : ∀ w ∈ w?, (x, w) ∈ R) :
    ∀ w' ∈ w?.map (f.map x), (x, w') ∈ S :=
```

**`Extractor.Straightline.map`** (`Refinement.lean:68-71`) — *helper (no consumer)*. Post-compose ArkLib's straight-line extractor with a witness map (same universe). Depends on: ArkLib `Extractor.Straightline`.

```lean
def Extractor.Straightline.map (f : StmtIn → WitIn → WitIn')
    (E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) :
    Extractor.Straightline oSpec StmtIn WitIn' WitOut pSpec :=
  fun stmtIn witOut tr log₁ log₂ ↦ f stmtIn <$> E stmtIn witOut tr log₁ log₂
```

### `LeanerVM/Protocol/ToArkLib/GuardedVerdict.lean`

**`Verifier.GuardedForm.of_probEvent_pos`** (`GuardedVerdict.lean:40-69`) — *helper*. If a guarded verifier can output a statement satisfying `P`, its check passes and its verdict satisfies `P`: the last obligation of every knowledge state function. Depends on: ArkLib `GuardedForm`, VCVio `probEvent`.

```lean
theorem Verifier.GuardedForm.of_probEvent_pos {V : Verifier oSpec StmtIn StmtOut pSpec}
    (G : V.GuardedForm) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (stmt : StmtIn) (tr : pSpec.FullTranscript)
    (P : StmtOut → Prop)
    (h : Pr[P | OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] > 0) :
    G.check stmt tr = true ∧ P (G.out stmt tr) :=
```

**`Reduction.mem_support_run_of_guarded`** (`GuardedVerdict.lean:73-112`) — *helper*. Every outcome of a run with a guarded verifier is a prover run with the verdict where the check passes, a rejection otherwise: how perfect completeness is proved. Depends on: ArkLib `Reduction.run`.

```lean
theorem Reduction.mem_support_run_of_guarded
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (G : reduction.verifier.GuardedForm) (stmt : StmtIn) (wit : WitIn)
    {y : Option ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut)}
    (hy : y ∈ support (reduction.run stmt wit).run) :
    ∃ pr ∈ support (reduction.prover.run stmt wit),
      y = if G.check stmt pr.1 then some (pr, G.out stmt pr.1) else none :=
```

### `LeanerVM/Protocol/ToArkLib/KeepOracles.lean`

**`keepOracles`** (`KeepOracles.lean:34-37`) — *helper*. The output-oracle description "the output oracles are the input oracles". Depends on: ArkLib `OracleOutputEmbedding`.

```lean
def keepOracles : OracleOutputEmbedding OStmt pSpec.Message OStmt where
  embed := Function.Embedding.inl
```

**`OracleVerifier.materializeOutput_of_keepOracles`** (`KeepOracles.lean:42-50`) — *helper*. Such a verifier outputs the oracles it was given. Depends on: `keepOracles`.

```lean
theorem OracleVerifier.materializeOutput_of_keepOracles {StmtIn StmtOut : Type}
    (V : OracleVerifier oSpec StmtIn OStmt StmtOut OStmt pSpec)
    (h : V.outputOracle = .inl (keepOracles OStmt pSpec)) (challenges : pSpec.Challenges)
    (o : ∀ i, OStmt i) (messages : pSpec.Messages) :
    V.materializeOutput challenges o messages = o :=
```

### `LeanerVM/Protocol/Spine/Phase.lean`

**`Def`** (`Phase.lean:37-38`) — *interface*. A phase: a component from a statement to a statement over the stack, with trivial witnesses. Depends on: `Component.Def`, `TheOracle`.

```lean
abbrev Def (StmtIn StmtOut : Type) : Type 1 :=
  Component.Def StmtIn (TheOracle I) Unit StmtOut (TheOracle I) Unit
```

**`Complete`** (`Phase.lean:41-44`) — *interface*. Its completeness half against two seams. Depends on: `Component.Complete`.

```lean
abbrev Complete {StmtIn StmtOut : Type} (D : Def I StmtIn StmtOut)
    (relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit))
    (relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)) : Type :=
  Component.Complete D relIn relOut
```

**`Security`** (`Phase.lean:47-50`) — *interface*. Its security half against two seams. Depends on: `Component.Security`.

```lean
abbrev Security {StmtIn StmtOut : Type} (D : Def I StmtIn StmtOut)
    (relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit))
    (relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)) : Type 1 :=
  Component.Security D relIn relOut
```

**`passThrough`** (`Phase.lean:55-56`) — *interface*. The pass-through phase. Depends on: `Component.passThrough`.

```lean
abbrev passThrough (f : StmtIn → StmtOut) : Def I StmtIn StmtOut :=
  Component.passThrough (TheOracle I) f
```

**`passThroughComplete`** (`Phase.lean:59-64`) — *interface*. Its completeness when the map carries one seam into the other. Depends on: `Component.passThroughComplete`.

```lean
def passThroughComplete (f : StmtIn → StmtOut)
    {relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit)}
    {relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)}
    (h : ∀ s o, ((s, o), ()) ∈ relIn → ((f s, o), ()) ∈ relOut) :
    Complete I (passThrough I f) relIn relOut :=
  Component.passThroughComplete (TheOracle I) f fun s o _ hin ↦ h s o hin
```

**`passThroughSecurity`** (`Phase.lean:68-74`) — *interface*. Its security when the map also reflects the second seam into the first (D.3 (a): impossible at the bus seam). Depends on: `Component.passThroughSecurity`.

```lean
def passThroughSecurity (f : StmtIn → StmtOut)
    {relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit)}
    {relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)}
    (hc : ∀ s o, ((s, o), ()) ∈ relIn → ((f s, o), ()) ∈ relOut)
    (h : ∀ s o, ((f s, o), ()) ∈ relOut → ((s, o), ()) ∈ relIn) :
    Security I (passThrough I f) relIn relOut :=
  Component.passThroughSecurity (TheOracle I) f (fun s o _ ↦ h s o) fun s o _ ↦ hc s o
```

### `LeanerVM/Protocol/Spine/Compose.lean`

**`commitSpec`** (`Compose.lean:51-51`) — *load-bearing*. The commit phase's schedule: one prover message, the stack. Depends on: `sendSpec`.

```lean
abbrev commitSpec : ProtocolSpec 1 := Component.sendSpec (Column I.μ)
```

**`commitDef`** (`Compose.lean:55-56`) — *load-bearing*. The commit phase: the send-oracle component at the stack. Depends on: `sendOracle`.

```lean
abbrev commitDef : Component.Def I.Stmt NoOracle (Column I.μ) I.Stmt (TheOracle I) Unit :=
  Component.sendOracle I.Stmt (Column I.μ)
```

**`commitExtractor`** (`Compose.lean:59-59`) — *load-bearing (named form)*. Its extractor: read the stack off the message. Depends on: `sendExtractor`.

```lean
abbrev commitExtractor := Component.sendExtractor (S := I.Stmt) (M := Column I.μ)
```

**`commitComplete`** (`Compose.lean:63-64`) — *load-bearing (named form)*. Its completeness from `M3Rel` to `Seam.commit`. Depends on: `sendOracleComplete`.

```lean
def commitComplete : Component.Complete (commitDef I) (M3Rel I) (Seam.commit I) :=
  Component.sendOracleComplete (M3Rel I)
```

**`commitSecurity`** (`Compose.lean:67-68`) — *load-bearing (named form)*. Its security at error zero. Depends on: `sendOracleSecurity`.

```lean
def commitSecurity : Component.Security (commitDef I) (M3Rel I) (Seam.commit I) :=
  Component.sendOracleSecurity (M3Rel I)
```

**`Phases where`** (`Compose.lean:73-84`) — *load-bearing*. The five phases after the commit, by their statement types. Depends on: `Phase.Def`, the four outputs.

```lean
structure Phases where
  bus : Phase.Def I I.Stmt (I.Stmt × BusOut I)
  table : Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)
  pub : Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I)
  flock : Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I)
  opening : Phase.Def I (I.Stmt × FlockOut I) Unit
```

**`Phases.toDef`** (`Compose.lean:89-91`) — *load-bearing*. The whole protocol as one component: the commit, then five appends. Depends on: `commitDef`, `Def.append`.

```lean
def Phases.toDef (P : Phases I) :
    Component.Def I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit :=
  (((((commitDef I).append P.bus).append P.table).append P.pub).append P.flock).append P.opening
```

**`Phases.Complete`** (`Compose.lean:94-104`) — *load-bearing*. The five completeness halves against the seams. Depends on: `Phase.Complete`, the seams.

```lean
structure Phases.Complete (P : Phases I) where
  bus : Phase.Complete I P.bus (Seam.commit I) (Seam.bus I)
  table : Phase.Complete I P.table (Seam.bus I) (Seam.table I)
  pub : Phase.Complete I P.pub (Seam.table I) (Seam.pub I)
  flock : Phase.Complete I P.flock (Seam.pub I) (Seam.flock I)
  opening : Phase.Complete I P.opening (Seam.flock I) (Seam.done I)
```

**`Phases.Complete.toDef`** (`Compose.lean:107-110`) — *helper*. The composed completeness. Depends on: `commitComplete`, `Complete.append`.

```lean
def Phases.Complete.toDef {P : Phases I} (C : P.Complete) :
    Component.Complete P.toDef (M3Rel I) (Seam.done I) :=
  (((((commitComplete I).append C.bus).append C.table).append C.pub).append C.flock).append
    C.opening
```

**`Phases.Security`** (`Compose.lean:113-123`) — *load-bearing*. The five security halves against the seams. Depends on: `Phase.Security`, the seams.

```lean
structure Phases.Security (P : Phases I) where
  bus : Phase.Security I P.bus (Seam.commit I) (Seam.bus I)
  table : Phase.Security I P.table (Seam.bus I) (Seam.table I)
  pub : Phase.Security I P.pub (Seam.table I) (Seam.pub I)
  flock : Phase.Security I P.flock (Seam.pub I) (Seam.flock I)
  opening : Phase.Security I P.opening (Seam.flock I) (Seam.done I)
```

**`Phases.Security.toDef`** (`Compose.lean:126-129`) — *load-bearing (named form)*. The composed security: the commit's, then five appends. Depends on: `commitSecurity`, `Security.append`.

```lean
def Phases.Security.toDef {P : Phases I} (S : P.Security) :
    Component.Security P.toDef (M3Rel I) (Seam.done I) :=
  (((((commitSecurity I).append S.bus).append S.table).append S.pub).append S.flock).append
    S.opening
```

**`leanVmPiop`** (`Compose.lean:134-136`) — *load-bearing*. The oracle protocol: the composed reduction. Depends on: `Phases.toDef`.

```lean
def leanVmPiop (P : Phases I) :
    OracleReduction []ₒ I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit P.toDef.pSpec :=
  P.toDef.red
```

**`leanVmVerifier`** (`Compose.lean:139-141`) — *load-bearing*. Its verifier. Depends on: `Phases.toDef`.

```lean
def leanVmVerifier (P : Phases I) :
    OracleVerifier []ₒ I.Stmt NoOracle Unit (TheOracle I) P.toDef.pSpec :=
  P.toDef.red.verifier
```

**`leanVmProver`** (`Compose.lean:144-146`) — *interface*. Its honest prover (not in either theorem's statement; `leanVmPiop` carries it). Depends on: `Phases.toDef`.

```lean
def leanVmProver (P : Phases I) :
    OracleProver []ₒ I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit P.toDef.pSpec :=
  P.toDef.red.prover
```

**`piopError`** (`Compose.lean:149-149`) — *load-bearing*. Its error per challenge: the phases' declarations side by side (section F). Depends on: `Def.append`.

```lean
def piopError (P : Phases I) : P.toDef.pSpec.ChallengeIdx → ℝ≥0 := P.toDef.err
```

**`piopExtractor`** (`Compose.lean:153-156`) — *load-bearing (named form)*. Its extractor: the composed one (D.5). Depends on: `Phases.Security.toDef`.

```lean
def piopExtractor (P : Phases I) (S : P.Security) :
    Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (I.Stmt × ∀ i, NoOracle i)
      (Column I.μ) Unit P.toDef.pSpec S.toDef.witMid :=
  S.toDef.extractor
```

**`piop_perfectCompleteness`** (`Compose.lean:162-165`) — *master theorem*. Given every phase's completeness, the honest prover convinces the verifier with probability one on every `(input, q)` with `M3Holds I input q`. Depends on: `leanVmPiop`, `M3Rel`, `Seam.done`, ArkLib `perfectCompleteness`.

```lean
theorem piop_perfectCompleteness (P : Phases I) (C : P.Complete) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I) :=
```

**`piop_rbrKnowledgeSoundness`** (`Compose.lean:172-177`) — *master theorem*. Given every phase's security, the verifier is round-by-round knowledge sound at the composed error, for the composed extractor and state function. Depends on: `leanVmVerifier`, `piopExtractor`, `piopError`, ArkLib `rbrKnowledgeSoundnessWorstCaseWith`.

```lean
theorem piop_rbrKnowledgeSoundness (P : Phases I) (S : P.Security) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel I)
      (Seam.done I) S.toDef.witMid (piopExtractor P S) (S.toDef.kSF init impl)
      (piopError P) :=
```

**`piop_rbrKnowledgeSoundness_exists`** (`Compose.lean:181-185`) — *master theorem (existential form)*. The same with the extractor and state function forgotten. Depends on: `piop_rbrKnowledgeSoundness`.

```lean
theorem piop_rbrKnowledgeSoundness_exists (P : Phases I) (S : P.Security) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCase init impl (M3Rel I)
      (Seam.done I) (piopError P) :=
```

### `LeanerVM/Protocol/Spine/Toy.lean`

**`shape`** (`Toy.lean:36-36`) — *test fixture*. One table of height two and width three. Depends on: `Shape`.

```lean
abbrev shape : Shape := ⟨1, fun _ ↦ 1, fun _ ↦ 3⟩
```

**`slice`** (`Toy.lean:42-44`) — *test fixture*. Column `i` is the slice at cells `2i, 2i+1`. Depends on: `Column`.

```lean
def slice (q : Column 3) (c : Col) : Column 1 :=
  ⟨#v[q.values.get ⟨2 * c.2.val, by have h : c.2.val < 3 := c.2.isLt; omega⟩,
      q.values.get ⟨2 * c.2.val + 1, by have h : c.2.val < 3 := c.2.isLt; omega⟩]⟩
```

**`extend`** (`Toy.lean:47-48`) — *test fixture*. The selector of column `i`: `(z, i mod 2, i div 2)`. Depends on: —.

```lean
def extend (c : Col) (z : Vector E 1) : Vector E 3 :=
  #v[z.head, if c.2.val % 2 = 1 then 1 else 0, if c.2.val / 2 = 1 then 1 else 0]
```

**`read_eval`** (`Toy.lean:52-57`) — *test fixture*. The law for the three slices. Depends on: `slice`, `extend`.

```lean
theorem read_eval (q : Column 3) (c : Col) (z : Vector E 1) :
    CMlPolynomialEval.eval₂Mle (slice q c).values (algebraMap K E) z =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) (extend c z) :=
```

**`layout`** (`Toy.lean:60-63`) — *test fixture*. The toy's layout. Depends on: `Layout`.

```lean
def layout : Layout 3 Col (fun _ ↦ 1) where
  read := slice
  extend := extend
```

**`constraint`** (`Toy.lean:66-66`) — *test fixture*. Column 2 is Boolean: `X₂² − X₂`. Depends on: CompPoly `CMvPolynomial`.

```lean
def constraint : CMvPolynomial 3 K := CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2
```

**`flush`** (`Toy.lean:77-78`) — *test fixture*. The one flush: `(X₀, 0, …)`, pushed. Depends on: —.

```lean
def flush : Side × Vector (CMvPolynomial 3 K) 16 :=
  (.push, Vector.ofFn fun k ↦ if k.val = 0 then CMvPolynomial.X 0 else 0)
```

**`boundary`** (`Toy.lean:89-92`) — *test fixture*. The one boundary block: pulls `([1, 1], 0, …)`. Depends on: `BoundaryBlock`.

```lean
def boundary : BoundaryBlock shape where
  κ := 1
  side := .pull
  coords := Vector.ofFn fun k ↦ if k.val = 0 then .known ⟨#v[1, 1]⟩ else .const 0
```

**`toy`** (`Toy.lean:95-111`) — *test fixture*. The toy instance: `d = 2`, column 1 a count column, the public line on column 2 with cells `(input, 0)`, `aux := True`. Depends on: everything above.

```lean
abbrev toy : M3Instance where
  toShape := shape
  Stmt := K
  constraints := fun _ ↦ [constraint]
  flushes := fun _ ↦ [flush]
  d := 2
  counts := fun _ ↦ [1]
  boundary := [boundary]
  μ := 3
  layout := layout
  publicLines := fun v ↦ [⟨⟨0, 2⟩, v, 0, true, by decide⟩]
  aux := fun _ ↦ True
  decAux := fun _ ↦ inferInstance
```

**`honest`** (`Toy.lean:114-114`) — *test fixture*. The honest stack `[1, 1, 1, 1, 1, 0, 0, 0]`. Depends on: `Column`.

```lean
def honest : Column 3 := ⟨#v[1, 1, 1, 1, 1, 0, 0, 0]⟩
```
