## C. Do the statements say what they claim?

### C.1 `M3Holds`, clause by clause, against the pinned specification

```lean
-- LeanerVM/Protocol/Spine/Instance.lean:196-220
def ConstraintsVanish (q : Column I.μ) : Prop :=
  ∀ j, ∀ C ∈ I.constraints j, ∀ x, C.eval (I.row q j x) = 0
def Balanced (q : Column I.μ) : Prop := (I.tuples q .push).Perm (I.tuples q .pull)
def CountsNonzero (q : Column I.μ) : Prop :=
  ∀ j, ∀ i ∈ I.counts j, ∀ x, (I.column q ⟨j, i⟩).values.get x ≠ 0
def PublicLinesHold (input : I.Stmt) (q : Column I.μ) : Prop :=
  ∀ l ∈ I.publicLines input,
    (I.column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩ = l.cell0 ∧
      (I.column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩ = l.cell1
def M3Holds (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Prop :=
  I.ConstraintsVanish q ∧ I.Balanced q ∧ I.CountsNonzero q ∧ I.PublicLinesHold input q ∧ I.aux q
```

`List.Perm` (Mathlib) is the relation "one list is a rearrangement of the other": the same
elements with the same multiplicities, in any order. `CMvPolynomial.eval` (CompPoly
`Multivariate/CMvPolynomial.lean:217`) evaluates a computable multivariate polynomial at a row,
a function from column index to `K`.

| Clause | What it says | Specification at `a386121f` | Agreement |
| --- | --- | --- | --- |
| `ConstraintsVanish` | every constraint polynomial of every table evaluates to `0` on every row `x ∈ {0,1}^{τ_j}` of that table, the row read off the stack | `05-arithmetization.tex:10`: "each a polynomial over `K` of degree at most `d` … required to vanish on every row in `{0,1}^{τ_j}`" | yes. The degree is not in the clause; it is the instance's field `d` with two proofs (`Instance.lean:128-132`). |
| `Balanced` | the list of every pushed tuple is a permutation of the list of every pulled tuple | `:14`: "The bus balances when its pushed tuples and its pulled tuples form the same multiset"; `:47` (Lemma 5.2): "`Π_P = Π_Q` if and only if `P = Q`" | yes: equality of multisets of `K^16`-tuples, counted in `ℕ`. The deployed check compares products of fingerprints (`:30-33`); the spec's Theorem 5.1 (`:37`) makes that a `4·2^μ/|E|` approximation of this clause, which is the bus phase's error to pay. |
| — the tuples | `tuples q s = flushTuples q s ++ boundaryTuples q s`: for every table `j`, every flush of side `s`, every row `x < 2^{τ_j}`, the 16 coordinate polynomials evaluated on the row; then for every boundary block of side `s`, every row `x < 2^κ`, its 16 coordinates (`Instance.lean:174-186`) | `:12`: "Table `T_j` has `n_j` flushes … each is either a push or a pull. Each one of the `m` coordinates in each tuple is a fixed polynomial of degree at most `d` in the table's columns. A few boundary tuples are pushed (resp. pulled) by default"; `:101`: "A block of a `2^κ`-row table holds `2^κ` leaves; the row-`z` leaf is … `c_i(z)` coordinate `i` of the row's tuple"; `:111`: boundary entries "a constant, the index column, a public component, or one committed column" | yes. Every row flushes, including the prover's fill rows (`08-end-to-end-protocol.tex:35-42`, which is why fill blocks are closed walks). `Coord.const / known / committed` is `:111`'s list, with the index column and a public component both `known`. Probed: the side filter, the row ranges, multiplicity (D.1). |
| `CountsNonzero` | every cell of every column listed in `counts j`, for every table, is nonzero | `06-bus-interactions.tex:78`: "All counts are nonzero exactly when their product is. The prover therefore sends that product … by GKR over the stacking of every count column"; `:74`: "Nothing checks the finalize counts" | yes, provided the instance lists exactly the tables' count columns and not the finalize counts (`layout.rs:412-414` per the blueprint's convention *Count tree*). The spine cannot check that; it is `leanIsaInstance`'s. |
| `PublicLinesHold` | for every line the statement names, cell 0 and cell 1 of its column are the line's two values | `08-end-to-end-protocol.tex:29`: "The public input is the first two memory cells `mem[g^0], mem[g^1]`, two 192-bit words (with top limb 0)"; the check `:31` | yes as a relation: with the three leanISA lines of Layer 3 (`mem_0, mem_1` with the words' limbs, `mem_2` with `0, 0`) it says the two cells are the two words with top limb zero. The relation is stronger than the deployed check (a line, not two cells), which is the phase's error to pay (`:33`, `1/|E|`). |
| `aux` | whatever the instance says | `:87-92` "BLAKE2s validity" | not checkable at the spine: see below. |

Against the verifier's accept list (`08-end-to-end-protocol.tex:100`: "the caps, the one bus
root for both sides, the nonzero count root, every sumcheck's rounds and final value, the
public-input line, flock's reduction, and the PCS opening"): the caps are outside by decision
(the blueprint `:556-559`, the adaptor takes admissibility as a hypothesis); the bus root is
`Balanced`; the count root is `CountsNonzero`; the sumchecks establish `ConstraintsVanish`
through the seams' claims; the line is `PublicLinesHold`; Flock is `aux`; the opening is the
ideal oracle. This agrees with the earlier review's table (`docs/reviews/protocol-spine.md:273-279`),
re-checked here against the tex at the pin.

**`M3Rel`** (`Instance.lean:230-231`) is `M3Holds` in ArkLib's shape: the statement is the
public input paired with the empty oracle family, the witness is the stack. Nothing is lost.

**The `aux` field.** `aux : Column μ → Prop` with `decAux : DecidablePred aux` is data of the
instance. The spine constrains it in no way: an instance with `aux := fun _ ↦ True` proves
knowledge of a stack whose BLAKE2s rows may be anything, and one with `aux := fun _ ↦ False`
has an empty relation. So the meaning of `M3Holds I` is exactly as trustworthy as the instance
`I`, and for the leanISA instance the field's meaning is fixed by the adaptor's theorem
`satisfiedBy_witnessOf` (`M3Holds → SatisfiedBy`, not built), which will have to derive
`Blake2sRowsValid` from `aux`. That is the right place: the spine cannot know Flock. What the
spine could do, and does not, is keep the field out of the relation it names "the relation the
verifier establishes" and put it where it is consumed. This is a design remark, not a defect
(section F, *the instance is data the theorems trust*). `decAux` is used by nothing
load-bearing: it makes `M3Holds` decidable for the tests' `#guard`s (section B, proposal 8).

### C.2 `Layout`

```lean
-- LeanerVM/Protocol/Spine/Instance.lean:73-81
structure Layout (μ : ℕ) (ι : Type) (κ : ι → ℕ) where
  read : Column μ → (c : ι) → Column (κ c)
  extend : (c : ι) → Vector E (κ c) → Vector E μ
  read_eval : ∀ (q : Column μ) (c : ι) (z : Vector E (κ c)),
    CMlPolynomialEval.eval₂Mle (read q c).values (algebraMap K E) z =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) (extend c z)
```

`CMlPolynomialEval.eval₂Mle t f z` (CompPoly) is the multilinear extension of the value table
`t` at the point `z`, the table's entries first mapped by the ring homomorphism `f` (here the
inclusion `K → E`, `algebraMap K E`). The law says: reading column `c` and extending it to `z`
gives the stack's extension at `extend c z`, for every stack, column and point.

What a mistaken or dishonest instance can do with it is in D.4, by probe: it can alias columns
(`toyAlias`, a `Layout`, whose relation is empty) and it cannot read anything but the stack
(the law fails at the all-zero and all-one stacks unless `read` depends on `q`). The stronger
statement, that the law **determines** `read` from `extend`, is on paper: for a cube point
`x` of the column, `read_eval` at `z = x` gives `(read q c)[x]`, the extension of a table at a
cube point being the entry, as `q̃(extend c x)`. So an instance's only layout data is
`extend`, and `read` with its law could be replaced by the definition
`read q c := ⟨Vector.ofFn fun x ↦ (q̃ (extend c (bits x))).limb 0⟩` together with the one
proof that this `read` obeys the law for the instance's `extend`, which holds exactly when
every `extend c x` at a cube point reads a `K`-valued combination of cells. The blueprint's
sentence "It is a reading law, not a stacking law: it does not say the columns are disjoint
slices of `q`" (`Instance.lean:71-72`, blueprint `:447-450`) is right and understates: it does
not say the columns are slices at all (an `extend` with a non-Boolean selector reads a
`K`-linear combination of slices).

Who rules aliasing out, and by which theorem: nothing in the spine; for leanISA, the
completeness-side adaptor theorems `m3Holds_stackOf` and `witnessOf_stackOf` (blueprint
`:817-819`), neither built. Until then the only instance whose relation is known to be
inhabited is the toy.

### C.3 The seams, as input and output relations

Each `Seam.x I` is `Seam.of I P` = `{p | P p.1.1 (theStack p.1.2)}` (`Seams.lean:166-167`): a
set of `((statement, oracle family), ())` with the predicate read on the one oracle. The
witness is `Unit` from the commit phase on; the stack is the oracle.

- **`Seam.commit`** = `M3Holds` of the oracle. Output of the commit phase (`sendOracle_relOut
  (M3Rel I)` is definitionally this set, which is why `commitSecurity` typechecks at
  `Compose.lean:67-68`), input of the bus phase. As the bus phase's input relation it is the
  whole of leanVM's arithmetic claim; the bus phase's knowledge soundness must reflect
  `Seam.bus` back into it: every constraint vanishing on the cube (from zerocheck claims at
  `ζ`, the escape charged to its own challenges), balance (from the grand product), counts
  (from the count root). The pass-through cannot (D.3 (a), machine-checked).
- **`Seam.bus`** (`:175-177`): every linear claim holds, every term has total degree `≤ I.d`,
  every column claim holds, the public lines hold, `aux` holds. As the **output** of the bus
  phase it is right that the lines and `aux` are carried untouched. As the **input** of the
  table phase it is quantified over by ArkLib's knowledge soundness for every statement
  (`rbrKnowledgeSoundnessWorstCaseWith`, `∀ stmtIn`, quoted in section D). Two consequences
  the blueprint does not draw:
  1. The degree conjunct is a property of the statement alone. For a statement with a term
     of degree `> I.d` the seam is empty whatever the stack, so `toFun_empty` makes the table
     phase's knowledge state false at the start; if the verifier could accept such a statement
     with a true final check, the state would be true at the end (`toFun_full`) and some
     challenge would have to pay for the flip. Probe D.2 shows a **true** cubic claim on the
     honest toy stack; the sibling dossier `gt-table-pub.md` (section 6, E.1 (a)) exhibits a
     statement on which every round polynomial is identically zero and a degree-blind verifier
     accepts with probability 1. So the table phase's verifier must compute `totalDegree` of
     every term it receives and reject above `I.d`: a guard leanVM's verifier does not have,
     dead in the composition, live in the phase's theorem. Our reading agrees with the sibling's.
  2. The same applies to everything else `Seam.bus` leaves free and the deployed table
     sumcheck fixes: the number of linear claims, the points of the terms, the tables they sit
     on. The sibling dossier establishes this by probe and proposes a `BusOut` in the shape of
     the Rust's `BusVerify` (its section 8, first finding). We agree, and add only that the
     degree conjunct is the smallest instance of the phenomenon and that the type-level fix
     (a subtype of polynomials within the bound, or forms indexed by the instance's own
     constraint and flush lists) removes the guard and the conjunct together.
  For **completeness** the conjunct does what the blueprint says (`:571-574`): the table
  phase's completeness is owed on statements within the bound only. For the **bus phase's
  knowledge soundness** it costs nothing: the bus verifier builds its terms from
  `I.constraints` and `I.flushes`, bounded by `constraints_degree` and `flushes_degree`.
- **`Seam.table`** (`:180-181`): column claims, lines, `aux`. Right for the deployed order
  (`08-end-to-end-protocol.tex:73-85`: table sumcheck, then public input), which is why the
  lines survive this seam and are consumed at the next.
- **`Seam.pub`** (`:184`): column claims and `aux`. The statement is no longer mentioned
  (D.2: the wrong public statement is inside this seam); that is right, the lines have become
  claims.
- **`Seam.flock`** (`:187-188`): column claims and weighted claims. `aux` is consumed here.
  Whether the Flock phase consumes column claims (the eighteen limbs) or passes them all on is
  the Flock dossier's question; the seam admits both.
- **`Seam.done`** (`:191`): `True`. Knowledge soundness with a trivial output relation is
  ArkLib's notion of a *proof*: `toFun_full`'s hypothesis becomes "the verifier can output
  something", that is, accepts (a rejecting run is `failure` in the `OptionT` layer and
  contributes no mass to the event, `Security/Basic.lean:329-342`). So
  `piop_rbrKnowledgeSoundness` reads: on every accepting full transcript the composed state is
  true; the state is `M3Holds` of the message after the commit round; a prover message never
  turns it true; a challenge does with probability at most its declared error. The plain
  reading, "the committed stack satisfies `M3Holds` except with probability the sum of the
  errors", is ArkLib's `rbrKnowledgeSoundness_implies_knowledgeSoundness`
  (`Security/Implications.lean:223-228`), `sorry` at the pin, and existential in the extractor.

**One remark on the oracle the seams are read through.** Every seam reads the stack through
`evalOracle` (`Field.lean:102-106`): a query is a point of `E^μ` and the answer is `q̃` there.
The specification's PCS interface is Definition 3.13 (`03-proving-primitives.tex:112-118`), a
*weighted* claim `⟨W, g⟩ = c` for any MLE-friendly weight, of which an evaluation is the case
`W = eq(r, ·)` (`:117`); and §8.5 says of the opening "This one opening discharges every pooled
claim; there is no separate reduction sumcheck" (`08-end-to-end-protocol.tex:99`). With an
evaluation oracle, a weighted claim (`Seam.flock`'s `WeightedClaim`) can only be checked by a
sumcheck ending in one evaluation query, which is the opening phase the blueprint's Layer 10
adds (`:1112-1113`). An oracle answering weighted queries (query `Weight μ`, answer
`Weight.pair`) would make the opening phase one challenge and one query, as the specification
has it. This is the spine's choice (convention *The oracle*, `:317`) and is examined by the
opening dossier; it is recorded here because `evalOracle` is load-bearing for both master
theorems.

### C.4 What the master theorems are, and what remains

```lean
-- LeanerVM/Protocol/Spine/Compose.lean:162-177
theorem piop_perfectCompleteness (P : Phases I) (C : P.Complete) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I) :=
  C.toDef.complete init impl
theorem piop_rbrKnowledgeSoundness (P : Phases I) (S : P.Security) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel I)
      (Seam.done I) S.toDef.witMid (piopExtractor P S) (S.toDef.kSF init impl)
      (piopError P) :=
  S.toDef.rbr init impl
```

Both are one-line proofs: the composed component's own field. They are composition theorems:
for every instance `I`, every bundle `P` of five phases with the right statement types, and
every proof of the five phases' completeness (resp. security) against the seams, the composed
protocol is complete (resp. round-by-round knowledge sound at the composed error). They say
nothing about leanVM. What remains, in order:

1. An instance: `leanIsaInstance prog s` (blueprint Layer 3). Category B data (layouts,
   separators, count columns, lines), trusted as a transcription and checked by the fixture.
2. Five phase definitions with leanVM's schedules and checks (Layers 6, 7, 8, 9, 10). Built:
   the public-input phase.
3. Their `Complete` and `Security` against the spine's seams. Built: the commit phase's
   (spine) and the public-input phase's. Not provable as the seams stand for the deployed
   table sumcheck (C.3, sibling dossier).
4. A bound on `piopError P` (C.5).
5. The adaptor's four theorems, for non-vacuity (`m3Holds_stackOf`) and for soundness
   (`satisfiedBy_witnessOf`).
6. The plain reading of round-by-round knowledge soundness (ArkLib, admitted), in a form that
   names the extractor if acceptance test 24 is to survive it (C.7).
7. Compilation (Layers 11 to 13).

The headline (`:11-17`) writes `piop_rbrKnowledgeSoundness (I : M3Instance) : for every
prover, leanVmVerifier accepts → except with probability piopError I, the extractor's column q
satisfies M3Holds I input q`. On `main`: there is no `piopError I` (the error is `piopError P`,
a function per challenge with no bound); "except with probability" is the plain form, admitted
upstream; "the extractor's column `q`" is no definition (D.5); and the theorem takes `P` and
`S`, absent from the headline. The sentence "states the two theorems that make it a proof
system for the constraint relation" overstates what is on `main` (finding *the headline
describes theorems that do not exist*).

### C.5 `piopError`

`piopError P := P.toDef.err` (`Compose.lean:149`), and `Def.append` assigns each challenge the
error its component declared (`Component.lean:148`,
`err := Sum.elim D₁.err D₂.err ∘ ChallengeIdx.sumEquiv.symm`). No statement of the spine bounds
it, sums it, or ties it to any parameter of leanVM; the phases declare it, and a phase may
declare `1` (D.3 (b), machine-checked). The blueprint's `piopError_le (hs : s.Admissible prog) :
Σ i, piopError s i ≤ 2 ^ 40 / |E| + flockError` (`:1130`) is stated over a `piopError s` the
spine does not have, and "the interactive error is its sum" (`:318`) is a sentence, not a
theorem. Finding *the declared error is unconstrained*, with the proposal, in section F.

### C.6 The quantification over `σ`, `init`, `impl`

`Component.Complete.complete` and `Security.kSF`, `Security.rbr` are stated for every
`{σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))`
(`Component.lean:84-85, 101-106`). `QueryImpl []ₒ m` (VCVio
`OracleComp/SimSemantics/QueryImpl/Basic.lean:36`) is a function from the queries of the
specification to computations; `[]ₒ` is `PEmpty →ₒ PEmpty` (VCVio `OracleSpec.lean:216`), so
there is exactly one `impl`, never called. `ProbComp σ` is a probabilistic computation with no
failure, so `init` always yields a state. The quantification is therefore without content: for
a deterministic verifier the event in `toFun_full` has probability `1` or `0` whatever `σ`,
`init`, `impl` (this is what `Verifier.GuardedForm.of_probEvent_pos`, `GuardedVerdict.lean:40-45`,
extracts). It is **forced by the upstream library**: ArkLib's `perfectCompleteness` and
`KnowledgeStateFunction` take `init impl`, and its composition theorem needs completeness of
the second component "from every shared state" (`OracleCompleteness.lean:63`,
`h₂ : ∀ s : σ, R₂.perfectCompleteness (pure s) impl rel₂ rel₃`), which is why the fields are
universally quantified rather than instantiated. Cost: the three binders appear in eleven
load-bearing declarations. No workaround short of a leanerVM-side wrapper (section B, proposal
9); retired when ArkLib offers an ambient-free form.

### C.7 `Refinement` and what T4 needs

```lean
-- LeanerVM/Protocol/ToArkLib/Refinement.lean:31-36, 55-57
structure Refinement {Stmt : Type} {W₁ W₂ : Type _} (R : Set (Stmt × W₁))
    (S : Set (Stmt × W₂)) where
  map : Stmt → W₁ → W₂
  map_valid : ∀ x w, (x, w) ∈ R → (x, map x w) ∈ S
theorem map_option_valid {R : Set (Stmt × W₁)} {S : Set (Stmt × W₂)} (f : Refinement R S)
    (x : Stmt) (w? : Option W₁) (h : ∀ w ∈ w?, (x, w) ∈ R) :
    ∀ w' ∈ w?.map (f.map x), (x, w') ∈ S
```

What is transported: validity of one witness slot (an `Option`, the shape of ArkLib's
straight-line extractor's output). Nothing probabilistic is proved in the repository, as the
blueprint says (`:582-586`). "Knowledge transports at the same error" (`:364-366`) is
therefore justified only by the pointwise step. The probabilistic step is, however, three
lines and needs no prover conversion: probe D.7 (`knowledge_transport`) proves it for
ArkLib's `knowledgeSoundnessWith`, by leaving the game alone and applying the map inside its
event; the target witness type may be in any universe (`Refinement`'s two universes are
independent, checked). T4 (`baseVerifier_extractsExecution`, `:1247-1248`) needs exactly this
shape: a bound on the event "the verifier accepts and the mapped extracted witness has no
execution", in the game of `verify_knowledgeSound`, which is not an ArkLib `knowledgeSoundness`
of a relation on `EnsembleWitness` (that would need `WitIn : Type`) but a statement about one
event of one game. The blueprint's "not proved … and has no consumer yet" should say instead
that it is proved in the event form (once the lemma is moved into the repository) and that
Layer 13 is its consumer. What T4 does still wait on is upstream: the plain form of the
round-by-round theorem (`Implications.lean:223-228`, `sorry` at the pin), whose conclusion is
`knowledgeSoundness`, existential in the extractor, so that the named extractor
`piopExtractor` would be lost at that step unless a `With` version is proved.
