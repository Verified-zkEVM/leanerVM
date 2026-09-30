# Dossier: the spine as built (task `code-spine`)

**Object reviewed:** leanerVM `main` at `b435631` — the five spine modules
`LeanerVM/Protocol/Spine/{Instance,Seams,Phase,Compose,Toy}.lean`, the generic modules
`LeanerVM/Protocol/ToArkLib/{Oracles,Component,PassThrough,SendOracle,Refinement,GuardedVerdict,KeepOracles}.lean`,
the statements of `ToArkLib/KnowledgeAppend.lean`, `Protocol/Field.lean` where the spine
unfolds to it, `Protocol/PublicInput.lean` where a probe needed a real phase, and
`tests/LeanerVMTests/Protocol/Spine.lean`; the blueprint's headline, "For zkVM engineers",
conventions, "The spine" with its sketch, Layers 3 and 6 to 13, acceptance tests 24 to 28 and
the interface list; the earlier review `docs/reviews/protocol-spine.md`; the ArkLib, VCVio and
CompPoly definitions the statements unfold to, at the pins ArkLib `dca90385`, CompPoly
`3468b38c`, VCVio `f9dc47d9`; the specification at leanVM `a386121f` (§3 Definition 3.13, §4,
§5, §6, §8).

**Ground moved during the review** (brief §8): the checkout now holds `main` at `144c5aa`
(Lean 4.34.1, all pins moved). Everything here is about `b435631`; every Lean line number is
`git show b435631:<path>`. All seven probes (`P1` to `P6`, with `P3` in three files) were run
and recorded **before** the move, at `b435631` with the old pins; their outputs are in the
appendix. Three probes (`P2Relation`, `P3aSeams`, `P5PassThrough`) use the numeral `(2 : K)`,
which at the old pin is the polynomial `x` (nonzero, not Boolean) and at the new CompPoly pin
is `0`; they must be re-run with `K.ofBits 2` after a rebuild, and the conclusions they support
are marked accordingly. One probe was planned and not written (the read-everything phase,
D.3 (d)); the sibling dossier reaches the same conclusion on paper.

## 0. Summary

**Conclusions.**

1. **No theorem of the spine is wrong for what it states**, every stated theorem is proved with
   the kernel's three standard axioms (probe P1), and `M3Holds` says what the specification's
   accept list says (C.1, clause by clause against the tex at the pin). The repository's tests
   establish non-vacuity of the four checkable clauses by value changes only; the probes add
   the two multiplicity cases (a tuple pushed twice and pulled once; pushed twice and never
   pulled, where a field-summed balance accepts), the side filter, and the row ranges (D.1).
   No defect found in the relation as a definition.
2. **The master theorems are composition theorems and their hypotheses are cheap to meet.**
   `Phases.Security toy` is inhabited by five phases that draw a challenge, check nothing and
   declare error `1` (probe P4, machine-checked, instance-independent); both master theorems
   hold of that protocol. Nothing in the spine bounds `piopError`, and the blueprint's
   `piopError_le` is stated over an argument the spine's `piopError` does not take. A second
   cheap inhabitant, at error `0`, is the zero-round phase whose verifier reads the whole stack
   through the evaluation oracle and decides the input seam itself (on paper, agreeing with the
   sibling dossier). What pins the phases to leanVM's is outside the oracle protocol: a bound
   on the error, the phases' definitions, and Layer 12's `verify_iff_compiled` with its fixture.
3. **The pass-through bus phase has no `Phase.Security`** — the type is empty (probe P5,
   `no_security`), where the test's docstring only asserts it.
4. **The composed extractor's output is the stack only when every phase has no round.** With
   the repository's own public-input phase in the bundle, `piopExtractor … extractOut` has type
   `Unit` and the `rfl` witness of acceptance test 24 is ill-typed (probe P3c); the stack is
   `extractMid` at round 0. No definition "the extracted stack" exists, so the headline's "the
   extractor's column `q`" names nothing. A classical phase extractor would go unnoticed by
   every check and would not matter, since a phase's witness is `Unit` and the stack comes from
   the commit phase's computable extractor alone (D.5).
5. **A layout may alias columns and empty the relation** (probe P2, `toyAlias`, a `Layout`),
   and the reading law determines `read` from `extend` (C.2, on paper). The spine proves
   nothing about an instance beyond that law; only the toy's relation is known inhabited on
   `main`.
6. **`Seam.bus` as an input relation forces guards into the table phase's verifier** that
   leanVM's has not (the degree conjunct at the least; C.3). This agrees with the sibling
   dossier `gt-table-pub.md`, whose `BusOut` redesign we endorse; the smallest fix is a subtype
   of polynomials within the bound.
7. **The audit surface** (B): 70 declarations and 217 code lines (382 with docstrings) for
   perfect completeness; 76 and 248 (432) for knowledge soundness in its existential form; 100
   and 354 (612) for the named form. Proposals that keep every theorem's meaning: delete
   `outputPure` (derivable for every component over the empty oracle, probe P6), derive
   `Layout.read` from `extend`, drop `Weight.mle` from the seam, put the degree bound in a type;
   and read the existential theorem first.
8. **The blueprint states the same objects two or three times, differently** (E.2, fifteen
   rows): the headline's and Layer 10's theorems, Layer 6's `BusOut`, Layer 7's types, Layer
   9's `FlockInterface`, Layer 10's `Weight`/`WeightedClaim`/`leanVmPiop`/`piopError` are
   pre-spine sketches the code does not implement; the text beside them says the spine's
   version is authoritative, the blocks were not rewritten.
9. Two claims of the blueprint about what is *not* proved are wrong in the other direction:
   the probabilistic transport of knowledge along the adaptor is three lines in the event form
   (probe P6, `knowledge_transport`, no prover conversion needed), and `Refinement`'s two
   witness universes are independent (checked).

**Findings by severity** (section F, each with its evidence and proposed change):

- *major*: the declared error is unconstrained — `piop_rbrKnowledgeSoundness` has content only
  with a bound on `piopError`, and the spine has none (proposal: the closed form fixed by the
  spine as `piopError I`, each phase's security demanded at it; or a bound as a field of
  `Phases.Security`).
- *major*: the degree conjunct of `Seam.bus` is a guard the table phase's verifier must run
  (agreeing with the sibling dossier; type-level fix).
- *minor*: the headline describes theorems that do not exist on `main`.
- *minor*: the extracted stack is not a definition; acceptance test 24's witness covers
  zero-round phases only.
- *minor*: `outputPure` is redundant (ArkLib's `Prover.instOutputIsPureEmpty` at the pin);
  `read` is determined by `extend`; `Protocol/Basic.lean` imports the arithmetization outside
  the wall's exceptions.
- *note*: the instance is data the theorems trust; knowledge transport is three lines; two
  dispositions of the earlier review are met only in part.

**Negative results.** Checked and found in order: the five clauses against
`05-arithmetization.tex:10-16, 101, 111`, `06-bus-interactions.tex:74-78`,
`08-end-to-end-protocol.tex:29-33, 100`; the side filter, row ranges and multiplicity of
`Balanced` (probe P2); each seam inhabited and refuted per conjunct (probe P3a); the commit
phase's state function and extractor as documented (probe P3b); axioms of all load-bearing
declarations and computability of the extractor chain (probe P1); the sketch of the spine
against the code, name by name (E.1: matches, with omissions listed); the wall (E.3);
`Seam.done = Set.univ`.

**Not done.** The read-everything phase probe (D.3 (d)); the formal emptiness of
`toyAlias`'s relation (evidence by exhaustive guard over a small range, argument on paper);
`Layout.read` determined by `extend` (on paper); the always-rejecting verifier's exclusion (a
reading of `Security extends Complete`, not a probe).

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

## D. Non-vacuity, by probe

All probes ran against leanerVM `main` at `b435631` (ArkLib `dca90385`, CompPoly `3468b38c`,
VCVio `f9dc47d9`), each under the shared lock. Their full sources and outputs are in the
appendix. "Accepted" below means the file elaborated with exit status 0, so every `#guard`
evaluated to `true` and every `example` and theorem was checked by the kernel.

Library objects used in this section, introduced once:

- **`OracleReduction`** (ArkLib): a pair of an honest prover and a verifier for a fixed message
  schedule (`ProtocolSpec n`: for each of `n` rounds, who speaks and the type of what is sent).
  The verifier may query the input oracles and the prover's messages.
- **`Verifier.GuardedForm`** (ArkLib `Security/CoordinateWiseSpecialSoundness/Guarded.lean:112`):
  the data of a Boolean check and a verdict function, with the proof that the verifier outputs
  the verdict when the check passes and rejects otherwise.
- **`Extractor.RoundByRound`** (ArkLib `Security/RoundByRound.lean:77`): not one function from
  transcripts to witnesses, but a family of intermediate witness types `WitMid m`, one per
  round boundary `m = 0 … n`, with `WitMid 0` the input witness type, a map `extractOut` from
  the output witness to `WitMid n`, and maps `extractMid m : WitMid (m+1) → WitMid m` that
  walk back one round at a time, each seeing the transcript so far.
- **`Verifier.KnowledgeStateFunction`** (ArkLib `RoundByRound.lean:164`): a predicate
  `toFun m stmt transcript witMid` that (`toFun_empty`) is the input relation on the empty
  transcript, (`toFun_next`) cannot be made true by a prover message (if it is true after the
  message on `w`, it was true before on `extractMid w`), and (`toFun_full`) is true on every
  full transcript on which the verifier can output a statement in the output relation.
- **`rbrKnowledgeSoundnessWorstCaseWith`** (ArkLib `RoundByRound.lean:553`): for one named
  extractor and one named knowledge state function, for every input statement, every challenge
  round and every fixed transcript prefix, the probability over the fresh challenge that the
  state goes from false to true is at most the error declared for that challenge.

```lean
-- .lake/packages/Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean:553-568 (ArkLib dca90385)
def rbrKnowledgeSoundnessWorstCaseWith
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ i : pSpec.ChallengeIdx,
  ∀ transcript : Transcript i.1.castSucc pSpec,
    Pr[fun challenge =>
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid
      | $ᵗ (pSpec.Challenge i)] ≤ rbrKnowledgeError i
```

Two facts about this definition drive the results of D.3. The error is any function
`ChallengeIdx → ℝ≥0`: nothing bounds it by one. And the statement bounds a probability by it:
with a declared error of `1` the inequality holds of every state function.

### D.1 `M3Holds` on the toy instance

**What the repository's tests do** (`tests/LeanerVMTests/Protocol/Spine.lean:26-98`, read in
full). The honest stack is accepted at statement `1` (`:26`). Five mutated stacks or statements
fail exactly one clause each, the three other checkable clauses being asserted to hold:
`badConstraint` (`:32-38`), `badBalance` (`:41-47`), `badCount` (`:50-56`), the wrong statement
(`:59-61`), `badLine` (`:65-71`). `badBalanceSum` (`:76-85`) is a stack whose pushed and pulled
first coordinates have the same sum in `K` and are different multisets. The fifth clause, `aux`,
is `True` on the toy and is tested by nothing. The claim of the test's docstring and of
acceptance test 27 ("each of the four checkable clauses failing alone") is met.

**What is missing, and added by probe `P2Relation.lean` (accepted).**

1. *Multiplicity.* Every mutation of the repository changes a **value**; none changes a
   **count**. The toy cannot: its table pushes two tuples and its boundary pulls two, whatever
   the stack. The probe builds two variants of the instance.
   - `toyOnce`: the boundary is one block of height one pulling `(1, 0, …)`. On the honest
     stack the pushed tuples are `(1,0,…), (1,0,…)` and the pulled tuple is `(1,0,…)`: the two
     sides are the same **set** (each tuple of one side occurs in the other, both guards pass)
     and different multisets. Only `Balanced` fails; `M3Holds` fails.
   - `toyNever`: no boundary. The tuple is pushed twice and never pulled. For each of the
     sixteen coordinates the sum over the pushed side equals the sum over the (empty) pulled
     side, `1 + 1 = 0` in characteristic two: a balance summed in the field accepts. Only
     `Balanced` fails; `M3Holds` fails. This is the case the module docstring of
     `Instance.lean` names (`:30-31`, "in characteristic two a tuple pushed twice and never
     pulled would sum to zero") and that no test exercised.
2. *The side filter.* `toySwap` exchanges the two sides (the table's flush pulls, the boundary
   pushes). `flushTuples` and `boundaryTuples` return the tuples on the declared side and none
   on the other (lengths `0, 2` and `2, 0`), and the honest stack satisfies `M3Holds toySwap`.
   The filters `decide (f.1 = s)` and `decide (b.side = s)` are therefore not swapped.
3. *The row ranges.* One tuple per row of the table (`2 ^ τ`) and one per row of a block
   (`2 ^ κ`, also for `κ = 0`).
4. *Which cells `CountsNonzero` ranges over.* Every row of every column listed in `counts`, and
   no other cell: a stack with zeros in column 0, column 2 and the padding cells satisfies the
   clause; a zero in either cell of column 1 fails it.

**Conclusion.** `Balanced` is a multiset equality counted in `ℕ` and the list construction is
right on every case tried. No defect found in the five clauses as definitions.

### D.2 The seams, one by one

Probe `P3aSeams.lean` (accepted). The repository gives the claims no decision procedure; the
probe supplies them by `inferInstanceAs` on the unfolded propositions and states, by `Iff.rfl`,
that the predicates it decides are the seams.

| Seam | Inhabitant (on the honest stack, statement `1`) | Near misses, each rejected |
| --- | --- | --- |
| `Seam.commit` | the honest stack (repository test `:26`, and `Iff.rfl` at `:166-167`) | the repository's five mutations |
| `Seam.bus` | the zerocheck claim of the toy's constraint at the points `(0)` and `(1)` with value `0`, and the column claim "column 0 at the point `(x)` is `1`" | a false linear claim; a **true** claim whose term is cubic; a false column claim; the wrong statement |
| `Seam.table` | the column claim | a false column claim; the wrong statement |
| `Seam.pub` | the column claim | a false column claim. The wrong statement is **inside** the seam: the public seam no longer mentions the statement |
| `Seam.flock` | the column claim and the weighted claim "the weight selecting cell 0 pairs to `1`" | a false weighted claim; a false column claim |
| `Seam.done` | everything | none: `Seam.done toy = Set.univ` (proved in the probe) |

Two further facts the probe establishes, both intended by the design and both worth stating in
the report because a reader of the seam table may assume the opposite.

- **A seam does not imply the relation before it.** On `badConstraint` (column 2 is `[2, 0]`,
  so the constraint `X₂² − X₂` is violated on row 0) the zerocheck claim at the point `(1)` with
  value `0` is true: the extension of the table `[a, 0]` is `(1 − ζ)·a`, zero at `ζ = 1`. So
  `((2, ⟨[zeroAt1], [col0One]⟩), badConstraint)` is in `Seam.bus toy` and `badConstraint` is
  outside `M3Holds toy 2`. This is the zerocheck escape; the bus phase's error must pay for it.
- **A seam does not say which claims are emitted.** `((2, ⟨[], []⟩), badConstraint)` is in
  `Seam.bus toy`.

### D.3 `Phases.Complete` and `Phases.Security`

#### (a) The repository's pass-through phases

`trivPhases` and `trivComplete` (`tests/…/Spine.lean:103-119`) inhabit `Phases toy` and
`Phases.Complete` with five zero-round phases that drop every claim. The test's docstring says
that `Phases.Security` "has no such inhabitant" and gives the reason ("dropping every claim is
… not knowledge sound"), but proves nothing. Probe `P5PassThrough.lean` (accepted;
`#print axioms no_security` gives the three standard axioms) proves it for the bus phase,
where it fails first:

```lean
/-- The reflection hypothesis of `Phase.passThroughSecurity` is false at the bus seam. -/
theorem not_reflects : ¬ ∀ (s : K) (o : ∀ i, TheOracle toy i),
    ((dropAll s, o), ()) ∈ Seam.bus toy → ((s, o), ()) ∈ Seam.commit toy

/-- No `Phase.Security` exists for the pass-through bus phase: not only the repository's
constructor fails, the type is empty. -/
theorem no_security (S : Phase.Security toy (Phase.passThrough toy dropAll) (Seam.commit toy)
    (Seam.bus toy)) : False
```

The proof takes the knowledge state function of `S` at the trivial shared-oracle state, the
statement `2` with the oracle `badConstraint` (outside `M3Holds`, inside the bus seam with no
claim, both by `decide +kernel`), and the empty transcript; the verifier accepts it with
probability one, so `toFun_full` makes the state true at the end, which for a phase with no
round is the beginning, where `toFun_empty` says the state is `M3Holds`. Exactly where the
task expected it to fail: a pass-through bus phase cannot reflect `Seam.bus` back into
`M3Holds`.

#### (b) A cheap inhabitant of `Phases.Security`: five phases that check nothing, at declared error 1

Probe `P4Junk.lean` (accepted; `#print axioms` gives `propext`, `Classical.choice`,
`Quot.sound`).

The phase `wasted f ε` has one round: the verifier draws a challenge in `E`, ignores it, makes
no query, and outputs `f` of its input statement. Its verifier accepts every transcript
(`wPure`, a `Verifier.PureForm`).

- It is perfectly complete against any two seams that `f` carries one into the other
  (`wastedComplete`): the hypothesis of the repository's `Phase.passThroughComplete`.
- With declared error `1` it has a `Phase.Security` against **any** two seams, under that
  completeness hypothesis alone (`wastedSecurity`). The knowledge state function is the input
  seam before the challenge and `True` after it (`wState`, which takes no hypothesis on `f` or
  on the seams); the bound is `Pr[…] ≤ 1` (`w_rbr`).

```lean
-- probes/code-spine/P4Junk.lean
def wState (f : StmtIn → StmtOut) :
    (wVerifier I f).toVerifier.KnowledgeStateFunction init impl relIn relOut
      (wExtractor I (StmtIn := StmtIn)) where
  toFun := fun m stmt _ _ ↦ if m.val = 0 then (stmt, ()) ∈ relIn else True
  toFun_empty := fun _ _ ↦ by simp
  toFun_next := fun m hm ↦ by
    fin_cases m
    exact absurd hm (by decide)
  toFun_full := fun _ _ _ _ ↦ by simp

noncomputable def junkSecurity : junkPhases.Security where
  bus := wastedSecurity toy _ fun _ _ h ↦ ⟨by simp, by simp, by simp, h.2.2.2.1, h.2.2.2.2⟩
  table := wastedSecurity toy _ fun _ _ h ↦ ⟨by simp, h.2.2.2.1, h.2.2.2.2⟩
  pub := wastedSecurity toy _ fun _ _ h ↦ ⟨by simp, h.2.2⟩
  flock := wastedSecurity toy _ fun _ _ _ ↦ ⟨by simp, by simp⟩
  opening := wastedSecurity toy _ fun _ _ _ ↦ trivial

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier junkPhases).toVerifier.rbrKnowledgeSoundnessWorstCase init impl (M3Rel toy)
      (Seam.done toy) (piopError junkPhases) :=
  piop_rbrKnowledgeSoundness_exists junkPhases junkSecurity init impl

theorem piopError_junk (i : junkPhases.toDef.pSpec.ChallengeIdx) : piopError junkPhases i = 1
```

So `Phases.Security toy` is inhabited, both master theorems apply to `junkPhases`, and the
protocol they are about commits to a stack and accepts it whatever it is. The knowledge theorem
is true of it because its error is `1` at each of its five challenges
(`piopError_junk`). Nothing in the construction uses the toy: the same five phases inhabit
`Phases.Security I` for every instance `I`.

**Reading.** `piop_rbrKnowledgeSoundness` has content only together with a bound on
`piopError P`. No such bound is stated in the spine, and the blueprint's `piopError_le`
(Layer 10, `:1130`) is stated over `(s : Sizes)`, a parameter the spine's `piopError P` does
not have (finding *the declared error is unconstrained*).

#### (c) An always-rejecting verifier

A verifier that always rejects is round-by-round knowledge sound at error zero (the state "the
input relation holds" never has to become true). It is excluded from `Phases.Security` by the
structure itself:

```lean
-- LeanerVM/Protocol/ToArkLib/Component.lean:90-93
structure Security (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    extends Complete D relIn relOut where
```

`Complete.complete` is perfect completeness on the input seam, so on any statement and stack in
the input seam the verifier accepts the honest run with probability one. `Seam.commit toy` is
inhabited (D.1). This is a reading of the definitions, not a probe: a machine-checked
refutation would need the probability of an event under a failing `OptionT` computation, which
adds nothing to the argument.

The exclusion is only as strong as the input seam is inhabited: on an instance whose relation
is empty (D.4 exhibits one) perfect completeness is vacuous and an always-rejecting bundle is a
`Phases.Security`.

#### (d) A phase that reads the whole stack

In the ideal oracle model the verifier may query the stack's extension at any point of `E^μ`,
any number of times: neither ArkLib's `OracleVerifier` nor the spine counts queries. At the
`2^μ` points of the cube the answers are the cells. `M3Holds` and every claim's `Holds` are
decidable. So for every seam there is a zero-round phase whose verifier reads the `2^μ` cells,
decides the **input** seam itself, rejects if it fails and otherwise outputs any statement in
the output seam (no claim at all will do). It is perfectly complete, and knowledge sound at
error zero: acceptance implies the input seam. Five of them inhabit `Phases.Security I` for
every `I`, with `piopError = 0` (there is no challenge).

This is **not machine-checked** here (the probe was not written: it needs an oracle-querying
verifier and the unfolding of `2^μ` simulated queries, and the machine's memory limit was
reached during this session). The sibling dossier `gt-table-pub.md` (section 6, E.4 item 6)
reaches the same conclusion on paper; the two readings agree. What would verify it: a probe on
an instance with `μ = 0` (one cell, one query), whose verifier is
`do let v ← query; if decide (relIn s ⟨#v[v.limb 0]⟩) then pure (f s) else failure`.

**What (b) and (d) mean together.** The hypotheses of the master theorems are satisfiable, for
every instance, by protocols that are not leanVM's: one with no check and error 1, one with no
interaction, error 0 and a verifier as expensive as the prover. This is expected of a
composition theorem. What pins the phases to leanVM's is outside the spine and, today, outside
the repository:

1. a bound on `piopError P` (excludes (b));
2. the phases' *definitions* being leanVM's, which no theorem of the oracle protocol states; it
   is Layer 12's `verify_iff_compiled`, together with the fixture "a proof of the pinned Rust
   prover is accepted by `verify`", that ties the composed verifier to the deployed one
   (excludes (d), whose transcript is empty);
3. review of each phase's `Def` against the specification.

### D.4 What a layout can do

Probe `P2Relation.lean`, last section (accepted).

`toyAlias` is the toy with the layout that reads **every** column from cells `0, 1`
(`extend c z = (z, 0, 0)` for every `c`). The reading law `read_eval` holds of it
(`alias_read_eval`, proved by the same `simp` call as the toy's), so it is a `Layout` and
`toyAlias` is an `M3Instance`. On it the three columns are one column, and `M3Holds` asks for
incompatible things: balance forces cells `0, 1` to be `1, 1` and the public line on column 2
forces cell 1 to be `0`. The honest stack fails; the exhaustive guard over cells `0, 1` and the
statement in `{0, 1, 2}` finds no satisfying stack. That the relation is empty for **every**
stack and statement is the two-line argument above, on paper; the guard is evidence, not a
proof.

Consequences, for the report:

- The master theorems hold of `toyAlias` (they hold of every instance). Completeness is then
  vacuous and knowledge soundness says that every accepting prover has been lucky.
- A layout **cannot ignore the stack**. This is a consequence of the law, on paper: if
  `read q c` did not depend on `q`, the law at the all-zero stack and at the all-one stack
  would give `0 = 1`, since the extension of a constant table is that constant at every point.
  More precisely the law **determines `read` from `extend`**: on a cube point `x` of the
  column, `(read q c)[x]` is the stack's extension at `extend c x`, and an extension at a cube
  point is the cell. So `read` is redundant data (proposal in section B), and the only freedom
  of an instance is `extend`.
- What a wrong `extend` costs is **completeness and faithfulness, never soundness** of the Lean
  chain. If the layout aliases or mixes columns, `M3Holds I` is a relation on the aliased
  columns; the adaptor's soundness lemma `satisfiedBy_witnessOf` (`M3Holds → SatisfiedBy`) is
  then a theorem about that instance and, if it is proved, the chain to `ValidExecution` is
  intact. What breaks is `m3Holds_stackOf` and `witnessOf_stackOf` (no stack packs distinct
  columns into the same cells), and the agreement with the deployed layout (the Lean verifier
  rejects the Rust prover's proofs).
- **Who rules such instances out.** Not the spine. For leanISA: `witnessOf_stackOf` and
  `m3Holds_stackOf` (blueprint Layer 3, not built) for non-vacuity, and the transcription of
  `witness.rs:67-101` with Layer 12's fixture for faithfulness. Until they exist, no statement
  on `main` says that the relation of any instance other than the toy is inhabited.

### D.5 The extractor

**Is anything marked `noncomputable`?** Probe `P1Axioms.lean`: `Lean.isNoncomputable` is
`false` for `piopExtractor`, `commitExtractor`, `Component.sendExtractor`,
`Phases.Security.toDef`, `Component.Security.append`, ArkLib's `Extractor.RoundByRound.append`,
`Component.passThroughExtractor`, `PublicInput.extractor` and `publicInputSecurity`. It is
`true` for `publicInputPhase` only (its error is a real number), as the blueprint says (`:1049`).

**Does `#print axioms` mean anything here?** No. It reports `propext, Classical.choice,
Quot.sound` for `piopExtractor`, for `commitExtractor` and for ArkLib's
`Extractor.RoundByRound.append`, all three computable definitions, because the proofs inside
them (the casts between witness types) use classical lemmas. `Classical.choice` in the axiom
list of a definition does not say that its **data** was chosen classically. The blueprint does
not claim otherwise; the earlier review's validation paragraph lists axioms and should not be
read as evidence of computability.

**Does the repository's test prove that the extractor returns the committed stack?** Only for
phases with no round. The test (`tests/…/Spine.lean:157-159`) is

```lean
example (S : trivPhases.Security) :
    (piopExtractor trivPhases S).extractOut ((1 : K), fun i : Fin 0 ↦ i.elim0)
      honestFullTranscript () = honest := rfl
```

It is true for the reason ArkLib's `append` gives (`Append/StateFunction.lean:129-139`): when
the second component has no round, the composed `extractOut` is the first component's applied
to the second's. With five zero-round phases the composed `extractOut` is the commit phase's,
which returns the first message. As soon as one phase has a round, the composed `extractOut`
is the **last** such phase's, and its value lives in that phase's last intermediate witness
type. Probe `P3cExtractor.lean`, with the repository's own `publicInputPhase` in the bundle and
four pass-throughs:

```lean
-- accepted
example : (realPubSecurity Sb St Sf So).toDef.witMid (Fin.last 3) = Unit := rfl
example : (realPubSecurity Sb St Sf So).toDef.witMid 0 = Column 3 := rfl
example (s : K) (tr : …Transcript (Fin.succ ⟨0, _⟩)) (w : …witMid (Fin.succ ⟨0, _⟩)) :
    (piopExtractor realPub (realPubSecurity Sb St Sf So)).extractMid ⟨0, _⟩
      (s, fun i : Fin 0 ↦ i.elim0) tr w = (tr ⟨0, _⟩ : Column 3) := rfl
-- rejected, as expected: the test's statement with this bundle
example (tr : realPub.toDef.pSpec.FullTranscript) :
    (piopExtractor realPub (realPubSecurity Sb St Sf So)).extractOut
      ((1 : K), fun i : Fin 0 ↦ i.elim0) tr () = honest := rfl
```

```text
P3cExtractor.lean:58:49: error: Type mismatch
  honest
has type
  Column 3
but is expected to have type
  (realPubSecurity Sb St Sf So).toDef.witMid (Fin.last realPub.toDef.n)
```

So for leanVM's phases "`piopExtractor … extractOut` returns the stack" is not a false
statement but an ill-typed one. The stack is what the composed extractor returns **at round
0**, by its `extractMid` at the commit round, and there it is the transcript's first message
whatever it is handed (third example). The spine defines no function "the stack extracted from
a full transcript" (the composite of `extractOut` and the `extractMid`s down to round 0); the
statement "the extractor's column `q` satisfies `M3Holds`" of the blueprint's headline is
therefore not a statement about any definition of the repository (finding *the extracted stack
is not a definition*).

**Could a phase's `Security` supply an extractor defined by `Classical.choice` without anything
noticing?** Yes as to the mechanism, and it would not matter as to the result.

- *Mechanism.* `Component.Security.extractor` is a field of type `Extractor.RoundByRound …`.
  Lean's types do not record computability. A phase author can write
  `noncomputable def fooSecurity : Phase.Security …` with a classical `extractMid`;
  `Phases.Security.toDef`, `piopExtractor` and both theorems accept it, `piopExtractor` itself
  stays computable (it is a projection of its argument), `#print axioms` does not change, and
  the repository's checks (`audit-lean.sh` forbids `axiom`, `sorry`, `admit`, `unsafe`,
  `native_decide`, per `AGENTS.md`) do not forbid `noncomputable`: `publicInputPhase` is
  already `noncomputable`, legitimately. ArkLib itself ships such an extractor,
  `Extractor.RoundByRoundOneShot.toRoundByRoundOfRel` (`RoundByRound.lean:118-123`,
  `if h : ∃ v, (stmtIn, v) ∈ relIn then h.choose else witIn`). Acceptance test 24 is enforced
  by review only.
- *Result.* From the commit phase on, a phase's input and output witness types are `Unit`
  (`Phase.Def`, `Phase.lean:37-38`), and `eqIn` forces its `WitMid 0` to be `Unit`. Whatever a
  phase's extractor does, at the seam it hands `()` to the phase before it. The stack comes
  from the commit phase's extractor alone, which is the spine's, is computable, and reads the
  message. A classical phase extractor cannot produce a stack. The risk acceptance test 24
  guards against (a witness chosen because one exists) is excluded by the **design** "the
  oracle is the witness", not by the test.

### D.6 The commit phase's security

Probe `P3bCommit.lean` (accepted), every statement by `Iff.rfl` or `rfl`:

```lean
-- Before the message: M3Holds of the candidate witness.
example (s : K) (o : ∀ i, NoOracle i) (w : Column 3) :
    ((commitSecurity toy).kSF init impl).toFun 0 (s, o) default w ↔ M3Holds toy s w := Iff.rfl
-- After the message: M3Holds of the message, whatever the candidate witness.
example (s : K) (o : ∀ i, NoOracle i) (tr : (commitSpec toy).FullTranscript) (w : Column 3) :
    ((commitSecurity toy).kSF init impl).toFun (Fin.last 1) (s, o) tr w ↔
      M3Holds toy s (tr 0) := Iff.rfl
-- The extractor: both maps return the message.
example … : (commitExtractor toy).extractOut (s, o) tr () = tr 0 := rfl
example … : (commitExtractor toy).extractMid 0 (s, o) tr w = tr 0 := rfl
```

The state function says what the docstring says (`SendOracle.lean:143-144`). Error zero is
right: the phase has no challenge (`sendOracle_rbr` is the elimination of an empty index type),
so its error function is the empty function and the `0` written in `sendOracle` (`:65`) is
never applied. The extractor is "read the message".

### D.7 Three facts behind sections B and C.7

Probe `P6Surface.lean` (accepted; both theorems with the three standard axioms).

1. `outputPure_of_def`: for every `Component.Def` whatsoever, `D.red.prover.OutputIsPure`
   holds, because the shared oracle specification is empty (`[]ₒ`) and a computation with no
   possible query is its pure result. ArkLib has this at the pin as the instance
   `Prover.instOutputIsPureEmpty` (`Composition/Sequential/NoAmbient.lean:39-42`), in a module
   the spine does not import. The field `Component.Complete.outputPure` is therefore
   redundant (section B).
2. `@Refinement : {Stmt : Type} → {W₁ : Type u_1} → {W₂ : Type u_2} → …`: the two witness
   universes are independent, so a refinement from the stack (`Type`) to Clean's
   `EnsembleWitness` (`Type 1`) can be formed, as the blueprint's ladder needs (`:364-369`).
   Checked by `#check` and by an example from `ℕ` to a structure in `Type 1`.
3. `knowledge_transport`: if a verifier is knowledge sound for `R` with a named straight-line
   extractor at error `ε` (ArkLib's `knowledgeSoundnessWith`), then, for the same provers and
   the same extractor, the probability that the verifier accepts and the extracted witness,
   mapped by a refinement `R → S`, is invalid for `S` is at most `ε`. Three lines: the event
   is monotone (`probEvent_mono`) and `map_valid` is the pointwise step. No prover conversion
   and no `Nonempty` hypothesis: the game is not changed, the map is applied inside its event.
   This is the probabilistic transport the blueprint says is not proved (`:582-586`), in the
   form Layer 13 needs (section C.7).

## B. The audit surface, measured

### B.1 Method

"Load-bearing" is taken literally: a declaration is counted when the **statement** of a master
theorem mentions it or unfolds to it, transitively, down to library objects. Three sets:

- **C**: what `piop_perfectCompleteness` unfolds to (`Compose.lean:162-164`): `Phases`,
  `Phases.Complete` (so `Phase.Def`, `Phase.Complete`, `Component.Def`, `Component.Complete`),
  `leanVmPiop` (so `Phases.toDef`, `Def.append`, `commitDef`, the send-oracle reduction),
  `M3Rel` (so `M3Holds` and everything under it), the six seams (so every claim and its
  `Holds`), `TheOracle` and the evaluation oracle.
- **Kx**: what `piop_rbrKnowledgeSoundness_exists` adds (`:181-184`): `Phases.Security`,
  `Phase.Security`, `Component.Security`, `leanVmVerifier`, `piopError`.
- **K**: what `piop_rbrKnowledgeSoundness` adds by naming its extractor and state function
  (`:172-176`, `S.toDef.witMid`, `piopExtractor P S`, `S.toDef.kSF init impl`): the
  composition of securities (`Security.append`, `Complete.append` for its `guarded`,
  `guardedAppend`, `stateFunctionOfEq`), the ported state-function append
  (`KnowledgeAppend.state`, `left`, `right`, `Witness`, the two witness lemmas,
  `appendGuarded`) and the commit phase's security (`commitSecurity`, `commitComplete`,
  `commitExtractor`, `sendOracleSecurity`, `sendOracleComplete`, `sendVerifierPure`,
  `sendExtractor`, `sendWitMid`, `sendStateFunction`, `sendOracle_relOut`).

Counting rule: a declaration's lines from its head to the end of its data body, excluding blank
lines, comment-only lines and, for definitions, proof fields (`complete`, `rbr`,
`toFun_empty/next/full`, `verify_eq`, …); "with docstrings" adds the docstring block above it
and the field docstrings inside it. Proof bodies of theorems are never counted. The script is
`probes/code-spine/surface.py`, which reads every file with `git show b435631:` and finds each
declaration by name; its output is reproduced below. Structures' field docstrings are counted
as docstrings, so `M3Instance` is 14 lines of code and 31 with its docstrings.

### B.2 The count

```text
C    2   6  Field.lean             67-69   structure Column
C    5   6  Field.lean             86-90   def limbsEquiv
C    1   2  Field.lean             93-93   instance instSampleableTypeE
C    5   7  Field.lean            102-106  instance evalOracle
C    1   2  Oracles.lean           26-26   abbrev NoOracle
C    1   2  Oracles.lean           29-29   abbrev OneOracle
C    4   5  Instance.lean          51-54   inductive Side
C    4   8  Instance.lean          57-63   structure Shape
C    1   2  Instance.lean          66-66   abbrev Shape.ColumnId
C    6  14  Instance.lean          73-81   structure Layout
C    4   7  Instance.lean          86-89   inductive Coord
C    4   8  Instance.lean          92-98   structure BoundaryBlock
C    6  15  Instance.lean         102-114  structure PublicLine
C   14  31  Instance.lean         119-148  structure M3Instance
C    1   1  Instance.lean         150-150  attribute [instance] M3Instance.decAux
C    1   2  Instance.lean         157-157  abbrev κ
C    1   2  Instance.lean         160-160  def column
C    2   3  Instance.lean         163-164  def row
C    4   5  Instance.lean         167-170  def coordCell
C    4   6  Instance.lean         174-177  def flushTuples
C    3   4  Instance.lean         180-182  def boundaryTuples
C    2   3  Instance.lean         185-186  def tuples
C    2   3  Instance.lean         197-198  def ConstraintsVanish
C    1   2  Instance.lean         201-201  def Balanced
C    2   3  Instance.lean         204-205  def CountsNonzero
C    4   5  Instance.lean         208-211  def PublicLinesHold
C    2   4  Instance.lean         219-220  def M3Holds
C    1   2  Instance.lean         226-226  abbrev TheOracle
C    2   4  Instance.lean         230-231  def M3Rel
C    4   8  Seams.lean             57-63   structure ColumnClaim
C    2   3  Seams.lean             66-67   def ColumnClaim.Holds
C    5  11  Seams.lean             71-79   structure VirtualTerm
C    3   4  Seams.lean             82-84   def VirtualTerm.table
C    2   3  Seams.lean             87-88   def VirtualTerm.eval
C    3   6  Seams.lean             91-95   structure LinearClaim
C    2   3  Seams.lean             98-99   def LinearClaim.Holds
C    4   9  Seams.lean            103-109  structure Weight
C    2   3  Seams.lean            112-113  def Weight.pair
C    3   6  Seams.lean            116-120  structure WeightedClaim
C    2   3  Seams.lean            123-124  def WeightedClaim.Holds
C    3   7  Seams.lean            130-134  structure BusOut
C    2   4  Seams.lean            137-139  structure TableOut
C    2   4  Seams.lean            142-144  structure PubOut
C    3   6  Seams.lean            147-151  structure FlockOut
C    1   2  Seams.lean            159-159  abbrev theStack
C    2   3  Seams.lean            166-167  def of
C    1   3  Seams.lean            171-171  def commit
C    3   5  Seams.lean            175-177  def bus
C    2   3  Seams.lean            180-181  def table
C    1   2  Seams.lean            184-184  def pub
C    2   3  Seams.lean            187-188  def flock
C    1   2  Seams.lean            191-191  def done
C    9  17  Component.lean         52-66   structure Def
C    1   1  Component.lean         68-68   attribute [instance] Def.msgOracle
C    7  12  Component.lean         76-85   structure Complete
C    6   7  Component.lean        143-148  def Def.append
Kx  12  20  Component.lean         90-106  structure Security
K    8  13  Component.lean        110-120  def stateFunctionOfEq
K    4   5  Component.lean        156-159  def guardedAppend
K    4   9  Component.lean        162-169  def Complete.append
K    8  14  Component.lean        174-184  def Security.append
K    2   3  KnowledgeAppend.lean   55-56   abbrev Witness
K    3   5  KnowledgeAppend.lean   60-62   theorem witness_left
K    3   5  KnowledgeAppend.lean   66-68   theorem witness_right
K    5   6  KnowledgeAppend.lean   71-75   def left
K    5   6  KnowledgeAppend.lean   78-82   def right
K   15  16  KnowledgeAppend.lean  182-196  def state
K    5  17  KnowledgeAppend.lean  474-488  def appendGuarded
C    2   3  SendOracle.lean        38-39   def sendSpec
C    6   7  SendOracle.lean        42-47   def sendProver
C    2   5  SendOracle.lean        50-53   def sendEmbedding
C    3   4  SendOracle.lean        56-58   def sendVerifier
C    5   6  SendOracle.lean        61-65   def sendOracle
K    3   5  SendOracle.lean        71-73   def sendOracle_relOut
K    2   4  SendOracle.lean       101-103  def sendVerifierPure
K    4   6  SendOracle.lean       121-125  def sendOracleComplete
K    1   2  SendOracle.lean       130-130  abbrev sendWitMid
K    5   7  SendOracle.lean       134-138  def sendExtractor
K    5  19  SendOracle.lean       145-161  def sendStateFunction
K    5   7  SendOracle.lean       172-177  def sendOracleSecurity
C    2   3  Phase.lean             37-38   abbrev Def
C    4   5  Phase.lean             41-44   abbrev Complete
Kx   4   5  Phase.lean             47-50   abbrev Security
C    1   2  Compose.lean           51-51   abbrev commitSpec
C    2   4  Compose.lean           55-56   abbrev commitDef
C    6  13  Compose.lean           73-84   structure Phases where
C    3   4  Compose.lean           89-91   def Phases.toDef
C    6  12  Compose.lean           94-104  structure Phases.Complete
C    3   4  Compose.lean          134-136  def leanVmPiop
C    4   6  Compose.lean          162-165  theorem piop_perfectCompleteness
Kx   6  12  Compose.lean          113-123  structure Phases.Security
Kx   3   4  Compose.lean          139-141  def leanVmVerifier
Kx   1   2  Compose.lean          149-149  def piopError
Kx   5   7  Compose.lean          181-185  theorem piop_rbrKnowledgeSoundness_exists
K    1   2  Compose.lean           59-59   abbrev commitExtractor
K    2   4  Compose.lean           63-64   def commitComplete
K    2   3  Compose.lean           67-68   def commitSecurity
K    4   5  Compose.lean          126-129  def Phases.Security.toDef
K    4   6  Compose.lean          153-156  def piopExtractor
K    6  11  Compose.lean          172-177  theorem piop_rbrKnowledgeSoundness

per file: code lines C / Kx / K ; all lines with docstrings
Field.lean               13    0    0     21
Oracles.lean              2    0    0      4
Instance.lean            75    0    0    139
Seams.lean               55    0    0    103
Component.lean           23   12   24     98
KnowledgeAppend.lean      0    0   38     58
SendOracle.lean          18    0   25     75
Phase.lean                6    4    0     13
Compose.lean             25   15   19    101

completeness theorem (C):                   code 217, with docstrings 382, declarations 70
knowledge theorem, existential form (C+Kx): code 248, with docstrings 432, declarations 76
knowledge theorem, With form (C+Kx+K):      code 354, with docstrings 612, declarations 100
```

In words. To read **what perfect completeness says**, an auditor reads 70 declarations,
217 lines of Lean (382 with their docstrings): 75 in `Instance.lean` (the instance and the
relation), 55 in `Seams.lean` (claims and seams), 25 in `Compose.lean`, 23 in
`Component.lean`, 18 in `SendOracle.lean` (the commit reduction), 13 in `Field.lean`, 6 in
`Phase.lean`, 2 in `Oracles.lean`. **Knowledge soundness in its existential form** adds 6
declarations and 31 lines (the `Security` structures, the verifier, the error). **Knowledge
soundness for the named extractor** adds 24 declarations and 106 lines, of which 38 are the
ported state-function append and 25 the commit phase's security data. The whole `With` form
is 100 declarations, 354 lines, 612 with docstrings.

The library objects the statements unfold to, by revision `dca90385` (ArkLib), `3468b38c`
(CompPoly), `f9dc47d9` (VCVio), not counted line by line:

- ArkLib: `ProtocolSpec`, `Direction`, `ChallengeIdx`, `MessageIdx`, `Transcript`,
  `FullTranscript`, `ProtocolSpec.append` (`++ₚ`) and `ChallengeIdx.sumEquiv`;
  `OracleInterface`; `Prover`, `OracleProver`, `Verifier`, `OracleVerifier`,
  `OracleOutputEmbedding`, `OracleVerifier.toVerifier`, `Reduction`, `OracleReduction`,
  `OracleReduction.append`, `Verifier.append`; `Prover.OutputIsPure`, `Verifier.PureForm`,
  `Verifier.GuardedForm`, `GuardedForm.append`, `PureForm.toGuardedForm`;
  `Reduction.completeness`, `perfectCompleteness`, `OracleReduction.perfectCompleteness`;
  `Extractor.RoundByRound`, `Extractor.RoundByRound.append`, `Verifier.KnowledgeStateFunction`,
  `rbrKnowledgeSoundnessWorstCase`, `rbrKnowledgeSoundnessWorstCaseWith`; `Verifier.run`,
  `Prover.run`, `Reduction.run` (through `perfectCompleteness`); `challengeQueryImpl`,
  `QueryImpl.addLift`.
- VCVio: `OracleComp`, `OracleSpec`, `[]ₒ` (`emptySpec`), `QueryImpl`, `simulateQ`,
  `ProbComp`, `OptionT`, `Pr[· | ·]` (`probEvent`), `$ᵗ` (`uniformSample`), `SampleableType`,
  `StateT`.
- CompPoly: `CMlPolynomialEval`, `evalMle`, `eval₂Mle`, `CMvPolynomial`, `CMvPolynomial.eval`,
  `totalDegree`, `BF64`, `BF64.Ext3`, `Extension.Ext.ofVector`, `Ext.coeffs`, `algebraMap K E`
  (through Mathlib), `Vector`.
- Mathlib: `List.Perm`, `Set`, `Finset.sum` (in `Weight.pair`), `NNReal`, `ENNReal`.

The earlier review counted "306 statement lines … about 400 lines" for the whole of the
spine's ten files (`docs/reviews/protocol-spine.md:426-448`), every declaration included. The
count here is smaller because it keeps to what the two statements unfold to and larger in the
`With` form than an auditor of the existential form needs.

### B.3 Proposals to reduce it

Each: what is removed, what it costs, whether any statement changes. Lines are code lines of
B.2.

1. **State the master knowledge theorem in the existential form and keep the named form as a
   lemma.** Removes from the reading list the 24 declarations of class K (106 lines): the
   composition of securities, the ported append, the commit phase's data. Costs: the named
   extractor leaves the theorem's statement; acceptance test 24 then rests on the lemma
   `piop_rbrKnowledgeSoundness` (kept) and on `piopExtractedStack_eq` (section F). Changes no
   statement; it changes which one is called the master theorem. Not recommended if the named
   extractor is what T4 must carry through Fiat–Shamir; recommended as the *reading order*
   (the existential theorem first, the named one as its refinement).
2. **Delete `Component.Complete.outputPure`** (2 lines, plus one line in every phase and in
   `Complete.append`): derivable for every component (D.7, ArkLib's
   `Prover.instOutputIsPureEmpty` at the pin). Costs one import (`NoAmbient`) or a four-line
   restatement. Changes no statement: `Complete` loses a field every instance discharges by
   `rfl`.
3. **Merge `TableOut` and `PubOut`** (4 lines, two structures that are both `columns : List
   (ColumnClaim I)`; `FlockOut` is `TableOut` plus `weighted`). Replace by one `Pool I` with
   `columns` and `weighted`, and let each seam say which list is empty where it must be
   (`Seam.table`: `weighted = []`). Costs: the statement types of three phases become the
   same, so a phase in the wrong slot is caught by its seam proof, not by its type; the
   docstrings' "column claims, now with the public words' claims" become a comment on the seam.
   Changes the statements of `Seam.table`, `Seam.pub` (one conjunct each) and the fields of
   `Phases`. Recommended only if the sibling dossier's `BusOut` redesign is adopted, so that the
   statement types are revisited once.
4. **Derive `Layout.read` from `extend`** (C.2; `read` and `read_eval` are 6 of `Layout`'s 6
   lines, replaced by one law on `extend`). Costs: a lemma "the extension at a cube point is
   the entry" (CompPoly has it as `eval_mle_eq_eval`, cited in `Field.lean:50`) and, for the
   toy, `slice` becomes a theorem. Changes the definition of `column` and hence of every
   clause, definitionally: no statement's meaning changes.
5. **Fold `Phase.Def/Complete/Security`** (10 lines): three abbreviations of `Component.*`
   at `TheOracle I` and `Unit`; `Phase.passThrough*` likewise. A phase author writes
   `Component.Def I.Stmt (TheOracle I) Unit …` once. Costs: longer signatures in `Phases`
   (five fields). Changes no statement. Marginal; the abbreviations are the documented
   interface and cost 13 lines with docstrings.
6. **Drop `Weight.mle` and `mle_eq`** (2 of `Weight`'s 4 lines): the seam never uses `mle`
   (`WeightedClaim.Holds` is `Weight.pair`, the cube sum). `mle` is the verifier's evaluator
   for the opening phase, a property of the *phase*, not of the claim's truth. Costs: the
   opening phase must carry the evaluator itself (as a field of its `Def`, or by requiring
   `Weight` to be `MLE-friendly` there). Changes the statement of `Seam.flock` by removing a
   field nobody reads there. Recommended: it also removes the temptation to prove the seam by
   `mle` rather than by the cube sum.
7. **`M3Instance.d` with its two proof fields** (3 lines) could be replaced by a subtype of
   polynomials on `constraints` and `flushes` (section F, the degree finding): the two
   proof fields go, `Seam.bus` loses a conjunct, the table verifier loses a guard. Changes the
   statements of `M3Instance` and `Seam.bus`, and of `VirtualTerm`.
8. **Drop `decAux`** from `M3Instance` (2 lines with the attribute): decidability of `aux` is
   used by nothing load-bearing; the `Decidable` instances for `M3Holds` serve the tests.
   Costs: the tests declare `instance : DecidablePred toy.aux` locally. Changes the statement
   of `M3Instance`. Weak: an instance that cannot decide its own `aux` is a smell, and the
   read-everything phase (D.3 (d)) needs it; keep unless the field list is revisited.
9. **The `{σ} init impl` binders** (eleven declarations): forced by ArkLib (C.6). A wrapper
   `Phase.Complete'` at `σ := Unit` would not compose (ArkLib's append needs every `s : σ`).
   Not removable at this pin.
10. **`sendOracle_relOut`** (3 lines) is `Seam.commit` under another name, needed because the
    generic send-oracle component is stated for any relation; `commitComplete`'s type
    ascription is what makes the two coincide. Keep; note in `Compose.lean` that the
    coincidence is definitional, so an auditor need not read `sendOracle_relOut`.
11. **`sendStateFunction`'s data is in the statement** (5 lines) only through the named form
    (K). If proposal 1 is taken it leaves the surface.

What is **not** proposed: removing `Phases.Complete` in favour of `Phases.Security`
(`Security extends Complete`, and completeness is landed before security per convention
*Holes*); removing `piop_rbrKnowledgeSoundness_exists` (it is the smaller statement).

Net effect of proposals 2, 4, 6 and 7, all of which keep the theorems' meaning: about 15
code lines and two proof obligations per phase (`outputPure`, the degree of its terms) off
the surface, and one guard out of the table phase's verifier.

## E. Conformance with the blueprint

All blueprint lines are those of `docs/roadmap/protocol-blueprint.md` at `b435631`; all Lean
lines those of `main` at `b435631`.

### E.1 The Lean sketch (`:442-554`) against the code, declaration by declaration

The sketch is a compressed transcription of the code and matches it in every name, field and
signature it gives, with the following differences (none changes a statement):

| Sketch | Code | Difference |
| --- | --- | --- |
| `:445` `structure Shape where (ntab : ℕ) (τ width : Fin ntab → ℕ)` | `Instance.lean:57-63` | none (compressed) |
| `:447-450` `Layout … read_eval : ∀ q c z, eval₂Mle (read q c) z = eval₂Mle q (extend c z)` | `:79-81` | the code's law is on `.values` with `algebraMap K E`; same statement |
| `:451` `Coord … known (col : Column κ)` | `:86-89` | none |
| `:453-454` `PublicLine … (sent : Bool) (pos : 0 < S.τ col.1)` | `:102-114` | none |
| `:455-466` `M3Instance` | `:119-148` | the sketch omits `decAux`'s `attribute [instance]` (`:150`); otherwise field for field |
| `:467` `def M3Instance.column I q c ; def M3Instance.row I q j x ; def M3Instance.tuples I q (s : Side)` | `:160, 163, 185` | the sketch omits `κ`, `coordCell`, `flushTuples`, `boundaryTuples` (`:157, 167, 174, 180`), which `tuples` unfolds to and an auditor must read |
| `:468` `Balanced I q (List.Perm)` | `:201` | none |
| `:469-471` `M3Holds`, `deriving instance Decidable` | `:219-223` | none |
| `:472` `abbrev TheOracle I : Fin 1 → Type := fun _ ↦ Column I.μ` | `:226` `OneOracle (Column I.μ)` | same type |
| `:473` `M3Rel` | `:230-231` | none |
| `:476-484` claims and outputs | `Seams.lean:57-151` | `Weight`'s `mle : Vector E μ → E` and `mle_eq` are elided as `…`; the `.Holds` of each claim (`:66, 98, 123`), `VirtualTerm.table`, `VirtualTerm.eval` and `Weight.pair` (`:82, 87, 112`) are not in the sketch and are load-bearing |
| `:485-490` seams | `:166-191` | `Seam.table/pub/flock/done` are summarised in words; the code is as summarised |
| `:493-498` `KnowledgeAppend` | `KnowledgeAppend.lean:474-478, 510-518` | `rbrKSWorstCaseWith` is an abbreviation of the sketch for `rbrKnowledgeSoundnessWorstCaseWith`; otherwise as stated |
| `:501-513` `Component.Def/Complete/Security` | `Component.lean:52-106` | the sketch writes `Extractor.RoundByRound []ₒ …`; the code writes `OracleSpec.emptySpec.{0, 0}` to pin a universe (`:96-99`), and says so |
| `:514-515` the three `append`s | `:143, 162, 174` | the sketch omits `guardedAppend` and `stateFunctionOfEq` (`:156, 110`), which `Security.append` unfolds to |
| `:517-521` pass-through, send-oracle | `PassThrough.lean`, `SendOracle.lean` | the sketch omits `sendOracle_relOut`, `sendVerifierPure`, `sendStateFunction`, `sendWitMid` (`SendOracle.lean:71, 101, 145, 130`), all in the knowledge theorem's statement (section B) |
| `:523-525` `Phase.*` | `Phase.lean:37-74` | none |
| `:528-548` `Compose.lean` | `Compose.lean:51-185` | none; the sketch's comment on `piopExtractor`, "commitExtractor, then the phases'", is right of `extractMid` and wrong of `extractOut` (D.5) |
| `:551-553` `Refinement` | `Refinement.lean:31-71` | none |

**Names the sketch or the interface list (`:1365-1385`) give that do not exist under that name
or signature on `main`:** none in the spine block of the list (`:1366-1385`) — every name was
found (`Side` … `Toy.layout`), except that the list names `Ensemble.toM3 (Layer 2)` (not
built, marked) and `Component.Security.{witMid, extractor, kSF, rbr}` (fields, exist).
**Public declarations of the reviewed modules that the list does not name:** `M3Instance.κ`,
`M3Instance.coordCell`, `flushTuples`, `boundaryTuples`, `M3Instance.decAux` (as an
instance), the five `.Holds`, `VirtualTerm.table`, `VirtualTerm.eval`, `Weight.pair`,
`Component.stateFunctionOfEq`, `rbrKnowledgeSoundnessWorstCaseWith_of_eq`,
`Component.guardedAppend`, `Component.passThroughProver/Verifier/Pure/Extractor/StateFunction`,
`passThrough_materializeOutput`, `passThroughVerifier_toVerifier_run`, `passThrough_rbr`,
`Component.passThroughComplete`, `Component.sendSpec/sendProver/sendEmbedding/sendVerifier`,
`sendOracle_relOut`, `sendOracle_outputPure`, `send_materializeOutput`,
`sendVerifier_toVerifier_run`, `sendVerifierPure`, `sendOracle_complete`,
`sendOracleComplete`, `sendWitMid`, `sendExtractor`, `sendStateFunction`, `sendOracle_rbr`,
`sendOracleSecurity`, `noOracle_eq`, `Refinement.id`, `Refinement.comp`,
`Verifier.GuardedForm.of_probEvent_pos`, `Reduction.mem_support_run_of_guarded`,
`keepOracles`, `OracleVerifier.materializeOutput_of_keepOracles`, everything in
`KnowledgeAppend` but the two named theorems, `Toy.Col`, `Toy.slice`, `Toy.extend`,
`Toy.read_eval`, `Toy.constraint`, `Toy.flush`, `Toy.boundary`. The list's sentence
"Everything not listed is a proof, a helper, or a test" (`:1419`) is false of the fourteen of
these that section B counts as load-bearing (the `.Holds`, `table`, `eval`, `pair`,
`coordCell`, the two tuple lists, `sendOracle_relOut`, `sendVerifierPure`,
`sendStateFunction`, `sendWitMid`, `guardedAppend`, `stateFunctionOfEq`).

### E.2 The blueprint's other statements of the same objects

| Object | Where | As stated there | The spine as built | Which the code implements |
| --- | --- | --- | --- | --- |
| the knowledge theorem | headline `:14-16` | `piop_rbrKnowledgeSoundness (I : M3Instance) : for every prover, leanVmVerifier accepts → except with probability piopError I, the extractor's column q satisfies M3Holds I input q` | `(P) (S : P.Security) init impl : (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel I) (Seam.done I) S.toDef.witMid (piopExtractor P S) (S.toDef.kSF init impl) (piopError P)` | the spine's; the headline's has no `P`, `S`, a numeric `piopError I`, and a plain-form conclusion |
| the knowledge theorem | Layer 10 `:1127-1129` | `piop_rbrKnowledgeSoundness (hs : s.Admissible prog) : (leanVmVerifier prog s input flock).rbrKnowledgeSoundness init impl (m3Relation prog s) Set.univ (piopError s)` | as above | the spine's; Layer 10's is over `prog s input flock`, has an admissibility hypothesis, the existential and averaged `rbrKnowledgeSoundness`, the relation `m3Relation prog s`, `Set.univ` for `Seam.done`, and `piopError s`. The text at `:1104-1106` says these are "the spine's, stated over `Phases I`", contradicting the block below it |
| the completeness theorem | headline `:12-13`; Layer 10 `:1124-1126` | `(I) : M3Holds I input q → the honest prover makes leanVmVerifier accept with probability 1`; `(hs : s.Admissible prog) : (leanVmPiop prog s input flock).perfectCompleteness init impl (m3Relation prog s) Set.univ` | `(P) (C : P.Complete) init impl : (leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I)` | the spine's; Layer 10's admissibility hypothesis is not in the code and is not needed (the sizes are inside `I`) |
| `leanVmPiop` | Layer 10 `:1116-1119` | `leanVmPiop (prog) (s) (input) (flock : FlockInterface prog s) : OracleReduction []ₒ (StmtIn := PublicInput) (OStmtIn := fun _ : Empty ↦ Unit) (M3Witness prog s) (StmtOut := Unit) (OStmtOut := fun _ : Empty ↦ Unit) Unit (pSpec := …) := commitPhase ⟫ busPhase ⟫ tableSumcheck ⟫ publicInputPhase ⟫ flock.reduction ⟫ openingPhase` | `leanVmPiop (P : Phases I) : OracleReduction []ₒ I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit P.toDef.pSpec := P.toDef.red` | the spine's; `input` is not an argument (it is the statement), the oracle families are `Fin 0`/`Fin 1` not `Empty`, the witness is `Column I.μ` not `M3Witness prog s`, the output oracle is the stack not `Unit`, and the phases are fields of `P`, not named definitions |
| `piopError` | conventions `:318`; Layer 10 `:1122`, `:1130` | "the closed form is a `def` next to the theorem, and the interactive error is its sum"; `piopError (s : Sizes) : (pSpec …).ChallengeIdx → ℝ≥0`; `piopError_le (hs) : Σ i, piopError s i ≤ 2 ^ 40 / |E| + flockError` | `piopError (P : Phases I) := P.toDef.err`; no bound | the spine's (finding *the declared error is unconstrained*) |
| `BusOut` | Layer 6 `:960-964` | `structure BusOut where ζ : Fin μ_bus → E ; rem : Fin 3 → E ; pool : List Claim ; α : Fin 4 → E ; β : E` | `structure BusOut (I) where linear : List (LinearClaim I) ; columns : List (ColumnClaim I)` (`Seams.lean:130-134`) | the spine's; Layer 6's carries the challenges and the three totals, the spine's carries claims (the sibling dossier proposes the shape between the two) |
| `busPhase.relOut` | Layer 6 `:965-966` | `{…| (∀ j, Σ_x eq(ζ_{<τ_j}, x) · B_j^s(x) = rem s) ∧ every pooled claim holds for q ∧ (count root ≠ 0)}` | `Seam.bus` (`:175-177`) | the spine's; Layer 6's has no zerocheck claims, no lines, no `aux`, a count-root conjunct, and the forms as one equation per side |
| the table phase's statement types | Layer 7 `:988` | `tableSumcheck (prog) (s) : OracleReduction []ₒ (StmtIn := BusOut) … (StmtOut := BusOut × ColumnClaims)` | `Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)` (`Compose.lean:78`) | the spine's; Layer 7's output keeps `BusOut` |
| `FlockInterface` | Layer 9 `:1077-1085` | `reduction : OracleReduction []ₒ (StmtIn := ColumnClaims) (OStmtIn := fun _ : Unit ↦ Column μ) Unit (StmtOut := WeightedClaim) … pSpecFlock ; limbColumns ; relIn ; relOut ; perfectCompleteness ; rbrKnowledgeSoundness : … rbrKnowledgeSoundnessWorstCase … flockError ; flockError_le` | `Phases.flock : Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I)` with `Phase.Complete`/`Phase.Security` at `Seam.pub`/`Seam.flock` | the spine's; Layer 9's has its own relations, the existential `rbrKnowledgeSoundnessWorstCase` (no named extractor), a single `WeightedClaim` output, and an oracle family over `Unit` |
| `Weight` | Layer 10 `:1109` | `structure Weight (μ) where (onCube : ETable μ) (mle : (Fin μ → E) → E) (mle_eq : ∀ r, mle r = evalMle onCube r)` | `Weight (μ : ℕ) … mle : Vector E μ → E` (`Seams.lean:103-109`) | the spine's: points are `Vector E μ` (convention *Hypercube* `:312`), not `Fin μ → E` |
| `WeightedClaim` | Layer 10 `:1110`; Layer 11 `:1173` | `WeightedClaim (μ) where (W : Weight μ) (c : E)`; `whirOpen … (StmtIn := Fin J → WeightedClaim μ)` | `WeightedClaim (I : M3Instance) where weight : Weight I.μ ; value : E` (`:116-120`) | the spine's: indexed by the instance, fields `weight`/`value`; Layer 11's `WeightedClaim μ` does not exist |
| the opening phase's statement | Layer 10 `:1112` | `openingPhase (μ) (J : ℕ) : OracleReduction []ₒ (StmtIn := Fin J → WeightedClaim μ) … (StmtOut := Unit)` | `Phases.opening : Phase.Def I (I.Stmt × FlockOut I) Unit` | the spine's; the input carries column claims and weighted claims as lists, and the statement |
| the extractor | conventions `:334`; `:100-101`; `:1133-1135`; acceptance test 24 `:1333-1340` | "the commit phase's (which reads the stack off the oracle message) followed by the phases'"; "`piopExtractor`, which reads the stack `q` off the oracle message, followed by `witnessOf`"; "the spine's test proves by `rfl` that `piopExtractor` returns the committed stack" | `piopExtractor P S := S.toDef.extractor`, ArkLib's `RoundByRound.append` nested five times | the spine's; the words are right of `extractMid` at round 0 and wrong of `extractOut` (D.5) |
| the relation ladder's transport | `:364-366`; `:582-586` | "along which knowledge transports at the same error (pointwise, `Refinement.map_option_valid`)"; "the probabilistic transport … is not proved … and has no consumer yet" | `map_option_valid` only | the spine's; the probabilistic form is three lines (D.7) |
| `Seam.done` | Layer 10 `:1144` | "`Set.univ` as the output relation says the last phase leaves nothing to check" | `Seam.done := of I fun (_ : Unit) _ ↦ True` (`:191`), equal to `Set.univ` (probe D.2) | the spine's; same set, different spelling |
| the hole interfaces | conventions `:332` | "a phase or generic component is two structures: `X.Def` (the reduction, its relations and its per-challenge error) and `X.Security`" | three: `Def`, `Complete`, `Security extends Complete`; the relations are not in `Def` but arguments of `Complete`/`Security` | the spine's |
| the relation of the first phase | conventions `:316` | "The relation of the first phase is `M3Rel I`, that is `M3Holds I input q` on the stack `q`" | `commitDef I` at `M3Rel I` | agree |

Layer 6's `BusOut`, Layer 7's types, Layer 9's `FlockInterface` and Layer 10's block are the
pre-spine sketches; the text around them (`:951-952`, `:983-984`, `:1103-1106`) says the
phases are "over `I : M3Instance`" and "the spine's", but the blocks were not rewritten. A
reader who trusts the blocks builds against types that do not exist. The sibling dossier
`gt-table-pub.md` records the same for Layer 7 (its finding *Layer 7's sketch and the
tracker's signature predate the spine*); we add Layers 6, 9, 10 and the headline.

**Proposed change** (one for all): replace each pre-spine block by a signature over the spine's
types — `busPhase (I) : Phase.Def I I.Stmt (I.Stmt × BusOut I)`, `busComplete`, `busSecurity`
at `Seam.commit`/`Seam.bus`; `tableSumcheck (I) : Phase.Def I (I.Stmt × BusOut I) (I.Stmt ×
TableOut I)`; `FlockInterface (I)` as the pair `Phase.Def I (I.Stmt × PubOut I) (I.Stmt ×
FlockOut I)` with its `Phase.Security` at `Seam.pub`/`Seam.flock`; `openingPhase (I) :
Phase.Def I (I.Stmt × FlockOut I) Unit`; delete Layer 10's `leanVmPiop … piopError_le` block
and point at the spine, keeping `piopError_le` restated over `I` (section F, first finding).

### E.3 Acceptance tests 24 to 28 against the code

| Test | Claim | Status on `main` |
| --- | --- | --- |
| 24, the extractor computes | `piopExtractor` is a definition whose `extractOut` reads the stack; witness the `rfl` test | `piopExtractor` and everything it unfolds to is computable (D.5, `isNoncomputable = false`); the `rfl` witness holds for zero-round phases only; a classical phase extractor would go unnoticed and would not matter (D.5) |
| 25, the wall | no module above the adaptor imports `LeanerVM.Arithmetization` | `git grep -n "import LeanerVM.Arithmetization" b435631 -- LeanerVM/Protocol` gives two hits: `LeanerVM/Protocol/FixedColumns.lean:11` (a listed exception, `:331`) and `LeanerVM/Protocol/Basic.lean:3` (`public import LeanerVM.Arithmetization.Basic`, an otherwise empty placeholder module from before the spine, not among the exceptions of convention *The wall*). The spine's own five modules and `ToArkLib/` import nothing from `LeanerVM/Arithmetization/`. Minor: delete `Protocol/Basic.lean` or list it. |
| 26, seams are the contract | the compositions typecheck only when the seams agree | true by construction (`Phases.Complete.toDef`, `Phases.Security.toDef`); the junk bundle of D.3 (b) also typechecks, so the test says nothing about content |
| 27, the toy is honest | the honest stack passes, each checkable clause fails alone | met by the tests; D.1 adds the multiplicity cases; the fifth clause is untestable on the toy |
| 28, the bus seam bounds the degree | `Seam.bus` carries `totalDegree ≤ I.d`, the cubic is rejected | met as a conjunct; its cost is a guard in the table phase (C.3) |

## F. Findings

Severities as the brief defines them. Line references to the blueprint are to
`docs/roadmap/protocol-blueprint.md` at `b435631`.

### The declared error is unconstrained: the knowledge theorem has content only with a bound on `piopError`

**Severity: major** (a statement cannot be stated as written: the headline's "except with
probability `piopError I`" has no counterpart). **Classification: an error of the blueprint**
(an omission the spine inherited).

**Evidence.** `piopError P := P.toDef.err` (`Compose.lean:149`); `Component.Def.err :
pSpec.ChallengeIdx → ℝ≥0` (`Component.lean:66`), declared by each phase; `Def.append` keeps
each component's declaration (`Component.lean:148`). ArkLib's bound is `Pr[…] ≤ err i`
(`RoundByRound.lean:568`) with no constraint on `err`. Probe `P4Junk.lean` (D.3 (b)): five
phases that draw a challenge and check nothing, each declaring error `1`, inhabit
`Phases.Security toy`; both master theorems hold of them; `piopError_junk : ∀ i, piopError
junkPhases i = 1`. The construction is instance-independent. The blueprint's only bound,
`piopError_le (hs : s.Admissible prog) : Σ i, piopError s i ≤ 2 ^ 40 / |E| + flockError`
(`:1130`), is over an argument `s` the spine's `piopError` does not take, and the convention
row *Errors* (`:318`, "the closed form is a `def` next to the theorem, and the interactive
error is its sum") names no theorem.

**Where the bound belongs.** Two designs are consistent with the spine; the second is
recommended.

- *A field of `Phases.Security`.* Add to `Phases.Security` (or to a new structure
  `Phases.Error`) a closed form `bound : ℝ≥0` and a proof `err_le : ∑ i, piopError P i ≤ bound`,
  and restate the master theorem's docstring with it. Cost: one field, and each phase's
  `Security` must come with a bound on its own `D.err` (a lemma per phase, summed by
  `Def.append`). It keeps the errors declared by the phases, so a phase author still writes
  the closed form, and the bound is a hypothesis of the composition, not a consequence.
- *A closed form fixed by the spine.* Make the error a function of the **schedule**, not a
  declaration: `Component.Def.err` is removed; `Component.Security` carries `err` with its
  `rbr`; the spine states, per phase slot, the closed form leanVM's analysis gives
  (`4·2^{μ_bus}/|E|` on `(α, β)` and `gkrError` for the bus, `(B+2)/|E|` and `3/|E|` per round
  for the table sumcheck, `1/|E|` for the public input, `flockError`, `(J−1)/|E|` and `2/|E|`
  per round for the opening; blueprint Layers 6 to 10), as a function `piopError I :
  ChallengeIdx → ℝ≥0` of the instance's sizes, and `Phases.Security` demands each phase's
  `rbr` **at that error**. Then `piopError I` exists as the headline writes it,
  `piopError_le` is a theorem of the spine about the instance's sizes (provable now, by
  `norm_num` at the caps once `leanIsaInstance`'s sizes exist), and a phase that cannot meet
  its slot's error has no `Security`. Cost: the schedules must then also be fixed by the spine
  (the error is indexed by the challenge), which the blueprint's convention *Holes* leaves to
  each phase's `Def`; this is the same move the sibling dossier recommends for `BusOut`'s
  shape, and Layer 12's `verify` needs the schedules fixed anyway.

**Proposed change to the blueprint.**
- *As it stands* (`:318`): "Errors | `ℝ≥0`, per verifier message, as ArkLib's
  `rbrKnowledgeError`; the closed form is a `def` next to the theorem, and the interactive
  error is its sum."
- *As proposed*: "Errors | `ℝ≥0`, per verifier challenge, as ArkLib's `rbrKnowledgeError`. The
  spine fixes the closed form of every phase's error as a function `piopError I` of the
  instance's sizes, and `Phases.Security` demands each phase's round-by-round bound at that
  error; `piop_rbrKnowledgeSoundness` is stated at `piopError I`, and `piopError_le` bounds its
  sum at the caps. A phase may not declare its own error: with an unconstrained declaration the
  knowledge theorem holds of a protocol that checks nothing (declared error 1)."
- Also `:1122` (`def piopError (s : Sizes)`) and `:1130` to be restated over `I`; and item 6
  of *What the spine fixes* (`:431-437`) to say that `piopError` is the spine's, not the
  phases'.

### The headline describes theorems that do not exist

**Severity: minor** (stale and imprecise text at the most-read place). **Classification: an
error of the blueprint.**

**Evidence.** `:11-17` against `Compose.lean:162-185` (C.4): no `piopError I`; no "except with
probability" (the theorem is round-by-round, the plain form is ArkLib's `sorry` at
`Implications.lean:223-228`); no "the extractor's column `q`" (no such definition, D.5); the
hypotheses `P`, `C`, `S` absent; `Set.univ`/`Seam.done` unmentioned. "States the two theorems
that make it a proof system for the constraint relation" (`:8-9`): on `main` they make
*any* five phases meeting the seams a proof system for `M3Rel I`, for any `I`.

**Proposed change.**
- *As it stands* (`:11-17`): the two pseudo-signatures.
- *As proposed*:
  ```text
  piop_perfectCompleteness (I : M3Instance) (P : Phases I) (C : P.Complete) :
    the honest prover of P convinces its verifier with probability 1 on every (input, q)
    with M3Holds I input q
  piop_rbrKnowledgeSoundness (I : M3Instance) (P : Phases I) (S : P.Security) :
    P's verifier is round-by-round knowledge sound for M3Rel I with the extractor
    piopExtractor P S at the error piopError I, so that (ArkLib's round-by-round-to-plain
    implication, admitted at the pin) an accepting prover's committed q satisfies
    M3Holds I input q except with probability Σ piopError I
  ```
  followed by: "Both are composition theorems: they hold of every bundle of phases that
  meets the seams, and say nothing of leanVM until `I` is `leanIsaInstance` and `P` is the
  five phases of Layers 6 to 10 with their proofs. What is proved on `main` is the spine, the
  commit phase and the public-input phase."

### The extracted stack is not a definition, and the `rfl` witness of acceptance test 24 covers zero-round phases only

**Severity: minor** (an acceptance test whose witness does not test what it says; avoidable
confusion about `piopExtractor`). **Classification: an error of the blueprint.**

**Evidence.** D.5: `P3cExtractor.lean`. With the repository's `publicInputPhase` in the bundle,
`(piopExtractor P S).extractOut` has type `S.pub.witMid (Fin.last 2) = Unit` and the test's
statement is ill-typed; the stack is `extractMid` at round 0. ArkLib's `RoundByRound.append`
(`Append/StateFunction.lean:129-139`) returns the second extractor's `extractOut` whenever the
second component has a round. The blueprint (`:1337-1339`): "the spine's test proves by `rfl`
that `piopExtractor` returns the committed stack on the honest transcript, whatever the
phases' extractors".

**Proposed change.**
- Code (spine): define `piopExtractedStack (P) (S) : (I.Stmt × ∀ i, NoOracle i) →
  P.toDef.pSpec.FullTranscript → Column I.μ`, the fold of `extractOut` and the `extractMid`s
  down to round 0 (cast by `eqIn`), and prove `piopExtractedStack P S s tr = tr ⟨0, _⟩` for
  every `P`, `S`, `s`, `tr` (the commit phase's `extractMid` ignores what it is handed,
  `SendOracle.lean:137`): a theorem for all phases, not a `rfl` on five empty ones. The tests'
  `rfl` example is then a corollary.
- Blueprint `:1333-1340`: replace "Witness: the spine's test proves by `rfl` that
  `piopExtractor` returns the committed stack on the honest transcript, whatever the phases'
  extractors" by "Witness: `piopExtractedStack_eq`, for every bundle and every transcript; the
  composed `extractOut` is the last phase's and is not the stack". Same at `:100-101` and
  `:1133-1135` ("reads the stack off that message" is true of `extractMid` at round 0).

### The degree conjunct of `Seam.bus` is a guard the table phase's verifier must run

**Severity: major** (a `Phase.Security` cannot be proved for a verifier that transcribes
leanVM's table sumcheck). **Classification: an error of the blueprint**; the sibling dossier
`gt-table-pub.md` (section 6, E.1 (a); section 8, first finding) establishes it with a probe
on which a degree-blind verifier accepts, and proposes the type-level shape. **We agree**, and
record only the mechanism in ArkLib's definition (C.3, item 1: `∀ stmtIn` with `toFun_empty`
an `iff`) and the smallest fix if the sibling's `BusOut` is not adopted: make
`VirtualTerm.poly` a subtype `{p : CMvPolynomial (I.width j) K // p.totalDegree ≤ I.d}` and
delete the conjunct; the seam then has four conjuncts, the test `cubicTerm` becomes a
typing failure, and acceptance test 28 is met by the type.

### The `outputPure` field is redundant, and `guarded` nearly so

**Severity: minor** (avoidable audit surface). **Classification: a deviation forced by an
upstream library**, retired when the pin includes a module the spine can import.

**Evidence.** D.7, `outputPure_of_def`: every `Component.Def` over `[]ₒ` has a pure prover
output, because no query is possible. ArkLib at the pin has the instance
`Prover.instOutputIsPureEmpty` (`NoAmbient.lean:39-42`), not imported by the spine, and
`Verifier.GuardedForm.ofEmpty` (`NoAmbient.lean:46-55`): every verifier over `[]ₒ` has a guarded
form, given a fallback verdict for the rejecting branch. The field `outputPure` is one of the
three of `Component.Complete` (`Component.lean:79-80`); every phase discharges it by
`⟨_, fun _ ↦ rfl⟩` (`PublicInput.lean:386`, `SendOracle.lean:78`, `PassThrough.lean:85`).

**Proposed change.** Code: delete the field; `Complete.append` takes the instance. Keep
`guarded`: the composed extractor names `G.out` (`Component.lean:178`), and a hand-written
verdict is what an auditor reads, where `ofEmpty`'s is "run the verifier". Blueprint `:505-507`
and the sketch accordingly.

### The instance is data the theorems trust, and nothing on `main` says any instance but the toy has an inhabited relation

**Severity: note.** **Classification: a deliberate deviation** (the wall), to be kept, with the
theorem it owes named.

**Evidence.** C.1 (`aux`), C.2 and D.4 (a `Layout` may alias columns; `toyAlias` has an empty
relation and is an `M3Instance`); `Layout.read_eval` is the only law an instance obeys.
Nothing in the spine relates two instances or bounds what an instance may declare; the master
theorems hold of every instance including the empty ones.

**Proposed change.** Blueprint, *What the spine fixes* item 1 (`:412-414`): append "An
instance is trusted data: the spine proves nothing about it beyond `read_eval`, and the master
theorems hold of instances whose relation is empty. For leanISA the instance is Category B
(layouts, separators, count columns, lines) and its non-vacuity is `m3Holds_stackOf` (Layer 3),
its faithfulness Layer 12's fixture."

### `read` is determined by `extend`

**Severity: minor** (avoidable audit surface; a field with a law where a definition would do).
**Classification: a design remark.**

**Evidence.** C.2, on paper (the extension of a table at a cube point is its entry). A probe
would be `Layout.read_eq_of_extend`; not run.

**Proposed change.** Code: `structure Layout (μ) (ι) (κ)` with `extend` and one law
`extend_inK : ∀ c x q, (q̃ (extend c (bits x))).IsInK` (or the equivalent on the `eq`
weights); `read` a definition. Every phase reads columns through `I.column` and is unchanged.
The toy's `slice` becomes a theorem. Blueprint `:447-450` accordingly.

### Knowledge transport along the adaptor is three lines in the event form

**Severity: note.** **Classification: an error of the blueprint** (a claim that something is
not proved and has no consumer, where it is provable now and Layer 13 consumes it).

**Evidence.** D.7, `knowledge_transport`; blueprint `:582-586`.

**Proposed change.** Blueprint `:582-586`: "The transport of knowledge along the adaptor is
proved in the event form: for the same game, provers and extractor, the probability that the
verifier accepts and the extracted witness, mapped by the refinement, is invalid is at most
the knowledge error (`Refinement.knowledge_transport`, an ArkLib candidate). It needs no prover
conversion, since the game's witness type is unchanged. Layer 13 consumes it. What T4 waits on
is the round-by-round-to-plain implication (ledger row *round-by-round implies plain*), whose
existential conclusion also forgets the named extractor; a `With` form is to be requested
upstream." Code: move the probe's theorem into `ToArkLib/Refinement.lean`.

### Two statements the earlier review's disposition recorded as met are met only in part

**Severity: note.** Evidence: `docs/reviews/protocol-spine.md:36` says the extractor test
"proves by `rfl` that `piopExtractor … returns the honest stack … for any `A` and `S`" (true
for zero-round phases only, above); `:39` says "No `trivSecurity` … was added, so the `rfl`
test quantifies over `S`" — the reason there is no `trivSecurity` is that none exists
(`no_security`, D.3 (a)), which the review's A6 reads as a property of the toy ("True on the
toy") without a proof. No change to the blueprint; the review file is a handoff.

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

## G. What was not verified, and what would verify it

| Claim | Status | What would verify it |
| --- | --- | --- |
| The relation of `toyAlias` is empty for every stack and statement (D.4) | evidence by an exhaustive `#guard` over cells `0, 1` and statements in `{0, 1, 2}` at the old pin; the paper argument is two lines | a theorem `∀ input q, ¬ M3Holds toyAlias input q`, whose proof needs CompPoly's evaluation of `X 0` on a row (no `eval_X` lemma at `3468b38c`; the sibling dossiers may have one) |
| `Layout.read` is determined by `extend` (C.2) | on paper | a lemma `read_eq_of_extend` from CompPoly's `eval_mle_eq_eval` (cited in `Field.lean:50`) |
| An always-rejecting bundle has no `Phases.Security` on an instance with an inhabited relation (D.3 (c)) | a reading of `Security extends Complete` and of `perfectCompleteness` | a probe with a rejecting zero-round verifier and `perfectCompleteness_eq_prob_one` |
| The read-everything phase inhabits `Phases.Security I` at error `0` for every `I` (D.3 (d)) | on paper; agrees with `gt-table-pub.md` section 6 | a probe on an instance with `μ = 0`: one oracle query, `if decide (relIn s ⟨#v[v.limb 0]⟩) then pure (f s) else failure`, with `Verifier.GuardedForm.of_probEvent_pos` for the state function |
| The probes that use `(2 : K)` mean the same at the new CompPoly pin | they do not (`(2 : K) = 0` there, brief §8); their conclusions are about `b435631` with the old pins, where `2 : K` is the polynomial `x` (`tests/…/Spine.lean:30`) | re-run `P2Relation`, `P3aSeams`, `P5PassThrough` with `K.ofBits 2` after the rebuild |
| Line numbers of `Field.lean` and `KnowledgeAppend.lean` | at `b435631` (the working tree had moved by the time the counting script first ran; the script was re-run on `git show b435631:` and the numbers in sections B and C are from that run) | — |
| The earlier review's validation paragraph (`docs/reviews/protocol-spine.md:19-28`) | not re-run (no build allowed); `#print axioms` re-established by probe P1 for the declarations listed there and more | `./scripts/validate.sh` on `b435631` |

## Appendix: the probes, in full

Every probe is a plain Lean file under `.claude/reports/blueprint-review/probes/code-spine/`, run from the repository root (leanerVM `main` at `b435631`, ArkLib `dca90385`) with

```sh
flock .claude/reports/blueprint-review/logs/lean.lock lake env lean .claude/reports/blueprint-review/probes/code-spine/<File>.lean
```

The output of each run is the file `<File>.out` beside it, reproduced below the source. An empty output with `exit=0` means every `#guard`, `example` and theorem of the file was accepted.

### `P1Axioms.lean`

```lean
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.ToArkLib.Refinement
import LeanerVM.Protocol.PublicInput

/-!
Probe P1 (code-spine): axioms and computability of the spine's load-bearing declarations.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

#print axioms piop_perfectCompleteness
#print axioms piop_rbrKnowledgeSoundness
#print axioms piop_rbrKnowledgeSoundness_exists
#print axioms piopExtractor
#print axioms commitExtractor
#print axioms Component.sendExtractor
#print axioms commitSecurity
#print axioms commitComplete
#print axioms Component.Security.append
#print axioms Component.Complete.append
#print axioms Phases.Security.toDef
#print axioms M3Holds
#print axioms Component.passThroughSecurity
#print axioms publicInputSecurity
#print axioms Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
#print axioms Verifier.KnowledgeStateFunction.appendGuarded
#print axioms Extractor.RoundByRound.append
#print axioms Refinement.map_option_valid
#print axioms Toy.read_eval

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for n in [``piopExtractor, ``commitExtractor, ``Component.sendExtractor,
      ``Phases.Security.toDef, ``Phases.Complete.toDef, ``Component.Security.append,
      ``Component.Complete.append, ``Extractor.RoundByRound.append, ``leanVmPiop,
      ``leanVmVerifier, ``leanVmProver, ``piopError, ``Phases.toDef, ``Component.Def.append,
      ``commitDef, ``Component.sendOracle, ``Component.sendProver, ``Component.sendVerifier,
      ``publicInputPhase, ``publicInputSecurity, ``publicInputComplete, ``commitSecurity,
      ``commitComplete, ``Component.passThrough, ``Component.passThroughSecurity,
      ``Component.passThroughExtractor, ``PublicInput.extractor, ``PublicInput.prover,
      ``PublicInput.verifier, ``Verifier.KnowledgeStateFunction.appendGuarded,
      ``Component.guardedAppend, ``M3Holds, ``Toy.toy, ``Toy.honest,
      ``Extractor.Straightline.map, ``OracleReduction.append] do
    logInfo m!"{n}: noncomputable={Lean.isNoncomputable env n}"
```

Output:

```text
'LeanerVM.Protocol.piop_perfectCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.piop_rbrKnowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.piop_rbrKnowledgeSoundness_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.piopExtractor' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.commitExtractor' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Component.sendExtractor' depends on axioms: [propext, Quot.sound]
'LeanerVM.Protocol.commitSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.commitComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Component.Security.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Component.Complete.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Phases.Security.toDef' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.M3Holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Component.passThroughSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.publicInputSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LeanerVM.Protocol.Verifier.KnowledgeStateFunction.appendGuarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Extractor.RoundByRound.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Refinement.map_option_valid' depends on axioms: [propext, Quot.sound]
'LeanerVM.Protocol.Toy.read_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
LeanerVM.Protocol.piopExtractor: noncomputable=false
LeanerVM.Protocol.commitExtractor: noncomputable=false
LeanerVM.Protocol.Component.sendExtractor: noncomputable=false
LeanerVM.Protocol.Phases.Security.toDef: noncomputable=false
LeanerVM.Protocol.Phases.Complete.toDef: noncomputable=false
LeanerVM.Protocol.Component.Security.append: noncomputable=false
LeanerVM.Protocol.Component.Complete.append: noncomputable=false
Extractor.RoundByRound.append: noncomputable=false
LeanerVM.Protocol.leanVmPiop: noncomputable=false
LeanerVM.Protocol.leanVmVerifier: noncomputable=false
LeanerVM.Protocol.leanVmProver: noncomputable=false
LeanerVM.Protocol.piopError: noncomputable=false
LeanerVM.Protocol.Phases.toDef: noncomputable=false
LeanerVM.Protocol.Component.Def.append: noncomputable=false
LeanerVM.Protocol.commitDef: noncomputable=false
LeanerVM.Protocol.Component.sendOracle: noncomputable=false
LeanerVM.Protocol.Component.sendProver: noncomputable=false
LeanerVM.Protocol.Component.sendVerifier: noncomputable=false
LeanerVM.Protocol.publicInputPhase: noncomputable=true
LeanerVM.Protocol.publicInputSecurity: noncomputable=false
LeanerVM.Protocol.publicInputComplete: noncomputable=false
LeanerVM.Protocol.commitSecurity: noncomputable=false
LeanerVM.Protocol.commitComplete: noncomputable=false
LeanerVM.Protocol.Component.passThrough: noncomputable=false
LeanerVM.Protocol.Component.passThroughSecurity: noncomputable=false
LeanerVM.Protocol.Component.passThroughExtractor: noncomputable=false
LeanerVM.Protocol.PublicInput.extractor: noncomputable=false
LeanerVM.Protocol.PublicInput.prover: noncomputable=false
LeanerVM.Protocol.PublicInput.verifier: noncomputable=false
LeanerVM.Protocol.Verifier.KnowledgeStateFunction.appendGuarded: noncomputable=false
LeanerVM.Protocol.Component.guardedAppend: noncomputable=false
LeanerVM.Protocol.M3Holds: noncomputable=false
LeanerVM.Protocol.Toy.toy: noncomputable=false
LeanerVM.Protocol.Toy.honest: noncomputable=false
LeanerVM.Protocol.Extractor.Straightline.map: noncomputable=false
OracleReduction.append: noncomputable=false
exit=0
```

### `P2Relation.lean`

```lean
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
```

Output:

```text
exit=0
```

### `P3aSeams.lean`

```lean
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput

/-!
Probe P3a (code-spine): each seam on the toy instance, an inhabitant and near misses; the
zerocheck escape; the commit phase's state function and extractor; the type of the composed
extractor's output when a phase has rounds.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

namespace Probe

/-! ## Decision procedures for the claims and the seams (the repository has none)

Spelled with `inferInstanceAs` on the unfolded proposition, as the repository's public-input
test does: the instance `by unfold …; infer_instance` elaborates and then exhausts the memory
under `#guard` (observed: exit 137 on the first version of this probe). -/

instance {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable (CMlPolynomialEval.eval₂Mle (I.column q c.col).values
    (algebraMap K E) c.point = c.value))

instance {I : M3Instance} (q : Column I.μ) (c : LinearClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable ((c.terms.map fun t ↦ t.eval q).sum = c.value))

instance {I : M3Instance} (q : Column I.μ) (c : WeightedClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable (c.weight.pair q = c.value))

/-- The predicate of the bus seam, on a statement and a stack. -/
def busPred (I : M3Instance) (s : I.Stmt × BusOut I) (q : Column I.μ) : Prop :=
  (∀ c ∈ s.2.linear, c.Holds q) ∧
  (∀ c ∈ s.2.linear, ∀ t ∈ c.terms, t.poly.totalDegree ≤ I.d) ∧
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q

/-- It is the bus seam, by definition. -/
example (I : M3Instance) (s : I.Stmt × BusOut I) (o : ∀ i, TheOracle I i) :
    ((s, o), ()) ∈ Seam.bus I ↔ busPred I s (o 0) := Iff.rfl

instance (I : M3Instance) (s : I.Stmt × BusOut I) (q : Column I.μ) :
    Decidable (busPred I s q) :=
  inferInstanceAs (Decidable ((∀ c ∈ s.2.linear, c.Holds q) ∧
    (∀ c ∈ s.2.linear, ∀ t ∈ c.terms, t.poly.totalDegree ≤ I.d) ∧
    (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q))

def tablePred (I : M3Instance) (s : I.Stmt × TableOut I) (q : Column I.μ) : Prop :=
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q

example (I : M3Instance) (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i) :
    ((s, o), ()) ∈ Seam.table I ↔ tablePred I s (o 0) := Iff.rfl

instance (I : M3Instance) (s : I.Stmt × TableOut I) (q : Column I.μ) :
    Decidable (tablePred I s q) :=
  inferInstanceAs (Decidable ((∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧
    I.aux q))

def pubPred (I : M3Instance) (s : I.Stmt × PubOut I) (q : Column I.μ) : Prop :=
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.aux q

example (I : M3Instance) (s : I.Stmt × PubOut I) (o : ∀ i, TheOracle I i) :
    ((s, o), ()) ∈ Seam.pub I ↔ pubPred I s (o 0) := Iff.rfl

instance (I : M3Instance) (s : I.Stmt × PubOut I) (q : Column I.μ) :
    Decidable (pubPred I s q) :=
  inferInstanceAs (Decidable ((∀ c ∈ s.2.columns, c.Holds q) ∧ I.aux q))

def flockPred (I : M3Instance) (s : I.Stmt × FlockOut I) (q : Column I.μ) : Prop :=
  (∀ c ∈ s.2.columns, c.Holds q) ∧ ∀ c ∈ s.2.weighted, c.Holds q

example (I : M3Instance) (s : I.Stmt × FlockOut I) (o : ∀ i, TheOracle I i) :
    ((s, o), ()) ∈ Seam.flock I ↔ flockPred I s (o 0) := Iff.rfl

instance (I : M3Instance) (s : I.Stmt × FlockOut I) (q : Column I.μ) :
    Decidable (flockPred I s q) :=
  inferInstanceAs (Decidable ((∀ c ∈ s.2.columns, c.Holds q) ∧ ∀ c ∈ s.2.weighted, c.Holds q))

/-! ## The claims of the probe -/

def eZero : E := 0
def eOne : E := 1
/-- A point of `E` outside `{0, 1}`: the image of `2 : K` (the polynomial `x`). -/
def eTwo : E := ofK 2

/-- Column 0 of the honest stack is `[1, 1]`: its extension is `1` everywhere. -/
def col0One : ColumnClaim toy := ⟨⟨0, 0⟩, #v[eTwo], eOne⟩
def col0Zero : ColumnClaim toy := ⟨⟨0, 0⟩, #v[eTwo], eZero⟩

/-- The zerocheck claim of the toy's constraint at the point `(0)`: value `0`. -/
def zeroAt0 : LinearClaim toy :=
  ⟨[⟨eOne, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[eZero]⟩], eZero⟩
/-- The same at the point `(1)`. -/
def zeroAt1 : LinearClaim toy :=
  ⟨[⟨eOne, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[eOne]⟩], eZero⟩
/-- The same with the wrong value. -/
def zeroWrong : LinearClaim toy :=
  ⟨[⟨eOne, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[eZero]⟩], eOne⟩
/-- A cubic term, whose claim is true of the honest stack (column 2 is `[1, 0]`, so `X₂³` is
`[1, 0]` and its extension at `(0)` is `1`). -/
def cubicTrue : LinearClaim toy :=
  ⟨[⟨eOne, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 * CMvPolynomial.X 2, #v[eZero]⟩], eOne⟩

/-- The stack of the repository's test `badConstraint`: column 2 is `[2, 0]`, not Boolean. -/
def badConstraint : Column 3 := ⟨#v[1, 1, 1, 1, 2, 0, 0, 0]⟩

/-! ## The bus seam -/

-- An inhabitant: the zerocheck claim and a column claim, on the honest stack at statement 1.
#guard busPred toy ((1 : K), ⟨[zeroAt0, zeroAt1], [col0One]⟩) honest
-- Near misses, one per conjunct.
#guard ¬ busPred toy ((1 : K), ⟨[zeroWrong], [col0One]⟩) honest          -- a false linear claim
#guard ¬ busPred toy ((1 : K), ⟨[cubicTrue], [col0One]⟩) honest          -- a true cubic claim
#guard cubicTrue.Holds honest                                            -- (it is true)
#guard ¬ busPred toy ((1 : K), ⟨[zeroAt0], [col0Zero]⟩) honest           -- a false column claim
#guard ¬ busPred toy ((0 : K), ⟨[zeroAt0], [col0One]⟩) honest            -- the wrong statement

-- The zerocheck escape: on `badConstraint` the constraint is violated on the cube (row 0), so
-- the claim at the point `(0)` is false, and the claim at the point `(1)` is true. The bus seam
-- holds of a stack outside `M3Holds`; the bus phase's error is what pays for it.
#guard ¬ toy.ConstraintsVanish badConstraint
#guard ¬ zeroAt0.Holds badConstraint
#guard zeroAt1.Holds badConstraint
#guard busPred toy ((2 : K), ⟨[zeroAt1], [col0One]⟩) badConstraint
#guard ¬ M3Holds toy (2 : K) badConstraint

-- A bus statement with no claim holds of every stack whose public line holds: the seam does
-- not say which claims are emitted.
#guard busPred toy ((2 : K), ⟨[], []⟩) badConstraint

/-! ## The table and public-input seams -/

#guard tablePred toy ((1 : K), ⟨[col0One]⟩) honest
#guard ¬ tablePred toy ((1 : K), ⟨[col0Zero]⟩) honest
#guard ¬ tablePred toy ((0 : K), ⟨[col0One]⟩) honest
#guard pubPred toy ((1 : K), ⟨[col0One]⟩) honest
#guard ¬ pubPred toy ((1 : K), ⟨[col0Zero]⟩) honest
-- The public seam no longer sees the statement: the wrong statement is inside it.
#guard pubPred toy ((0 : K), ⟨[col0One]⟩) honest

/-! ## The Flock seam -/

/-- The weight that selects cell 0 of the stack. -/
def cell0Weight : Weight 3 where
  onCube := Vector.ofFn fun i ↦ if i.val = 0 then 1 else 0
  mle := fun r ↦ CMlPolynomialEval.evalMle (Vector.ofFn fun i ↦ if i.val = 0 then 1 else 0) r
  mle_eq := fun _ ↦ rfl

def w0One : WeightedClaim toy := ⟨cell0Weight, eOne⟩
def w0Zero : WeightedClaim toy := ⟨cell0Weight, eZero⟩

#guard flockPred toy ((1 : K), ⟨[col0One], [w0One]⟩) honest
#guard ¬ flockPred toy ((1 : K), ⟨[col0One], [w0Zero]⟩) honest
#guard ¬ flockPred toy ((1 : K), ⟨[col0Zero], [w0One]⟩) honest

/-! ## The last seam has no near miss: it is the whole set -/

example : Seam.done toy = Set.univ := Set.eq_univ_of_forall fun _ ↦ trivial

end Probe
```

Output:

```text
exit=0
```

### `P3bCommit.lean`

```lean
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput

/-!
Probe P3b (code-spine): each seam on the toy instance, an inhabitant and near misses; the
zerocheck escape; the commit phase's state function and extractor; the type of the composed
extractor's output when a phase has rounds.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

namespace Probe

/-! ## The commit phase: state function and extractor -/

section Commit

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

-- Before the message: `M3Holds` of the candidate witness.
example (s : K) (o : ∀ i, NoOracle i) (w : Column 3) :
    ((commitSecurity toy).kSF init impl).toFun 0 (s, o) default w ↔ M3Holds toy s w := Iff.rfl

-- After the message: `M3Holds` of the message, whatever the candidate witness.
example (s : K) (o : ∀ i, NoOracle i) (tr : (commitSpec toy).FullTranscript) (w : Column 3) :
    ((commitSecurity toy).kSF init impl).toFun (Fin.last 1) (s, o) tr w ↔
      M3Holds toy s (tr 0) := Iff.rfl

-- The extractor: both maps return the message.
example (s : K) (o : ∀ i, NoOracle i) (tr : (commitSpec toy).FullTranscript) :
    (commitExtractor toy).extractOut (s, o) tr () = tr 0 := rfl
example (s : K) (o : ∀ i, NoOracle i) (tr : (commitSpec toy).FullTranscript) (w : Column 3) :
    (commitExtractor toy).extractMid 0 (s, o) tr w = tr 0 := rfl

-- The commit phase's security is the one the composition starts from.
example : (commitSecurity toy).extractor = commitExtractor toy := rfl
example : (commitDef toy).n = 1 := rfl

end Commit

end Probe
```

Output:

```text
exit=0
```

### `P3cExtractor.lean`

```lean
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput

/-!
Probe P3c (code-spine): the type and the value of the composed extractor when a phase has
rounds. The last declaration is expected to fail.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

namespace Probe

/-! ## The composed extractor when a phase has rounds -/

/-- The toy's phases with the real public-input phase (two rounds) and four pass-throughs. -/
noncomputable def realPub : Phases toy where
  bus := Phase.passThrough toy fun s ↦ (s, ⟨[], []⟩)
  table := Phase.passThrough toy fun p ↦ (p.1, ⟨[]⟩)
  pub := publicInputPhase toy
  flock := Phase.passThrough toy fun p ↦ (p.1, ⟨[], []⟩)
  opening := Phase.passThrough toy fun _ ↦ ()

example : realPub.toDef.n = 3 := rfl

section

variable (Sb : Phase.Security toy realPub.bus (Seam.commit toy) (Seam.bus toy))
  (St : Phase.Security toy realPub.table (Seam.bus toy) (Seam.table toy))
  (Sf : Phase.Security toy realPub.flock (Seam.pub toy) (Seam.flock toy))
  (So : Phase.Security toy realPub.opening (Seam.flock toy) (Seam.done toy))

/-- A security bundle whose public-input field is the repository's. -/
def realPubSecurity : realPub.Security := ⟨Sb, St, publicInputSecurity toy, Sf, So⟩

-- The output slot of the composed extractor is the public-input phase's last intermediate
-- witness, `Unit`: it is not the stack.
example : (realPubSecurity Sb St Sf So).toDef.witMid (Fin.last 3) = Unit := rfl

-- The stack is what the composed extractor returns at round 0, from the transcript's first
-- message.
example : (realPubSecurity Sb St Sf So).toDef.witMid 0 = Column 3 := rfl

-- At round 0 the composed extractor returns the transcript's first message, whatever the
-- phases' extractors and whatever intermediate witness it is handed.
example (s : K)
    (tr : realPub.toDef.pSpec.Transcript (Fin.succ (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3)))
    (w : (realPubSecurity Sb St Sf So).toDef.witMid (Fin.succ (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3))) :
    (piopExtractor realPub (realPubSecurity Sb St Sf So)).extractMid
      (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) (s, fun i : Fin 0 ↦ i.elim0) tr w =
        (tr ⟨0, Nat.zero_lt_succ 0⟩ : Column 3) := rfl

-- EXPECTED TO FAIL: the repository's test statement, with the real public-input phase in the
-- bundle. The output slot is `Unit`, so the statement "`extractOut` returns the stack" does not
-- typecheck.
example (tr : realPub.toDef.pSpec.FullTranscript) :
    (piopExtractor realPub (realPubSecurity Sb St Sf So)).extractOut
      ((1 : K), fun i : Fin 0 ↦ i.elim0) tr () = honest := rfl

end

end Probe
```

Output:

```text
.claude/reports/blueprint-review/probes/code-spine/P3cExtractor.lean:58:49: error: Type mismatch
  honest
has type
  Column 3
but is expected to have type
  (realPubSecurity Sb St Sf So).toDef.witMid (Fin.last realPub.toDef.n)
exit=1
```

### `P4Junk.lean`

```lean
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.ToArkLib.GuardedVerdict
import LeanerVM.Protocol.ToArkLib.KeepOracles

/-!
Probe P4 (code-spine): `Phases.Security` of the toy instance is inhabited by five phases that
check nothing, each with one wasted challenge whose declared error is `1`.

A phase `wasted f ε`: the verifier draws one challenge in `E`, ignores it, and maps the
statement by `f`. It is complete whenever `f` carries the input seam into the output seam
(the pass-through's completeness). With declared error `ε = 1` it is round-by-round knowledge
sound for *any* two seams: the state is the input seam before the challenge and `True` after
it, and a probability is at most `1`.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp
  OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Probe

variable (I : M3Instance) {StmtIn StmtOut : Type}

/-- One round: a challenge in `E`. -/
@[reducible]
def wSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[E]⟩

instance : ∀ i, OracleInterface (wSpec.Message i)
  | ⟨0, h⟩ => nomatch h

instance : ∀ i, SampleableType (wSpec.Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType E)

/-- The prover receives the challenge and outputs the mapped statement. -/
def wProver (f : StmtIn → StmtOut) :
    OracleProver []ₒ StmtIn (TheOracle I) Unit StmtOut (TheOracle I) Unit wSpec where
  PrvState := fun _ ↦ (StmtIn × ∀ i, TheOracle I i) × Unit
  input := _root_.id
  receiveChallenge
    | ⟨0, _⟩ => fun st ↦ pure fun _ ↦ st
  sendMessage
    | ⟨0, h⟩ => nomatch h
  output := fun st ↦ pure ((f st.1.1, st.1.2), ())

/-- The verifier ignores the challenge, queries nothing and maps the statement. -/
def wVerifier (f : StmtIn → StmtOut) :
    OracleVerifier []ₒ StmtIn (TheOracle I) StmtOut (TheOracle I) wSpec where
  verify := fun s _ ↦ pure (f s)
  outputOracle := .inl (keepOracles (TheOracle I) wSpec)

theorem wVerifier_run (f : StmtIn → StmtOut) (s : StmtIn) (o : ∀ i, TheOracle I i)
    (tr : wSpec.FullTranscript) :
    (wVerifier I f).toVerifier.run (s, o) tr = pure (f s, o) := by
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl]
  rfl

/-- The verifier accepts every transcript. -/
def wPure (f : StmtIn → StmtOut) : (wVerifier I f).toVerifier.PureForm where
  verify := fun p _ ↦ (f p.1, p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ wVerifier_run I f s o tr

/-- The phase, with a declared error `ε` on its one challenge. -/
noncomputable def wasted (f : StmtIn → StmtOut) (ε : ℝ≥0) : Phase.Def I StmtIn StmtOut where
  n := 1
  pSpec := wSpec
  red := ⟨wProver I f, wVerifier I f⟩
  err := fun _ ↦ ε

theorem wProver_run_support (f : StmtIn → StmtOut) (s : StmtIn) (o : ∀ i, TheOracle I i)
    (pr : wSpec.FullTranscript × (StmtOut × ∀ i, TheOracle I i) × Unit)
    (hpr : pr ∈ support ((wProver I f).run (s, o) ())) : pr.2 = ((f s, o), ()) := by
  have h0 : wSpec.dir 0 = .V_to_P := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_one,
    Prover.processRound_of_dir_eq_V_to_P 0 h0] at hpr
  simp only [ChallengeIdx, Challenge, wProver, id_eq, liftM_pure, bind_pure_comp, map_pure,
    pure_bind, Functor.map_map, support_map, Set.mem_image] at hpr
  obtain ⟨r, -, rfl⟩ := hpr
  rfl

variable {relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit)}
  {relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)}

/-- Completeness, under the pass-through's hypothesis. -/
noncomputable def wastedComplete (f : StmtIn → StmtOut) (ε : ℝ≥0)
    (hc : ∀ s o, ((s, o), ()) ∈ relIn → ((f s, o), ()) ∈ relOut) :
    Phase.Complete I (wasted I f ε) relIn relOut where
  outputPure := ⟨_, fun _ ↦ rfl⟩
  guarded := (wPure I f).toGuardedForm
  complete := fun init impl ↦ by
    apply Reduction.perfectCompleteness_of_run_support
    intro stmtIn witIn hIn x hx
    obtain ⟨s, o⟩ := stmtIn
    obtain ⟨pr, hpr, rfl⟩ :=
      Reduction.mem_support_run_of_guarded _ (wPure I f).toGuardedForm (s, o) witIn hx
    have hout := wProver_run_support I f s o pr hpr
    have hc' : (wPure I f).toGuardedForm.check (s, o) pr.1 = true := rfl
    rw [if_pos hc']
    refine ⟨_, rfl, ?_, congrArg Prod.fst hout⟩
    have hw : pr.2.2 = () := rfl
    exact hw ▸ hc s o hIn

/-- The extractor keeps the trivial witness. -/
def wExtractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
    (StmtIn × ∀ i, TheOracle I i) Unit Unit wSpec (fun _ ↦ Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ ↦ ()
  extractOut := fun _ _ _ ↦ ()

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- A knowledge state function for ANY two seams: the input seam before the challenge, `True`
after it. No hypothesis on `f`, `relIn`, `relOut`. -/
def wState (f : StmtIn → StmtOut) :
    (wVerifier I f).toVerifier.KnowledgeStateFunction init impl relIn relOut
      (wExtractor I (StmtIn := StmtIn)) where
  toFun := fun m stmt _ _ ↦ if m.val = 0 then (stmt, ()) ∈ relIn else True
  toFun_empty := fun _ _ ↦ by simp
  toFun_next := fun m hm ↦ by
    fin_cases m
    exact absurd hm (by decide)
  toFun_full := fun _ _ _ _ ↦ by simp

/-- Round-by-round knowledge soundness at declared error `1`: a probability is at most one. -/
theorem w_rbr (f : StmtIn → StmtOut) :
    (wVerifier I f).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
      (fun _ ↦ Unit) (wExtractor I) (wState I init impl f) (fun _ ↦ 1) := by
  intro stmtIn i tr
  simp

/-- The security half at declared error `1`, under the completeness hypothesis alone. -/
noncomputable def wastedSecurity (f : StmtIn → StmtOut)
    (hc : ∀ s o, ((s, o), ()) ∈ relIn → ((f s, o), ()) ∈ relOut) :
    Phase.Security I (wasted I f 1) relIn relOut where
  toComplete := wastedComplete I f 1 hc
  witMid := fun _ ↦ Unit
  extractor := wExtractor I
  kSF := fun init impl ↦ wState I init impl f
  rbr := fun init impl ↦ w_rbr I init impl f

/-! ## The toy's five phases, checking nothing -/

/-- Five phases that draw a challenge and drop every claim. -/
noncomputable def junkPhases : Phases toy where
  bus := wasted toy (fun s ↦ (s, ⟨[], []⟩)) 1
  table := wasted toy (fun p ↦ (p.1, ⟨[]⟩)) 1
  pub := wasted toy (fun p ↦ (p.1, ⟨[]⟩)) 1
  flock := wasted toy (fun p ↦ (p.1, ⟨[], []⟩)) 1
  opening := wasted toy (fun _ ↦ ()) 1

/-- `Phases.Security` of the toy is inhabited by them. -/
noncomputable def junkSecurity : junkPhases.Security where
  bus := wastedSecurity toy _ fun _ _ h ↦ ⟨by simp, by simp, by simp, h.2.2.2.1, h.2.2.2.2⟩
  table := wastedSecurity toy _ fun _ _ h ↦ ⟨by simp, h.2.2.2.1, h.2.2.2.2⟩
  pub := wastedSecurity toy _ fun _ _ h ↦ ⟨by simp, h.2.2⟩
  flock := wastedSecurity toy _ fun _ _ _ ↦ ⟨by simp, by simp⟩
  opening := wastedSecurity toy _ fun _ _ _ ↦ trivial

example : junkPhases.toDef.n = 6 := rfl

/-- Their completeness halves. -/
noncomputable def junkComplete : junkPhases.Complete :=
  ⟨junkSecurity.bus.toComplete, junkSecurity.table.toComplete, junkSecurity.pub.toComplete,
    junkSecurity.flock.toComplete, junkSecurity.opening.toComplete⟩

/-- Both master theorems hold of the junk protocol. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop junkPhases).perfectCompleteness init impl (M3Rel toy) (Seam.done toy) :=
  piop_perfectCompleteness junkPhases junkComplete init impl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier junkPhases).toVerifier.rbrKnowledgeSoundnessWorstCase init impl (M3Rel toy)
      (Seam.done toy) (piopError junkPhases) :=
  piop_rbrKnowledgeSoundness_exists junkPhases junkSecurity init impl

/-- Appending keeps a constant declared error. -/
theorem append_err_const {S₁ S₂ S₃ W₁ W₂ W₃ : Type} {ι₁ ι₂ ι₃ : Type} {O₁ : ι₁ → Type}
    {O₂ : ι₂ → Type} {O₃ : ι₃ → Type} [∀ i, OracleInterface (O₁ i)]
    [∀ i, OracleInterface (O₂ i)] [∀ i, OracleInterface (O₃ i)]
    (D₁ : Component.Def S₁ O₁ W₁ S₂ O₂ W₂) (D₂ : Component.Def S₂ O₂ W₂ S₃ O₃ W₃) (c : ℝ≥0)
    (h₁ : ∀ i, D₁.err i = c) (h₂ : ∀ i, D₂.err i = c) : ∀ i, (D₁.append D₂).err i = c := by
  intro i
  change Sum.elim D₁.err D₂.err (ChallengeIdx.sumEquiv.symm i) = c
  cases ChallengeIdx.sumEquiv.symm i with
  | inl a => exact h₁ a
  | inr b => exact h₂ b

/-- Every challenge of the junk protocol carries the declared error `1`. -/
theorem piopError_junk (i : junkPhases.toDef.pSpec.ChallengeIdx) : piopError junkPhases i = 1 := by
  unfold piopError Phases.toDef
  refine append_err_const _ _ 1 (append_err_const _ _ 1 (append_err_const _ _ 1
    (append_err_const _ _ 1 (append_err_const _ _ 1 ?_ ?_) ?_) ?_) ?_) ?_ i
  · rintro ⟨j, hj⟩
    fin_cases j
    exact absurd hj (by decide)
  all_goals intro _; rfl

#print axioms junkSecurity
#print axioms piopError_junk

end Probe
```

Output:

```text
'Probe.junkSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.piopError_junk' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

### `P5PassThrough.lean`

```lean
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose

/-!
Probe P5 (code-spine): the pass-through bus phase of the repository's test (`trivPhases.bus`)
has no `Phase.Security` against the spine's seams, on the toy instance.

`badConstraint` at statement `2` is outside `M3Holds` and the pass-through's output on it (no
claim) is inside the bus seam. A knowledge state function must be true at the end of an
accepting transcript and, the phase having no round, the end is the beginning, where the state
is the input seam.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp
  OracleSpec ProtocolSpec

namespace Probe

/-- The test's stack `badConstraint`: column 2 is `[2, 0]`. -/
def badConstraint : Column 3 := ⟨#v[1, 1, 1, 1, 2, 0, 0, 0]⟩

/-- The statement map of `trivPhases.bus`: no claim. -/
def dropAll (s : K) : K × BusOut toy := (s, ⟨[], []⟩)

/-- Outside the relation. -/
theorem bad_not_m3Holds : ¬ M3Holds toy (2 : K) badConstraint := by decide +kernel

/-- Inside the bus seam, with no claim. -/
theorem bad_mem_bus :
    ((dropAll 2, fun _ : Fin 1 ↦ badConstraint), ()) ∈ Seam.bus toy :=
  ⟨by simp [dropAll], by simp [dropAll], by simp [dropAll], by decide +kernel, trivial⟩

/-- The reflection hypothesis of `Phase.passThroughSecurity` is false at the bus seam. -/
theorem not_reflects : ¬ ∀ (s : K) (o : ∀ i, TheOracle toy i),
    ((dropAll s, o), ()) ∈ Seam.bus toy → ((s, o), ()) ∈ Seam.commit toy := fun h ↦
  bad_not_m3Holds (h 2 (fun _ ↦ badConstraint) bad_mem_bus)

/-- The empty implementation of the empty shared oracle. -/
def noImpl : QueryImpl []ₒ (StateT Unit ProbComp) := fun t ↦ PEmpty.elim t

/-- No `Phase.Security` exists for the pass-through bus phase: not only the repository's
constructor fails, the type is empty. -/
theorem no_security (S : Phase.Security toy (Phase.passThrough toy dropAll) (Seam.commit toy)
    (Seam.bus toy)) : False := by
  have ksf := S.kSF (pure ()) noImpl
  let stmt : K × ∀ i, TheOracle toy i := (2, fun _ ↦ badConstraint)
  let tr : (Phase.passThrough toy dropAll).pSpec.FullTranscript := fun i ↦ Fin.elim0 i
  have htr : tr = (default : (Phase.passThrough toy dropAll).pSpec.Transcript 0) :=
    funext fun i ↦ Fin.elim0 i
  have hpos : Pr[fun stmtOut ↦ (stmtOut, ()) ∈ Seam.bus toy | OptionT.mk do
      (simulateQ noImpl ((Phase.passThrough toy dropAll).red.verifier.toVerifier.run stmt
        tr)).run' (← (pure () : ProbComp Unit))] > 0 := by
    have hrun : (Phase.passThrough toy dropAll).red.verifier.toVerifier.run stmt tr =
        pure (dropAll 2, fun _ ↦ badConstraint) :=
      Component.passThroughVerifier_toVerifier_run (TheOracle toy) dropAll 2
        (fun _ ↦ badConstraint) tr
    rw [hrun]
    change Pr[_ | OptionT.mk (do let st ← (pure () : ProbComp Unit); (simulateQ noImpl
      (OptionT.run (pure (dropAll 2, fun _ : Fin 1 ↦ badConstraint)))).run' st)] > 0
    rw [OptionT.run_pure, simulateQ_pure]
    rw [gt_iff_lt, probEvent_pos_iff]
    refine ⟨(dropAll 2, fun _ ↦ badConstraint), ?_, bad_mem_bus⟩
    simp
  have hfull := ksf.toFun_full stmt tr () hpos
  rw [htr] at hfull
  exact bad_not_m3Holds ((ksf.toFun_empty stmt _).mpr hfull)

#print axioms no_security

end Probe
```

Output:

```text
'Probe.no_security' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

### `P6Surface.lean`

```lean
import LeanerVM.Protocol.ToArkLib.Component
import LeanerVM.Protocol.ToArkLib.Refinement

/-!
Probe P6 (code-spine): three facts behind section B's proposals and section C.7.

1. The field `Component.Complete.outputPure` holds of every component: the shared oracle is
   empty, so the prover's output makes no query. (ArkLib has this at the pin as the instance
   `Prover.instOutputIsPureEmpty`, `Composition/Sequential/NoAmbient.lean:39-42`, in a module
   leanerVM does not import and whose `.olean` is not built; it is restated here.)
2. The universes of `Refinement`: whether its two witness types may live in different
   universes (`Column μ : Type`, Clean's `EnsembleWitness : Type 1`). The last `example` of that
   section is the one that decides it.
3. Knowledge transports along a refinement at the same error, with the map applied in the
   event and the game, the provers and the extractor left alone.
-/

open OracleComp OracleSpec ProtocolSpec LeanerVM.Protocol
open scoped NNReal

namespace Probe

/-! ## 1. `outputPure` is automatic -/

/-- The result of a computation that has no possible oracle query (ArkLib
`NoAmbient.lean:25-27` at `dca90385`, restated). -/
def runEmpty {α : Type} : OracleComp []ₒ α → α
  | .pure a => a
  | .liftBind t _ => isEmptyElim t

/-- Every computation over the empty specification is its pure result (`NoAmbient.lean:30-35`,
restated). -/
theorem eq_pure_runEmpty {α : Type} (oa : OracleComp []ₒ α) : oa = pure (runEmpty oa) := by
  cases oa with
  | pure a => rfl
  | queryBind t _ => exact isEmptyElim t

/-- The field `outputPure`, for every component, from its definition alone. -/
theorem outputPure_of_def {StmtIn : Type} {ιi : Type} {OStmtIn : ιi → Type} {WitIn : Type}
    {StmtOut : Type} {ιo : Type} {OStmtOut : ιo → Type} {WitOut : Type}
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]
    (D : Component.Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut) :
    D.red.prover.OutputIsPure :=
  ⟨fun st ↦ runEmpty (D.red.prover.output st),
    fun st ↦ eq_pure_runEmpty (D.red.prover.output st)⟩

#print axioms outputPure_of_def

/-! ## 3. Knowledge transports along a refinement, in the event -/

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- If `E` extracts a witness of `R` except with probability `ε`, then the same extractor
followed by the map of a refinement from `R` to `S` yields a witness of `S` except with
probability `ε`. -/
theorem knowledge_transport {R : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {W₂ : Type} {S : Set (StmtIn × W₂)} (f : Refinement R S)
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec} {ε : ℝ≥0}
    (h : verifier.knowledgeSoundnessWith init impl R relOut E ε)
    (stmtIn : StmtIn) (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    let exec := do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
        ← (Reduction.mk prover verifier).runWithLog stmtIn witIn
      let extractedWitIn? ←
        liftM (E stmtIn witOut transcript proveQueryLog.fst verifyQueryLog).run
      return (stmtIn, extractedWitIn?, stmtOut, witOut)
    Pr[fun ⟨stmtIn, extractedWitIn?, stmtOut, witOut⟩ =>
        (∀ w ∈ extractedWitIn?, (stmtIn, f.map stmtIn w) ∉ S) ∧ (stmtOut, witOut) ∈ relOut
      | OptionT.mk do (simulateQ pImpl exec.run).run' (← init)] ≤ ε :=
  le_trans (probEvent_mono fun _ _ hx ↦
    ⟨fun w hw hR ↦ hx.1 w hw (f.map_valid _ _ hR), hx.2⟩) (h stmtIn witIn prover)

#print axioms knowledge_transport

/-! ## 2. The universes of `Refinement` -/

#check @Refinement

/-- A witness type in `Type 1`, as Clean's `EnsembleWitness` is. -/
structure Big : Type 1 where
  carrier : Type

/-- Decides the question: a refinement from a relation whose witness is in `Type` to one whose
witness is in `Type 1`. Accepted if the two witness universes of `Refinement` are independent,
rejected if `{W₁ W₂ : Type _}` gave them one universe. -/
example : Refinement (Stmt := Unit) {p : Unit × ℕ | True} {p : Unit × Big | True} where
  map := fun _ n ↦ ⟨Fin n⟩
  map_valid := fun _ _ _ ↦ trivial

end Probe
```

Output:

```text
'Probe.outputPure_of_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.knowledge_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
@Refinement : {Stmt : Type} → {W₁ : Type u_1} → {W₂ : Type u_2} → Set (Stmt × W₁) → Set (Stmt × W₂) → Type (max u_1 u_2)
(two linter warnings on unused binder names, omitted)
exit=0
```
