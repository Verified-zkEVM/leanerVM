# Review: the proof-system spine (PR #58)

Reviewed on 2026-09-28 against branch `docs/protocol-spine` at `00ab835` (five commits over
`main` at `cd5f60a`), read-only, with the repository's `adversarial-review` skill. Sources:
leanVM at the pin `a386121f84292f6fa663aaa3e570c15bc0240ea2` (`doc/leanvm/body/03`, `04`, `05`,
`06`, `08`; `crates/lean_vm/src/{witness.rs,leaf.rs,tables.rs,cpu/layout.rs,cpu/mod.rs}`),
ArkLib `dca90385` (`OracleReduction/Security/{Basic,RoundByRound,Implications}.lean`,
`Composition/Sequential/{Append/Security,OracleCompleteness}.lean`,
`CoordinateWiseSpecialSoundness/Guarded.lean`, `OracleInterface.lean`), ArkLib pull request
#615 at `ca7a2577` (`Append/Knowledge.lean`), CompPoly `3468b38c`
(`Multivariate/CMvPolynomial.lean`), Clean `93c9d1ef` (`Air/{FlatComponent,FlatEnsemble}.lean`),
and leanISA Layers 5 to 8 (`LeanerVM/Arithmetization/{Channels,Boundary,Statement}.lean`).
Every changed Lean file was read in full; the blueprint, the status file, the PR body, the hole
comment on #12 and the bodies of #18 and #38 to #44 were read for intent.

This is an implementation handoff. Findings are confirmed against `00ab835`; the fixes below
are work to implement, and the disposition table is for whoever lands them.

Validation of the reviewed commit passed:

- `./scripts/validate.sh` (exit 0; the axiom audit reports 2757 declarations and no unexpected
  axiom); `audit-lean.sh`, `check-layers.sh`, `check-imports.sh`, `check-repository.sh` each
  pass on their own.
- `#print axioms` on `piop_perfectCompleteness`, `piop_rbrKnowledgeSoundness`,
  `commitSecurity`, `Component.sendOracleSecurity`, `Component.passThroughComplete`,
  `Toy.read_eval`: `propext`, `Classical.choice`, `Quot.sound` only.
- `KnowledgeAppend` elaborates as a `Prop` (a structure with one propositional field), as the
  trusted-surface convention wants (discharged on the branch, see the disposition).

## Disposition

| Finding | Disposition |
| --- | --- |
| A1 (high): `Seam.bus` admits claims the table sumcheck cannot prove | Met: `M3Instance.d` with the proof fields `constraints_degree` and `flushes_degree` (the toy's `d := 2`); `VirtualTerm.poly : CMvPolynomial (I.width j) K` with the `E` weight per term, so a bus form is a list of terms and no `E`-coefficient polynomial is built; `Seam.bus`'s second conjunct, every term of every linear claim of total degree at most `I.d`; tests `constraintTerm` (degree 2 accepted), the cubic rejected, and a bus statement carrying `cubicTerm` proved outside `Seam.bus`; blueprint acceptance test 28, status decision 14. Deviation: the toy's two degree proofs go through `totalDegree_equiv` and Mathlib's `MvPolynomial` degree lemmas, not `decide`, which cannot unfold CompPoly's `X` and `*` inside a `module` (status finding E9); the plain test file decides the same degrees by `decide +kernel`. |
| A2 (high): the auxiliary predicate's strength is undetermined, and each choice breaks one direction of the Flock seam or the adaptor | Met in the documentation: the strong reading adopted (status decision 12); the blueprint's Layer 3 and Layer 9 and the status file's I2 and P6 rows record the two #3 dependencies (`satisfiedBy_witnessOf` discharges `blake2s_valid` through #3's "the R1CS holds ⇒ the limb slots compress"; `stackOf` takes #3's witness generator, `FlockWitnessGen`, as an explicit argument). No Lean change is possible until #3 supplies a term; the toy's `aux` is `True`. Left for the author (a Lean edit outside this pass): the `Instance.lean` module docstring still glosses `aux` as "for leanISA, that the BLAKE2s rows are valid compressions", the weak reading, and the `aux` field docstring does not yet name the obligation (fix 1 and the guard comment of fix 3). |
| A3 (medium): the master knowledge theorem does not name its extractor | Met: `Component.Security` carries `witMid`, `extractor`, `kSF` and `rbr` in ArkLib's `rbrKnowledgeSoundnessWorstCaseWith` form; `piopExtractor A P S` is a definition, `piop_rbrKnowledgeSoundness` is stated for it and its state function, and `piop_rbrKnowledgeSoundness_exists` is the existential corollary; the test proves by `rfl` that `piopExtractor A trivPhases S` returns the honest stack on `honestFullTranscript`, for any `A` and `S`. Design change from the fix as written: `KnowledgeAppend` has two fields, not four, `kSFAppend` (the knowledge state function of `E₁.append E₂ G.out`) and `append` (the bound), because the appended extractor is ArkLib's own `Extractor.RoundByRound.append` at the pin; the composed extractor therefore does not depend on the assumption, only its state function and the bound do. `KnowledgeAppend` became data (`Type 1`), no longer a `Prop`; and the assumption is discharged: `KnowledgeAppend` deleted, #615's proof ported to `ToArkLib/KnowledgeAppend.lean`, so `Component.Security.append`, `piopExtractor P S` and the two knowledge theorems take no `A`, and the `rfl` test is stated for any `S`. |
| A4 (medium): `publicCells` cannot be served by the public-input phase as specified | Met, by the recommended fix: `PublicLine` (`col`, `cell0`, `cell1`, `pos : 0 < τ col.1`), `publicLines`, `PublicLinesHold`; the toy's public line is column 2 with cells `(v, 0)`, and the mutation `badLine` fails the line clause alone; the blueprint's Layer 8 (P5) is over the lines, with one challenge and no prover message, and leaves the Rust's two scalars and combined check to Layer 12 to reconcile; status decision 13. |
| A5 (medium): `satisfiedBy_witnessOf` as stated in the roadmap is unprovable (the caps) | Met in the documentation: `satisfiedBy_witnessOf (hs : s.Admissible prog) (h : M3Holds …)` in the blueprint's Layer 3, with the reason and where the hypothesis is discharged (Layer 13: `verify` checks the announced sizes); decision 8's wording in the status file. |
| A6 (low): no `Phase.Security` inhabitant and no pass-through knowledge half | Met: `Component.passThroughExtractor`, `passThroughStateFunction`, `passThrough_rbr`, `passThroughSecurity` and `Phase.passThroughSecurity`, knowledge sound at error zero when `f` reflects the output relation into the input relation; the tests inhabit a `Phase.Security` by the identity pass-through at the public-input seam. No `trivPhases.Security` term was added, so the `rfl` test of A3 quantifies over `S`. |
| B1 (low): citation drift, and the PDF handed to the review is not the pinned text | Met: `Instance.lean` cites §5.1 for the flushes and §4.1 with §5.4 equation (2) for `Layout`; the status file's finding S14 records that `leanVM-b-2.pdf` is not the pinned text and must not be cited. |
| B2 (low): status finding S13 is stated against a text that is not the pin | Met: S13 retired in the status file, with the reason (`05-arithmetization.tex:37` at the pin already says `4·2^μ/|E|`). |
| I1 (medium): `E`-coefficient polynomials have no ring operations at the pin | Not needed after A1: every polynomial is over `K`; recorded as status finding E7. |
| I2 (low): scalar prover messages have no `OracleInterface` | Met: `instOracleInterfaceE` and `instOracleInterfaceListE` in `LeanerVM/Protocol/Field.lean` (ArkLib's `OracleInterface.instDefault`), with `#synth` guards in `tests/LeanerVMTests/Protocol/Field.lean`; status finding E8. |
| I3 (low): the layout plan covers aligned blocks only; the eighteen virtual limb columns need a strided reader | Met in the documentation: the blueprint's Layer 3 gives the layout two readers (#18's `Blocks` for the aligned blocks, a strided reader for the limb slots of `q_flock`, the slot map `FlockInterface.limbColumns`), Layer 9 names `limbColumns` the strided reader, and the status file's I2 and #18 rows say so. |
| C1 (low): the PR body is stale after `00ab835` | The proposed "What is added" section, updated to the final names, is under [Edits to make on GitHub](#edits-to-make-on-github-not-applied-by-this-review), for the author to post. `Extractor.Straightline.map` is kept, as an ArkLib candidate without a consumer yet. |
| C2 (low): module docstrings do not state the target contribution | Met: `Compose.lean`'s module docstring states what the two theorems assume and where they sit (the ideal oracle model, an abstract instance, conditional only on the phases' proofs since the append was ported, see A3); the Category A and T4 classification is in the proposed PR body. |
| H1 to H6: audit-surface compressions | Met: H1 (`Shape`, `Shape.ColumnId`; `Coord`, `BoundaryBlock` and `PublicLine` over `(S : Shape)`; `M3Instance extends Shape`), H2 (`deriving instance Decidable`), H3 (`Seam.of`), H4 (`read_eval` as one `simp`, the two private lemmas deleted), H5 (the shorter `guardedAppend`), H6 (the pass-through's knowledge half and `Phase.passThroughSecurity`). Deviation under H1 and A1: `Toy.lean` gained three imports (CompPoly's `Multivariate.MvPolyEquiv.Eval` and `Multivariate.Operations`, Mathlib's `Algebra.MvPolynomial.CommRing`) for its two degree proofs, which go through Mathlib (status finding E9). |

## Verdict in one paragraph

No theorem statement is wrong for what it says, every stated theorem is proved with the kernel's
standard axioms, `M3Holds` is non-vacuous and each clause is load-bearing on the toy, the seams
compose by definition, and the two master theorems are inhabited by the five pass-through
phases. The defects are at the level the user asked about: the *interfaces*. As built, the
seams and the instance admit inputs the intended phases cannot serve (A1, A4), leave the one
predicate that crosses into the Flock roadmap under-determined in a way that makes one of its
two natural readings incomplete (A2), certify an existential extractor where the roadmap
promises a computable one (A3), and the adaptor's soundness theorem cannot be stated as the
roadmap writes it (A5). None of these shows up while the holes are open; each shows up as an
unprovable `Complete` or an unstatable adaptor lemma the moment a hole is filled. All are
cheap to fix in the spine now and expensive after P1 to P8 are written against the current
seams.

## Pass A: specification

### A1 (high). `Seam.bus` admits linear claims the table sumcheck cannot prove

`Seams.lean:60-88`, `VirtualTerm.poly : CMvPolynomial (I.width j) E` with no degree bound, and
`Seam.bus` (`:159-163`) says only that every listed claim holds. The table phase's completeness
obligation, `Phase.Complete I P.table (Seam.bus I) (Seam.table I)`, therefore ranges over every
`BusOut` whose claims are *true*, including ones the honest bus phase never emits: a term whose
polynomial has degree 5, or a polynomial with `E` coefficients that no honest run produces.

Concrete failure. Take the toy, `deg5 : VirtualTerm toy := ⟨1, 0, X₂ ^ 5, #v[0]⟩`, and the
statement `((1, ⟨[⟨[deg5], deg5.eval honest⟩], []⟩), fun _ ↦ honest)`. It is in `Seam.bus toy`
(the claim is true by construction). The table sumcheck of §5.5 sends cubic round polynomials;
the summand `eq(ζ, X) · X₂(X)^5` has degree 6 in each variable, so the honest prover's round
polynomial fails the verifier's degree check or the final check, and `tableSumcheck` is not
perfectly complete on this input. Hence `Phases.Complete` has no inhabitant whose `table` field
is the intended phase, and `piop_perfectCompleteness` is vacuous for the real protocol. (The
snippet does not even elaborate at the pin, for the reason in I1; the type admits it.)

The same over-generality applies to the *points*: a generic eq-weighted sumcheck (Layer 4) is
complete for arbitrary per-term points, so that part is not a defect, but the degree is.

Fix, in this order:

1. Give the instance its degree, as the hole-S specification asked ("constraint polynomials of
   degree ≤ 2"): a field `d : ℕ` on `M3Instance` with `constraints_degree : ∀ j, ∀ C ∈
   constraints j, C.totalDegree ≤ d` and `flushes_degree` likewise (CompPoly's
   `CMvPolynomial.totalDegree`, `CMvPolynomial.lean:231`, is computable, so the toy discharges
   them by `decide`). leanISA's instance has `d = 2` (`leanIsaInstance_degree`, Layer 3).
2. Change `VirtualTerm.poly` to `CMvPolynomial (I.width j) K` and `VirtualTerm.table` to
   `Vector.ofFn fun x ↦ ofK (t.poly.eval (I.row q t.j x))`. Every claim the protocol raises is
   an `E`-linear combination of `K`-polynomials of the row: a zerocheck claim is `(1, j, C_{j,i},
   ζ_{<τ_j})`; a bus form `B^s_j = Σ_b eq(sel_b, ζ_hi) (β − Σ_i eq(α, i) c_{b,i})` is the list of
   terms `(eq(sel_b, ζ_hi) · eq(α, i), j, c_{b,i}, ζ_{<τ_j})` plus one term `(eq(sel_b, ζ_hi) ·
   β, j, C 1, ζ_{<τ_j})`. This also removes the need to lift `I.constraints` to `E` (no
   `CMvPolynomial.map` exists at the pin) and sidesteps I1 entirely.
3. Add the degree conjunct to `Seam.bus`: `∀ c ∈ p.1.1.2.linear, ∀ t ∈ c.terms,
   t.poly.totalDegree ≤ I.d`. The bus phase's knowledge soundness then owes it, by
   construction; the table phase's completeness may assume it.
4. Test: on the toy, a `BusOut` carrying a degree-3 term is not in `Seam.bus` (by `decide` on
   the new conjunct), and the degree-2 zerocheck claim of the toy's constraint is.

### A2 (high). The auxiliary predicate is under-determined, and each reading breaks a direction

`Instance.lean:122-125`: `aux : Column μ → Prop`, "what the Flock phase establishes about the
stack beyond the polynomial checks (for leanISA, that the BLAKE2s rows are valid
compressions)". The blueprint's Layer 3 and Layer 9 (`FlockInterface.relIn`: "the eighteen
column claims are true of `limbColumns` and the rows are valid compressions") say the same:
the weak reading, `aux q := ∀ row, Blake2sRelation (limbs read from q_flock)`.

The Flock phase's completeness is stated at `Seam.pub → Seam.flock`: on every stack with
`aux q`, the honest prover convinces the verifier. Flock's argument is a zerocheck and lincheck
over the *R1CS witness* packed into the `q_flock` region (§4.2, §8.5 "BLAKE2s validity",
Annex C), and that region was committed in the commit phase. Under the weak reading a stack
whose eighteen limb slots hold a valid compression and whose other `q_flock` slots are zero
satisfies `M3Holds`, and no honest Flock prover can convince on it: the wires are wrong and
cannot be changed after the commitment. So `Phase.Complete I P.flock (Seam.pub I) (Seam.flock
I)` is false for the intended phase, and `piop_perfectCompleteness` is vacuous for it.

Under the strong reading, `aux q := Flock's R1CS holds of the bits of the q_flock region`,
completeness of the Flock phase is fine, and two adaptor obligations move into #3's territory:
`satisfiedBy_witnessOf` needs #3's soundness lemma "R1CS satisfied ⇒ the limb slots
compress" to discharge `blake2s_valid`, and `stackOf` (the completeness direction,
`m3Holds_stackOf`) must *compute* the R1CS witness from the limbs, since an `EnsembleWitness`
carries the limbs and nothing else. Neither is written anywhere; both are the kind of unknown
the user asked for.

Fix (a decision for the user, then text):

1. Adopt the strong reading. Rewrite the `aux` docstring: "the predicate the Flock phase proves
   of the committed region: for leanISA, that Flock's R1CS holds of the bits packed into
   `q_flock`; the compression of the eighteen limb slots is a consequence (#3's soundness
   lemma), never the predicate itself".
2. Blueprint Layer 3: `witnessOf` reads the limbs off `q_flock`; `satisfiedBy_witnessOf`
   consumes #3's "R1CS ⇒ compression"; `stackOf` consumes #3's witness generator (or the
   completeness ladder starts from the prover's stack, which already holds the wires, and
   `m3Holds_stackOf` is stated on that: say which). Blueprint Layer 9 and the P6 and I2 hole
   sections: the same two named dependencies. Status decision list: record it as a decision
   (the next free number).
3. Test on the toy: nothing (its `aux` is `True`); a guard comment on `aux` naming the
   obligation is enough until #3 supplies a term.

### A3 (medium). The master knowledge theorem does not name its extractor

`Compose.lean:143-149` proves `rbrKnowledgeSoundnessWorstCase`, which is `∃ WitMid extractor
kSF, …` (ArkLib `RoundByRound.lean:534`); `Component.Security.rbr` (`Component.lean:87-89`) and
`KnowledgeAppend` (`:96-110`) are in the same existential form. The composed extractor is
therefore *some* extractor, and nothing ties it to `commitExtractor` followed by identities.
The Compose docstring ("Its extractor begins with the commit phase's, which reads the stack off
the first message; the later phases' extractors are the identity") and the PR body claim more
than the theorem states, and convention *Extractors* / acceptance test 24 ("the extractor
computes") are not enforced by any statement: a hole could discharge `Phase.Security` with
ArkLib's classical `toRoundByRoundOfRel` and the master theorem would not notice.

ArkLib #615 (`Append/Knowledge.lean:482-488`) proves the extractor-naming form,
`append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first (G : V₁.GuardedForm) (K₁ K₂) (h₁ :
V₁.rbrKnowledgeSoundnessWorstCaseWith … W₁ E₁ K₁ ε₁) (h₂ : …) : (V₁.append
V₂).rbrKnowledgeSoundnessWorstCaseWith … (Witness W₁ W₂) (E₁.append E₂ G.out)
(KnowledgeStateFunction.appendGuarded G K₁ K₂) …`, and derives the existential form from it
(`:570-581`); the shape the spine copied is the derived one.

Fix:

1. `Component.Security` carries the data: fields `witMid : Fin (D.n + 1) → Type`, `extractor :
   Extractor.RoundByRound []ₒ (StmtIn × ∀ i, OStmtIn i) WitIn WitOut D.pSpec witMid`, `kSF : ∀
   {σ} init impl, D.red.verifier.toVerifier.KnowledgeStateFunction init impl relIn relOut
   extractor`, `rbr : ∀ {σ} init impl, …rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
   witMid extractor (kSF init impl) D.err`.
2. `KnowledgeAppend` in the `With` form, carrying the two constructions it needs as fields
   (their types are the spine's to write; #615's `Extractor.RoundByRound.append` and
   `KnowledgeStateFunction.appendGuarded` are the terms): `witAppend`, `extractorAppend`,
   `kSFAppend`, and `append` stated with them. C1 supplies all four from #615.
3. `Security.append` composes the data; `Phases.Security.toDef` likewise; a definition
   `piopExtractor (A) (P) (S) : Extractor.RoundByRound …` and `piop_rbrKnowledgeSoundness`
   stated `With` it. `commitSecurity` names `commitExtractor` (it already does, inside the
   proof).
4. Test: with A6's `passThroughSecurity`, `trivSecurity : trivPhases.Security` exists on the
   toy, and `#guard`/`example` that `(piopExtractor A trivPhases trivSecurity).extractOut`
   applied to the honest transcript returns `honest` (needs a `KnowledgeAppend` term only for
   the *statement*; state the example over a variable `A`).

If the refactor is judged too heavy for this PR, the minimum is to delete the two overstated
sentences (docstring and PR body) and to say in the blueprint that acceptance test 24 is met by
the commit phase alone until `KnowledgeAppend` is stated in the `With` form.

### A4 (medium). `publicCells` cannot be served by the public-input phase as specified

`Instance.lean:73-80, 118-119`: `publicCells : Stmt → List (PublicCell …)`, an arbitrary list of
(column, row, value). The public-input phase of §8.2 and `cpu/mod.rs:745-755` draws one
`r_m`, reads two scalars, checks the line `(1 + r_m)·mem[g^0]_ℓ + r_m·mem[g^1]_ℓ` for the two
low limbs, and pools three claims at `(r_m, 0, …, 0)` on `mem_0, mem_1, mem_2` (the third with
value 0). That phase presupposes that the public cells are rows 0 and 1 of three columns of
one table; it is not definable over an arbitrary `List PublicCell` (which row pairs share a
line? which columns get a scalar?). A generic P5 over the list as built can only pool one
`ColumnClaim` per cell at a Boolean point, with no challenge and no message: sound, complete,
and a different schedule from the Rust stream, which K3's `verify_iff_compiled` would then
have to reconcile (two redundant scalars in the proof).

Fix (recommended): replace `PublicCell` by a *line*: `structure PublicLine … where col :
ColumnId …; cell0 cell1 : K` with the clause `PublicLinesHold input q := ∀ l ∈ I.publicLines
input, (I.column q l.col).values.get 0 = l.cell0 ∧ (…).get 1 = l.cell1` (this needs `1 < 2 ^ τ`,
which every leanISA column of the memory table has; state `idx : Fin 2` cast, or require
`0 < τ` on the column through a proof field). The leanISA instance has three lines, on
`mem_0, mem_1, mem_2`, the third with cells `0, 0`. P5 then is generic: one challenge, for each
line pool `⟨col, (r, 0, …), (1 + r)·a + r·b⟩`, sending nothing (the two Rust scalars are
redundant with what the verifier computes, and are K3's encoding to check, like the dropped
round coefficient). Alternative: keep cells and accept the Boolean-point P5; then write that
decision into the P5 and K3 hole sections. Note for K3 either way: the Rust checks the one
combined equation `c_0 + Y·c_1 = interp(pi_0, pi_1, r)` (`cpu/mod.rs:751-753`), which is
equivalent to the two limb equations because `1, Y, Y²` is a `K`-basis of `E` and the cells are
`K`-valued.

### A5 (medium). `satisfiedBy_witnessOf` as the roadmap states it is unprovable

Blueprint Layer 3 and the I2 hole section: `satisfiedBy_witnessOf (h : M3Holds (leanIsaInstance
prog s) input q) : SatisfiedBy prog input (witnessOf prog s q)`. `SatisfiedBy` has the conjunct
`caps : Caps w` (`Statement.lean:250-266`): the memory log-size window, every height at most
`2^maxLogRows`, the `BLAKE2S` floor, and `WellShapedData`. Decision 8 puts the caps outside
`M3Holds`, so nothing in the hypothesis bounds `s`: for `s.logMem = 40` the conclusion is
false. The same `s` also breaks the other direction silently: `imageOf` truncates at
`maxLogMem` (`Channels.lean`, `imageOf`), so `SeedRowsAreTheImage (witnessOf q)` fails for an
over-cap image.

Fix: `satisfiedBy_witnessOf (hs : s.Admissible prog) (h : M3Holds …)` and `m3Holds_stackOf (h :
SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)` (the latter already carries the
admissibility through `Caps`). The hypothesis is available at K4 because `verify` checks the
announced sizes before the oracle protocol starts (`read_public`, `cpu/mod.rs:130-178`), and
`verify_iff_compiled` quantifies `∃ s, s.Admissible prog ∧ …`. Update the blueprint's Layer 3
block, the I2 hole section on #12, and `docs/roadmap/protocol-status.md` (decision 8's
wording: "the caps are not a clause of `M3Holds`; they are a hypothesis of the adaptor's
soundness theorem, discharged by the compiled verifier").

### A6 (low). No `Phase.Security` inhabitant; no pass-through knowledge half

`tests/LeanerVMTests/Protocol/Spine.lean:98-112` inhabits `Phases` and `Phases.Complete` with
five pass-through phases and says why `Phases.Security` has none: dropping every claim is not
knowledge sound. True on the toy. But the pass-through *is* knowledge sound whenever `f`
reflects the output relation into the input relation (`∀ s o w, ((f s, o), w) ∈ relOut → ((s,
o), w) ∈ relIn`), at error zero, with the identity extractor; that is the shape of every
bookkeeping step inside P5 and P6, and on an instance with no constraints, no flushes, no
counts, no public cells and `aux := True` it inhabits every `Phase.Security` field, so that
`Phases.Security.toDef A S` has an instance for any `A`. Prototyped: see H6 below.

Fix: add `Component.passThroughSecurity` to `PassThrough.lean` (H6 has the text), and a test
`trivSecurity` on an all-trivial instance (or on the toy for the `opening` and `flock` fields,
whose seams reflect trivially).

### Pass A, clean

- `M3Holds` on the toy: the honest stack passes; each of the four checkable clauses fails alone
  (`badConstraint` at statement 2, `badBalance`, `badCount`, the wrong statement); the
  characteristic-2 witness `badBalanceSum` is accepted by a field sum and rejected by
  `List.Perm`. Non-vacuity of the relation and of each clause is established.
- `Seam.commit` is `M3Holds` of the oracle by `Iff.rfl`; `Seam.done` is `Set.univ` and the
  master theorems are meaningful with it: ArkLib's `toFun_full` reads "the verifier can output
  *anything* in `Set.univ`" as "the verifier accepts", and `perfectCompleteness` with
  `relOut = Set.univ` says the honest run never fails (ArkLib measures failure of the `OptionT`
  as not-the-event; the spine's proofs go through `perfectCompleteness_of_run_support`, which
  confirms that reading).
- `KnowledgeAppend` matches ArkLib #615's `append_rbrKnowledgeSoundnessWorstCase_of_guarded_first
  (V₁ V₂) (G : V₁.GuardedForm) {ε₁ ε₂} (h₁) (h₂)` up to argument order: the claimed
  substitution holds (subject to A3, which moves both to the `With` form).
- The `Layout` law (`read_eval`) is enough for every phase: the opening phase needs only that a
  column claim at `z` is the stack's claim at `extend c z`, and it holds equally for an aligned
  block (`extend c z = z ++ sel`) and for a strided slice (`extend c z = bits ++ z`), which is
  what the eighteen virtual BLAKE2s limb columns need (`cpu/mod.rs:790-814`, `SlotClaim::Strided`).
  What pins `read` to the Rust layout is `witnessOf_stackOf`, as the docstring says.
- `Coord.committed c (h : τ c.1 = κ)` forces a κ = 0 block (the state boundary) to be
  constants only, which is exactly the Rust (`layout.rs:355-358`, `Const(g_pow(final_pc))`).
- The five clauses against the verifier's accept list of §8.5 (last step): the caps (outside,
  documented), one bus root for both sides (`Balanced`), the nonzero count root
  (`CountsNonzero`, since a product in a field is nonzero iff every factor is), every
  sumcheck's rounds and final value (`ConstraintsVanish`, and the bus and boundary claims
  through the seams), the public-input line (`PublicCellsHold`, six cells), Flock's reduction
  (`aux`), the PCS opening (the ideal oracle model). Seven checks, five clauses, two outside by
  design and documented.
- Target classification: the PR names Category A, T4's ideal-oracle half, both master theorems
  conditional; adequate and not overstated (except A3's extractor sentence).

## Pass B: fidelity

Category A throughout; what was checked is that each Category-B *shape* the spine fixes matches
the pin, and that every divergence from the specification is documented.

| Artifact | Source at the pin | Lean | Match |
| --- | --- | --- | --- |
| bus width, separator first, zero padding | §5.1 (`05-arithmetization.tex:12, 16`) | `Vector _ 16`, `flushes` "separator first", `Coord.const 0` | yes |
| boundary coordinate vocabulary | §5.4 "Settling it" (`:111`): a constant, the index column, a public component, one committed column; `leaf.rs:21-48` `Const, Index, Public, Col` | `Coord.const / known / committed` | yes (`Index` and `Public` are both `known`) |
| table flush coordinates | §5.1: any polynomial of degree ≤ 2; `leaf.rs` `Col, GCol, Prod, Sum` | `CMvPolynomial (width j) K` per coordinate | yes; degree unbounded (A1) |
| count tree | §6.2 "The count product"; `layout.rs:412-414`: the tables' count columns only | `counts : (j) → List (Fin (width j))`; the block tables have none | yes |
| state boundary | §6.1; `layout.rs:355-358` | κ = 0 blocks of constants | yes |
| seed and finalize | §6.2 flush rules; `layout.rs:359-395` | boundary blocks with `known` index and program columns, `committed` limbs and counts | yes |
| public input | §8.2; `cpu/mod.rs:745-755` | six `PublicCell`s | expressible; shape mismatch with the phase (A4) |
| accept relation | §5.1 line 4, §6.2, §8.2, §8.5 | `M3Holds` | yes (table above) |

Divergences documented in the module docstrings: the caps outside the relation; the commit
phase sends the stack itself (the ideal oracle model, WHIR in Layer 11); `aux` abstract; the
zerocheck escape charged to the bus phase; balance counted in ℕ against Clean's field sum.
Divergences not documented: A2 (which predicate `aux` is) and A4 (the public-input shape).

### B1 (low). Citation drift, and the PDF is not the pinned text

- `Instance.lean:17-18`: "the bus flushes, each a side and sixteen coordinate polynomials with
  the domain separator first (§5.2)": that is §5.1 (the M3 model); §5.2 is the grand product.
- `Instance.lean:53-55` (`Layout`): "§5.4, equation (2)" is the leaf decomposition, which does
  read the selector; the primary source of `P̃_i(z) = q̃(z, sel_i)` is §4.1
  (`04-committing-the-witness.tex:12`). Cite both.
- The document handed to this review, `leanVM-b-2.pdf`, differs from `doc/leanvm/body/` at the
  pin: its §5.2 gives the product-check error as `5·2^μ/|E|` with "Proof. Easy", while
  `05-arithmetization.tex` at `a386121f` (after `63b6fe01`, "doc: clean 05-arithmetization.tex",
  one hour before the pin) gives `4·2^μ/|E|` (Theorem 5.1, line 37) with the lemma's proof
  `TODO` (line 51). The tex at the pin is the authority (`docs/leanvm-target.md`); note this
  in the survey record so the PDF is not cited again.

### B2 (low). Status finding S13 is stated against a text that is not the pin

`docs/roadmap/protocol-status.md`, S13 (2026-09-24): "§5.2 charges the product check
`5·2^μ/|E|` … The specification's bound is loose, not wrong." At the pin §5.2 already says
`4·2^μ/|E|` (Theorem 5.1). Retire S13 or re-point it at the revision that says 5.

## Interface friction with leanISA (the user's first question)

The adaptor (hole I2) must give, for `I := leanIsaInstance prog s`, `witnessOf : Column I.μ →
EnsembleWitness (leanIsaEnsemble prog)` with `M3Holds I input q → SatisfiedBy prog input
(witnessOf q)`, and `stackOf` the other way. The thirteen conjuncts of `SatisfiedBy`
(`Statement.lean:311-343`), clause by clause:

| `SatisfiedBy` conjunct | Comes from | Work in I2 | Risk |
| --- | --- | --- | --- |
| `public_input_eq` | `PublicCellsHold` (six cells) or the refinement's `Stmt` argument | `witnessOf` sets `publicInput := PublicIO.ofInput input` (the map has `input`) | none |
| `constraints : w.Constraints` (Clean; asserts and lookups on every row of every table, the verifier included) | `ConstraintsVanish` | I1's `toM3_constraints_iff` (Clean #466); the verifier and seven components have no assert; leanISA uses no Clean lookup (checked) | none beyond I1 |
| `state_balanced`, `mem_balanced`, `bytecode_balanced` (three `List.Perm`s of typed messages without separator) | `Balanced` (one `List.Perm` of 16-tuples) | filter the one permutation by coordinate 0, then map "drop the separator and the zero tail" (`List.Perm.filter`, `List.Perm.map`); needs I1's `toM3_flushes_eq` and that leanISA's `busTuple` is the instance's flush polynomial evaluated | medium: the heaviest lemma; the boundary tuples must match `memRowOf`/`bytecodeRowOf` rows exactly (`bytecodeColumn` of #41 against `entry`) |
| `counts_nonzero` (message coordinate 1 of every pull of the six tables) | `CountsNonzero` (every cell of every count column) | per table: the pull's count coordinate is `Expression.var` of a count column (`memRead`, `bytecodeRead`: `count` is passed as a column by every Layer 6 table; checked) | low; a Category-B transcription of `count_columns()` per table |
| `caps` | nothing | a hypothesis (A5) | A5 |
| `index_columns` | construction: `idx := gpow i` from the `known` index column | none | none |
| `seed_rows` | construction, if `s.logMem ≤ maxLogMem` | none | A5 |
| `bytecode_rows` | construction: `bytecodeRowOf prog i (cntfin_bc[i])` | none | none |
| `blake2s_valid` | `aux` | #3's "R1CS ⇒ compression" under the strong reading; nothing under the weak | A2 |
| `word0_eq`, `word1_eq` | `PublicCellsHold` (cells 0, 1 of `mem_0, mem_1`, zeros of `mem_2`) with `MemImage.read_gpow` (`κ < 64`, from the caps) | small | A5 (the cap) |

The reverse direction (`m3Holds_stackOf`): `Balanced` from the three `BalancedPair`s needs
that every flush tuple of the instance carries one of the three separators (by construction) and
the union of three permutations; `aux (stackOf w)` needs the Flock wires (A2); the rest is the
table above read backwards. Universe: `EnsembleWitness` is in `Type 1` (a `Component` bundles
`TypeMap`s), so `Refinement`'s `W₂ : Type _` is the right generality and
`Extractor.Straightline.map` (`WitIn' : Type`) cannot serve the adaptor; it has no consumer
in the roadmap and could be dropped or kept as an ArkLib candidate.

Three further frictions found while checking, none of them a spine defect but each a surprise
for the first hole that meets it:

### I1 (medium). `E`-coefficient polynomials have no ring operations at the pin

`E` (`BF64.Ext3`) has `DecidableEq` (`Extension.Ext.instDecidableEq`) and a coefficient-wise
`BEq` (`Extension.Ext.instBEq`) but no `LawfulBEq E`; CompPoly's `CMvPolynomial.C`, `X`,
`monomial`, `Add`, `Mul` all require `[BEq R] [LawfulBEq R]` (`CMvPolynomial.lean:55-85`).
Verified: `#synth LawfulBEq E` and `#synth Mul (CMvPolynomial 3 E)` fail; the `K` versions
succeed. So the bus phase cannot *build* a `VirtualTerm.poly` over `E` today. A1's fix (K
coefficients, E weights) removes the need; otherwise Layer 0 owes `instance : LawfulBEq E`
(provable, `instBEq` is coefficient-wise) or a `DecidableEq`-derived `BEq` at higher priority.

### I2 (low). Scalar prover messages have no `OracleInterface`

`Component.Def` requires `[∀ i, OracleInterface (pSpec.Message i)]`; `#synth OracleInterface E`
and `OracleInterface (List E)` fail at the pin (ArkLib's trivial oracle is a `def`, the
`Inhabited` default, not an instance: `OracleInterface.lean:88-98`). Every phase that sends a
scalar or a round polynomial will declare one. Put two instances in `Protocol/Field.lean`
(the message is returned whole; query `Unit`) so P1 to P8 do not each invent one.

### I3 (low). The layout plan covers aligned blocks only

Status file, #18's row: "`Blocks` inhabits `Layout` (`read := unstack`, `extend := (· ++
selector)`, `read_eval := stack_eval`)". That reads aligned blocks. The eighteen BLAKE2s limb
columns are virtual (`layout.rs:20-28`, `tables.rs:829`), read from `q_flock` at a fixed
low-bit slot (`cpu/mod.rs:790-814`), i.e. a strided slice: `extend c z = slotBits ++ z`. The
`Layout` law admits it; `Blocks` does not express it. I2's `leanIsaInstance.layout` needs a
second reader, and the slot map is #3's (`FlockInterface.limbColumns`). Record it in the I2
hole section so the adaptor is not sized on `Blocks` alone.

## Pass C: hygiene

The ten Lean files are clean: one- or two-line docstrings, module docstrings carrying the
rationale, no proof narration, `public section`s, narrow imports, `snake_case` theorems. Notes:

- C1 (low): the PR body predates `00ab835`: it names `Transport.lean` (now
  `ToArkLib/Refinement.lean`), "six `module` files" under `Spine/` (five, plus five under
  `ToArkLib/`), and the extractor sentence of A3. Rewrite the "What is added" section from
  the file list.
- C2 (low): no module docstring states the target contribution. `Compose.lean`'s should:
  "Category A; the ideal-oracle half of T4 (`docs/architecture.md`); both theorems conditional
  on `Phases.*` and, for knowledge, on `KnowledgeAppend`".
- `Component.lean:129-132`: `guardedAppend` through `cast (congrArg …)`; H5 gives the shorter
  form.
- `Refinement.lean`: `Extractor.Straightline.map` has no consumer (above); keep or drop, say
  which.
- `Instance.lean` and `Seams.lean` docstrings cite the specification only, as convention
  *Generic code* asks; good. The `Toy` docstring's "cells 6 and 7 padding" and the `extend`
  bit order (`z, i mod 2, i div 2` for cell `z + 2i`) were checked.
- Status file, survey record 2026-09-28: the `Generic/` → `ToArkLib/` rename applies to six
  open pull requests on rebase; the blueprint's convention row says so, the PR bodies of #38 to
  #43 do not. Leave a one-line comment on each when this PR merges.

## Relation to the open pull requests

The spine redefines nothing that #18 or #38 to #43 define, and stacks on none of them by design
(the hole table: S consumes Layer 0 only). Points of contact to keep straight:

- `Weight.pair` (`Seams.lean:104-106`) is the inner product `Σ_i W[i]·q[i]` that #43's
  `pairing_batchWeight` and #38's `isValid_iff_pairing` are stated over on `CMlPolynomialEval`.
  When #43 lands, restate `Weight.pair` through its pairing (one line) or have P7 prove the
  bridge; do not let two pairings coexist.
- `Layout` is the interface #18's `Blocks` inhabits (`unstack`, `selector`, `stack_eval`), for
  aligned blocks (I3).
- `Coord.known` takes a `Column κ`; #41's `idxColumn` and `bytecodeColumn` supply the two
  columns of the leanISA boundary blocks.
- `VirtualTerm` is what #39's `fingerprintFactorPoly` (degree 4 in `(α, β)`) will be folded
  into, per term (A1's shape makes that a list of `K`-polynomial terms with `E` weights).

No stacking or joint review is needed; review #58 on its own.

## Auditable base (the user's fourth question)

Line counts at `00ab835`, `LeanerVM/Protocol/Spine/*` and `LeanerVM/Protocol/ToArkLib/*`:

| file | total | doc | statements | proof / body | other |
| --- | --- | --- | --- | --- | --- |
| `Spine/Compose.lean` | 166 | 69 | 43 | 13 | 41 |
| `Spine/Instance.lean` | 221 | 81 | 74 | 18 | 48 |
| `Spine/Phase.lean` | 68 | 21 | 13 | 5 | 29 |
| `Spine/Seams.lean` | 193 | 90 | 43 | 15 | 45 |
| `Spine/Toy.lean` | 101 | 29 | 18 | 29 | 25 |
| `ToArkLib/Component.lean` | 165 | 50 | 48 | 24 | 43 |
| `ToArkLib/Oracles.lean` | 35 | 17 | 3 | 0 | 15 |
| `ToArkLib/PassThrough.lean` | 100 | 23 | 17 | 32 | 28 |
| `ToArkLib/Refinement.lean` | 74 | 25 | 13 | 8 | 28 |
| `ToArkLib/SendOracle.lean` | 191 | 41 | 34 | 68 | 48 |
| total | 1314 | 446 | 306 | 212 | 350 |

"Statements" are declaration heads up to `:=`/`where` plus structure and inductive fields;
"doc" is every comment line; "other" is blanks, imports, namespaces and `variable`s. The
surface a human must read is the 306 statement lines plus the definition bodies that carry
meaning (the clause definitions of `Instance.lean`, `Def.append`, `passThrough`,
`sendOracle`, `toy`), about 400 lines, against 212 lines of proof. That ratio is already good;
the compressions below take about 26 lines off the surface and, more usefully, take the
three-parameter noise out of `Instance.lean` and the projection chains out of the seams.

Compressions, each prototyped against the pin without editing the repository (every variant
was checked as a `module` and again joined with the unchanged downstream files and the tests,
under the lakefile's options); the text is in the appendix.

| # | Where | What | Lines | Verdict |
| --- | --- | --- | --- | --- |
| H1 | `Instance.lean` | a `Shape` record (`ntab`, `τ`, `width`) with `Shape.ColumnId`; `Coord`, `BoundaryBlock`, `PublicCell` take `(S : Shape)`; `M3Instance extends Shape`; the abbrev `M3Instance.ColumnId` and the top-level `ColumnId` go | 0 | adopt: it removes the three-parameter lists everywhere, every downstream file and test compiles unchanged; the blueprint's sketch needs the new names |
| H2 | `Instance.lean` | `deriving instance Decidable for ConstraintsVanish, Balanced, CountsNonzero, PublicCellsHold` and `… for M3Holds` in place of the five hand-written instances; the per-clause `#guard`s still work | −9 | adopt |
| H3 | `Seams.lean` | one helper `Seam.of (P : S → Column I.μ → Prop) : Set ((S × ∀ i, TheOracle I i) × Unit)` and each seam as a predicate of `(s, q)`; no `p.1.1.2`, no `theStack p.1.2`; tests unchanged (`Iff.rfl`, `trivial`, the projections). A `Pool` structure with `toPool` coercions was also tried and is longer (+22) and worse for the tests | −2 | adopt H3; reject `Pool` |
| H4 | `Toy.lean` | `read_eval` by `fin_cases c <;> simp [eval₂Mle, evalMle, evalMleValues, evalMleStep, map, Vector.head, Vector.tail, extend, slice]`, the two private lemmas deleted; CompPoly has no slice lemma; #18's `evalMle_append_boolVec` is the general one and an `eval₂Mle` form of it was prototyped on #18 (`eval₂Mle_append_boolVec`), after which the toy's `read_eval` is one application | −14 | adopt now; restate through #18's lemma when it lands |
| H5 | `Component.lean` | `cast (congrArg _ (OracleVerifier.append_toVerifier _ _).symm) (G₁.append G₂)`; the `▸` forms do not elaborate (the verifier is not syntactically an `append`) | −1 | adopt |
| H6 | `PassThrough.lean`, `Phase.lean` | `passThroughExtractor`, `passThroughStateFunction`, `passThrough_rbr`, `passThroughSecurity` (A6) and a `Phase.passThroughSecurity` wrapper; checked on the toy at `Seam.pub` with `id` | +44, +9 | adopt (new proved surface, the pattern every bookkeeping step will use) |

Not worth doing: making the clauses and `M3Holds` `abbrev`s (−12, changes reducibility for
`simp`); a flagged seam `Seam.after claims (cells aux : Bool)` (+23, `true → P` everywhere).

## Tests to add

1. (A1) a `BusOut` with a degree-3 term is rejected by the seam's degree conjunct; the toy's
   zerocheck claim is accepted.
2. (A3) `piopExtractor` on `trivSecurity` reads the stack off the honest transcript.
3. (A6) `trivSecurity` inhabits `Phases.Security` on an all-trivial instance.
4. (A4) after the `PublicLine` change: the honest stack at statement 1 passes, the stack with
   cell 1 of column 2 changed fails the line clause alone.
5. (I1, I2) `#synth` guards in `tests/LeanerVMTests/Protocol/Field.lean` for the two new
   instances, so a pin bump that supplies them upstream is noticed.

## Not checked

- ArkLib #615's proofs were not audited; only the statement shapes (`Append/Knowledge.lean`)
  were read.
- leanth's explore branch is private; the "pattern" claims of the PR body were not verified.
- The Rust `count_columns()` per table were not enumerated (I2's job; the spine is generic).
- `Blake2sRelation` (`CompressCells` on nine cells) has no `DecidablePred` instance, but
  `unfold Blake2sRelation; infer_instance` closes `Decidable (Blake2sRelation r)`, so the
  weak reading of `aux` is decidable; under A2's strong reading `decAux` is Flock's R1CS check,
  #3's to supply.

## Appendix: the compression texts

Prototyped on `00ab835`; each compiles as given (H4 and H6 with `#print axioms` at the
kernel's standard three).

H1, `Instance.lean`:

```lean
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

inductive Coord (S : Shape) (κ : ℕ)
  | const (c : K)
  | known (col : Column κ)
  | committed (c : S.ColumnId) (h : S.τ c.1 = κ)

structure BoundaryBlock (S : Shape) where … coords : Vector (Coord S κ) 16
structure PublicCell (S : Shape) where col : S.ColumnId; idx : Fin (2 ^ S.τ col.1); val : K

structure M3Instance extends Shape where
  Stmt : Type
  …                                   -- ntab, τ, width deleted
  boundary : List (BoundaryBlock toShape)
  layout : Layout μ toShape.ColumnId (fun c ↦ τ c.1)
  publicCells : Stmt → List (PublicCell toShape)
-- `M3Instance.ColumnId` deleted: `I.ColumnId` resolves through `extends`.
def coordCell (q : Column I.μ) {κ : ℕ} : Coord I.toShape κ → Fin (2 ^ κ) → K

-- Toy.lean
abbrev shape : Shape := ⟨1, fun _ ↦ 1, fun _ ↦ 3⟩
abbrev Col : Type := shape.ColumnId
def boundary : BoundaryBlock shape where …
abbrev toy : M3Instance where
  toShape := shape
  Stmt := K
  …
```

H2, `Instance.lean`:

```lean
deriving instance Decidable for ConstraintsVanish, Balanced, CountsNonzero, PublicCellsHold
-- The relation is decidable: every clause is a finite check over computable data.
deriving instance Decidable for M3Holds
```

H3, `Seams.lean`:

```lean
/-- The seam of a predicate of the statement and the stack behind the one oracle. -/
def of {S : Type} (P : S → Column I.μ → Prop) : Set ((S × ∀ i, TheOracle I i) × Unit) :=
  {p | P p.1.1 (theStack p.1.2)}

def commit := of I (M3Holds I)
def bus := of I fun (s : I.Stmt × BusOut I) q ↦ (∀ c ∈ s.2.linear, c.Holds q) ∧
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicCellsHold s.1 q ∧ I.aux q
def table := of I fun (s : I.Stmt × TableOut I) q ↦
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicCellsHold s.1 q ∧ I.aux q
def pub := of I fun (s : I.Stmt × PubOut I) q ↦ (∀ c ∈ s.2.columns, c.Holds q) ∧ I.aux q
def flock := of I fun (s : I.Stmt × FlockOut I) q ↦
  (∀ c ∈ s.2.columns, c.Holds q) ∧ ∀ c ∈ s.2.weighted, c.Holds q
def done := of I fun (_ : Unit) _ ↦ True
```

H4, `Toy.lean` (the two private lemmas deleted):

```lean
theorem read_eval (q : Column 3) (c : Col) (z : Vector E 1) :
    CMlPolynomialEval.eval₂Mle (slice q c).values (algebraMap K E) z =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) (extend c z) := by
  fin_cases c <;> simp [CMlPolynomialEval.eval₂Mle, CMlPolynomialEval.evalMle,
    CMlPolynomialEval.evalMleValues, CMlPolynomialEval.evalMleStep, CMlPolynomialEval.map,
    Vector.head, Vector.tail, extend, slice]
```

and, on #18 (`Multilinear.lean`, for when it lands):

```lean
theorem eval₂Mle_append_boolVec {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (t : CMlPolynomialEval R (k + m)) (f : R →+* S) (z : Vector S k) (j : Fin (2 ^ m)) :
    eval₂Mle t f (z ++ (boolVec j : Vector S m)) = eval₂Mle (slice t j) f z := by
  rw [eval₂Mle, evalMle_append_boolVec]
  congr 1
  ext i hi
  simp [slice, CMlPolynomialEval.map]
```

H5, `Component.lean`:

```lean
  cast (congrArg _ (OracleVerifier.append_toVerifier _ _).symm) (G₁.append G₂)
```

H6, `PassThrough.lean` (after the completeness section) and `Phase.lean`:

```lean
/-! ## Knowledge soundness -/

/-- The extractor keeps the witness. The shared oracle is written `OracleSpec.emptySpec.{0, 0}`
rather than `[]ₒ` to pin a universe `Extractor.RoundByRound` leaves free. -/
def passThroughExtractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
    (StmtIn × ∀ i, OStmt i) W W !p[] (fun _ ↦ W) where
  eqIn := rfl
  extractMid := fun i ↦ Fin.elim0 i
  extractOut := fun _ _ w ↦ w

variable (f : StmtIn → StmtOut) {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)}
  {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}
  (h : ∀ s o w, ((f s, o), w) ∈ relOut → ((s, o), w) ∈ relIn)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function: the input relation, at the only round. -/
def passThroughStateFunction :
    (passThroughVerifier OStmt f).toVerifier.KnowledgeStateFunction init impl relIn relOut
      (passThroughExtractor OStmt) where
  toFun := fun _ stmt _ w ↦ (stmt, w) ∈ relIn
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ Fin.elim0 m
  toFun_full := fun stmt tr w hpos ↦ by
    obtain ⟨s, o⟩ := stmt
    rw [passThroughVerifier_toVerifier_run OStmt f s o tr] at hpos
    change Pr[_ | OptionT.mk (do let st ← init; (simulateQ impl
      (OptionT.run (pure (f s, o)))).run' st)] > 0 at hpos
    exact h s o w (by simp at hpos; exact hpos.2)

include h in
/-- Round-by-round knowledge soundness at error zero: no challenge, the witness is kept. -/
theorem passThrough_rbr :
    (passThroughVerifier OStmt f).toVerifier.rbrKnowledgeSoundnessWorstCase init impl relIn
      relOut (fun i ↦ Fin.elim0 i.1) :=
  ⟨fun _ ↦ W, passThroughExtractor OStmt, passThroughStateFunction OStmt f h init impl,
    fun _ i ↦ Fin.elim0 i.1⟩

/-- The security half, whenever `f` carries the input relation into the output relation and
back. -/
def passThroughSecurity (hc : ∀ s o w, ((s, o), w) ∈ relIn → ((f s, o), w) ∈ relOut) :
    Security (passThrough OStmt f) relIn relOut where
  toComplete := passThroughComplete OStmt f hc
  rbr := fun init impl ↦ passThrough_rbr OStmt f h init impl

-- Phase.lean
def passThroughSecurity (f : StmtIn → StmtOut) {relIn : …} {relOut : …}
    (hc : ∀ s o, ((s, o), ()) ∈ relIn → ((f s, o), ()) ∈ relOut)
    (h : ∀ s o, ((f s, o), ()) ∈ relOut → ((s, o), ()) ∈ relIn) :
    Security I (passThrough I f) relIn relOut :=
  Component.passThroughSecurity (TheOracle I) f (fun s o _ ↦ h s o) fun s o _ ↦ hc s o
```

Two proof notes carried over from the prototype: the `change` in `toFun_full` is needed
(without it `simp` leaves `simulateQ impl (pure …)` unreduced), and pattern-matching
`fun ⟨s, o⟩ …` there times out at `whnf`, so keep the `obtain`. Under A3's `With` refactor the
`rbr` field becomes `rbrKnowledgeSoundnessWorstCaseWith` at `passThroughExtractor` and
`passThroughStateFunction`, which the prototype already names.

## Proposed PR body (C1), to replace "What is added"

`LeanerVM/Protocol/Spine/` (five `module` files: `Instance`, `Seams`, `Phase`, `Compose`,
`Toy`), `LeanerVM/Protocol/ToArkLib/` (five `module` files that are candidates for ArkLib:
`Oracles`, `Component`, `PassThrough`, `SendOracle`, `Refinement`) and
`tests/LeanerVMTests/Protocol/Spine.lean`; the file list of the "What the spine fixes" section
of the blueprint names what each holds. The sentence on the composed extractor should say what
the master theorem states after A3 is dispositioned (either "the extractor is
`piopExtractor`, the commit phase's followed by the phases'", or "an extractor exists; naming
it waits on the `With` form of `KnowledgeAppend`").

## Edits to make on GitHub (not applied by this review)

The branch meets the findings above; the pull request body and the hole comment on #12 still
describe the reviewed commit. The texts below are for the author to paste.

**Pull request #58, the "What is added" section**, replaced whole by:

```markdown
## What is added

`LeanerVM/Protocol/Spine/` (five `module` files: `Instance`, `Seams`, `Phase`, `Compose`, `Toy`),
`LeanerVM/Protocol/ToArkLib/` (six `module` files that are candidates for ArkLib: `Oracles`,
`Component`, `KnowledgeAppend`, `PassThrough`, `SendOracle`, `Refinement`), two oracle instances
for scalar messages in `LeanerVM/Protocol/Field.lean`, and
`tests/LeanerVMTests/Protocol/Spine.lean`; the sketch under "What the spine fixes" in
`docs/roadmap/protocol-blueprint.md` names what each file holds.

- `Instance.lean`: `Shape`, `Layout`, `Coord`, `BoundaryBlock`, `PublicLine`, `M3Instance` (with
  the degree bound `d` and its proofs `constraints_degree`, `flushes_degree`), the five clauses,
  `M3Holds` (decidable) and `M3Rel`.
- `Seams.lean`: `ColumnClaim`; `VirtualTerm`, a `K`-polynomial of a table's row with an `E`
  weight; `LinearClaim`, `Weight`, `WeightedClaim`; the phase outputs; the six seams through
  `Seam.of`, `Seam.bus` bounding the total degree of every term by `I.d`.
- `Component.lean`, `PassThrough.lean`, `SendOracle.lean`, `Phase.lean`: `Component.Def`,
  `Complete` and `Security` (a `Security` carries its extractor and knowledge state function)
  with their `append`, both proved; the pass-through and the one-message commit shape, each with
  both halves proved; their `Phase.*` specialisations.
- `KnowledgeAppend.lean`: the knowledge-soundness append ArkLib admits at the pin, ported with
  its attribution from ArkLib #615's `Append/Knowledge.lean` at `ca7a2577`, under
  `LeanerVM.Protocol` with ArkLib's names: `Verifier.KnowledgeStateFunction.appendGuarded` (the
  knowledge state function of the appended extractor, ArkLib's own
  `Extractor.RoundByRound.append`) and
  `Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first` (the bound, each
  challenge keeping its component's error). Deleted when the pin moves past #615.
- `Compose.lean`: the commit phase (both halves proved, at error zero), `Phases`,
  `Phases.Complete`, `Phases.Security`, `leanVmPiop`, `piopError`, `piopExtractor`, and the
  master theorems `piop_perfectCompleteness`, `piop_rbrKnowledgeSoundness` and
  `piop_rbrKnowledgeSoundness_exists`.
- `Refinement.lean`: `Refinement`, `Refinement.map_option_valid`, and
  `Extractor.Straightline.map` (an ArkLib candidate with no consumer yet).
- `Toy.lean`: one table of width 3 and height 2 on a stack of height 8, with one constraint, one
  push, one boundary pull, one count column, one public line and `d = 2`.

The knowledge theorem is stated for the named extractor `piopExtractor`: the commit phase's,
which reads the stack off the first message, followed by the phases', appended through the
verdicts by ArkLib's own `Extractor.RoundByRound.append`, with the ported knowledge state
function and bound. Category A; the ideal-oracle half of T4 (`docs/architecture.md`); both
master theorems are conditional on the phases' proofs only. The knowledge composition is proved
with no assumed statement (the port of ArkLib #615, which closes hole C1), and the kernel axiom
audit covers it (2884 declarations): `#print axioms` on `piop_rbrKnowledgeSoundness`,
`Component.Security.append`, `Phases.Security.toDef` and the two ported theorems gives
`propext`, `Classical.choice` and `Quot.sound` only.
```

**The hole comment on #12**, the bodies of four sections replaced by:

```markdown
**I2, the adaptor (Layer 3).** Produces `leanIsaInstance`, `stackOf`, `witnessOf`,
`satisfiedBy_witnessOf`, `m3Holds_stackOf`, `witnessOf_stackOf`. Consumes the spine, I1, leanISA
Layers 5 to 8, #38, #40 and #3. `leanIsaInstance` has `d := 2` and three public lines, on
`mem_0, mem_1, mem_2` (the third with cells `0, 0`). Its layout has two readers: #18's `Blocks`
for the aligned blocks, and a strided reader for the eighteen BLAKE2S limb slots of `q_flock`
(`cpu/mod.rs:790-814`), the slot map being #3's `FlockInterface.limbColumns`.
`satisfiedBy_witnessOf (hs : s.Admissible prog) (h : M3Holds …)`: the caps are not a clause of
`M3Holds` and `imageOf` truncates above `maxLogMem`, so the conclusion needs the hypothesis,
which K4 discharges because `verify` checks the announced sizes. `aux` is the strong reading,
Flock's R1CS on `q_flock`, so `satisfiedBy_witnessOf` discharges `blake2s_valid` through #3's
lemma "the R1CS holds ⇒ the limb slots compress", and `stackOf` computes the R1CS wires from the
limbs with #3's witness generator, an explicit argument until #3 supplies it.
```

```markdown
**P5, the public-input phase (Layer 8).** Produces `publicInputPhase` with both halves, from
`Seam.table` to `Seam.pub`, over `I.publicLines`. The verifier draws one `r ∈ E` and pools, for
each line, the column claim `col~(r, 0, …, 0) = (1 + r)·cell0 + r·cell1`; the prover sends
nothing. Error `1/|E|` on the one challenge. The Rust sends `c_0, c_1` and checks
`c_0 + Y·c_1 = interp(pi_0, pi_1, r)` (`cpu/mod.rs:745-755`): the two accept the same stacks,
because the cells are `K`-valued and `1, Y, Y²` is a `K`-basis of `E`, but not the same
transcripts, and the two scalars are Layer 12's encoding to read and reconcile (K3). Tests on the
toy: the honest run accepted; the stack `badLine` rejected. The smallest hole, a good first one.
```

```markdown
**P6, the Flock phase (Layer 9).** Produces `FlockOut`, `limbColumns`, `flockError_le`; the
inhabitant is #3's. `FlockInterface.relIn` carries the strong `aux`: Flock's R1CS holds of the
bits packed into `q_flock` (Annex C.1, §4.2), and the eighteen column claims are true of
`limbColumns`, the strided reader of the limb slots (`cpu/mod.rs:790-814`). That the limb slots
compress is #3's soundness consequence of the predicate, consumed by the adaptor (I2), never the
predicate itself: the phase's completeness needs the R1CS wires already committed in `q`.
```

```markdown
**C1, the knowledge-soundness append (ledger A2).** Done on the spine's branch (#58), as the
port: `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean` ports, with its attribution, ArkLib #615's
`ArkLib/OracleReduction/Composition/Sequential/Append/Knowledge.lean` at `ca7a2577`, under
`LeanerVM.Protocol` with ArkLib's names: `Verifier.KnowledgeStateFunction.appendGuarded` (the
knowledge state function of the appended extractor `E₁.append E₂ G.out`, ArkLib's own
`Extractor.RoundByRound.append`) and
`Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first` (the bound, each challenge
keeping its component's error), with the kernel's three axioms. Its two witness lemmas reuse the
pinned ArkLib's proofs, and the wrappers into the existential and averaged forms are left out.
`Component.Security.append` and the master knowledge theorem take no assumption. The file is
deleted, and its two names in `Component.lean` replaced by ArkLib's, when the pin moves past
#615. Close the hole when #58 merges.
```

When #58 merges, a one-line comment on each of #38 to #43 that `Generic/` becomes `ToArkLib/`
(or `ToCompPoly/`) on rebase, as noted under Pass C.
