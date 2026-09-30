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
