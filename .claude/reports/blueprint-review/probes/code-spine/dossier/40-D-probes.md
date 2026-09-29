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
that `Phases.Security` "has no such inhabitant". Probe `P5PassThrough.lean`: see the result
recorded below the table of this section.

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

### D.7 Record of the pass-through probe

See the end of this file's appendix entry `P5PassThrough.lean`; the result is reported in the
summary and in section D.3 (a) once the probe has run.
