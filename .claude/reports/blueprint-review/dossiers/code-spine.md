# Dossier: the spine as built (task `code-spine`)

Reviewed: leanerVM `main` at `b435631` (the checkout is on the branch
`docs/protocol-blueprint-review`, created from it; its tracked sources are those of `main`).
Libraries at the pins: ArkLib `dca90385`, CompPoly `3468b38c`, VCVio `f9dc47d9`. leanVM at
`a386121f`.

**Status of this file: in progress.** Sections are added in the order D, C, F, B, E, A; a
section that is not there yet is not written yet.

## 0. Summary

(Provisional; rewritten when the dossier is complete.)

Read in full: `LeanerVM/Protocol/Spine/{Instance,Seams,Phase,Compose,Toy}.lean`,
`LeanerVM/Protocol/ToArkLib/{Oracles,Component,PassThrough,SendOracle,Refinement,GuardedVerdict,KeepOracles}.lean`,
the statements of `KnowledgeAppend.lean`, `LeanerVM/Protocol/Field.lean`,
`LeanerVM/Protocol/PublicInput.lean`, `tests/LeanerVMTests/Protocol/Spine.lean`, the blueprint's
headline, conventions, spine section, Layers 3 to 13, acceptance tests and interface list, the
earlier review `docs/reviews/protocol-spine.md`, the ArkLib definitions the statements unfold
to, and the specification's §4, §5, §6, §8 and Definition 3.13.

Conclusions so far:

1. No theorem of the spine is wrong for what it states, and `M3Holds` is a sound and
   non-vacuous definition on every case probed, including the multiplicity cases the
   repository's tests lack.
2. The master theorems are composition theorems. Their hypotheses are satisfiable, for every
   instance, by phases that check nothing, because the error a phase declares is unconstrained
   (machine-checked: `Phases.Security toy` inhabited at error 1).
3. The composed extractor's output is not the stack as soon as a phase has a round; the
   repository's `rfl` test covers zero-round phases only.
4. A layout can alias columns and empty the relation; the reading law determines `read` from
   `extend`.

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
  have K := S.kSF (pure ()) noImpl
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
  have hfull := K.toFun_full stmt tr () hpos
  rw [htr] at hfull
  exact bad_not_m3Holds ((K.toFun_empty stmt _).mpr hfull)

#print axioms no_security

end Probe
```

Output: not recorded.
