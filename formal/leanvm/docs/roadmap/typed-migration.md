# The proof spine on ArkLib's typed framework: the migration plan

This page reopened the protocol blueprint's decision 24 ("stay on `OracleReduction`"), which is
now reversed, and planned the move of the proof system from ArkLib's legacy `OracleReduction` framework to its typed
`Interaction` framework (`ArkLib/Interaction/`, over PolyFun's interaction trees), at the pins of
`upstreams.json` (ArkLib `4dae3acf`, VCVio `afa6593f`, PolyFun `41d3b21d`, Lean `v4.34.1`). It
says what used the legacy framework, what the typed framework has, what was built, in what
order the work moved, what was restated, and where it stands (the progress log at the end).

Nothing proved changes: the definitions and statements of `LeanerVM/Spec/` stay as they are, the
front page (`LeanVM.knowledgeSoundness_holds`, `LeanVM.completeness_holds`) keeps its statements
and its three kernel axioms, and an intermediate statement is restated in the typed framework only
at the same error terms and the same knowledge notion (round-by-round knowledge soundness, worst
case over prefixes, for a named computable extractor).

## What uses the legacy framework

47 files of `LeanerVM/` (14,000 lines) and 13 test modules (3,700 lines) name the legacy
framework's carriers (`ProtocolSpec`, `OracleReduction`, `OracleVerifier`, `Verifier.GuardedForm`)
or its knowledge notion (`Extractor.RoundByRound`, `Verifier.KnowledgeStateFunction`,
`rbrKnowledgeSoundnessWorstCaseWith`), directly or through the local component layer
(`Component.Def`, `Front`, `Complete`, `Security`). They fall in four groups.

| Group | Files | Role |
| --- | --- | --- |
| Generic components (upstream candidates) | `ToArkLib/`: `Component`, `KnowledgeAppend`, `ExtractIn`, `PassThrough`, `SendOracle`, `GuardedVerdict`, `KeepOracles`, `FrontVerifier`, `Refinement`, `Refutation`, `TranscriptMap`, `Schedule`, `SendChecked`, `SampleChallenge`, `Batch`, `QueryCheck`, `SumcheckRound`, `Sumcheck`, `GrandProduct`, `GrandProductSecurity`, `Flock/{Zerocheck, Lincheck, RingSwitch, Reduction, Security}`; `Oracles`, `InnerProduct` (oracle interfaces only) | the component layer, its composition (completeness by ArkLib's theorem, knowledge by the local port of ArkLib #615), and the components every phase is assembled from |
| Phases | `PublicInput`, `TableSumcheck`, `Bus`, `BusSecurity`, `Flock`, `Opening` | the five phases after the commitment, each a `Component.Def` with its `Complete` and `Security` at its slot's schedule and error |
| The spine | `Spine/Errors` (the slots' schedules and errors), `Spine/Phase`, `Spine/Compose`, `Piop` | the commit phase, the bundle `Phases`, the composition and the two master theorems, and their leanVM instance |
| The end-to-end front | `EndToEnd/Front/`: `BusComponent`, `BusDoom`, `BusGkr`, `BusGkrArk`, `BusPhase`, `BusSpec`, `FlockArk`, `PubEscape`, `TableArk`, `TablePhase` | what the verifier program's doom reads off the phases' one-round components |

What the front page uses of them was measured on the built tree (the constants reachable from the
values of the two front-page theorems, theorem bodies included): from the legacy framework, only
definitions (the carriers, `Verifier.run`, `Verifier.GuardedForm`, `KnowledgeStateFunction` with
its three laws, `Extractor.RoundByRound`, `rbrKnowledgeSoundnessWorstCaseWith`, `OracleInterface`)
and no theorem. The path is narrow: the end-to-end argument (the random-oracle potential of
`Compile/Rom/`, see [e2e-rom-design.md](e2e-rom-design.md)) reads each front phase as a sequence
of one-round components, a checked message or a checked challenge, and uses of each component's
security two relation-level facts: a message that passes its check into the output relation came
from the input relation (`Security.say_in_of_out`, `sendChecked_reflect`, `say_keep`), and from
outside the input relation a challenge passes into the output relation with probability at most
the error (`Security.draw_prEvent_le`, `sample_escape`, `draw_escape_le`). About fifteen named
one-round securities are read this way (`Bus.rootsSecurity`, `Bus.valuesSecurity`,
`Bus.challengeSecurity`, `SumcheckRound.sendPolySecurity`, `SumcheckRound.drawChallengeSecurity`,
`Gkr.childrenSecurity`, `Gkr.lambdaSecurity`, `xiSecurity`, `finalValuesSecurity`, Flock's
`zcEndSecurity`, `linEndSecurity`, `skipDrawSecurity`, `drawPointSecurity`, `ringStartSecurity`,
`ringDrawSecurity`, `ringFinalSecurity`). The composed phase securities, the spine
(`Spine/Phase`, `Spine/Compose`, `Piop`), the knowledge composition (`KnowledgeAppend`,
`ExtractIn`), the opening, `PassThrough`, `SendOracle`, `QueryCheck`, `Refinement` and
`TranscriptMap` are off the front page's path: they are what the protocol blueprint's master
theorems state, proved and tested, but the front page does not consume them.

## What the typed framework has at the pin

| Needed | Typed counterpart at the pin | Gap |
| --- | --- | --- |
| A message schedule | `Interaction.Oracle.TypeTree` (`.public Moves rest`, `.oracle Messages rest`), `Protocol`, `RoleDecoration`, `OracleDecoration` | none; leanVM's schedules are linear trees with fixed move types |
| Transcripts and prefixes | `ExecutionPath`, `BranchPath`, `ExecutionPrefix` (`Oracle/Prefix.lean`) | none |
| Prover, verifier, reduction, execution | `Prover.Strategy`, `Verifier.Strategy`, `Verifier.Fragment`, `Oracle.Reduction`, `executeStrategies` (`Oracle/Execution.lean`) | a verifier's leaf is a value, so rejection is an `Option` output; there is no guarded form, so the front verifier (a check and a verdict on the path) is built here |
| Sequential composition | `PFunctor.FreeM.append`, `Verifier.append`, `executeStrategies_append` (`Oracle/Sequential.lean`), `OrderedExecution` with `run_preserves_support` (`Oracle/Composition.lean`) | completeness of an appended reduction for relations, the counterpart of the legacy `Complete.append`, is built here |
| Round-by-round knowledge soundness, named extractor, worst case | `KnowledgeCertificate` (backward witness maps `RoundExtractor`, `IsProverPreserving`, `IsLocallyBounded` at every authored verifier prefix), `TerminalRelation`, `SamplesChallenges`, `native_badChallenge_bound` (`Oracle/Security/Knowledge.lean`, `KnowledgeComposition.lean`) | the certificate lives on a bare tree; the bundle that ties it to a reduction's verifier and its relations (the counterpart of `Component.Security`) is built here |
| Its composition | `KnowledgeCertificate.append`, `sequential`, `sequentialTerminalRelation` | none: it replaces the local port of ArkLib #615 (`KnowledgeAppend`), whose ledger row then closes |
| The oracle interface of a message | `OracleInterface` of `ArkLib/OracleReduction/OracleInterface.lean`, which the typed framework itself imports (`Oracle/TypeTree/Decoration.lean`, `Oracle/Virtual.lean`) | none; this one legacy import stays, with the typed framework |
| A sumcheck with a knowledge notion | the typed sumcheck (`ProofSystem/Sumcheck/Interaction/`) has round-by-round soundness for one polynomial, no extractor | not needed: leanVM's sumchecks are its own (Layer 4), ported here with their knowledge certificates |
| An adaptor from `OracleReduction` | none | not needed: the migration ports each component instead of adapting it, and keeps the legacy and typed versions side by side until the spine moves |

Every typed declaration consumed is checked with `#print axioms` first; the knowledge,
composition and execution files listed above are free of `sorryAx` at the pin.

### How the notions correspond

For a linear schedule of `n ≥ 1` rounds and a front verifier (a check and a verdict on the
statement and the path, the oracles handed on), the legacy and typed notions say the same thing,
at the same errors:

* the knowledge state after round `m` (`kSF m stmt tr`) is the knowledge state at the prefix of
  `m` moves (`RoundExtractor.knowledgeState`), and `extractMid` is the backward map at the move;
* `toFun_empty` is the certificate's input state being the input relation (an equivalence,
  `KnowledgeCertificate.changeInputState`);
* `toFun_next` is `IsProverPreserving`;
* `toFun_full` (an accepting verdict in the output relation forces the last state) becomes the
  terminal relation: the state after the last move is defined to be "the check passes and the
  verdict with the witness is in the output relation" (`TerminalRelation`, an equivalence by
  definition), and the legacy laws at the last move follow from `toFun_full`;
* the worst-case bound at challenge `i` and prefix `tr` is `IsLocallyBounded` at the receiver
  node reached by `tr`, with the uniform sampler and the error `err i`, linked to the verifier by
  `SamplesChallenges`.

A zero-round component has no node to carry the last state, and the typed terminal relation then
asks the input and output relations to agree, which a check does not give. The migration fuses
every zero-round step (`passThrough`, the checks of `queryCheck`) into the round before or after
it; every phase and every slot of the spine has at least one round.

## What is built

Every generic piece is an upstream candidate under `LeanerVM/Protocol/ToArkLib/Typed/`, written
for ArkLib's other consumers, recorded in the protocol blueprint's upstream ledger, and free of
the legacy framework except `OracleInterface`.

1. **Front verifiers** (`Typed/Front.lean`): for a tree of public moves with a sampler at each
   receiver node (the samplers of a `RoundExtractor.ChallengeSchedule`), the verifier that
   samples there, reads the prover's moves, and returns a verdict of the path (an `Option`);
   its `SamplesChallenges`, proved once.
2. **The component bundle** (`Typed/Component.lean`): a component's tree, roles, schedule,
   honest prover and front verdict; its completeness (every outcome of the honest execution, on
   the input relation, is accepted into the output relation; this is the legacy perfect
   completeness, the typed executions being lossless); its security at a schedule of errors (for
   each input statement and oracles, a `KnowledgeCertificate` whose challenges are the
   component's schedule and whose terminal relation is the output relation); `Security.mono`.
3. **The one-round components** (`Typed/SendChecked.lean`, `Typed/SampleChallenge.lean`): a
   checked message and a checked challenge, both halves, from the same hypotheses as the legacy
   ones, and the relation-level read-offs the end-to-end front uses.
4. **Composition** (`Typed/Append.lean`): two components in sequence, the trees and schedules
   appended, completeness by `executeStrategies_append`, security by
   `KnowledgeCertificate.sequential` at the errors side by side.
5. **The multi-round components**: the sumcheck round and its rounds, the sumchecks of Layer 4
   with their transport, batching by powers, the grand-product argument, Flock's zerocheck,
   lincheck and ring switch, the query check fused with batching.
6. **The phases, the spine and the master theorems**, at the same slots, errors and extractor.

## Order of work

Each stage ends in a green `lake build` and `lake test` on `h1` and a local commit on
`FV-typed`. The legacy and typed versions live side by side until the spine moves, so every stage
leaves both the legacy master theorems and the front page proved.

| Stage | Moves | Ends with |
| --- | --- | --- |
| 0 | this plan | the plan committed |
| 1 | `Typed/Front`, `Typed/Component`, `Typed/SendChecked`, `Typed/SampleChallenge`, with tests on concrete inhabitants and a negative test per load-bearing hypothesis | the typed foundation |
| 2 | the end-to-end front: each one-round security it reads becomes the typed component's, built from the same hypothesis (extracted from the legacy definition into a lemma both use); `BusComponent`, `BusDoom`, `FlockArk`, `PubEscape` read typed securities | the front page free of the legacy framework, checked by the dependency count above |
| 3 | `Typed/Append`: composition of completeness and security | composition |
| 4 | the public-input phase, typed | its legacy phase still in `Piop` |
| 5 | the sumcheck rounds, the sumchecks, batching, the table sumcheck phase | likewise |
| 6 | the grand-product argument and the bus phase | likewise |
| 7 | Flock's components and the Flock phase | likewise |
| 8 | the commit phase, the opening, `Spine/Errors`, `Spine/Phase`, `Spine/Compose`, `Piop`, `Refinement`; the master theorems restated | the spine typed |
| 9 | the legacy files deleted, their tests moved, decision 24 reversed in the blueprint, the ledger and the status page updated | the migration done |

Stage 2 comes before the phases because the front page needs only the one-round components.
Until stage 7 the end-to-end front reads typed one-round securities that are not yet the parts of
a typed phase; each phase's stage builds that phase from the very securities the front reads, so
after stage 7 the front again rests on the phases' proved securities and nothing else.

## Risks

* **Dependent types.** Appended trees, paths and decorations meet only up to casts
  (`runtimeBranch_append`, `toTypeTree_append`); concrete schedules reduce, generic ones need
  the transport lemmas ArkLib states. Keeping every leanVM tree linear, with move types that do
  not depend on earlier moves, keeps the casts generic and few.
* **Slot equalities.** The legacy slots fix schedules up to definitional equality (`busSpec I`,
  `gkrSpec`); the typed trees must meet the same equalities, or the slots take an explicit
  transport, decided at stage 3.
* **Volume.** About 14,000 lines move; the plan's stages are independent enough to stop after
  any of them with both the legacy and the typed statements proved.
* **The extractor computes** (decision 11): the backward maps of a `KnowledgeCertificate` are
  data, and the typed securities keep errors out of compiled code as the legacy ones do
  (`@[macro_inline]` on `mono` and `append`).

## The result

The proof system is on the typed framework. `git grep ArkLib.OracleReduction -- LeanerVM` finds
two imports, both of `ArkLib.OracleReduction.OracleInterface`, in `ToArkLib/Oracles.lean` and
`ToArkLib/InnerProduct.lean`: `OracleInterface` is the class the typed framework itself imports
for its oracle messages (`Oracle/TypeTree/Decoration.lean`), not part of the legacy framework's
reductions or security notions. The legacy component layer and every legacy half of a phase are
deleted; the typed declarations carry the legacy names.

Statements restated, at the same errors and the same knowledge notion (worst case over prefixes,
a named computable extractor):

| Legacy | Typed | Why |
| --- | --- | --- |
| `piop_perfectCompleteness`: `(leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I)` | `piop_completeness`: every outcome of the honest execution, for any input oracles, sends the stack, is accepted and lands in `Seam.done`; `piop_perfectCompleteness`: the acceptance has probability one | the typed execution is an `OracleComp` with no failure and no shared-oracle state, so perfect completeness is a statement on the support |
| `piop_rbrKnowledgeSoundness` at `piopError I` for `piopExtractor P S` and its state function | `piop_knowledgeSoundness`: a `KnowledgeCertificate` from `M3Holds` whose extractor is `piopExtractor P S s`, whose challenges are the slots' samplers at `piopErrors I` and are what the verifier draws (`SamplesChallenges`); `piopTerminal` its terminal relation, `Seam.done` at the verifier's verdict; `piop_badChallenge` the reading of a false acceptance | ArkLib's typed knowledge notion is the certificate; the state function becomes the backward maps' knowledge state |
| `piopExtractedStack_eq`: the fold of the extractors returns the committed message | `piopExtractedStack_eq`: `extractWitness` on every execution path is the message the path sends | the transcript is an execution path |
| `piopError_le`: `∑ i, piopError I i ≤ overE (2^32 + 2^31 + 2^20)` | `piopErrors_bounded`: the errors along every path sum to at most the same | a typed schedule is a tree; its errors are summed along paths |
| `leanVm_perfectCompleteness`, `leanVm_rbrKnowledgeSoundness` | `leanVm_perfectCompleteness`, `leanVm_knowledgeSoundness` | the same at every instance |
| `Sumcheck.transport` along a `TranscriptMap` | `Sumcheck.transport` by `Typed.Security.decode` | the wire message decoded at the first node |
| `Refinement.knowledge_transport` in ArkLib's straight-line game | `Refinement.knowledge_transport`: a false mapped extraction on an accepting path has a bad challenge | the typed framework states knowledge as a certificate, not a game |
| each `…_not_rbr`, `…_no_stateFunction` | `…_one_le`, `…_no_security` (and `Typed.sampleChallenge_one_le`, `sendChecked_no_security`, `Security.one_le_of_escape`) | refutations of a typed security at any extractor |
| a phase's `Complete` (a reduction's perfect completeness) and `Security` (a state function and its bound) | `Typed.Complete` on honest runs and `Typed.Security` (backward maps, prover preservation, local bounds, terminal relation) | the typed bundle |

The opening's query check had no round; it is now the protocol's leaf (`Typed/Commit`): the
verifier asks the stack the batched claim after the five phases, and the opening phase is the
batching, ending in `Seam.opened`.

## Progress log

| Date | Stage | State |
| --- | --- | --- |
| 2026-10-18 | 0 | Survey and plan written. |
| 2026-10-18 | 1 | `Typed/Front`, `Typed/Component`, `Typed/SendChecked`, `Typed/SampleChallenge` built, tested (`tests/LeanerVMTests/Protocol/Typed.lean`). The security bundle holds the backward witness maps and propositions only, so it computes; `Security.certificate` assembles ArkLib's `KnowledgeCertificate`. |
| 2026-10-18 | 2 | The end-to-end front reads typed one-round securities: `Typed/Batch`; typed steps and securities beside the legacy ones (`…T`: the bus's challenge, roots and values, the sumcheck round's message and challenge, the grand product's combiner and descendants, Flock's seven, the final values, `TableArk`'s `xiSecurity`, the public-input phase's `PublicInput.security`), each from the hypothesis lemma the legacy one now uses too; `BusComponent` deleted, `BusDoom` and `FlockArk` restated. The front page's reachable constants include, from `ArkLib/OracleReduction/`, only `OracleInterface` and `instDecidableEqOption` (`Prelude.lean`), neither of the legacy framework's notions. |
| 2026-10-18 | 3 | `Typed/Append`: two components in sequence (`Def.append`, with `Samplers.append`, `Errors.append`, `proverAppend`); completeness on honest runs (`Runs`, with `runs_of_mem_support` linking it to ArkLib's `executeStrategies`, and `runs_append`); knowledge soundness through ArkLib's `RoundExtractor.append`, `changeInputState`, `isProverPreserving_append`, `isLocallyBounded_append` and `TerminalRelation.append`, a rejection entering a false state (`falseExtractor`). `Complete` is now stated on honest runs, `Complete.execute` its reading on the execution; provers are strategies with no setup. A composed security computes (`@[macro_inline]` on `mono` and `append`, extractors built from extractors). Composition needs one witness type through both components, which every leanVM component has. |
| 2026-10-18 | 3, 4 | Slots in the type (`Typed.Slot`, `Def … σ`), as the legacy schedules are; `PublicInput.complete`; the typed spine slots begin (`Spine/Slots.lean`). |
| 2026-10-18 | 5 | `Typed/PassThrough`, `Typed/Schedule`; the sumcheck round and rounds, Layer 4's sumchecks, and the table sumcheck phase (`tableSumcheck`, both halves at `tableErrors I`). |
| 2026-10-18 | 6 | The grand-product argument (`gkr`, both halves at `Typed.gkrErrors`) and the bus phase (`busPhase`, both halves at `busErrors I`). |
| 2026-10-18 | 7 | Flock's components, the Flock argument (`Flock.flock`, `flockComplete`, `flockSecurity` at `flockErrorsT`) and the Flock phase (`flockPhase`, both halves at `flockErrors I`, the generic errors within the slot's by `flockErrorsT_le_flockErrorsOf`). Each front phase is now built, on the typed framework, from the one-round securities the end-to-end front reads. |
| 2026-10-18 | 8 | The spine typed: `Typed/Commit` (the witness sent as an oracle message, a front component over it, one question at the leaf through `priorQuery`; completeness, and the knowledge certificate whose extractor reads the witness off the message), `implAfter` and `runs_of_mem_support_leaf` in `Typed/Front`, path sums of errors (`Errors.along`, `Errors.Bounded`) with the slots' bounds; the opening as batching (`opening`) into `Seam.opened`, the question to the stack (`stackQuestion`) the spine's; `Spine/Compose` replaced by the typed bundle and master theorems (`piop_perfectCompleteness`, `piop_knowledgeSoundness`, `piopExtractedStack_eq`, `piop_badChallenge`, `piopErrors_bounded`), and `Piop` on it. |
| 2026-10-18 | 9 | The legacy framework deleted: the component layer (`Component`, `KnowledgeAppend`, `ExtractIn`, `PassThrough`, `SendOracle`, `GuardedVerdict`, `KeepOracles`, `FrontVerifier`, `Refutation`, `TranscriptMap`, `Schedule`, `SendChecked`, `SampleChallenge`, `QueryCheck`, `Batch`, `Spine/Phase`) and every legacy half of a phase; `Spine/Errors` keeps `overE`. The typed declarations take the legacy names. `Typed/Decode` and `Sumcheck.transport`; `Refinement.knowledge_transport` on certificates; `Typed.Security.one_le_of_escape`; the library's refutations ported. The tests moved to the typed statements. Gate on `h1`: `./scripts/validate.sh` and `lake exe node-vectors`. |
