# Status: the leanVM proof system on ArkLib

Where the [protocol blueprint](protocol-blueprint.md) stands on `main` at `ad0c5f0` (2026-10-07),
checked on 2026-10-07; a row marked *on merge* lands with its pull request. This file says what is built and what the built work still owes the
blueprint. What is wanted is the blueprint's; who is taking which hole is issue
[#12](https://github.com/Verified-zkEVM/leanerVM/issues/12)'s; discrepancies in the leanVM sources
are in [leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin). Open pull requests
are not part of `main`.

The pins are those of `upstreams.json`: leanVM `a386121f`, ArkLib `7653a901`, CompPoly
`572f9973`, Clean `42fe4b26`, VCVio `a4232d08`, PolyFun `41d3b21d`, Lean and Mathlib `v4.34.1`
([dependencies.md](../dependencies.md#lean-434-port-review)).

## On `main`

| Hole | Pull request | Commit | Merged |
| --- | --- | --- | --- |
| field instances (Layer 0) | #15 | `51021d9` | 2026-09-11 |
| the spine | #58 | `5cb7da6` | 2026-09-28 |
| the knowledge-soundness composition, ported from ArkLib #615 | #58 | `5cb7da6` | 2026-09-28 |
| tables and stacking (Layer 1) | #59 | `f4d858c` | 2026-09-29 |
| the public-input phase with the specification's check (Layer 8), both halves | #60 | `b435631` | 2026-09-29 |
| no hole: the upgrade to Lean 4.34.1 and the new pins | #61 | `144c5aa` | 2026-09-29 |
| the wall, and the field instances' inner-product oracle | #64 | `3cf0139` | 2026-10-02 |
| the spine at the slots' schedules and errors | #65 | `ca34001` | 2026-10-02 |
| tables and stacking's strided reader, and the public-input phase's pool from the values sent | #66 | `b692351` | 2026-10-02 |
| fingerprint and collision bound (Layer 5): the fingerprint polynomial | #39 | `24860c3` | 2026-10-05 |
| the public-input phase with the deployed check (Layer 8) | #72 | `c9bd599` | 2026-10-05 |
| grand-product GKR: definition and completeness (Layer 5) | #62 | `7d8252d` | 2026-10-05 |
| grand-product GKR: knowledge soundness (Layer 5) | #70 | `a100d8b` | 2026-10-05 |
| sumcheck: definitions and completeness (Layer 4) | #75 | `c70f552` | 2026-10-06 |
| sumcheck: knowledge soundness (Layer 4) | #76 | `a11ca6d` | 2026-10-06 |
| batching by powers (Layer 4) | #77 | `a4981a4` | 2026-10-07 |
| table sumcheck phase: definition and completeness (Layer 7) | #85 | `a6659e6` | 2026-10-07 |
| table sumcheck phase: knowledge soundness (Layer 7) | #87 | `ad0c5f0` | 2026-10-07 |
| fingerprint and collision bound (Layer 5): the product lemma and the collision bound | #78 | on merge | on merge |
| bus phase: definition and completeness (Layer 6) | #79 | on merge | on merge |
| bus phase: knowledge soundness (Layer 6) | #80 | on merge | on merge |

The two master theorems are proved over an abstract instance and are conditional on the five
phases after the commitment; of those, the public-input phase is built, with the specification's
check and with the check of the deployed verifiers, and the bus phase, both halves, with #79 and
#80. `#print axioms` gives the kernel's three
axioms, and no `sorryAx`, for the two master theorems, both halves of the commit phase and of
each version of the public-input phase, Lemma 5.2 and Theorem 5.1 (`sideProduct_poly_eq_iff`,
`card_sideProduct_collision_le`, `sideProduct_collision`), and the bus phase's results
(`busComplete`, `leaf_decomposition`, `Bus.sum_forms_eq_total_iff`,
`Bus.prod_countLeaves_ne_zero_iff`, `Bus.ridersZero_iff`, `Blocks.prod_stackAt`,
`busSecurity`). The grand-product GKR's definition and completeness
(`LeanerVM/Protocol/ToArkLib/GrandProduct.lean`: `gkr` at the slot's schedule `gkrSpec`,
`gkrComplete`) stand on two generic one-round components, a checked message
(`ToArkLib/SendChecked.lean`) and a checked challenge (`ToArkLib/SampleChallenge.lean`), a
sumcheck round of their own composed from the two (`ToArkLib/SumcheckRound.lean`), and the
product tree and partial sums (`ToCompPoly/ProductTree.lean`, `ToCompPoly/PartialSum.lean`).
Its knowledge soundness (`ToArkLib/GrandProductSecurity.lean`: `gkrSecurity` at
`gkrError F (1 / |F|) nside μ`) stands on the two components' security halves, the round's
(`SumcheckRound.roundsSecurity`, for a consistent and sound family carrying no witness) and a
table's zeroness on a partial point (`ToCompPoly/Restriction.lean`), which tracks the riders
and the descendants' values while the coordinates of a point are drawn one at a time. Layer 4's sumcheck (`ToArkLib/Sumcheck.lean`) is a virtual
polynomial (`Sumcheck.Virtual`: tables read off the context and a formula of the point and the
tables' values), its sumcheck over a cube weighted per coordinate (`Sumcheck.weighted`, binding
the highest variable first, the tables' values at the final point as its last message), the
plain and the normalized variants as its two weightings (`Sumcheck.plain`,
`Sumcheck.normalized`), their perfect completeness and their round-by-round knowledge soundness
at `d / |F|` per round (`Sumcheck.weightedSecurity`, `plainSecurity`, `normalizedSecurity`),
and the transport of round-by-round knowledge soundness to a verifier that decodes a round
message sent without one coefficient (`Sumcheck.transport`, on the generic
`ToArkLib/TranscriptMap.lean`); with the weighted cube sums and the degree in each coordinate it
needs (`ToCompPoly/WeightedCube.lean`, `ToCompPoly/IndividualDegree.lean`). Batching by powers
(`ToArkLib/Batch.lean`: `Component.batch`, `batchComplete`, `batchSecurity` at `(k − 1) / |F|`)
stands on the power combination and its root count of #43 (`ToCompPoly/PowerBatching.lean`,
carried with its author; its uniform-sample bound is superseded by `batchSecurity` and gone); the
GKR's combiner is `Component.batch`. The table sumcheck phase (Layer 7,
`LeanerVM/Protocol/TableSumcheck.lean`) is `ξ` as `Component.batch` of the constraints' and the
sides' claims, Layer 4's plain sumcheck on `τ_max` variables of `tableSummand`, and the final
values; with the sum over the cube (`sum_tableSummand`, `tableSummand_target`), the degree in
each variable (`tableSummand_degree`), `tableSumcheckComplete` and its round-by-round knowledge
soundness at the slot's error (`tableSumcheckSecurity`); with tables read on more variables than
they have (`ToCompPoly/Multilinear.lean`: `lowCoords`, `repeatHigh`), the multilinear weight of a
point and the coordinates weighted `(0, 1)` (`ToCompPoly/WeightedCube.lean`: `prodWeight`,
`weightedCubeSum_lowCoords`), and the degree of a polynomial with mapped coefficients and of the
weight (`ToCompPoly/IndividualDegree.lean`). The fingerprint polynomial of a tuple
(`ToCompPoly/Fingerprint.lean`, #39) and, with #78, the product polynomial of a multiset of
tuples with its injectivity and its collision count (`ToArkLib/GrandProductPoly.lean`), and their
leanVM reading (`Fingerprint.lean`: `fingerprint`, `sideProduct`, `sideProduct_poly_eq_iff`,
`sideProduct_collision`) complete the fingerprint hole. The bus phase's definition and
completeness (`LeanerVM/Protocol/Bus.lean`: `busPhase` at the slot's schedule,
`leaf_decomposition`, `busComplete`) stand on the grand-product argument, the product of a
stack's cells (`Blocks.prod_stackAt`) and the fingerprint; its knowledge soundness
(`LeanerVM/Protocol/BusSecurity.lean`: `busSecurity` at the slot's error `busError I`) on the
grand-product argument's knowledge soundness and the collision bound. Nothing else is built:
the other phases, the other generic components, the Clean bridge, the adaptor, WHIR, the Merkle
trees, the compiled verifier and the base theorems.

## What the built work owes the blueprint

The built work meets the blueprint except where it differs from it deliberately or settles what
the blueprint leaves open, as listed below. The spine's review against the blueprint and the
pinned sources is [archived](../reviews/protocol-spine-revision.md).

- **The layout's law.** `Layout` keeps the lift `extend` and one law, but the law is the
  reading law on the derived `Layout.read`, not "a cube point of the column lifts to a cube
  point of the stack": `z ↦ (z, z)` sends the cube to the cube and `q̃(z, z)` is no column's
  extension. `Layout.read` decodes the lifted cube point (`boolIndex`, the inverse of
  `boolVec` on the cube).
- **Typed claim pools.** The pools the phases hand on are vectors whose lengths the instance
  fixes (`busClaims`, `tableClaims`, `pubClaims`, `poolSize`): one claim per boundary column,
  per column of each sumcheck table, per public line, and the Flock phase's weighted claim.
  The blueprint's pools are lists; with lists the opening's error `(J − 1)/|E|` is no closed
  form of the instance, since `J` is the pool's length. For the same reason `M3Instance`
  carries `nLines`, with `publicLines : Stmt → Vector (PublicLine _) nLines`.
- **The weight's ring is a parameter**: `Weight E n` (`ToArkLib/InnerProduct.lean` is generic
  over two rings and a homomorphism), where the blueprint writes `Weight n`.
- **Message shapes of the slots.** A sumcheck round sends its `d + 1` coefficients as
  `Vector E (d + 1)`; the grand-product argument sends each tree's descendants as
  `Fin 3 → Vector E (2 ^ ρ)` and draws the combination challenges one round each; the Flock
  slot's zerocheck rounds are two blocks, of `8` and of `kBatch` rounds, since their errors
  differ; the boundary values and the table sumcheck's final values are vectors of the
  instance's lengths; `pubSpec` and `openingSpec` are constants, the same for every instance.
- **The schedule combinators are generic** (`ToArkLib/Schedule.lean`): one message, one
  challenge, a sumcheck round of a degree, the layers of a grand-product argument and the whole
  argument (`gkrSpec`, `gkrError`), over any challenge type, with their instances and their
  errors from a unit; `Spine/Errors.lean` instantiates them at `E` and `overE 1`, and the
  grand-product argument of #62 consumes them. Instances of appended schedules are applied by
  name (`msgAppend`, `chalAppend`): instance search does not find ArkLib's instances for the
  messages and challenges of two schedules side by side when the schedules are concrete, and
  ArkLib's own files apply them by name too. A bundle of a schedule with its two instance
  families and its error would replace the named instances; not tried.
- **The Flock slot sends two values after the zerocheck**, `v_a` and `v_b`: both deployed
  verifiers derive the third, `v_c`, from the running claim
  (`crates/flock/src/zerocheck.rs:421-422`, `verifier.py:1148-1149`). The slot's exact error sum
  (`sum_flockErrorOf`) is what the blueprint's `flockError_le` only bounds.
- **Deleted as unused**: the field instances `instOracleInterfaceE` and `instOracleInterfaceListE`
  (the message schedules carry their own interfaces) and `Phase.Guarded`.
- **The front phases carry a witness** (decision 31): `Phases` holds them as `Phase.FrontDef`,
  a component with a `Component.Front`, the proof that its verifier is a check and a verdict on
  the statement and the transcript that hand the stack on. `FrontDef.ofFrontVerifier` builds one
  from a `FrontVerifier`, a verifier typed without access to the stack, and
  `Component.Front.append` composes the witnesses, so a phase assembled from generic components
  (the grand-product argument, through `gkrFront`) fits the slot. The proofs are stated on the
  component `FrontDef.toDef`. The spine's revision had typed the front phases instead, which no
  composition of ArkLib oracle verifiers could meet.
- **`piopError_le`** takes the sizes as hypotheses (`μ_bus ≤ 30`, `τ_max ≤ 32`, `B ≤ 2^16`,
  `kBatch ≤ 32`, `J ≤ 2^16`) and bounds the sum by `(2^32 + 2^31 + 2^20)/|E|`; the numeric
  test shows it below `2^{-159}`. That the leanISA instance meets the hypotheses at admissible
  sizes is the adaptor's to prove.
- **The refutation lemmas** are `Verifier.not_rbr_of_escape`, the certain-escape lemma for a
  check that later challenges follow, `Verifier.not_rbr` and `Verifier.not_rbr_zero` derived
  from it, and `Reduction.not_perfectCompleteness_of_reject` (with a primed form for the empty
  shared oracle), in `ToArkLib/Refutation.lean`.
- **`Component.Extraction`** sits between `Guarded` and `Security`: the extractor and its
  state function without the bound, which `piopExtractor` reads. A security computes too:
  `Security.mono` and `Security.append` are inlined before compilation, so the errors, real
  numbers, stay in types and proofs, and `Phases.Security.toDef` is a plain `def`; a security
  takes no real number as an argument. `piopExtractedStack_eq` goes through
  `Extractor.RoundByRound.ReadsFirst`: an extractor whose first step reads the first message
  returns it on every transcript, and a sequence of extractors keeps its first part's first
  step.
- **Layer 1's pruning.** `unstack_eval`, `bytecodeColumn_slot` and the reading lemmas behind
  the layouts (`Layout.readWith_comap`, `Blocks.readWith_extendPoint`, `Blocks.readWith_strided`)
  are private; `stackColumn_eval`, `stackColumn_eval_ambient`, `stack_eval_ambient_zero`,
  `evalMle_lagrangeBasis`, `slice_bytecodeColumn`, `readColumn_stackColumn`, `idxColumn_get`,
  `bytecodeSlotColumn`, `prodVars` and its two lemmas are gone, with `BlockClaims.lean` and its
  test; the adaptor builds the slot columns it needs. The generic helpers the deleted module
  consumed (`unstack_eval₂_eq_sumCube`, `unstack_eq_of_window_eq`) stay as upstream material.
- **Layer 8's verifier** is `verifierWith` at the check and the pool from the values sent, a
  shape the refutation tests instantiate with the check removed, weakened to its first value,
  the unsent line's claim dropped, the cells swapped and an extra check. The pool (`pooledFrom`)
  takes the proof that the message has one value per sent line, and every verifier of that
  shape rejects another message before its check: the length is no check a variant can drop.
  The blueprint's `claimsFrom` on a bare list would need a value for a missing entry, and the
  computed value, the only candidate, is the one choice no refutation can catch. The alias
  `PublicInput.pSpec` is gone; the slot is `pubSpec`.
- **The deployed public-input check** is the specification phase's prover with a verifier that
  checks one equation on the two public words, `c₀ + y·c₁ = (1 + r)·w₀ + r·w₁` (`checkWords`;
  `cpu/mod.rs:752-755`, `verifier.py:1400`, `aggregate.py:1680-1683`), at the same slot and error. Where it
  differs from the blueprint, or what it leaves to the work after it:
  - `deployedPublicInputPhase` is a `Phase.FrontDef`, the type `Phases.pub` has (decision 31); the
    blueprint's signature says `Phase.Def`. Its public surface mirrors the specification phase's:
    `deployedVerifier`, `deployedGuarded`, `deployed_complete`, `deployedStateFunction` and
    `deployed_rbr` stand beside the declarations the hole lists.
  - `accepts_two_challenges` states its hypotheses inline: the blueprint's `Accepts` would clash
    with `PublicInput.accepts`, and inline it shows that the pooled claim on the top limb is one
    of them. Off the shape of two sent lines `checkWords` is the specification's check, as the
    blueprint's "otherwise" has it, so that `checkWords_of_check` holds of every instance.
  - The message is no function of the statement and the challenge, as the specification's is, so
    the knowledge state function says after the challenge that some message is accepted
    (`deployedStateFunction`); the bound is the specification's `1/|E|`, over
    `bad_challenge_unique_words`.
  - The sources pool the top limb at the constant `0`; the phase pools the value computed from
    the statement. They agree where the top line is zero, which the public words' zero top limb
    gives (`read_public` rejects a nonzero one, `cpu/mod.rs:139-143`), and on a statement whose
    top line is not zero the constant is unsound (tested). That `leanIsaInstance` has a zero top
    line, and lists `mem_0` then `mem_1` as its two sent lines (`checkWords` reads their cells as
    the limbs `y⁰` and `y¹` of the two words), is the adaptor's to prove.
- **The grand-product GKR (Layer 5)** is at the spine's slot schedule and error: `gkr` carries
  no error and is typed at `gkrSpec F nside μ` of `ToArkLib/Schedule.lean`, whose design it owns,
  `gkrComplete` extends `Component.Guarded`, and its knowledge soundness `gkrSecurity` is stated
  at `gkrError F (1 / |F|) nside μ`, with `|F|` written `Nat.card F`; the slot's unit
  `overE 1` is the same number written with `Fintype.card E`, and the slot takes it through
  `Component.Security.mono`. It is at the slot's verifier type too: `Phase.FrontDef` is a
  component with a `Component.Front` witness, a check and a verdict on the statement and the transcript that hand
  the stack on, which `gkrFront` provides by composing the parts' witnesses through
  `Component.Front.append`; a test builds the bus phase's shape around `gkr 3 toy.μBus` as a
  `Phase.FrontDef` at `busSpec toy`.
  Its sumcheck rounds are the generic round of `ToArkLib/SumcheckRound.lean`
  (`SumcheckRound.rounds`) on a family of its own (`Gkr.family`: the eq-weighted partial sums,
  honest polynomials computed as sums of products of affine factors, the domain
  `SumcheckRound.normalizedWeights`, binding the lowest variable first, and the riders'
  condition). The table sumcheck (Layer 4, below) is the same round on another family, so the
  module stays as the round both share. The GKR does not consume `Sumcheck.normalized`, the
  normalized variant over a virtual polynomial, which binds the highest variable first and
  carries a side condition no challenge changes, where the GKR's security tracks its riders
  challenge by challenge (`Gkr.familyT`). Its combiner, `Gkr.lambdaStep`, is batching by powers: `Component.batch` at the batching map, taking the
  statement maps as arguments (a relabelling pass-through before it would put a `!p[]` into the
  schedule and break the definitional equality with `stepSpec`; one after it would add a step,
  its security and a `mono` for nothing), its combined claim `powerBatch`, its completeness
  `batchComplete` and its security `batchSecurity`, and the descendants' check combines by
  `powerBatch` too; the count it used, `SumcheckRound.card_filter_powerSum_eq_le`, is gone for
  #43's `card_false_batch_le`. The blueprint is asked, through a `docs(protocol)`
  pull request, for three changes: the unused last combiner moves out of the generic `gkr` into
  the bus phase (it is a leanVM transcript quirk, `gkr.rs:423`); the GKR's knowledge soundness
  lists batching by powers among its needs; the normalized sumcheck the GKR consumes is the
  generic round on its family (as the sumchecks' entry below asks). Its knowledge soundness,
  `gkrSecurity`, is proved on the generic round's, `SumcheckRound.roundsSecurity` for any
  consistent and sound family, not on Layer 4's `Sumcheck.normalizedSecurity` as the holes
  table's *Needs* has it. Its riders' state is the blueprint's: zero tables inside the argument,
  and at the last layer zero on the coordinates drawn so far (`Gkr.progTrack`, through
  `RestrictedZero` on a `Partial` point), so a rider's escape at a challenge is one value and is
  dominated by the claim's; the descendants' values are tracked the same way across the
  combination challenges.
  The refutations of its two checks are theorems on the generic components with the check
  removed, whatever the extractor and the state function:
  `SumcheckRound.drawChallenge_unchecked_not_rbr` (no knowledge error below one for the round's
  challenge, from the honest polynomial at a wrong claim) and
  `Component.sendChecked_no_stateFunction` (no knowledge state function at all for the
  descendants' message), instantiated on the three sixteen-leaf trees in the tests. Its security
  definitions are plain `def`s and compute at `E`: none takes a real number or a `Fintype`
  instance (`Fintype E` is noncomputable). Each is stated at its exact error, `N / |F|` with
  `Nat.card` under `[Finite F]`, the counts of bad challenges as `Nat.card` of a subtype, and
  raised with `Component.Security.mono`; the tests build `gkrSecurity` at the slot's error and
  its extraction as `def`s at `E`.
  Where it differs from Layer 5's sketch: the riders are
  an argument of the relations (`Gkr.relIn`, `Gkr.relOut`) and of `gkrComplete`, not of `gkr`,
  which never reads them; a rider's variable count is a `Fin (μ + 1)`, so that its low point
  exists; a round message is the polynomial's coefficients, not a polynomial with a degree
  bound, so the degree bound is the message's length; the first step reads the roots through a
  statement map (`Gkr.rootStmt`), since the schedule has no pass-through before the first
  layer.
- **The fingerprint and the collision bound (Layer 5)** are in two modules, not in the GKR's:
  the product polynomial of a multiset of tuples over any ring, its injectivity and the count of
  its collisions are generic (`ToArkLib/GrandProductPoly.lean`, carried from Elias Judin's
  branch for #33, ArkLib issue #901), and the reading at `K`, `E` and sixteen coordinates is a
  leanVM module (`Fingerprint.lean`), since a generic module names no protocol constant.
  `sideProduct_collision` bounds the collisions of two multisets of at most `N` tuples, the
  bus phase taking `N = 2 ^ μ_bus`; its counting form, `card_sideProduct_collision_le`, counts
  the colliding challenges with `Nat.card`, the form a computable security consumes. The
  blueprint's Layer 5 file line and its Interfaces list are owed an edit for both, through a
  `docs(protocol)` pull request.
- **The bus phase (Layer 6)** is at the slot's schedule `busSpec I`, a `Phase.FrontDef`
  (decision 31; the blueprint's signature says `Phase.Def`), assembled from a checked challenge
  `(α, β)`, a checked message (the roots, the check `R_c ≠ 0`), `gkr 3 μ_bus` and a message (the
  boundary values) through `Component.Front.append`. Where it differs from Layer 6's sketch:
  - The side conditions are one structure, `Bus.Conditions`: the blueprint's two (`1 ≤ I.d`, a
    table with a constraint fits in the leaf stacks' depth) and that the pull and count sides fit
    in `2 ^ μ_bus`, which an instance does not guarantee since `μ_bus` is the push side's depth,
    and without which a side would be truncated. The deployed verifier asserts the fits of its
    layouts (`leaf.rs:130-134`; it asks the pull side's depth to equal the push side's, which
    is stronger) and rejects a point shorter than `τ_max` (`constraints.rs:251-253`).
    `τ_max ≤ μ_bus` is derived (`Conditions.τmax_le`). That `leanIsaInstance` meets
    `Bus.Conditions` at admissible sizes is the adaptor's to prove; `leanVmPhases` needs it.
  - A block of leaves is a `Bus.Source` (a boundary block, one flush of one table, one count
    column); a side's blocks are listed by `Bus.sources` and stacked by a stable sort, largest
    first. `pushLeaves`, `pullLeaves` and `countLeaves` are the three sides of
    `Bus.sideLeaves`; a count leaf is the count cell itself.
  - `leaf_decomposition` is stated per side with each block's leaf extension as the verifier
    writes it (`Source.leafEval`): `β − Σ_i eq(α, i)·c̃_i` for a block of tuples, the column's
    extension for a count column.
  - A form's terms: for a flush block, its weight times `β` against the constant `1` and its
    weight times `−eq(α, i)` against coordinate `i`'s polynomial; for a count column, its weight
    against the column's variable. The bus phase pools no claim on a table's column.
  - The riders are the tables' constraints and one rider on no variable that is zero exactly when
    the public lines and the Flock predicate hold (`Bus.linesRider`): the grand-product
    argument's relations carry only its leaves and riders, and the two predicates of
    `Seam.commit` the bus does not touch travel through it this way. The table sumcheck carries
    the same two predicates, with the bus phase's column claims, as Layer 4's side condition
    (`TableSumcheck.side`), since a sumcheck has no riders; a generic frame for front components
    (a predicate of the data and the oracles a component hands on, conjoined to both of its
    relations) would serve both and replace this rider.
  - A committed boundary column's value is read at its place among `I.boundaryColumns`
    (`Bus.valueOf`), and its claim's point is the first `κ` coordinates of `ζ`.
  - The unused last combiner stays inside `gkr`; the blueprint's request to move it into the bus
    phase is not met.
  - The check `R_c ≠ 0` is refuted at the roots step: without it the step has no knowledge state
    function from `Bus.afterChallenge` to the grand-product argument's input relation, whatever
    the extractor, on any instance with a balanced stack whose constraints, lines and Flock
    predicate hold but with a zero count (the bus tests' `roots_unchecked_no_stateFunction`; the
    tests' zero-count stack is such a stack by `#guard`, since the kernel cannot evaluate a
    constraint or the bus's permutation on a concrete stack). It is at the step's relations, as
    the grand-product argument's refutations are; a refutation at the phase's seams is not
    attempted: it would take a generic backward induction over the rounds (from a statement with
    no witness, a set of prefixes closed under every challenge, with a message for every prover
    round, and accepted at the end, leaves an error of one at some challenge; the review's probe
    compiles one), and that the unchecked phase's honest prover is accepted after every vector
    of challenges, which needs the support of ArkLib's `Prover.run` round by round. Owed.
  - Its knowledge soundness, `busSecurity`, is composed from its steps' at the completeness
    half's intermediate relations: `Bus.afterChallenge` after `(α, β)` (the products agree, the
    counts are nonzero, the constraints vanish, the lines and the Flock predicate hold), then the
    grand-product argument's input and output relations. The challenges' count of bad values is
    `card_sideProduct_collision_le` at `N = 2 ^ μ_bus`, with `|E|` written `2 ^ 192` (`card_E`):
    the count is a number the compiled security holds, and `Nat.card E` does not compute. The
    convention *Errors* rewrites `|E|` to `2^192` only in the numeric test, so it is owed a
    rewording.
  - The phase is run by parts in the tests (the challenges and roots, the leaves at a point, the
    last step); the grand-product argument between them is the one its own tests run by hand.
  - The knowledge-soundness half consumes, besides the phase, `Bus.afterChallenge`,
    `prod_pushLeaves`, `prod_pullLeaves`, `Bus.prod_countLeaves_ne_zero_iff`,
    `Bus.ridersZero_iff`, `Bus.riders_vanish_iff`, `Bus.sum_forms_eq_total_iff`,
    `Bus.lowPoint_point`, `Bus.sideTuples_perm`, `Bus.blocks_total` and `push_fits`.
  - The blueprint is owed a `docs(protocol)` edit: Layer 6's signatures (`busPhase I h` with
    `Bus.Conditions`, a `Phase.FrontDef`; `countLeaves I q` without challenges;
    `leaf_decomposition` per side; `busSecurity I h` at `(busPhase I h).toDef`), and the
    Interfaces list (`Bus.Conditions`, `Blocks.prod_stackAt`, `Blocks.total_eq_sum`).

- **The sumchecks (Layer 4), definitions, completeness and knowledge soundness** stand on the
  GKR's round (`ToArkLib/SumcheckRound.lean`), which is now the sumcheck's round engine and
  stays: a family of claims, honest polynomials, a weighted domain per round and a side
  invariant, with the rounds' completeness and knowledge soundness. Where the built work differs
  from Layer 4's sketch:
  - `Virtual F X O W n m` carries the tables (functions of the public data, the oracles' contents
    and the witness), and its formula reads the public data and the point as well as the tables'
    values, so that factors the verifier evaluates itself (an equality polynomial, a padding
    product) are part of the formula; the sketch's formula reads the values only, with the
    heights, the padding `∏_{k ≥ τ_j} X_k` and the factor `eq(ζ_{<τ_j}, ·)` inside
    `Sumcheck.plain`. Those are leanVM's table sumcheck's choices, so the table sumcheck (Layer 7)
    builds them into its formula and lifts a table of `τ_j` variables to `τ_max` itself; the
    generic sumcheck takes no heights.
  - The degree is a hypothesis of completeness, `IndividualDegreeLE (V.summand ctx) d` (degree at
    most `d` in each variable of the composed summand), not the sketch's `formula_poly` (a total
    degree of the formula in the values), which says nothing of the point's factors. The bound is
    computed coordinate by coordinate (`DegreeLEAt`), since the table sumcheck's padding and
    equality factors sit in different coordinates: their degrees add to four over all
    coordinates and to three in each (tested). `DegreeLEAt.mvPolynomial_eval` bridges a
    constraint: a polynomial of total degree `d` in tables' extensions has degree `d` in each
    variable.
  - Plain and normalized are one construction over weights per coordinate, unit weights and the
    weights `(1 - p_k, p_k)` of a point (`Sumcheck.eqWeights`); both bind the highest variable
    first, as leanVM's table sumcheck does. The GKR's layers bind the lowest variable first
    through their own family on `SumcheckRound.normalizedWeights` (above), so the rounds, their
    completeness and their knowledge soundness are written once, in `SumcheckRound`, and the
    equality weights twice, the same weights read in opposite orders. `Sumcheck.normalized` (the
    virtual form) is not what the GKR consumes, and no phase consumes it yet; WHIR's folding
    rounds are interleaved with commitments and would take `SumcheckRound` rounds, not the whole
    component. The blueprint is asked, through a
    `docs(protocol)` pull request, to say so: the normalized sumcheck the GKR consumes
    (decision 16, the *Sumcheck variants* convention, the GKR rows' *Needs* and the Interfaces
    list) is `SumcheckRound.rounds` on `SumcheckRound.normalizedWeights`, and
    `Sumcheck.normalized` is kept, with its security, only if a consumer is named, or dropped.
    Until then both stay, since the hole names them.
  - The honest round polynomial interpolates the next claim at `d + 1` distinct nodes, a
    parameter of the definition (`nodes`, injective for completeness): a field of characteristic
    two has no `0, 1, …, d`.
  - The rounds and the last message are exposed apart (`Sumcheck.rounds`, `Sumcheck.final`, with
    their completeness and front witnesses), since the table slot nests its schedule to the left,
    `draw ++ rounds ++ say`, and a test builds the table slot's shape from them. The last message
    takes its output map (`final V out`, `finalComplete` for any output relation the true values
    land in), so that the table phase outputs its own statement, `I.Stmt × TableOut I`, at the
    slot's schedule; `finalOut` and `relOut` are the default.
  - The relations carry a side condition on the context (`relIn V wt side`, `relOut V side`, the
    family's invariant), which no challenge changes: what the table phase's seams say beside the
    claim (the column claims carried forward, the public lines, `aux`) rides through the
    sumcheck, at no cost in the error, since a challenge cannot make a false side condition
    true.
  - `Sumcheck.transport` is stated per round, for any security of the round, from the wire: a
    round sent with `d` of its `d + 1` coefficients (`wireSpec`), decoded injectively onto the
    messages that pass the round's check (`decodeWire`, `encodeWire_decodeWire`,
    `decodeWire_encodeWire`). It rests on a theorem for any verifier and any causal map of
    transcripts from one schedule to another with the same directions that carries the
    challenges across bijectively (`Verifier.rbrKnowledgeSoundnessWorstCaseWith_comap`); the
    map need not be injective. The map of the whole protocol's transcripts, and Fiat–Shamir's
    absorption of the wire, are the compiled verifier's to build.
  - Knowledge soundness is the rounds' (`SumcheckRound.roundsSecurity`, for the family with no
    side invariant, so its soundness clause is vacuous) followed by the last message's at error
    zero, with the extractor that keeps the witness; its hypotheses are completeness's, the
    degree in each variable and distinct nodes, since the round's bound compares the recorded
    polynomial with the honest one. Each security is a plain `def` that computes at `E`, stated
    at `d / |F|` with `|F|` written `Nat.card F`, and a test raises the rounds of a cubic plain
    sumcheck over the toy's stack to the table slot's per-round error `overE 3`. What the table
    phase composes at `tableSpec` is `roundsSecurity` and `finalSecurity` (any output map and
    output relation from which the values and the side condition follow), with `rel_zero` and
    `mem_rel_self` relating the seams to the family's relations.
  - Owed: the securities take the nodes' injectivity, which the verifier does not read (its
    verifier and the relations are the same for every choice of nodes). Dropping it needs the
    round's security in `SumcheckRound` stated for prover polynomials apart from the family, and
    a family whose honest polynomial is the true round polynomial, chosen classically; that
    family is data the compiled security would have to build, so the securities would stop
    computing (acceptance test 24). Kept until the module goes upstream, where a consumer's honest
    prover may not interpolate; the table phase proves the injectivity once, for completeness.
  - The final check comes with its refutation (`final_unchecked_no_stateFunction`: without it the
    last message has no knowledge state function at all); the round check's is the base's
    `SumcheckRound.drawChallenge_unchecked_not_rbr`.
  - Decision 33 is taken by default: the sumcheck is written here. ArkLib's legacy sumcheck has
    its knowledge soundness admitted; its typed sumcheck proves completeness and plain soundness
    for one polynomial with unit weights, and no open pull request adds knowledge soundness to
    either (the survey is in the watch list below).

- **The table sumcheck phase (Layer 7)** is at the slot's schedule `tableSpec I`. Where it differs
  from Layer 7's sketch, or what it leaves to the work after it:
  - `tableSumcheck` is a `Phase.FrontDef`, the type `Phases.table` has (decision 31); the sketch
    says `Phase.Def`.
  - `tableSummand I` is a `Sumcheck.Virtual` (Layer 4's form) whose public data is the statement,
    the bus output and `ξ` (`TableSumcheck.Data`), where the sketch takes `s` and `ξ` as
    arguments; the degree three is a theorem (`tableSummand_degree`), not part of the type. Its
    tables are the sumcheck tables' columns read on the `τ_max` variables, the same in every
    slice of the coordinates their table lacks (`repeatHigh`), so that the last message is the
    columns' values at the final point's low coordinates; the equality factor and the padding
    are the formula's, as the multilinear weight of each table's coordinates (`prodWeight` of
    `tableWeights`: those of `eq(ζ_m, ·)` below `τ_t`, `(0, 1)` above), which in characteristic
    two is the deployed `∏_{m<τ_t} (1 + ζ_m + r_m) · ∏_{m≥τ_t} r_m` (tested).
  - `tableSummand_target` is stated under the bus seam. What the security reads is the identity
    before it, `sum_tableSummand`: the sum over the cube is the true values (each constraint's
    extension at `ζ`, each side's forms summed) batched by the powers of `ξ`, so it is the target
    exactly when the bus seam's two claims hold (`trueValues_eq_claimed_iff`).
  - Completeness takes `I.d ≤ 2`: the slot's rounds are cubic and the summand has degree `d + 1`
    in each variable. It is the phase's side condition, as the bus phase's are (decision 30);
    that the leanISA instance has `d = 2` is the adaptor's to state.
  - `ξ` is #77's `Component.batch` over the `B + 3` claimed values, zero for each constraint
    then the three totals, numbered table by table (`constraintPos`, `position_val`), so the
    branch stacks on #77; the final values are numbered the same way (`columnPos`).
  - The honest prover interpolates its round polynomials at `0, 1, y, y + 1`
    (`TableSumcheck.nodes`).
  - Knowledge soundness (`tableSumcheckSecurity`) takes `I.d ≤ 2` too, and needs it for the
    error: a summand of higher degree in a variable would let a cubic message agree with the true
    round polynomial at more than three challenges. It is #77's `batchSecurity` with the true
    values `trueValues`, fixed before `ξ`, then Layer 4's `roundsSecurity` and `finalSecurity`
    through `finalClaims_holds_iff`, raised to `tableError` by `Component.Security.mono`; a plain
    `def`, inhabited at `E` in the tests.
  - The refutations of the phase's two checks are tests: `final_unchecked_no_stateFunction`, from
    `Component.sendChecked_no_stateFunction` at the phase's output map and the table seam (Layer
    4's lemma of that name is stated at the default output map), and `round_unchecked_not_rbr`,
    Layer 4's round refutation on the phase's family. The batching step has no check: the target
    is derived from the bus totals, never sent.
  - Owed: the spine's `M3Instance.lowPoint` is the generic `lowCoords` at a sumcheck table's
    height (the same term); it is to be written so once the bus phase's branch, whose proofs
    unfold `lowPoint` by name, has merged. The review is
    [archived](../reviews/protocol-table-sumcheck.md).

## What can start now

The spine's slots are on `main`, so the phases are written against them. These can start: Clean
expressions as polynomials (Layer 2), the Flock phase's definition and completeness (Layer 9),
the WHIR opening, and the Merkle trees with the WHIR parameters (Layer 11).

## Upstream watch

External work that may feed or replace a hole. The state of each is on GitHub.

| Upstream | Hole | What it would replace or feed | Adopt when |
| --- | --- | --- | --- |
| ArkLib #615 | the knowledge-soundness composition | the port `ToArkLib/KnowledgeAppend.lean` | some ArkLib framework proves a guarded-first append for the named form |
| ArkLib's typed framework (its roadmap items 3–4; #1251) | the spine | the framework decision (decision 24) | it has round-by-round knowledge soundness and its composition |
| ArkLib #1245 | the list-binding compilation | the local stateless round-by-round-to-plain corollary | merged, for its soundness half |
| ArkLib #1244, #1128, #1129 | the sumchecks | the classical leaf's repair (the verifier evaluates the sent polynomial; its knowledge soundness stays admitted); honest round identities over one `MvPolynomial` | reference only |
| ArkLib #1261, #1269, #1274, #1277 | the sumchecks | the typed sumcheck's round-by-round soundness and state-restoration security, for one polynomial with unit weights and no witness | when the typed framework proves round-by-round knowledge soundness (decision 24) |
| ArkLib's computable sumcheck (#1214, #1242, #1243; at the pin) | the sumchecks; the GKR's rounds | the round of `ToArkLib/SumcheckRound.lean`, which sends the coefficients as one message and weights the domain | an adaptor to `OracleReduction` and a weighted domain exist (decision 33) |
| ArkLib #818, #383, #992 | the GKR; WHIR | patterns for a layer and for a proximity test as reductions | never as they are |
| ArkLib #848, #469, #627 | the compiled verifier | Fiat–Shamir and BCS statements | a chain-based transform with proof of work, which none of them is |
| ArkLib issues #900, #901 | tables and stacking; the fingerprint | the requests for stacking and fingerprints upstream | when the pull requests open |
| VCVio #571 | the Merkle trees | leanVM's trees on VCVio's library | the fit lemma holds (decision 32) |
| Clean #466 | Clean expressions as polynomials | the proof-side bridge | merged and the pin bumped |
| Clean #464, #20 | the adaptor | leanISA's `BalancedPair` | merged and the pin bumped |
| Clean #446, #23 | the adaptor | the three fixed-column conjuncts | merged and the pin bumped |

Two checks are owed at the current pins and have not been made: whether
`ReedSolomon.mcaError_affineLine_johnson_le`'s constant meets Annex B's per-level budget at the
pinned parameters, and whether Clean `42fe4b26` contains any of Clean #446.

The survey log kept here until 2026-09-29 is archived in
[protocol-survey-record.md](../reviews/protocol-survey-record.md); the library limits it recorded
are in [dependencies.md](../dependencies.md#limits-that-bind-the-proof-system), the Lean pitfalls
in [tests/README.md](../../tests/README.md), the findings against the sources in
[leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin), and the decisions in the
blueprint.
