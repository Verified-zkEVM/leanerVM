# Status: the leanVM proof system on ArkLib

Where the [protocol blueprint](protocol-blueprint.md) stands on `main` at `b692351` (2026-10-02),
checked on 2026-10-02; a row marked *on merge* lands with its pull request. This file says what is built and what the built work still owes the
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
| grand-product GKR: definition and completeness (Layer 5) | #62 | on merge | on merge |
| sumcheck: definitions and completeness (Layer 4) | #75 | on merge | on merge |
| sumcheck: knowledge soundness (Layer 4) | #76 | on merge | on merge |
| Flock phase: definition and completeness (Layer 9) | #86 | on merge | on merge |
| Flock phase: knowledge soundness (Layer 9) | #88 | on merge | on merge |

The two master theorems are proved over an abstract instance and are conditional on the five
phases after the commitment; of those, the public-input phase is built, with the specification's
check and with the check of the deployed verifiers. `#print axioms` gives the kernel's three
axioms, and no `sorryAx`, for the two master theorems and both halves of the commit phase and of
each version of the public-input phase. On the branch of #62, the grand-product GKR's
definition and completeness (`LeanerVM/Protocol/ToArkLib/GrandProduct.lean`: `gkr` at the
slot's schedule `gkrSpec`, `gkrComplete`) stand on two generic one-round components, a
checked message (`ToArkLib/SendChecked.lean`) and a checked challenge
(`ToArkLib/SampleChallenge.lean`), a sumcheck round of their own composed from the two
(`ToArkLib/SumcheckRound.lean`), and the product tree and partial sums
(`ToCompPoly/ProductTree.lean`, `ToCompPoly/PartialSum.lean`). On the branch stacked on
it, the GKR's knowledge soundness (`ToArkLib/GrandProductSecurity.lean`: `gkrSecurity` at
`gkrError F (1 / |F|) nside μ`) stands on the two components' security halves, the
round's (`SumcheckRound.roundsSecurity`, for a consistent and sound family carrying no
witness) and a table's zeroness on a partial point (`ToCompPoly/Restriction.lean`), which
tracks the riders and the descendants' values while the coordinates of a point are drawn
one at a time. On the branch stacked on that one, Layer 4's sumcheck (`ToArkLib/Sumcheck.lean`): a
virtual polynomial (`Sumcheck.Virtual`: tables read off the context and a formula of the point and
the tables' values), its sumcheck over a cube weighted per coordinate (`Sumcheck.weighted`, binding
the highest variable first, the tables' values at the final point as its last message), the plain
and the normalized variants as its two weightings (`Sumcheck.plain`, `Sumcheck.normalized`), their
perfect completeness, and the transport of round-by-round knowledge soundness to a verifier that
decodes a round message sent without one coefficient (`Sumcheck.transport`, on the generic
`ToArkLib/TranscriptMap.lean`); with the weighted cube sums and the degree in each coordinate it
needs (`ToCompPoly/WeightedCube.lean`, `ToCompPoly/IndividualDegree.lean`). On the branch of
#76, their round-by-round knowledge soundness at `d / |F|` per round (`Sumcheck.weightedSecurity`,
`plainSecurity`, `normalizedSecurity`). On the branch of #86, the Flock phase's
definition and completeness (`Protocol/Flock.lean`: `flockPhase` at the slot `flockSpec`,
`flockComplete`, `flockError_le`), the generic Flock argument for a batch of Boolean R1CS blocks
at leanVM's sizes and constants (`ToArkLib/Flock/`, `Parameters/Flock.lean`). On the branch of
#88, stacked on it, its knowledge soundness (`flockSecurity`, on the generic
`ToArkLib/Flock/Security.lean` and the field facts of `Protocol/FlockFields.lean`). Nothing else is
built: the other phases, the other generic components, the Clean bridge, the adaptor, WHIR, the
Merkle trees, the compiled verifier and the base theorems.

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
- **The bus phase's side conditions** (decision 30) gain that the pull and count leaves fit in
  `2 ^ μBus`: the deployed verifier asserts it (`leaf.rs:123-146`) and an instance does not
  guarantee it, since `μBus` is the push side's depth.
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
  challenge by challenge (`Gkr.familyT`). One stand-in is left: its combiner, `Gkr.lambdaStep`,
  stands in for `batch nside`, which can take it only as `sampleChallenge` at the batching map,
  taking the statement maps as arguments: a relabelling pass-through on either side would put a
  `!p[]` into the schedule and break the definitional equality with `stepSpec`. When that hole
  lands in that form, the combiner becomes it. The blueprint is asked, through a `docs(protocol)`
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
- **The Flock phase (Layer 9)** is the generic Flock argument of `ToArkLib/Flock/` (an ArkLib
  candidate: block R1CS, tables, round polynomials, zerocheck, lincheck, ring switching and their
  composition `Flock.flock`) at leanVM's sizes, constants and region (`Protocol/Flock.lean`).
  Where it differs from Layer 9's sketch, or what it leaves to the work after it:
  - `FlockRegion` carries the block's R1CS, `r1cs : BlockR1CS E 14` (the Boolean matrices `A`,
    `B` with the forward and backward walks that evaluate them, and the proofs that the walks
    compute the products), in place of the sketch's opaque `Holds` and `decHolds`, and
    `FlockRegion.Holds` is defined from it: every block of the region's bits, packed 64 to a cell,
    satisfies the R1CS and holds `1` at position `512` (decision 12, strengthened: the predicate
    is the R1CS, not any predicate an instance names). The verifier's lincheck terminal needs the
    circuit; an opaque predicate gives it nothing to evaluate.
  - `FlockSpec` is not declared here. It names leanISA's `Blake2sRelation` and `Blake2sRow`, which
    the wall forbids above the adaptor; it moves to the adaptor (Layer 3), where its inhabitant,
    with the BLAKE2s circuit and its walks, supplies `leanIsaInstance`'s region (`#3`'s). The phase
    needs only the region.
  - The phase is written for every circuit; the BLAKE2s walk transcribed from
    `blake2s_row_values` (`verifier.py:1180-1301`) is the region's data for the leanISA instance,
    owed with `FlockSpec`'s inhabitant. So is the test of the circuit walk against the Python.
  - The honest run is on a tiny argument (two skipped values, two blocks of four wires): an
    `E` multiplication costs about 2 ms in the interpreter and an inversion about 1 s, and
    leanVM's sizes are a block of `2^14` positions. The slot's typing, the constants and the zero
    region's failure are checked at leanVM's sizes, by theorems and `#guard`s.
  - The skip nodes carry their inverse Lagrange denominators (`Flock.SkipDomain`), computed once
    per node set, so no Lagrange weight inverts at run time. The deployed verifiers keep one
    denominator (`verifier.py:1104-1124`: the skip domain is a subspace, so every node has the same
    one); the leanVM domain computes all 192 from the nodes (`SkipDomain.ofPts`), and the
    one-denominator form, with the theorem that it is the same, is left to the compiled verifier.
  - The zerocheck's and the lincheck's rounds are the generic round (`SumcheckRound.rounds`) on
    families of their own: `Flock.zcFamily` (normalized, lowest variable first, its invariant the
    constant position's residual on the batch coordinates drawn so far) and `Flock.linFamily`
    (plain, highest variable first). Like the GKR's, the zerocheck binds the lowest variable first
    and its invariant moves challenge by challenge, which `Sumcheck.normalized` does not do.
  - `sum_flockErrorOf` is public, for `flockError_le`.
  - Knowledge soundness (`flockSecurity`, #88, stacked on #86) is the generic
    `Flock.flockSecurity` at leanVM's constants, raised to the slot's error by `Security.mono`. It
    takes two facts about the constants that completeness does not, proved in
    `Protocol/FlockFields.lean`: the fixed coordinates' weights are `F_2`-independent
    (`fixedWeights_independent`), and ring switching is injective (`ringSwitch_injective`, through
    `1, y^{2^k}, y^{2^{k+1}}` being a `K`-basis of `E`, `limbs_eq_zero_of_frob`). The sketch's
    third fact, that the 64 `c_k` are distinct monomials, is not needed: a stage-by-stage count
    replaces Schwartz–Zippel.
  - The proved error is below the slot's: `2/|E|` on a batch round where the slot charges
    `3/|E|`, and `1/|E|` on a ring-switching coefficient where it charges `2^{2^{5−p}−1}/|E|`
    (`flockError_le_flockErrorOf`; `(3k + 169)/|E|` in all, `sum_flockError_generic`). The slot's
    error is kept, since the spine fixes it; the blueprint is asked, through a `docs(protocol)`
    pull request, whether to lower it (the findings *Ring switching's error* and *The constant
    position's error* in [leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin)).
  - Refutations, as theorems on the generic components, whatever the extractor and the state
    function: the lincheck's terminal check (`linEnd_unchecked_no_stateFunction`), the zeros on
    the skip nodes (`skipDraw_unzeroed_not_rbr`: interpolating values sent at every node) and
    the constant position's `α³` term (`alphaDraw_noConst_not_rbr`). The target `T` computed from
    the `s_i` has its rejection test (wrong slices give a false weighted claim); the weighted
    claim entering the pool is the output seam, which the security's output hypothesis reads.
    Counterexamples on small parameters show the two facts above are load-bearing (a Boolean
    fixed coordinate, the generator `1`).
  - `FlockSpec`'s inhabitant, which the hole names beside `flockSecurity`, is owed with the
    BLAKE2s circuit (#3's); the security, like the definition, holds for every circuit.

## What can start now

The spine's slots are on `main`, so the phases are written against them. These can start: Clean
expressions as polynomials (Layer 2), batching (Layer 4), the fingerprint (Layer 5), the WHIR
opening, and the Merkle trees with the WHIR parameters (Layer 11). The table sumcheck (Layer 7)
stacks on the sumcheck's definitions and knowledge soundness. The Flock phase's knowledge
soundness (Layer 9) is built on the branch stacked on the Flock phase's. The GKR's knowledge
soundness on the generic round (Layer 5) is built on the branch stacked on #62.

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
| ArkLib #1256, #1257 (and #615) | the Flock phase | the packing coordinates, observations and batching of Diamond–Posen ring switching, and the Flock paper's quirky layout | never as they are: leanVM's ring switching is the Frobenius-map variant (Annex A), whose soundness needs none of them; `ToArkLib/Flock/` is the candidate instead |
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
