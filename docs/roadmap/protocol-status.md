# Status: the leanVM proof system on ArkLib

Where the [protocol blueprint](protocol-blueprint.md) stands on `main` at `08dd030` (2026-10-07),
checked on 2026-10-10; a row marked *on merge* lands with its pull request. This file says what is built and what the built work still owes the
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
| fingerprint and collision bound (Layer 5): the product lemma and the collision bound | #78 | `3c7ecbe` | 2026-10-07 |
| bus phase: definition and completeness (Layer 6) | #79 | `97ef4d4` | 2026-10-07 |
| bus phase: knowledge soundness (Layer 6) | #80 | `b12a9e8` | 2026-10-07 |
| the opening phase (Layer 10), without `leanVmPhases` | #81 | `08dd030` | 2026-10-07 |
| Flock phase: definition and completeness (Layer 9) | #86 | on merge | on merge |
| Flock phase: knowledge soundness (Layer 9) | #88 | on merge | on merge |
| Flock phase: the product-gate circuit library (Layer 9) | #92 | on merge | on merge |
| Flock phase: the BLAKE2s circuit (Layer 9) | #93 | on merge | on merge |
| Flock phase: `FlockSpec` and its BLAKE2s inhabitant (Layer 9) | #94 | on merge | on merge |
| the oracle protocol: `leanVmPhases` and leanVM's master theorems (Layer 10) | #95 | on merge | on merge |
| Clean expressions as polynomials (Layer 2) | #96 | on merge | on merge |
| the adaptor: the leanISA instance, its stack and the witness read off it (Layer 3) | #97 | on merge | on merge |
| the adaptor: soundness, discharging the BLAKE2s validity (Layer 3) | #98 | on merge | on merge |
| the adaptor: completeness and the witness read back (Layer 3) | #99 | on merge | on merge |

The two master theorems are proved over an abstract instance and are conditional on the five
phases after the commitment; on `main`, the public-input phase is built, with the specification's
check and with the check of the deployed verifiers, the bus phase, both halves, with #79 and
#80, the table sumcheck, both halves, with #85 and #87, and the opening phase, both halves, with
#81. With the Flock phase (#86, #88), all five are built, and the branch of the oracle protocol
instantiates the master theorems at leanVM's phases (`Protocol/Piop.lean`: `leanVmPhases`,
`leanVmComplete`, `leanVmSecurity`, `leanVm_perfectCompleteness`, `leanVm_rbrKnowledgeSoundness`)
for every instance meeting the bus phase's conditions and the degree bound `I.d ≤ 2`. `#print axioms` gives the kernel's three
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
grand-product argument's knowledge soundness and the collision bound. The opening phase
(`LeanerVM/Protocol/Opening.lean`: `openingPhase`, `openingComplete`, `openingSecurity` at the
slot's error `(J − 1) / |E|`, `J` the pool's size) is batching by powers followed by a generic
zero-round step whose verifier asks an input oracle one question and checks the answer
(`ToArkLib/QueryCheck.lean`: `Component.queryCheck`, and the composition
`Component.batchQuery` with its two halves and its refutation), on the inner-product weights
combined by powers (`ToArkLib/WeightBatch.lean`). On the branch of #86, the Flock phase's
definition and completeness (`Protocol/Flock.lean`: `flockPhase` at the slot `flockSpec`,
`flockComplete`, `flockError_le`), the generic Flock argument for a batch of Boolean R1CS blocks
at leanVM's sizes and constants (`ToArkLib/Flock/`, `Parameters/Flock.lean`); on the branch of
#88, stacked on it, its knowledge soundness (`flockSecurity`, on the generic
`ToArkLib/Flock/Security.lean` and the field facts of `Protocol/FlockFields.lean`). On the
branches stacked on the oracle protocol's, the Clean bridge (`ToClean/ComponentPolynomial.lean`:
`Expression.toCMvPolynomial` and `Component.toM3` with their two translation theorems, over a
verbatim copy of Clean's expression polynomials in `ToClean/ExpressionPolynomial.lean`) and the
adaptor: the leanISA instance with the deployed stack layout (`Protocol/LeanIsa.lean`:
`leanIsaInstance`, `witnessOf`, `stackOf`, `leanIsa_conditions`), its soundness
(`LeanIsa/Sound.lean`: `satisfiedBy_witnessOf`, which discharges `SatisfiedBy`'s BLAKE2s validity
from the Flock region by `blake2sRowsValid_witnessOf`) and its completeness
(`LeanIsa/Complete.lean`: `m3Holds_stackOf`, `witnessOf_stackOf`), on the bus read as one bus and
the relations' clauses as equivalences (`LeanIsa/Bus.lean`, `LeanIsa/Relation.lean`). The byte
hasher and the digest encoding (`Protocol/Blake2sHash.lean`) and the WHIR parameters
(`Parameters/Whir.lean`) are on `main` (#67). On the branch `feat/protocol-merkle-octopus`, the
Merkle trees over a byte hash (`Protocol/Merkle.lean`, generic in `ToVCVio/Merkle.lean`): the root
(`merkleRootWith`, `merkleRoot`), a phase's pruned opening as the verifier checks it
(`merkleVerifyWith`, `merkleVerify`), the prover's commitment, with the tree built once, and
its openings (`merkleCommitWith`, `merkleCommit`, `merkleOpen`), completeness
(`merkleVerifyWith_merkleOpen`), the node query model (`nodeModel`), and the reading as VCVio's
batch opening for every hash (`toBatchOpening`, `merkle_fits`); they replace the single-path
check of #67 and its binding as a computed collision. On the branch
`feat/protocol-merkle-binding`, their binding by replaying the hash log
(`Protocol/MerkleBinding.lean`, generic in `ToVCVio/MerkleLog.lean`): the rows read off a log
(`extractRows`, in one pass `extractAllRows`), `binding_of_log`, which equates an accepted
opening's rows with them unless the log is inconsistent or shows a collision or a fresh hit, and
`extractRows_determined`.
Nothing else is built: the other generic components, the WHIR opening, the compiled verifier and
the base theorems.

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
  sizes is still owed: the adaptor proves the phases' side conditions, not these sizes.
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
  computed value, the only candidate, is the one choice no refutation can catch.
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
    the limbs `y⁰` and `y¹` of the two words), holds by the definition of its `publicLines`,
    which the instance tests check.
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
    `τ_max ≤ μ_bus` is derived (`Conditions.τmax_le`). `leanIsaInstance` meets
    `Bus.Conditions` at every size (`leanIsa_conditions`).
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
- **The opening phase (Layer 10)** is `Component.batchQuery` at the slot's schedule `draw E`
  (`draw E ++ₚ !p[]` is `draw E` by `rfl`, its instances included): `Component.batch` draws `ρ`
  (the specification's `λ`) and combines the pooled values into the batched claim
  `⟨W_ρ, C_ρ⟩`, `W_ρ` the pool's weights combined by the powers of `ρ` (`Weight.batch`); a
  zero-round query check (`Component.queryCheck`) asks the stack `⟨W_ρ, q⟩` and accepts when the
  answer is `C_ρ`. Its knowledge soundness is `batchSecurity`'s, the state after the challenge
  that the batched claim holds (`Opening.BatchedHolds`). The pool takes the powers as both
  deployed verifiers do: the Flock phase's weighted claims first, then the column claims in
  their order, each the weighted claim at the equality kernel of its point lifted through the
  layout (`Opening.pool_weighted`, `Opening.pool_column`; specification §8.5,
  `doc/leanvm/body/08-end-to-end-protocol.tex:94-101`, `crates/pcs/src/stack_open.rs:518-526`,
  `python-verifier/verifier.py:1409-1413`). Where it differs from Layer 10's section, or what
  it leaves to the work after it:
  - `leanVmPhases` is not in `Opening.lean` but in `Protocol/Piop.lean`, on the branch that
    composes the phases after the Flock phase's: it needs every phase, which the hole's row in the
    blueprint does not list among its *Needs*, and the opening should not import them all. There,
    `leanVmComplete` and `leanVmSecurity` fill the two bundles and the spine's master theorems
    become leanVM's: `leanVm_perfectCompleteness` and `leanVm_rbrKnowledgeSoundness`, for every
    instance meeting the bus phase's `Bus.Conditions` and the table sumcheck's `I.d ≤ 2`; the
    toy meets both, and so does a test instance whose column is a Flock region with the BLAKE2s
    circuit's R1CS; statement locks spell the two theorems at both. The blueprint's
    `leanVmPhases (I) (h₁ h₂)` takes both conditions; here `leanVmPhases` takes the bus phase's
    alone, since the phases themselves need nothing else, and the degree bound goes to the two
    bundles.
  - The section's protocol-level honest run accepted by `#guard` is not written: at the toy the
    bus phase's GKR and the table sumcheck run in `E`, which the interpreter computes slowly, and a
    pass-through has the empty schedule, not a slot's, so no bundle of pass-throughs fills
    `Phases`.
    `piopExtractedStack_eq` holds of every bundle and is the spine's test.
  - The blueprint is asked, through a `docs(protocol)` pull request, to move `leanVmPhases` and
    the protocol-level test to a hole of their own, "the oracle protocol", needing every phase,
    and to list `Component.queryCheck` and `Component.batchQuery` among the generic components.
  - Beyond the hole's names, the tests use `Opening.pool`, `Opening.values`, `Opening.weight`,
    `Opening.batched`, `Opening.question`, `Opening.check`, `Opening.accepts_iff`,
    `Opening.columnWeighted_holds_iff`, `Opening.answer_weight_iff`,
    `Opening.batched_holds_iff`, `Opening.pool_weighted` and `Opening.pool_column`; the bodies of
    the two halves use `Opening.batched_of_flock` and `Opening.answers_of_not_flock`.
  - The refutations of its check are tests: on the toy, the verifier with no check on the
    answer, the one that checks the first pooled claim alone, and the one that combines the
    claims with unit weights (two copies of one false claim cancel in characteristic two); on an
    instance with a Flock region, the one that combines the column claims alone and drops the
    weighted claim. Each accepts a pool outside the Flock seam at every challenge, so none has a
    knowledge error below one, whatever its extractor and state function
    (`Component.batchQuery_not_rbr`). The bound is attained: a pool of four claims is accepted
    at three challenges.

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
  - `FlockSpec` (`Protocol/FlockSpec.lean`) is stated against the cell relation
    `CompressCells` of `Semantics/Blake2s.lean` on eighteen limbs (`LimbsCompress`), in place of
    the sketch's leanISA `Blake2sRelation` on `Blake2sRow`, which the wall forbids above the
    adaptor. The adaptor relates the two: `Blake2sRelation r` is `LimbsCompress` of `r`'s eighteen
    value limbs in column order (`blake2sRelation_ofFn`). Its fields are the R1CS (`r1cs : BlockR1CS E 14`, matching
    `FlockRegion`), the slots, soundness (`compress_of_holds`), the honest column `gen` and
    completeness (`holds_gen`, `slots_gen`); the sketch's `Holds`/`decHolds` are the region's.
    The phase needs only the region.
  - The phase is written for every circuit; the fast circuit walks of the BLAKE2s matrices (the
    deployed `blake2s_row_values`, `verifier.py:1180-1295`, and the Rust `marginal_walk`) are owed
    by the leanISA instance, whose region they evaluate; they enter through
    `FlockSpec.compress_of_region` and `region_holds_gen`, which need only the matrices to agree.
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
  - `FlockSpec`'s inhabitant, which the hole names beside `flockSecurity`, is
    `Blake2sFlock.blake2sFlockSpec` (`Protocol/FlockSpec.lean`): the R1CS of the BLAKE2s circuit
    with the naive walks (which do not run at leanVM's size), the deployed slots
    (`hash_flock.rs:93-115`), soundness from `blake2s_sound`, and the honest column of the
    circuit's traces. Both directions are theorems. As test evidence, the executor's row and the
    RFC 7693 vector round-trip through the honest column, and the honest column of eight
    compressions equals, by digest, the region the pinned prover commits
    (`scripts/dump-flock-column-rust.sh`). The security, like the definition, holds for every
    circuit.
  - The circuit library the inhabitant is written in, with #92, stacked on #88: product-gate
    circuits over GF(2) as data (`ToArkLib/Flock/Circuit.lean`: linear
    forms as bitsets, gates, the lowering `toBlockR1CS`, the honest `trace`; the lowering's two
    directions `trace_satisfies` and `holds_eq_trace`, `gates_of_holds`), a builder with
    soundness and gate-count contracts (`ToArkLib/Flock/Builder.lean`) and the 32-bit adders
    (`ToArkLib/Flock/Words.lean`). Clean was measured and not used for the block: its expression
    trees are traversed unmemoised and its R1CS export allocates a fresh signal per product.
  - The BLAKE2s compression circuit in it (`Protocol/Blake2sCircuit.lean`, Category B, from
    `crates/flock/src/hash.rs` and `verifier.py:1180-1295`): `blake2sCircuit` (14720 product
    gates from 1280, then the 256 output rows) and `bounded_blake2s`, from the gate-count
    contracts. Both directions are theorems: `blake2s_sound`/`blake2s_sound_words` (a satisfying
    Boolean block with `1` at position 512 carries at its output positions `compress` of the
    words at its input positions) and `blake2s_complete` (the trace of any input satisfies the
    R1CS, keeps its inputs and carries their compression). That its rows are the deployed ones
    is test evidence, not a theorem: a digest of every row equals the Python walk's
    (`scripts/dump-flock-circuit-digest.py`).

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
    the leanISA instance has `d = 2` by definition.
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

- **The Clean bridge (Layer 2)** is a Clean candidate (`ToClean/`), computable over CompPoly
  and written over Clean #466's `degreeBound`, `WithinWidth` and `toBoundedPolynomial` (claimed
  by #28; on Clean's main, but in no Clean revision built for Lean 4.34). Until the pin contains
  it, `ToClean/ExpressionPolynomial.lean` is a verbatim copy of Clean's module, deleted at the
  bump (the watch list). Where it differs from the sketch:
  - Tables are generic over the type of bus sides; leanISA's carry the arithmetization's
    `Direction`, mapped to the spine's `Side` by the instance. The counted channels are a
    predicate, and the count columns are listed in column order, each once, as the Rust's
    `count_columns()` are.
  - Flushes drop Clean's multiplicities; `UnitMultiplicities`, which the kernel checks for
    leanISA's components, says there is none to drop.
  - `eval_toCMvPolynomial` is stated on a row of the width's cells (on a longer array it is
    false); `eval_fromArray_truncate` covers other rows.
- **The adaptor (Layer 3).** Where it differs from the sketch:
  - The instance's tables are the Rust's global column order: the memory columns, `BFCNT`,
    `QFLOCK`, then the six opcode tables. `Sizes` carries `0 < logMem`, which `PublicLine`
    needs; `stackOf` takes the sizes rather than a proof that `Sizes.ofWitness` returns them.
  - `witnessOf` takes the Flock specification, whose slots the layout reads the limbs at.
  - `witnessOf_stackOf` gives the opcode tables cell for cell within the components' widths: a
    witness's rows may carry cells past the width, which no constraint reads and the stack drops.
  - The blueprint's stacked-and-read-back test is not evaluated: even a stack of `2^15` cells
    does not evaluate in the interpreter in fifteen minutes. The read-back is the theorem `witnessOf_stackOf`; the
    stack's offsets are tested against the pinned Rust (`scripts/dump-leanisa-layout-rust.sh`),
    and the limbs' cells against the Flock region's slots.
  - The adaptor is `LeanIsa.lean` and five modules under `LeanIsa/`; the wall's allow-list
    admits the directory.
  - `leanIsaRefinement` is the adaptor as the spine's `Refinement` from `M3Rel` to
    `SatisfiedBy`. Owed: the sizes `piopError_le` assumes, at admissible sizes (`μ_bus ≤ 30`
    follows through the stack bound `leanIsaμ ≤ 28`, not from `logMem ≤ 32` alone). The base
    theorems apply `satisfiedBy_witnessOf` inside their event, so no knowledge transport along it
    is owed.
- **The Merkle trees (Layer 11)** are the Rust's over a byte hash, read as VCVio's (decision 32),
  on the branch `feat/protocol-merkle-octopus`. `merkleVerifyWith` is a phase's pruned opening in
  any monad, calling the hash once per stored row and once per rebuilt node, in the Rust's order
  (nine calls for the octopus of the Rust's test). Where it differs from the sketch:
  - `merkle_fits` reads the result through `Id.run`, and its row conjunct includes
    `rowWords ≤ leafWords`, without which it is false (a four-word row in three-word leaves has
    itself as its leaf image); the blueprint's sketch now says so.
  - The Rust's checks that the leaf count is a power of two and that some query is made are
    subsumed: the tree has `2^depth` leaves, and the walk over an opening of no query has no node
    to read at the top. The Rust also returns each query's full path, which is dropped.
  - The single-path check, its completeness and its binding as a computed collision are deleted.
  - Binding is log replay, on the branch `feat/protocol-merkle-binding`, deterministic and over
    any encoding of leaves and nodes into one query domain (`ToVCVio/MerkleLog.lean`).
    `extractTree` reads a tree top-down off a log, a node's children those of the first logged
    query answered by it that parses as a node (`nodePreimage`), and `leafPreimage` a leaf's
    payload; `extractLeaves` does it for every position in one pass, by hash maps
    (`extractLeaves_eq`). `MerkleTree.binding_of_log`: if the walk over a pruned opening at
    strictly increasing positions in the tree, every hash answered from the log
    `logA ++ logV`, reaches `root`, the log is `Consistent`, has no collision (`HasCollision`) and
    no `FreshHit` (a query of `logV` that `logA` never asks, answered by a root or a child of a
    node query of `logA`), then every opened payload is the one read off `logA` at its position.
    `MerkleTree.extractLeaf_determined`: with a consistent log and no fresh hit, the leaves read
    off the whole log under a root are those read off `logA`. A fresh hit grows with `logV`, the
    roots and `logA`'s known digests, and is a hit at the first occurrence of its input
    (`FreshHit.mono_logV`, `FreshHit.mono_roots`, `Known.mono`, `Fresh.anti`, `FreshHit.first`).
    Each condition has a toy mutation in which the check accepts a payload other than the
    extracted one, or with none extracted, and only that condition fails
    (`tests/LeanerVMTests/Protocol/MerkleBinding.lean`).
    leanVM's instance (`Protocol/MerkleBinding.lean`): `extractRows` takes the row width as well
    as the leaf width, since a row may begin with zero words, and is `none` where the leaf query
    found is not a row's leaf image; `binding_of_log` is stated for `merkleVerifyWith` run in
    `Option` with every hash answered by a partial oracle whose answers are logged, and equates
    the rows it returns with the leaf images of the rows read off `logA` at the queries;
    `extractRows_determined` is the instance of `extractLeaf_determined`.
  - Where binding differs from the docs pull request's sketch: the module is
    `ToVCVio/MerkleLog.lean`; the known digests are the roots and the children of `logA`'s node
    queries only (an answer of `logA` hit by a fresh query is a collision, and the extraction never
    descends into a sibling), and only fresh queries of `logV` are constrained; consistency is a
    hypothesis, since an input answered in `logV` other than in `logA` defeats the extraction.
    `fold_map` (the walk commutes with a map of node algebras) is added to `ToVCVio/Merkle.lean`.
  - Owed: `merkle_fits` is the reading as VCVio's and is not on the binding path; that
    `toBatchOpening` selects exactly the queried positions, with their leaf digests as values, is
    tested and not proved. The blueprint's decision 32 and the hashed-leaf hole are revised in the
    docs pull request. In Layer 12: that `merkleVerifyWith` run with the hash as a random-oracle
    query answered by BLAKE2s is `merkleVerify`; the probability of a collision or a fresh hit on
    the logged game. A root is never a 32-byte block of a query: the chain absorbs it as two
    scalars, each in an observe block (`transcript.rs:52`, `lib.rs:85`), so the in-play digests of
    a prefix must include the digest decoded from two consecutive observe blocks of its chain for
    a fresh hit on a root to be a hit.
- **The honest prover, compiled** (*on merge* of the stateful-provers branch). No target theorem
  advances and no statement changes: `leanVmFastProver` (`Protocol/HonestProver.lean`) is an
  honest-prover refinement, a prover whose run is `leanVmProver (leanVmPhases I h)`'s
  (`leanVmFastProver_run`), so `leanVmFast_perfectCompleteness` is the master theorem's
  completeness for it, with the same verifier. It carries prover state through the bus phase, the
  table sumcheck and the Flock phase (`Component.Cached`); the commitment, the public-input check
  and the opening run their honest provers. The BLAKE2s inhabitant's R1CS walks the compiled
  circuit's words (`ProductCircuit.toBlockR1CSE`, equal to the circuit's R1CS by
  `toBlockR1CSE_eq`). WHIR's opening has a cached prover, `whirOpenCached`
  (`Protocol/Whir/Cached.lean`), whose run is `whirOpen`'s. At the smallest admissible size the
  whole oracle protocol's prover runs in 25 s; WHIR at that size (`μ = 19`) takes 4 min to encode
  the committed word and 5 min to open (`bench/README.md`). Owed: a prover of the compiled
  protocol (Layer 12) that runs `leanVmFastProver` and `whirOpenCached` together.

## What can start now

The spine's slots are on `main`, so the phases are written against them. These can start: the
WHIR opening with the WHIR parameters (Layer 11), and the charged invariant (Layer 12). The Merkle
trees are on the branch `feat/protocol-merkle-octopus`, and their binding by log replay on
`feat/protocol-merkle-binding`.

*On merge* of #103, the first slice of the WHIR opening is on `main`: the novel basis, the
encoder as a linear injection with its distance, and the column weights with their `κ`-step
extension (`Protocol/NovelBasis.lean`: `encode`, `encode_eq_eval`, `encode_eq_of_agree`,
`encode_injective`, `encodeLinear`, `columnWeight`, `columnWeightMle`, `vanish_eq`). The blueprint
then owes two edits: its `novelBasis` is `basisElt` (the novel basis is `novelPoly`), and the reuse
row for CompPoly's `AdditiveNTT` is instantiated at `K`'s basis by the test against
`computableAdditiveNTT`, with the polynomial half restated at `K` (the module docstring says why).

*On merge* of #108, the opening of WHIR and its completeness are on `main`: `whirOpen` and
`whirOpen_perfectCompleteness` for any chain of levels (`Protocol/Whir/Open.lean`, `Ladder`), with
the fold identities and the stack's relayout (`Protocol/WhirFold.lean`, `Protocol/Whir/`), and the
generic components it is built from, which are upstream candidates (`queryRecord`,
`sendOracleBeside`, `mapWitness`, `passCheck`, the schedule of a list of steps, the sumcheck of a
product of two tables). The blueprint's Layer 11 is updated with it: the input is the one batched
claim (`Weight E μ × E`), not `Fin J → WeightedClaim μ`; the rounds are the plain sumcheck on the
product of the weight and the table, lowest variable first, with three coefficients per round
polynomial where the stream carries two; the modules are `LeanerVM/Protocol/Whir/` with the generic
parts in `ToArkLib/`; the stack and the witness are `E`-valued, with what the wiring owes. The pull
request that wires `whirOpen` into the opening phase owes the `K`-to-`E` lift of the witness. A
weight's table is lazy (`Weight.cube`), and the verifier folds each queried row once, so the
verifier runs at a deployed size: the test runs the chain of `(28, 1)` at one query per level
(`tests/LeanerVMTests/Protocol/WhirDeployed.lean`).

*On merge* of #109, the soundness of the opening is on `main`: `whirOpen_rbrSoundness`,
round-by-round soundness for the list relation, at the errors of Annex B's `thm:rbr` per challenge
(`Protocol/Whir/OpenSound.lean`), with the lists of a word, the fold-list lemma and the counting it
rests on (`Whir/Lanes.lean`, `Stage.lean`, `Counting.lean`) and the security half of each generic
component. It takes, per level, `Par`: a threshold, a list bound and a bound on the bad folds, in
counting form (`ListBound`, `McaBound`), inhabited at exact agreement and, for the list bound, at
unique decoding (`Whir/Exact.lean`); `stackRel_subset_relOpen` shows the honest inputs are in the
relation. The blueprint's Layer 11 is updated with it (the theorem's statement and the interfaces).
The theorem is not knowledge soundness.

*On merge* of the Johnson-regime pull request (branch `feat/protocol-mca-johnson`), the opening is
round-by-round sound at leanVM's parameters with no hypothesis: `deployed_rbrSoundness`
(`Protocol/Whir/Deployed.lean`) is `whirOpen_rbrSoundness` at the chain of every admissible
`(μ, R)`, each level's `Par` built by `johnsonPar` (`Protocol/Whir/Johnson.lean`) from the level's
slack. The threshold is the exact `⌈(√ρ + η)·n⌉₊`, computed in naturals (`threshold`,
`threshold_eq_ceil`); the list bound is ArkLib's pairwise Johnson bound,
`L = ⌊n(a − D)/(a² − nD)⌋` (`listBound_johnson`); the bad folds are `mcaCount κ R η`, Annex B's
constant rounded up from rational bounds so that every parameter is computed
(`mcaConstant_le_mcaCount`), from `mcaJohnson_annexB` through `mcaBound_of_mcaJohnson`, the encoder's code being ArkLib's
Reed–Solomon code (`encode_mem_code`, `exists_encode_of_mem_code`). The generic half is
`ToArkLib/McaJohnson.lean`: `McaJohnson`, its inhabitant at [BCHKS25]'s constant,
`mcaError_foldLine_eq_affineLine`, and the count of bad seeds an error bound gives. The slacks are
the Rust's doubles, dumped (`Parameters/Whir.lean`, `slacks`). The tests
(`tests/LeanerVMTests/Protocol/WhirJohnson.lean`) check `mcaConstant` against Annex B's formula,
that all 224 levels fit, and that `2^{ℓ−1}·mcaConstant ≤ 2^{64}` at each; `L_0` is 23 to 122 (the
Annex's `1/(2η₀√ρ₀)` is 110 to 648). Still owed: the wiring into the opening phase (the `K`-to-`E`
lift of the witness), and knowledge soundness through list binding (Layer 12).

*On merge* of the Fiat–Shamir chain's pull request, the first piece of Layer 12 is on `main`:
the chain, transcribed from `fiat_shamir/src/lib.rs` (`Protocol/Transcript.lean`: `FsState`,
`observe`, `sample`, `powBase`, `powOk`, `grind`, `checkPow`), every operation generic in the
64-byte hash `H : List UInt8 → m Digest` with the deployed instances in `Deployed`, and the
statement's constants computed by `blake2sBytes` directly, never through `H` (`programHash`, the
hash of the stacked bytecode table; `fsSeed`, `fs_seed`'s 78-byte preimage hashed; and the
starting state `FsState.seed`, the hash of `fsSeed` and the public input's lanes);
`FsState.checkPow_of_grind`: the verifier's check accepts the prover's nonce and lands in its
state, for every hash function. The tests are known answers dumped from the pinned Rust
(`scripts/dump-fs-chain-rust.sh`): the program hash, the seed, observes, squeezes, the grinding
base and an 8-bit grind (nonce 262). The chain computes the Rust's values; it differs only in that
the prover's nonce search takes fuel, where the Rust loops, and that at `bits ≥ 64`, outside the
Rust's debug assertion and far above the deployed `17`, `powOk` asks for a zero first word where a
release build of the Rust masks the shift.

*On merge* of the proof object's pull request, stacked on the chain's: the proof and its
transcript, transcribed from `fiat_shamir/src/transcript.rs` and `cpu/mod.rs:108-178`
(`Protocol/Proof.lean`). `Proof M` is a stream of `E` and the opening phases, generic in the
opening type `M`, which the Merkle trees will fix. The reader (`ReaderState`, `ReadM` over the
hash's monad, failing with a `ReadError`) has `nextScalar(s)`, `nextRoot`, `nextRoundPoly`,
`sample`, `checkPow`, `nextOpening` (with an authenticator), `finish` and `readSizes` (the
announced sizes and `read_public`'s setup checks, `setupOk`); the writer (`WriteM`) mirrors it.
`Proof.announced?` and `Proof.sizes?` read the sizes off the stream, and
`announced?_of_readSizes` says the reader accepts only those. `RoundPoly.decode` derives the
dropped coefficient from the claim as `transcript.rs:289-309` does (`c_1` in a plain round, `c_0`
with the equality weight factored out); `decode_encode`, `encode_decode` and `check_of_decode`
make it an injection onto the polynomials that pass the round's check, and
`Reader.nextRoundPoly_eq` says that reading a round is reading `d` scalars and decoding them, so
its chain effect does not depend on the claim. The round trip is
`ReadsBack`, proved for each pair of mirrored operations at every hash function in `Id` and
composed along `bind`; `runRead_runWrite`: the reader run on what the writer wrote returns the
related value and the writer's chain state, with nothing left over. The tests read the Rust's
transcript (a root, a cubic plain and a quartic factored round, a grind) back to the Rust's
values and challenges, and each reader check rejects its mutation. The transcript differs from
the Rust's in no accepted proof: a memory log-size of `0` fails `Proof.announced?` where the Rust
fails its window; a round takes its degree where the Rust takes its number of coefficients, and at
degree `0`, where the Rust asserts, the reader rejects and the writer writes a wire the reader
rejects; a round's coefficients are observed as they are read, as in the Python verifier; and the
sizes' limbs are checked after all eight are read. The blueprint's Layer 12 sketch owes these
edits:
- `Proof` is generic in its opening type.
- `RoundPoly.decode` takes the factored weight `eq?` and returns `Vector E (d + 1)`, the type of
  `SumcheckRound.Message`, not `Fin (d + 1) → E`.
- The sizes come with the rate (`Proof.announced?`), and `Proof.sizes?` is their first component.
- The prover's grind takes fuel and returns the nonce (`grind fuel s bits`); the verifier's check
  takes it (`checkPow s bits nonce`).
- The chain's names: the 64-byte step is `FsState.stepBytes` (the sketch's `Block` and `step`),
  absorbed by `observe`, `sample` and `absorbNonce`; the grinding predicate (`grinds`) is
  `powOk`; the challenge of a digest (`chalOfDigest`) is `FsState.challengeOf`.

*On merge* of the chain-history pull request, the hash oracle and the chain read off a log are on
`main` (`Protocol/RandomOracle.lean`). The oracle is `hashSpec` (`List UInt8 →ₒ Digest`), queried
by `hashQuery`, run by `runBlake2s` (every query answered by `blake2sBytes`) or `runRandom`
(VCVio's lazy random oracle from the empty cache, with the final cache); a uniform digest is
VCVio's vector sampler over Mathlib's enumeration of `UInt32`, and `card_digest` counts `2^256`.
`prEvent_challengeOf`: the challenge of a uniform digest is uniform on `E`;
`prEvent_lowBitsZero`: a grinding check of `bits ≤ 64` bits passes on a uniform digest with
probability `2^-bits`. The chain's steps are `Block`s, an observe, a squeeze or a nonce
(`Transcript.lean`: `Block.input`, `FsState.step` and its agreement with `observe`, `sample` and
`absorbNonce`, the parser `Block.parse?` with `parse?_input`, over the byte decoders
`digestOfBytes` and `kOfBytes` of `Blake2sHash.lean`). `chainHistory` reads a chain back from a
state to the seed through the generic `HashChain.history` (`ToVCVio/HashChain.lean`), over the
generic log predicates `Consistent`, `HasCollision`, `Fresh` and `HasHit` (`ToVCVio/QueryLog.lean`;
a hit is a fresh answer in play after the entries before it, for an in-play function of the
prefix), which have the shapes of the Merkle log replay's and are for it to reuse. The digests in
play (`inPlay`) are fixed roots (the seed among them), the halves of every logged 64-byte input,
and the Merkle roots the log's chains absorb as two consecutive observes (`rebuiltRoots`), so the
hit is a function of the prefix, as the charged invariant needs.
`chainHistory_of_noCollision_noSeed` (a logged chain is its history when the log has no collision
and no answer is the seed); `chainHistory_take_of_noCollision_noHit` (in a consistent log with no
collision and no hit, the history is in the log before any query from the chain's last state that
is none of its steps: the next step, `chainHistory_take_of_step`, the grinding base or the
grinding check); `chainHistory_determined`. A Merkle node, a 64-byte input of the same oracle, may
parse as a step and is one more entry of the log. The tests: the random oracle's answer to a fresh
query is uniform, a repeated query is answered from the cache, the log of an honest chain (with a
node beside it) gives back its blocks and states, also before the grinding base, and a collision,
an answer equal to the seed, a state produced after the query using it, and a fresh node answered
by an absorbed root each break the history or are a hit. It still owes `decodePrefix`, the lemma
that the verifier's chain walk logs its chain, and the lemma that `HasCollision`, `HasHit` and
`chainHistory` read the same on the game's `withQueryLog` log (repeats included) and on the
charged invariant's log of fresh queries, given `Consistent`; it is stated once both branches are
on `main`.

*On merge* of the sharper query-error pull request, WHIR's query positions cost
`((a − 1) / n)^t` instead of `(a / n)^t`, `a` the level's threshold and `n` its positions:
`card_agree_folded_lt` (`Protocol/Whir/FoldSound.lean`) proves that a table satisfying the residual
claim outside its language agrees with the folded word on fewer than `a` positions, which its
argument already derived, and `card_positions_bad_le`, `card_final_positions_le`,
`positionsSecurity`, `finalPositionsSecurity`, `levelErr` and `finalErr` (hence `openErr` and
`listBindingError`) count `(a − 1)^t` choices. Annex B's `thm:rbr` states `(1 − γ_i)^{t_i}`; with
`a = ⌈(1 − γ) n⌉`, `a − 1 < (1 − γ) n`, so the entry is below the Annex's at every level. With
`a^t` the entry exceeded `2^-111` at 48 of the 224 deployed levels, the threshold rounding up past
the `(1 − γ) n` the query counts were optimised for (worst `2^-110.34`: stack size `16`, rate
`2⁻¹`, level `2`, `t = 30`, `a = 40`, `n = 2^9`), so the 17 bits of grinding gave `2^-127.34`;
with `(a − 1)^t` every level is below `2^-111` (worst `2^-111.0002`, stack size `23`, rate `2⁻²`,
level `0`), so `2^-128` after grinding.

*On merge* of the charged-budgets pull request, the generic probability the random-oracle bound of
`verify_knowledgeSound` (Layer 12, toward T4) consumes is on `main` beside the charged invariant
(`ToVCVio/ChargedInvariant.lean`, `ToVCVio/UniformSample.lean`, `ToVCVio/EventExpectation.lean`).
Budgets: `expected_charge_le_of_isQueryBound` (a charge paid by a query bound of VCVio's general
form, its budget priced) and `expected_charge_le_sum` (a sum of components, component `j` at most
`κ j` on the queries satisfying `p j` and zero elsewhere, has expected total at most
`∑ j, n j * κ j` for at most `n j` such queries, `IsQueryBoundP`). A kind is read off the query
input, so it counts every query of its shape. The adversary's run is budgeted by its `Q` queries.
The verifier's run can only be budgeted by its total `V`, not by `rounds`: a Merkle node query
`left ++ right` with sibling bytes the prover chose can have a squeeze step's shape, so the
blueprint's `niError_le` term `(Q + rounds)·2^-128` becomes `(Q + V)·2^-128`, beside a `hashTerm`
that already carries `Q + V`. Two runs in sequence: `prEvent_simulateQ_bind_le_lintegral` bounds an
event of `oa >>= ob` against a stateful oracle by the expectation over the first run's end of `1`
on its bad event and of the second run's bound otherwise;
`QueryHistory.prEvent_bind_le_of_potential` starts the second run from the potential the first
leaves, so the groups the adversary leaves open are counted once; the supremum form
`prEvent_simulateQ_bind_le_add_iSup` would count them twice.
Uniform laws: the first half of a bijection, coordinatewise on tuples, low digits, first entries,
and digits in chunks are uniform. In `RandomOracle.lean`: `prEvent_challengeOf_tuple` (the
challenges of `m` fresh digests are uniform on `Fin m → E`), `challengeBits` and
`challengePositions` (WHIR's positions, `sample_queries_ordered`, faithful for `1 ≤ b < 64`, which
the tests check of every deployed level), and `prEvent_positions_uniform` (with `t ≤ m⌊192/b⌋`, the
`t` positions of `m` fresh squeezes are uniform on `Fin t → Fin (2^b)`). The tests check the
positions against the Rust's two-limb read by hand-computed values. It still owes the lemma that
the verifier's `walkPositions` reads `challengePositions` of its squeezes' challenges, the step of
the potential for a group's later queries, and `misbehaves_rom` itself.

*On merge* of the list-binding branch (`feat/protocol-list-binding`), the list-binding compilation
is on `main` (`Protocol/ListBinding.lean`, `Protocol/Whir/Decode.lean`, the `K` word `KWord` in
`Protocol/Whir/Word.lean`, and the generic `ToArkLib/Relist.lean`, `ToArkLib/SendEncoded.lean`,
`ToArkLib/MapOracles.lean`, `ToArkLib/FirstRound.lean`, `ToCompPoly/LinearSolve.lean`).
`listBinding_compile` is the security of `commitWord ⟫ fronts ⟫ batch ⟫ openInput ⟫ whirOpen L`
from `M3Rel I` to acceptance at `listBindingError`: `L₀` times the oracle protocol's errors on its
challenges, `L₀` level 0's list bound, and `openErr L ps` on WHIR's; for every bundle of phases
with its security, every chain with its parameters and every `ListDecoder` at level 0's threshold
`(L.headPar ps).a`. The extractor list-decodes the committed `K` word and picks the first stack
satisfying `M3Holds` (`commitPick`): the stack it returns is that one whenever there is one
(`listBinding_extractedStack_eq`), and at round `1` the state function holds exactly when there is
one (`listBinding_kSF_one`), so a failed extraction leaves the state function false for every
witness. `ListDecoder` is specified by WHIR's list relation (`mem_iff`); its inhabitants are
`ListDecoder.bruteForce` (Gaussian elimination over `K` on every set of `2 ^ κ` positions),
`ListDecoder.exactFirst` (the exact path, `exactFast_eq`, then a fallback) and, at exact
agreement, `ListDecoder.exact`; `isInK_of_cl` makes the members of a `K` word's list `K`-valued.
The exact path is one elimination over `K` with all lanes as one right-hand side,
`O(2^(3κ) + 2^(2κ+ℓ))` operations, and a check of the whole word, `2^(κ+R+ℓ)` encodings of
`O(κ · 2^κ)` operations each; it is not the deployed prover's inverse transform.
`Component.Front.relist` is the generic step. `listBinding_perfectCompleteness` is the other half,
from the phases' completeness: each carries over to the phase over the word
(`Component.Front.overComplete`) at its seam read on the honest word, and WHIR's opening receives
the honest word of the stack in `E` (`kwordOf_lift`). The shapes differ from the blueprint's sketch
in four places: `relist` takes the front component over the new oracles with a proof that its
check and verdict are the old ones (`Front.over` builds it, answering the oracle queries the front
verifier never makes), and the list is a `List` with a length bound; the committed word is a `K`
word (`KWord`), so that every member of its list is a stack, and a zero-round step `openInput`
reads it in `E` for WHIR (a virtual output oracle, `Component.mapOracles`), whose security is the
seam to `relOpen` (`relist_of_relOpen`); `listBinding_compile` takes the height equation
`κ + sh.ℓ = I.μ`; `exactFast_eq` holds at every threshold `2 ^ κ ≤ a ≤ 2 ^ (κ + R)`, with no
unique-decoding condition. It still owes the inverse additive transform for a fast exact path at
deployed sizes and the instantiation at the deployed chain with a Johnson list bound; and, since
the committed word is a `K` word, `verify_iff_compiled` must read the level-0 rows of a proof as
`K` symbols (the deployed commitment's leaves), not as `E` ones.

*On merge* of the deployed list-binding branch (`feat/protocol-list-binding-deployed`, stacked on
the list-binding and Johnson-regime branches), the compilation holds at leanVM with no hypothesis:
`listBinding_deployed` (`Protocol/ListBindingDeployed.lean`) is `listBinding_compile` at the
leanISA instance of every program and admissible announcement, at every valid rate, with
`leanVmPhases`, `leanVmSecurity` (`leanIsa_conditions`, `I.d ≤ 2`), WHIR's `deployedChain` and its
parameters, and `deployedDecoder`; `listBinding_deployed_rbrKnowledgeSoundness` and
`listBinding_deployed_perfectCompleteness` are its halves. Since the Johnson branch computes each
level's bad-fold count (`mcaCount`), the chain is data and `listBinding_deployed` is a definition
with no `noncomputable`: its extractor compiles. Level 0 of the chain is also computed on its own
(`deployedHeadShape`, `deployedHeadKap`, `deployedHeadThreshold` in `Protocol/Whir/Deployed.lean`;
`deployedChain_head` decides on the window that the chain's level 0 is that one: six folds,
`μ − 6` variables left, `johnsonPar`'s threshold, 726 at `μ = 15` and rate `2⁻¹`).
`deployedDecoder` is `ListDecoder.nttFirst` over `ListDecoder.bruteForce`, built at those indices,
and `deployedPick` is the commitment's extractor there, which compiles without building the chain
(`deployedPick_eq_commitPick`); `listBinding_deployed_kSF_one` (at round `1`, for every witness,
the state function holds exactly when `deployedPick` succeeds) and
`listBinding_deployed_extractedStack_eq` (the extracted stack is the pick) are stated with it, and
`commitPick_eq_some` gives `M3Holds` of what it returns. The generic `listBinding_kSF_one` takes a
symbolic round `k` with `k.val = 1`: a literal round makes the elaborator evaluate the schedule's
length, through the chain, at the deployed instance. The fast exact path is the additive transform
(`Protocol/Whir/Transform.lean`: `fwd`, `inv`, `encodeFast`, proved against `encode` by
`fwd_getElem`, `fwd_inv`, `inv_fwd`, `encodeFast_getElem`; `encodeMatrix` is its row
`novelAt`), and `exactNtt` (`Protocol/Whir/DecodeNtt.lean`) interpolates each lane on the first
coset and checks it on every coset; `ListDecoder.decode_eq_of_codeword` makes its candidate the
whole list. `kwordOfFast` is the honest word by the same transform (`kwordOfFast_eq`). Measured in
compiled code (a local harness, not committed) on the honest word of a random stack, with this
branch's field arithmetic (the specification's; the compiled fast paths are another branch): at
`μ = 15` the decode takes 45 s at rate `2⁻¹` and 80 s at `2⁻²`, the honest word 7 s and 14 s; at
`μ = 16`, 106 s and 192 s, the word 17 s and 38 s; the list is the stack every time. The brute
force behind the exact path is exact but runs on toy words only, so a dishonest word at a deployed
size has no executable extraction. Still owed: an efficient list decoder for words off the code.

*On merge* of the random-oracle definitions pull request, the game and the per-challenge budgets
are on `main`. `Protocol/RandomOracleGame.lean`: `loggedGame V prog input A` runs the adversary
(`A : OracleComp hashSpec (Proof PrunedMerklePaths)`) logged, then `V hashQuery prog input proof`
logged, with `V` any function of `verifyWith`'s shape (`VerifierWith`) until the executable
verifier lands; `Run` holds the proof, the two logs and the verdict. `extract F prog input proof
log` is computable: the announcement through `setupOk`'s checks, the level-0 root from stream
scalars `8, 9`, every level-0 row under it by `extractAllRows` at `level0Lanes` words in leaves of
`2^ℓ` words, a missing row zero, the stored row's lanes reversed as the Rust stores them
(`laneRow`, `whir.rs:1305-1316`), then `deployedPick`; `extracts_iff_isSome` makes `Extracts`'s
`M3Holds` automatic. `Hit` and `HashMisbehaves` take the proof's roots and the flip as parameters,
since both read the verifier's chain walk; `core` instantiates the flip with the transcript
decoder's clause. `Bad` and `bad_density` are the event and the bound of `listBinding_deployed`'s
`rbr` at the unit shared oracle. `Protocol/ListBindingBudget.lean`,
`Protocol/Whir/DeployedBudget.lean` and the generic `ToArkLib/ScheduleBounds.lean`:
`listBindingMark` marks WHIR's query positions, and `listBindingError_deployed_le` bounds every
other challenge by `2^-128` and the query positions by `2^-111`, so by `2^-128` after the 17 bits
of grinding, at every admissible announcement and rate (`Whir.deployed_fits` decides the window,
`L₀ ≤ 122`; `leanIsa_μBus_le`, `leanIsa_B_le`, `leanIsa_poolSize_le` bound the front at leanISA).
The executable verifier must read the level-0 openings at the wire shape `extract` reads: rows of
`level0Lanes prog s (deployedHeadKap μ ρ)` words, leaves of `2^ℓ` words for level 0's fold `ℓ`
(`deployedHeadShape μ ρ`), depth `deployedHeadKap μ ρ + (deployedHeadShape μ ρ).R`.
`deployedHeadKap_eq` decides `deployedHeadKap μ ρ = μ − initialFold` on the window, so
`level0Lanes` is the verifier branch's `Verify.nLanes`, which `extract` takes at assembly. The
blueprint has the three edits these definitions asked of it: Layer 11's threshold is
`a = ⌈(1 − γ) 2^{κ+R}⌉`, its `thm:rbr` query entry is `((a − 1) / n)^t`, and Layer 12's `Hit` and
`HashMisbehaves` take the proof's roots and the flip as parameters, with no "earlier answer" in play
(an earlier answer to another input is a collision). Still owed: the flip, the proof's roots,
`core` and `misbehaves_rom`.

*On merge* of the executable verifier's stacked pull requests (on the proof object's and the
Merkle trees', with the fast field arithmetic merged), the rest of Layer 12's verifier is on
`main`, slice by slice.

- **The setup** (`Protocol/Verify/Setup.lean`): `setup?` reads the announced sizes and rate off
  the stream and makes `read_public`'s checks before any hash; `leanVm prog s`, `stackMu`,
  `nLanes` (the level-0 rows' committed lanes, `witness.rs:97-101`) and `ladderOf` are what they
  fix; `walkSetup` observes the sizes and reads the root; `samples`, `readRound(s)` and
  `replayRounds` are the walk's primitives and the algebra's round decoding. Two changes keep the
  verifier from building what it never reads: a known boundary coordinate carries its column as a
  thunk and the evaluator of its extension (`Coord.known`, `Coord.ofColumn`; leanISA's
  `idxCoord`, the closed form `idxColumnEval`, and `entryCoord`), so that the leanISA instance's
  boundary no longer computes the `2^logMem` index column; and two `@[csimp]` theorems
  (`LeanIsa.opcodeTable_eq_tab`, `LeanIsa.width_eq_tab`: each opcode table is converted from its
  component once), beside the stateful provers' `Blocks.selectorWeight_eq_selectorWeightFast` (a
  block's selector weight is a product, not an entry of a whole Lagrange basis). The fixture:
  `scripts/dump-proof-rust.sh` proves the
  division program of the Rust suite (`lean_compiler/tests/suite/field_div.rs`, with its fill
  blocks, 2048 instructions) at the test rate and prints the program, its hash, the public input,
  the stream (770 scalars) and the pruned openings (four levels) as the text of
  `tests/LeanerVMTests/Protocol/RustProofData.lean`; `RustProof.lean` loads it, checks the
  program against the Rust's program hash, and checks the setup against the second verifier's
  reading (`μ = 20`, 33 lanes, queries `224, 56, 32, 22`, `μ_bus = 18`, five boundary columns,
  104 column values) and its rejections.
- **The bus phase** (`Protocol/Verify/Bus.lean`): `walkBus` reads `α`, `β`, the two roots, the
  combiners and the layers from the root down (`gkrRadices`: one binary layer first at an odd
  depth) and the boundary values; `busStep` checks the count root, replays the layers
  (`replayGkr`: each round decoded with the point's equality weights, the descendants checked
  against the combined final claim as `Gkr.combineCheck` does, the next point `(u, c)`) and hands
  on the oracle verifier's own `Bus.busOut`, generic over the instance (`leanVmBus` at leanISA's).
  On the fixture the walk squeezes the second verifier's challenges, the nine layers replay to its
  bus point and the three totals are its totals (`tests/LeanerVMTests/Protocol/VerifyBus.lean`,
  with the zero count, a flipped descendant, a flipped round coefficient, a changed root and a
  missing value rejected).
- **The table sumcheck and the public input** (`Protocol/Verify/Tables.lean`): `walkTables` and
  `walkPub`; `tableStep` is the oracle verifier's (the target batched from the totals, the rounds
  decoded, `Sumcheck.finalCheck` of the table summand, `TableSumcheck.tableOut`), `pubStep` the
  deployed one (`PublicInput.checkWords`, `pooledFrom`). The fixture found the `DEREF` table's
  flush order differing from the Rust's ([leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin));
  the leanISA table now reads in the Rust's order, and on the fixture both phases pass
  (`VerifyTables.lean`, with a flipped column value, a flipped round coefficient, a missing value,
  a flipped public value and a third public value rejected).

## Upstream watch

External work that may feed or replace a hole. The state of each is on GitHub.

| Upstream | Hole | What it would replace or feed | Adopt when |
| --- | --- | --- | --- |
| ArkLib #615, #1295 (merged after the pin) | the knowledge-soundness composition | the port `ToArkLib/KnowledgeAppend.lean` | a verbatim copy of #1295 at the next refactor; deleted at the bump that contains it |
| ArkLib's typed framework (its roadmap items 3–4; #1251; a knowledge notion since #1259–#1261) | the spine | the framework decision (decision 24) | it has round-by-round knowledge soundness and its composition at the pin |
| ArkLib #1263, #1264 (merged after the pin) | the random-oracle theorems | state-restoration knowledge soundness from local round-by-round certificates, in the typed framework | reference only (decision 36) |
| ArkLib #1245 | none | the round-by-round-to-plain corollary, which no theorem here uses | reference only |
| ArkLib #1244, #1128, #1129 | the sumchecks | the classical leaf's repair (the verifier evaluates the sent polynomial; its knowledge soundness stays admitted); honest round identities over one `MvPolynomial` | reference only |
| ArkLib #1261, #1269, #1274, #1277 | the sumchecks | the typed sumcheck's round-by-round soundness and state-restoration security, for one polynomial with unit weights and no witness | when the typed framework proves round-by-round knowledge soundness (decision 24) |
| ArkLib's computable sumcheck (#1214, #1242, #1243; at the pin) | the sumchecks; the GKR's rounds | the round of `ToArkLib/SumcheckRound.lean`, which sends the coefficients as one message and weights the domain | an adaptor to `OracleReduction` and a weighted domain exist (decision 33) |
| ArkLib #818, #383, #992 | the GKR; WHIR | patterns for a layer and for a proximity test as reductions | never as they are |
| ArkLib #1256, #1257 (and #615) | the Flock phase | the packing coordinates, observations and batching of Diamond–Posen ring switching, and the Flock paper's quirky layout | never as they are: leanVM's ring switching is the Frobenius-map variant (Annex A), whose soundness needs none of them; `ToArkLib/Flock/` is the candidate instead |
| ArkLib's appended-schedule instances (`ProtocolSpec.instSampleableTypeChallengeAppend`, the `Inhabited` and `OracleInterface` instances, `OracleReduction/Composition/Sequential/SeqCompose.lean:448-483` at the pin; upstream `main` unchanged on 2026-10-23) | every phase run through `Prover.run` | `ToArkLib/AppendLazy.lean`: the instances are `Fin.fappend₂`, whose strict compiled code reads entry `i` at right length `n` in about `C(n + i, i)` reads of the level below, exponential in the depth of a schedule appended on the right (261 s for 9 trivial sumcheck rounds); `Fin.dappend` and `Fin.happend` have the same shape | ArkLib redefines the instances by a comparison at the seam; then delete `AppendLazy.lean` |
| ArkLib #848, #469, #627 | the compiled verifier | Fiat–Shamir and BCS statements | a chain-based transform with proof of work, which none of them is |
| ArkLib issues #900, #901 | tables and stacking; the fingerprint | the requests for stacking and fingerprints upstream | when the pull requests open |
| VCVio #571 | Merkle binding by log replay | `ToVCVio/MerkleLog.lean` | VCVio proves extraction with hashed leaves on one shared oracle |
| VCVio #817 | the charged invariant | the laws of the scalar expectation, copied verbatim as `ToVCVio/ScalarExpectation.lean` | at the bump that contains it, delete the copy |
| VCVio #823, #824, #826, #828 | the charged invariant | fresh-query bounds with a fixed error per key | reference only: the flip charge depends on the cache |
| Clean #466 (merged 2026-10-05), #474 | Clean expressions as polynomials | `ToClean/ExpressionPolynomial.lean`, a verbatim copy of Clean's module | a pin holds both #466 and #474's Lean 4.34 fix; then delete the copy and import `Clean.Circuit.ExpressionPolynomial` |
| Clean #464, #20 | the adaptor | leanISA's `BalancedPair` | merged and the pin bumped |
| Clean #446, #23 | the adaptor | the three fixed-column conjuncts | merged and the pin bumped |
| CompPoly (issue to open: word arithmetic for `BF64`, degree-three `Ext`) | none: compiled speed of `K` and `E` everywhere | `Parameters/ToCompPoly/BF64Fast.lean`, `Parameters/ToCompPoly/ExtensionFast.lean`. Upstream would attach the `@[csimp]` theorems to `BF64.mul` and `Ext.mul` (or store a `BF64` as a `UInt64`), so the instance-level substitutions here become unnecessary: the candidate is the algorithms and their proofs | CompPoly merges them; then delete both modules and their imports in `Parameters/Field.lean` |

One check is owed at the current pins and has not been made: whether Clean `42fe4b26` contains
any of Clean #446. Whether `ReedSolomon.mcaError_affineLine_johnson_le` meets Annex B's per-level
budget was checked on 2026-10-19: it does, with Annex B's own constant, at every deployed level
(least margin 128.19 bits), so the admitted `rs_mcaError_le_in_johnson_range` is not needed
([whir-mca-budget.md](../reviews/whir-mca-budget.md)).

The survey log kept here until 2026-09-29 is archived in
[protocol-survey-record.md](../reviews/protocol-survey-record.md); the library limits it recorded
are in [dependencies.md](../dependencies.md#limits-that-bind-the-proof-system), the Lean pitfalls
in [tests/README.md](../../tests/README.md), the findings against the sources in
[leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin), and the decisions in the
blueprint.
