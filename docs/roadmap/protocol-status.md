# Status: the leanVM proof system on ArkLib

Where the [protocol blueprint](protocol-blueprint.md) stands on `main` at `32dbe65` (2026-09-30),
checked on 2026-09-30. This file says what is built and what the built work still owes the
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

The two master theorems are proved over an abstract instance and are conditional on the five
phases after the commitment; of those, the public-input phase is built. `#print axioms` gives the
kernel's three axioms, and no `sorryAx`, for the two master theorems and both halves of the commit
and public-input phases. Nothing else is built: the other phases, the generic components, the
Clean bridge, the adaptor, WHIR, the Merkle trees, the compiled verifier and the base theorems.

## What the built work owes the blueprint

The blueprint was revised on 2026-09-30 after a review of its faithfulness to leanVM, its
non-vacuity and its audit surface. The revisions the work on `main` owed it are built and in
review as three stacked pull requests, #64 (the wall and the field instances), #65 (the spine)
and #66 (tables and stacking, the public-input phase); each is a checklist line of #12. Where
the built work differs from the blueprint, deliberately:

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
- **Instances of appended schedules are applied by name** (`msgAppend`, `chalAppend` in
  `Spine/Errors.lean`): instance search does not find ArkLib's instances for the messages and
  challenges of two schedules side by side when the schedules are concrete, and ArkLib's own
  files apply them by name too.
- **The front phases are typed** (decision 31): `Phases` holds them as `Phase.FrontDef`, whose
  verifier is a `FrontVerifier` with no access to the stack, and their proofs are stated on the
  lifted component `FrontDef.toDef`.
- **`piopError_le`** takes the sizes as hypotheses (`μ_bus ≤ 30`, `τ_max ≤ 32`, `B ≤ 2^16`,
  `kBatch ≤ 32`, `J ≤ 2^16`) and bounds the sum by `(2^32 + 2^31 + 2^20)/|E|`; the numeric
  test shows it below `2^{-159}`. That the leanISA instance meets the hypotheses at admissible
  sizes is the adaptor's to prove.
- **The refutation lemmas** are `Verifier.not_rbr`, `Verifier.not_rbr_zero` and
  `Reduction.not_perfectCompleteness_of_reject` (with a primed form for the empty shared
  oracle), in `ToArkLib/Refutation.lean`.
- **`Component.Extraction`** sits between `Guarded` and `Security`: the extractor and its
  state function without the bound, so that `piopExtractor` computes while the errors, real
  numbers, make `Security.append` noncomputable. `piopExtractedStack_eq` goes through
  `Extractor.RoundByRound.ReadsFirst`: an extractor whose first step reads the first message
  returns it on every transcript, and a sequence of extractors keeps its first part's first
  step.
- **Layer 1's pruning.** `unstack_eval` and `bytecodeColumn_slot` are private;
  `stackColumn_eval`, `stackColumn_eval_ambient`, `stack_eval_ambient_zero`,
  `evalMle_lagrangeBasis`, `slice_bytecodeColumn`, `prodVars` and its two lemmas are gone, with
  `BlockClaims.lean` and its test; `bytecodeSlotColumn` stays for the adaptor's boundary blocks.
- **Layer 8's verifier** is `verifierWith` at the check and the pool from the values sent, a
  shape the refutation tests instantiate with the check removed, weakened to its first value,
  the unsent line's claim dropped, the cells swapped and an extra check.
- **The deployed public-input check** is a hole of its own, not built.

Open pull requests that the revision changes: #62 (the GKR's definition) has the normalized round
and the leaves as functions of the context, and gains the riders, the last unused combiner and
the spine's slot shape (`gkrSpec 3 μ` and `gkrError 3 μ` of `Spine/Errors.lean`, whose grouping
per layer is combiner, rounds, descendants, combination challenges); #42 (honest sumcheck
algebra) serves the plain variant, and conflicts with `main`; #39 (fingerprints) and #43 (power
batching) rebase onto `main` from the closed #18's branch and move from `Generic/` to the `To*`
folder of their objects, #43 feeding the opening phase.

## What can start now

The spine's revision first: every phase is written against its slots. Independent of it: the
revisions of Layers 0 and 1, the wall's rule, Clean expressions as polynomials (Layer 2), the
sumcheck variants and batching (Layer 4), the fingerprint and the GKR (Layer 5), the WHIR opening,
and the Merkle trees with the WHIR parameters (Layer 11). The public-input phase's deployed check
follows its pool's revision.

## Upstream watch

External work that may feed or replace a hole. The state of each is on GitHub.

| Upstream | Hole | What it would replace or feed | Adopt when |
| --- | --- | --- | --- |
| ArkLib #615 | the knowledge-soundness composition | the port `ToArkLib/KnowledgeAppend.lean` | some ArkLib framework proves a guarded-first append for the named form |
| ArkLib's typed framework (its roadmap items 3–4; #1251) | the spine | the framework decision (decision 24) | it has round-by-round knowledge soundness and its composition |
| ArkLib #1245 | the list-binding compilation | the local stateless round-by-round-to-plain corollary | merged, for its soundness half |
| ArkLib #1244, #1128, #1129 | the sumchecks | the classical leaf's repair; honest round identities | reference only |
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
