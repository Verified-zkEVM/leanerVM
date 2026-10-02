# Status: the leanVM proof system on ArkLib

Where the [protocol blueprint](protocol-blueprint.md) stands on `main` at `3cf0139` (2026-10-02),
checked on 2026-10-02; a row marked *on merge* lands with its pull request. This file says what is
built and what the built work still owes the blueprint. What is wanted is the blueprint's; who is
taking which hole is issue [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12)'s;
discrepancies in the leanVM sources are in
[leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin). Open pull requests are not
part of `main`.

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
| grand-product GKR: definition and completeness (Layer 5) | #62 | on merge | on merge |

The two master theorems are proved over an abstract instance and are conditional on the five
phases after the commitment; of those, the public-input phase is built. `#print axioms` gives the
kernel's three axioms, and no `sorryAx`, for the two master theorems and both halves of the commit
and public-input phases. The grand-product GKR's definition and completeness are built
(`LeanerVM/Protocol/ToArkLib/GrandProduct.lean`: `gkr` at the slot's schedule `gkrSpec`,
`gkrComplete`), on two generic one-round components, a checked message
(`ToArkLib/SendChecked.lean`) and a checked challenge (`ToArkLib/SampleChallenge.lean`), a
sumcheck round of their own composed from the two (`ToArkLib/SumcheckRound.lean`), and the
product tree and partial sums (`ToCompPoly/ProductTree.lean`, `ToCompPoly/PartialSum.lean`).
Nothing else is built: the other phases, the other generic components, the Clean bridge, the
adaptor, WHIR, the Merkle trees, the compiled verifier and the base theorems.

## What the built work owes the blueprint

The blueprint was revised on 2026-09-30 after a review of its faithfulness to leanVM, its
non-vacuity and its audit surface. The work on `main` predates the revision and owes it the
following; each item is a checklist line of #12.

- **Field instances (Layer 0).** The stack's oracle becomes the inner product
  (`innerProductOracle`: query `Weight n`, answer `W.pair q`), with `Weight`, `Weight.pair` and
  `eqWeight` moved below `Field.lean` and `answer_eqWeight` in place of `evalOracle_answer`; the
  consumers restated with `eval₂Mle` (`FixedColumns.lean`, the tests of `Field.lean` and
  `FixedColumns.lean`). The `K` sampler's docstring says it is only the building block of the
  `E` sampler; the module docstring loses its roadmap references; the test comments name the
  column `[1, x, x + 1, x^2]` by its `K.ofBits` words.
- **The spine.** `err` leaves `Component.Def`; `Component.Guarded` (the guarded form; `outputPure`
  goes, derived from ArkLib's `Prover.instOutputIsPureEmpty`) is extended by `Complete` and
  `Security`, and `Security.append` builds no completeness. The five slots get their schedules
  and closed-form errors (`busSpec` … `openingSpec`, `busError` … `openingError`, `piopError I`,
  `piopError_le`), and `Phases.Security` is at them. `BusOut` takes the shape of the Rust's
  `BusVerify` (`RowPoly`, `Form`, point, forms, totals, columns) and `Seam.bus` follows;
  `LinearClaim`, `VirtualTerm` and the degree conjunct go. `M3Instance` gains the sumcheck-table
  predicate with `τmax`, `μBus`, `B`, and `flock : Option FlockRegion`, from which `aux` is
  defined. `Layout` keeps `extend` and one law, `read` becoming a definition. New:
  `piopExtractedStack` with `piopExtractedStack_eq`, `Refinement.knowledge_transport`, and the
  front phases' oracle-freeness (decision 31). `PassThrough.lean`'s header names ArkLib's
  `ReduceClaim.oracleReduction`; `ToVCVio/UniformSample.lean`'s counting bound gives way to VCVio's
  `SampleableType.prEvent_uniformSample_le_div_iff`, keeping the subsingleton form.
- **Tables and stacking (Layer 1).** The strided reader: `sliceLow`, `evalMle_boolVec_append`,
  `Blocks.stridedLayout`, `Layout.piecewise`, tested against the Python's
  `Placement.stack_point`. `BlockClaims.lean` and its test are deleted (no consumer), and so are
  `bytecodeColumn_slot` and its examples, replaced by the sixteen-instruction `#guard` against the
  Rust encoder. `prodVars` and its two lemmas, `unstack_eval`, `stack_eval_ambient_zero`,
  `stackColumn_eval`, `stackColumn_eval_ambient`, `slice_bytecodeColumn` and
  `evalMle_lagrangeBasis` (CompPoly has `eqTilde_eq_prod`) become private or go;
  `bytecodeSlotColumn` stays if the adaptor's boundary blocks use it.
- **The public-input phase (Layer 8).** The pool reads the values sent (`pooledFrom`, in the
  verifier, the prover's output, the guard and the state function), which makes the check
  load-bearing: today a verifier that ignores the message has the same theorems. The refutations
  of the check removed, weakened, swapped and doubled join the tests, with the generic
  `not_rbr` and `not_perfectCompleteness` in `ToArkLib/`. The deployed check is a new hole.
- **The grand-product GKR (Layer 5)** is at the spine's slot shape: `gkr` carries no error and
  is typed at the schedule `gkrSpec F nside μ` of `ToArkLib/Schedule.lean`, whose design it
  owns, and `gkrComplete` extends `Component.Guarded`; its knowledge soundness is to be stated
  at `gkrError F u nside μ`. Two of its parts are local stand-ins for Layer 4's components: its
  sumcheck rounds, `SumcheckRound.round` on `SumcheckRound.normalizedWeights`, for
  `Sumcheck.normalized`; its combiner, `Gkr.lambdaStep`, for `batch nside`. When those holes
  land, the parts become them, and `ToArkLib/SumcheckRound.lean` merges into the sumcheck's
  module or goes. The refutations of its two checks, the round check and the descendants'
  check, come with its knowledge soundness, which they refute. Where it differs from Layer 5's
  sketch: the riders are an argument of the relations (`Gkr.relIn`, `Gkr.relOut`) and of
  `gkrComplete`, not of `gkr`, which never reads them; a rider's variable count is a
  `Fin (μ + 1)`, so that its low point exists; a round message is the polynomial's coefficients,
  not a polynomial with a degree bound, so the degree bound is the message's length.
- **The wall.** `LeanerVM/Protocol/Basic.lean`, an empty module, imports the arithmetization: it
  goes (with its line in `LeanerVM.lean`) or drops the import. The rule goes into
  `scripts/check-layers.sh` with the blueprint's allow-list, and a planted violation into
  `scripts/test-policy-checks.py`.

Open pull requests that the revision changes: #42 (honest sumcheck algebra) serves the plain
variant, and conflicts with `main`; #39 (fingerprints) and #43 (power batching) rebase onto `main`
from the closed #18's branch and move from `Generic/` to the `To*` folder of their objects, #43
feeding the opening phase.

## What can start now

The spine's revision first: every phase is written against its slots. Independent of it: the
revisions of Layers 0 and 1, the wall's rule, Clean expressions as polynomials (Layer 2), the
sumcheck variants and batching (Layer 4), the fingerprint (Layer 5), the GKR's knowledge
soundness on its local round (Layer 5), the WHIR opening,
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
