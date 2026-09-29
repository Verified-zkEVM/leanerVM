## Status: complete (2026-09-26)

Every applicable target, R1–R12 (applications A1–A3, P13, P14 and concrete proof-size certificates excluded), is on `main`. The last port slice was #1217. Main is at `40c6adef1` (#1220), and main CI on #1217 passed.

- **Source coverage:** of the source modules in scope, 361 (83,800 lines) were ported, some under new names or split across general owners. Another 138 (39,646 lines) were already on `main`. `tools/rs-port plan` reports 0 lines not yet on `main` for every target.
- **Ledger and correspondence:** `docs/design/reed-solomon-port.md` has one row per landed slice (deduplicated in #1219), and `docs/design/reed-solomon-port-correspondence.md` maps source names to library names. Those two files, not the tables below, are the record of what landed where.
- **Cleanups after the last slice:**
  - #1219 deduplicated the ledger rows and removed a stale `[DKTZ26]` note; `references.bib` has both `DKT26` and `DKTZ26`.
  - #1220 renamed `ReedSolomon.agreementThreshold` to `capacityAgreementThreshold` so it no longer collides with `ReedSolomon.HiddenDerivative.agreementThreshold`. It also removed four redundant theorems.
  - #1221 derives the pair and Frobenius graph-line recognition theorems from their power-batched counterparts.
- **Proof-checking speedups:** #1076, #1077, #1079, #1200, #1202, #1203, #1207, #1209, #1210 and #1211.
- **Merge policy:** the 2026-09-21 policy below was superseded on 2026-09-22. Port PRs then merged once CI was green.

Nothing in this issue is still open. The sections below are the historical handoff and plan, kept for reference; their "current state" and "next" wording describes 2026-09-22.

# Port-owner handoff

## Mission and authority

Own the port of the Reed–Solomon beyond-Johnson formalization into ArkLib end to end. Maintain the mathematical correspondence, choose and revise the library architecture, implement small dependency-coherent PRs, arrange independent review, repair findings and CI, land accepted work, and keep this issue and the repository ledger current. Continue dependency-ready work while other PRs build. Do not repeatedly stop for routine implementation, branch, review, or publication decisions.

**Merge policy (updated 2026-09-21 by Quang):** the port owner opens, revises, validates and keeps PRs green autonomously, but **does not merge any PR until Quang explicitly says to merge it**. Stacked follow-on work proceeds on unmerged parent branches instead of waiting for merges. When Quang authorizes a merge, merge with the exact expected head (`--match-head-commit`) and verify the MERGED state; an admin override may bypass only the approval requirement, never a failed or unrun mathematical, trust, or integration gate. Do not change repository protections or merge unrelated PRs. No upstreaming to Mathlib or CSLib is required; reusable results can land in ArkLib. Ask Quang about a genuinely substantive scope/mathematical decision or unavailable external dependency, not routine maintenance.

Use bounded **Sol high** implementation subagents for independent packages, each with an isolated worktree, explicit ownership, a concrete deliverable, and acceptance checks. The coordinator owns integration and the final review; authors do not approve their own work. Parallelize development and review rather than sharing writable Lake build directories. Do not manufacture extra tasks or tests to fill worker slots.

## Non-negotiable architecture objective

Organize mathematics by its actual dependencies, not by where it happened to live in the paper branch. Identify the **most general useful theorem**, place its proof and documented public API in the canonical owner, expose the useful arbitrary-code interface where applicable, and let Reed–Solomon supply only genuinely polynomial-specific hypotheses. A generic helper hidden underneath an unnecessarily RS-specific public theorem is insufficient.

Typical direction: generic sets/predicates/embeddings or algebra → arbitrary-code theorem → RS specialization. Do not introduce algebra/code assumptions into pure enumeration, polynomial imports into ordinary matrix theory, or RS imports into generic Johnson bounds. Search exact pinned dependencies and existing ArkLib representations first. Generality must preserve meaningful guarantees and constants, not assume the desired result through a vacuous certificate or create speculative framework layers.

The #908–#910 revisions are the concrete standard: predicate filtering belongs to Finset; sample-incidence finiteness follows from uniqueness of samples rather than construction of interpolants; the exact integer Johnson bound applies to arbitrary alphabets and possibly infinite codes and reaches the existing list-decoding API. See the required objective and acceptance contract below for the full review checklist.

## Sources and public continuity

- Canonical plan and live status: this issue, including R1–R12, A1–A3, P1–P14, intermediate results, warning signs, and decoder obligations below.
- Version-controlled source/owner ledger: [docs/design/reed-solomon-port.md](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/design/reed-solomon-port.md). It inventories T1–T6 and later slices. Extend it for every new slice, recording exact declarations, semantic generalizations and deferred scope. Keep volatile CI/merge status in this issue.
- Paper/artifact pin: [`quangvdao/rs-beyond-johnson@60b725780efd1265fec241ddc7197423daf52717`](https://github.com/quangvdao/rs-beyond-johnson/tree/60b725780efd1265fec241ddc7197423daf52717), including `scripts/lean-statements/sources.json`.
- Mathematical source: [`quangvdao/ArkLib@a5aa2677fee4e3a79d6bb05136631cce4a08587d`](https://github.com/quangvdao/ArkLib/tree/a5aa2677fee4e3a79d6bb05136631cce4a08587d). Start with `docs/reed-solomon-results.md` and `ArkLib/Data/CodingTheory/ReedSolomon/PaperGuide.lean`. A source pin is correspondence evidence, not the target's dependency environment.
- Decoder source is separate: [`ffab000e71c5b19e8a19bebadcc0050eac1366e3`](https://github.com/quangvdao/ArkLib/tree/ffab000e71c5b19e8a19bebadcc0050eac1366e3). It is not a completed verified fast decoder. Preserve missing execution, backend, coverage, and cost obligations.
- T2/#877 and T6/#875 have separate immutable donors, recorded in the ledger. Do not falsely attribute their named theorem families to `a5aa2677`.

No collaborator needs a local-only artifact to continue: source commits, PR diffs, the plan, and CI are public. Do not publish unrelated private manuscripts or uncommitted material.

## Completed foundation-batch design record

The two scopes below were the design contract for #923 and #924 and are now implemented, reviewed, and locally validated. Keep them as correspondence and review records, not as the next implementation queue. The live queue and exact continuation steps are in the clean stop checkpoint above. Do not recreate #919–#925; use their repository ledger entries and exact PR diffs. Continue to use isolated worktrees, private writable dependency artifacts, independent review, and coordinator-owned integration for the remaining packages.

### P1 next — differential-polynomial core

Start from #921's ordinary partial-derivative/iterate and weighted-degree APIs. Proposed owners: `Data/Polynomial/Differential/{Types,Basic,JetDegree}.lean`. Port the usable core from source `Diff/{Types,Basic}.lean`: `JetVariable`, `DifferentialPolynomial`, specialization hom/evaluation, `jetEvaluation`, `polynomialJet`, `jetDegree`, `separant`, `differentialWeight`, and `differentialWeightedDegree`, with generator/evaluation and boundary-weight equations. Add the specialization-degree result from `SpecializationDegree.lean` and `jetTotalDegree`, its characterization, `jetDegree_le_total`, and `separant_total_le` from `TotalJetDegreeRootCount.lean` at this owner, rather than under root counting.

`jetTotalDegree` can be stated over a commutative semiring. Bridge it to P3's exponent-level `totalJetDegree`; do not introduce a second `jetWeight` representation. Preserve useful equation lemmas if a specialization hom changes definitional reduction. Defer local Taylor/contact/multiplicity/descent. Ordinary derivatives need characteristic guards; Hasse contact/substitution does not. Zero jet weights are valid for specialization bounds, but finite-dimensional spaces need separate coordinate caps. Reassess P3's characteristic-certificate field: the source specialization proof does not use it, so a guard-free interface may be appropriate.

Acceptance: ordinary-import clients should apply the source specialization and jet-degree shapes, include characteristic-zero and positive-characteristic boundaries where relevant, and exercise zero jet weights without asserting false finiteness. Expose intermediate degree lemmas as documented public results. Do not claim the root-counting theorem is ported by this core.

### P5 next — finite quotients and zero-locus cardinality

Build on #922's finite/retained minimal primes and arbitrary-extension point covers, and #919's agreement deletion bounds. Extract the independent finite-quotient and `ncard`-versus-`finrank` results from source `ZeroLocus/ZeroDimensional.lean`, choosing a generic quotient/algebra owner before adding geometry adapters. Search pinned Mathlib for equivalent APIs first. The concrete source family is `zeroLocusPointHom`, its injectivity, `finite_zeroLocus_of_finite_quotient`, and `ncard_zeroLocus_le_finrank_quotient`. Establish finiteness before interpreting `ncard`, and count `F`-algebra homomorphisms from the actual `F`-coordinate quotient into the extension field `E`, bounded by the quotient’s `F`-finrank. This is a Hilbert-foundation slice; defer the source `finite_zeroLocus_and_ncard_le_of_krullDimLE_zero` wrapper unless an actual consumer justifies it. That wrapper needs finite variables for the module-finiteness implication.

Keep the distinction between algebraic components and field-valued points: a retained minimal prime need not have any points over the chosen field. Algebraic closure is unnecessary for the point covers already in #922, but is needed where a later converse infers dimension zero from finitely many rational points. Preserve properness when extracting a dimension from a Hilbert polynomial; `natDegree 0 = 0` is not a dimension certificate. Principal-cut dimension drop and the full sharp incidence ratio remain separate slices.

Acceptance: derive the source finite-quotient cardinality contract through the generic API, test the zero/trivial quotient boundary, and exhibit the hypotheses required for any dimension interpretation. Do not carry geometry assumptions into a purely finite-dimensional algebra result.

### Other dependency-ready continuations

- **P2:** #920 supplies shifted and column budgets, including primitive forms. Move on to symbolic-interpolation consumers using those APIs; do not copy `ShiftedDegreeKernel` or `ColumnDegreeKernel` again. A rank-only shifted statement needs justification because row weights depend on the selected rows. Preserve truncated slot counts and forced-zero entries.
- **P4:** after #915, port total-degree estimates, fraction-field nonvanishing bridges, and actual regularity/root-presentation consumers. Respect degree drop and the nonzero combined-degree guard.
- **P9:** after #917, consider exact-simplex/Finsupp bridges and shell counts, then continuous volumes, floor-cell transfers, moments, and parameter consumers. Discrete simplex counting does not prove those later estimates.
- **P12a:** after #918, port scalar exceptional-set counting and exact-agreement transfers, then concrete providers. The common row-functional argument and generic MCA transfer do not complete the source cardinality theorems or R11/R12. Keep the tensor-tight theorem separate.

### Review lessons from this batch

1. Compare exact declarations and conclusions, not similar names. Source `powerProjectionBadArbitrary` is a predicate; its counting proof is `interleaved_powerProjectionBadArbitrary_finset_card_le`. Extracting a common proof step does not port the full theorem.
2. Generalize assumptions and imports together. #918 removes incidental RS imports; #921 exposes nonzero degree-cast assumptions rather than excluding characteristic zero with a blanket strict characteristic bound.
3. Publish useful intermediate results. #917 exposes sharp binomial estimates; #920 retains a useful primitive `degreeLT` theorem consumed by its generalization. Avoid both hiding reusable facts and retaining unused wrappers merely because the source had them.
4. Test meaningful failure boundaries: #919 needs `k ≤ A` for its weaker bound; #921 needs nonzero input for order-zero nonvanishing and suitable coefficient hypotheses; zero weights do not imply finite-dimensionality.
5. Read docstrings as mathematical claims. #922's formal point-cover theorem was correct, but prose suggesting every retained component had field-valued points was too strong and was corrected.
6. Tie review and validation to exact heads and inspect the combined result. Summary-only CI on a conflicting/stacked PR is not a substantive build. Keep original source credits, final owner mappings, and deliberately deferred conclusions visible.

## Review, validation, and revision protocol

For each slice record source declarations, generalized exported types, canonical owner, dependencies, consumer/specialization, and intentionally deferred scope. Independently inspect assumptions, quantifier order, constants, edge cases, imports, public usability, and proof structure. Main theorem families and useful intermediate results need dedicated discoverable modules with comprehensive reader-facing docstrings and spaced annotations explaining substantive hypotheses and conclusions.

Read current `AGENTS.md`, `CONTRIBUTING.md`, validation scripts and workflow triggers. Run full `./scripts/validate.sh --axioms` before commit/push; stage new paths and regenerate the umbrella. Follow applicable documentation/site checks. Use meaningful ordinary-import acceptance clients, not a test quota. Audit principal axiom cones and transitive assumptions, not merely new `sorry` tokens or the baseline exit code. No new admissions, axioms/native trust, suppression switches, or baseline expansion hiding debt. Keep examples/nondefault libraries within explicit validation coverage.

All-eight combined local validation passed on tree `845cb8898df3cad0737002273304b80553f1f88a`: 12,773 declarations/518 modules, unchanged 291 baseline sorry-tainted declarations, zero nonstandard taint; lexical trust audit found no new admissions/native trust. Independent review verified each substantive blob against its owner PR. This is historical evidence, not permission to skip checks after a future change. Exact dependencies at this checkpoint: Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; CompPoly `7e3683ba72f61c1f3c2deda85953ce26392f0771`; VCVio `7a4d7ee254165f2fcf3282c7d2e6f204056e5121`.

CI automatically runs for main-targeting PRs; a stacked PR can display only a successful summary job. Explicitly dispatch substantive workflows at the exact head when necessary, then verify main/queue integration after retargeting. After squash merges, recompute unique diffs and dependency ancestry. Preserve source/author credits and record revised names and owner moves. Revise the plan when evidence supports a better abstraction; obtain independent review of the new boundary before dependents rely on it.

## Completion and communication

Keep several genuinely independent packages moving without duplicating builds. Report concrete progress, findings, exact blockers, and the next action. Do not repeat stale migration/approval blockers or imply an idle agent is monitoring CI. A stopped handoff leaves pending actions explicit.

Completion of a PR is not completion of P2/P12a, the mathematical paper, or the decoder. Track the R1–R12/A1–A3 contracts and the separate decoder gaps to their actual destination theorems. The decoder's 100-based recipe and current mathematical 300-based recipe are distinct until a proved bridge exists; a finite-list existence theorem or conditional backend does not certify a fast implementation or complexity. Close this issue only under the completion conditions below, with explicit accepted follow-ups for any deferred scope.

---

# Detailed plan and historical evidence

The handoff above is the current operational status. Earlier status checkpoints below are historical; preserve their source evidence without treating old open/blocked states as current.

## Required port objective: general results first, Reed–Solomon as a specialization

The port should turn the paper formalization into a reusable mathematical library organized by actual mathematical dependencies. For every result family, identify the most general useful statement supported by the argument, prove it in its canonical owner, and derive Reed–Solomon results by supplying the genuinely polynomial-specific hypotheses. Preserving the source statement is a correspondence obligation; preserving its specialization, namespace, proof organization, or directory is not an architectural goal.

This is a merge requirement for every package, including already published PRs. A compiling literal extraction or a generic private helper does not satisfy it when the usable public theorem remains unnecessarily tied to Reed–Solomon.

### Required design and review procedure

1. **Identify the mathematical core before choosing the owner.** Audit which assumptions the argument actually needs: arbitrary types, predicates and embeddings; finite set families; arbitrary codes and agreement/distance; algebraic structures; or specifically polynomial evaluation. Remove incidental field, finiteness, coordinate, representation, and RS assumptions when the guarantee survives. Preserve substantive hypotheses, quantifier order, constants, endpoint behavior, and finiteness guarantees.
2. **Search existing APIs at the actual dependency pins.** Extend canonical representations and theorem families instead of introducing parallel decoder, code, agreement, distance, or cardinality APIs. Document whether an existing theorem already supplies the result, needs a bridge, or is weaker/different.
3. **Expose both the reusable core and useful consumer interfaces.** Where applicable, use the dependency direction `generic mathematics → arbitrary-code theorem → RS specialization`. Pure filtering/enumeration results should not require coding theory; generic counting should not require polynomials. A raw finite-set inequality alone is insufficient when other codes need the same list-decoding bridge. Use existing `Code.agree`, list sets, `Lambda`, and `IsListDecodable` interfaces where appropriate.
4. **Make reusable results discoverable.** Give meaningful intermediate theorem families canonical files, mathematical names, comprehensive reader-facing module/declaration documentation, and a clear proof outline. RS specializations should invoke these results and prove only the additional RS facts. Do not maintain a second specialized copy of the generic proof.
5. **Justify the abstraction boundary.** Generality should expose a meaningful mathematical contract, not replace the desired conclusion with an assumed certificate or introduce speculative frameworks, redundant bundles, or layers with no purpose. A concrete self-contained generic theorem is sufficient justification; a second application is useful evidence, not a quota. Do not strengthen assumptions or weaken bounds merely to make an abstraction convenient.
6. **Review independently before acceptance.** Record the source statement, generalized statement, remaining RS hypotheses, canonical owners/import direction, and specialization proof. Check ordinary-import usability and the relevant edge cases, including infinite alphabets/candidate sets and empty/oversized thresholds. If a useful generalization is missed, revise the package and affected dependents before landing; historical green builds or earlier reviews do not waive this requirement.

### Concrete repairs establishing this standard

| Package | Required reusable result | RS specialization / acceptance boundary |
|---|---|---|
| T3 / #908 | Exact finite-output specifications and candidate filtering for arbitrary input/message/ambient types, embeddings, and acceptance predicates; preserve completeness and output-size bounds. Reuse existing owners where available. | Degree-bounded polynomials, degree-space inclusion, and evaluation agreement instantiate the general interface. The filtering proof itself has no semiring, field, or RS dependency. |
| T4 / #909 | Finite-set-family sample-incidence theorem: each candidate has at least `A` positions, each `k`-sample belongs to at most one candidate, and `k ≤ A`; conclude candidate finiteness and `L * choose A k ≤ choose n k`. Expose an arbitrary-code agreement specialization. | Polynomial uniqueness supplies sample identification. The existential finite-list/counting result should not require constructing Lagrange interpolants. Any separately retained interpolation construction needs an explicit distinct purpose. |
| T5 / #910 | Generic pairwise-intersection counting plus an arbitrary-code exact integral Johnson list bound, explicit list finiteness, and appropriate bridges to the established list-decoding API. | Polynomial uniqueness supplies the pairwise-agreement bound. The numerical bound and general coding theorem belong outside the RS namespace; RS is a thin corollary. |

**Historical requirement (subsequently fulfilled before merge):** #908, #909, and #910 required these architecture revisions and renewed independent review/validation. Earlier extraction reviews and green checks describe their earlier implementations, not acceptance under this clarified requirement. Recompute the stack after generalization: the generic Johnson theorem should not depend on RS incidence merely because the original PR stack did.

Apply this same investigation to all subsequent algebra, kernel, interpolation, geometry, root-counting, transfer, and decoder packages. Update the source-to-destination ledger with the general theorem and its RS specialization, including any revised package dependencies. This objective is part of completion, not optional cleanup after the paper theorems land.

## Historical assignments after the Lean 4.34 merge

#903 merged as `fa14552d40e793f2ea26e65c440306aae0c08a26`. Its tree matches the reviewed prospective migration base. The migration is no longer a blocker; older preflight/status entries below are historical and are being superseded by final-head validation.

At that earlier checkpoint, three Sol high implementation workers were assigned isolated worktrees:

- **First tranche:** refresh the six existing PRs against Lean 4.34 main and revise #908–#910 under the required generalization objective above. Reassess their stack from the resulting generic dependencies; architecture revisions need fresh review and validation.
- **P2, first bounded slice:** extract canonical actual-row basis selection and a coherent first polynomial-kernel degree-height result. Confirm exact dependencies before finalizing the slice; do not pull the whole kernel hierarchy into one PR.
- **P12a, first bounded slice:** extract generic finite-subspace avoidance, preserving its sharp field-cardinality bound. Search current dependencies first and avoid duplicating an existing theorem. Interleaving endpoints are outside this slice.

The coordinating agent reviews source correspondence, ownership, statements, and final diffs independently of each implementer. New packages require the acceptance gates below before publication/landing. These assignments do not mark all of P2 or P12a complete.

## Outcome and scope

Port the formalization accompanying **Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs** into ArkLib through small, independently reviewable PRs. Improve the library architecture during the port: reusable intermediate theorems should have canonical owners, discoverable names, and mathematical documentation. A successful build alone does not meet the acceptance bar.

This issue coordinates the paper port. #854 remains the historical BCPZZ26 low-rate project; do not silently replace its mathematical scope. #855 is closed as an obsolete statement scaffold; #908 proposes its proved reusable exact-list specification. The historical low-rate headline remains in #854. #857, #875, and #877 retain useful mathematics. #906 supplies the canonical agreement interfaces and is merged as `68726031f01e0b79759dce718fce77ac81fb317a`; reuse those definitions. #905 is a separate binary-field development, not a mandatory dependency of this port.

**Historical first-tranche assignment (completed):** a persistent Sol high implementation worker owned the six first-tranche units below. The coordinating agent owns integration and this ledger; independent Astra low reviewers audit architecture, source correspondence, and the plan. A worker does not approve its own changes. This assignment is coordination, not a claim of completion or merge authorization.

### Authoritative sources

- [Paper/artifact snapshot `60b725780efd1265fec241ddc7197423daf52717`](https://github.com/quangvdao/rs-beyond-johnson/tree/60b725780efd1265fec241ddc7197423daf52717), including its [literal statement manifest](https://github.com/quangvdao/rs-beyond-johnson/blob/60b725780efd1265fec241ddc7197423daf52717/scripts/lean-statements/sources.json). The published PDF SHA-256 is `b67c188ec477b6063caf9c1c06b214c71e358ff09b9517adcdb1db212ea2700a`. A manuscript revision requires an explicit scope/correspondence update.
- **Mathematical source:** [`a5aa2677fee4e3a79d6bb05136631cce4a08587d`](https://github.com/quangvdao/ArkLib/tree/a5aa2677fee4e3a79d6bb05136631cce4a08587d). Start with its [reader guide and result inventory](https://github.com/quangvdao/ArkLib/blob/a5aa2677fee4e3a79d6bb05136631cce4a08587d/docs/reed-solomon-results.md) and [mathematical entrypoint](https://github.com/quangvdao/ArkLib/blob/a5aa2677fee4e3a79d6bb05136631cce4a08587d/ArkLib/Data/CodingTheory/ReedSolomon/PaperGuide.lean).
- **Independent generic implementation donors:** T2 preserves [#877 at `8b1698ab6f73d89bcc36b7936a8ce87cd20bc9d4`](https://github.com/Verified-zkEVM/ArkLib/blob/8b1698ab6f73d89bcc36b7936a8ce87cd20bc9d4/ArkLib/Data/Polynomial/FractionFieldResultant.lean); T6 preserves [#875 at `0ffecb528a8a63eb9522b68d7061e0b671339a47`](https://github.com/Verified-zkEVM/ArkLib/blob/0ffecb528a8a63eb9522b68d7061e0b671339a47/ArkLib/Data/MvPolynomial/WeightedDegree.lean). Their named public theorem families are not present in the mathematical snapshot above. These are useful independently developed prerequisites/complements, not literal extractions from that snapshot. Retain their original source-file credits.
- **Separate decoder source:** [`ffab000e71c5b19e8a19bebadcc0050eac1366e3`](https://github.com/quangvdao/ArkLib/tree/ffab000e71c5b19e8a19bebadcc0050eac1366e3), especially [PaperAlgorithms](https://github.com/quangvdao/ArkLib/blob/ffab000e71c5b19e8a19bebadcc0050eac1366e3/ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/PaperAlgorithms.lean).
- Initial target audit: ArkLib main [`18a3cde4156707a25ed206f6fbc41ae450373e9f`](https://github.com/Verified-zkEVM/ArkLib/tree/18a3cde4156707a25ed206f6fbc41ae450373e9f), Lean 4.33.1. Re-resolve main and all dependency pins for each slice.

All source paths below refer to the immutable mathematical revision unless explicitly marked decoder or covered by the T2/T6 implementation-donor exceptions above. Do not use an arbitrary local checkout or copy its uncommitted work. A later source revision needs a recorded semantic diff and a revised correspondence ledger. Publication of these pins and their historical validation are not fresh validation of the port.

## Lean 4.34 migration boundary

#903 owns the ongoing Lean 4.34.0 upgrade. At this issue's initial audit, head `0ac48c55f40e0278e642b2ea42f291f803df4f48` is open and has a failing interaction acceptance check; the upgrade has not established a green integration base. Its description's draft/stack status may lag hosted metadata. Subsequent migration update: head `d6a7826798fc565f8b57c5c2eb2945d97d7c91d6` is mergeable with all substantive checks passed; it is still open and is not a merged integration base.

1. Prepare extraction, ownership decisions, documentation, and narrowly scoped source repairs now.
2. Default code landing for this port is **after #903 merges**. Preparation against 4.33.1 is useful but does not satisfy the final gate. Do not import the migration branch wholesale into feature PRs.
3. After the bump lands, freeze the resulting main SHA and its resolved Lean/Mathlib/CompPoly/VCVio pins. Search those exact dependencies again before retaining local helpers: the migration already removes helpers newly supplied by CompPoly.
4. Rebase/restack each slice and rerun all required checks. A changed proof or API boundary needs renewed semantic review, even if the conflict was easy to resolve textually.
5. If the upgrade is delayed, complete independent preparation and record the exact blocked checks. Do not weaken a theorem, add an admission, change dependencies opportunistically, or call a failed partial validation a pass.

The migration is owned separately. Port workers must preserve its checkout and other contributors' worktrees and use isolated writable build directories.

### Combined Lean 4.34 preflight

An isolated preview combined main `68726031f01e0b79759dce718fce77ac81fb317a` with the exact green #903 head `d6a7826798fc565f8b57c5c2eb2945d97d7c91d6`, then applied all six unique tranche diffs in T1, T2, T3, T4, T5, T6 order. The prospective base tree is `04ea468988f26afd161457ab32ae13f391d26e72`; the full tested tree after the compatibility patch below is `72c298d179593eabc57b81c0b9b7b841be4bb753`. These are local reproducibility identifiers, not published commits or merged-main acceptance claims; the public parent/source revisions and patch suffice to reconstruct the source.

- Toolchain: Lean `v4.34.0`; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; CompPoly `7e3683ba72f61c1f3c2deda85953ce26392f0771`; VCVio `7a4d7ee254165f2fcf3282c7d2e6f204056e5121`.
- All 12 focused production/client targets compiled, followed by successful full `./scripts/validate.sh --axioms`: 12,729 declarations in 511 modules, no new axiom/admission taint, and no nonstandard axioms. The existing unrelated baseline contains 291 sorry-tainted declarations; this is not a whole-library claim of admission freedom.
- A separate audit of 23 representative tranche exports found only `propext`, `Classical.choice`, and `Quot.sound` in their dependency cones.
- Independent source review approved the compatibility patch. Mathlib's coefficient API is now polynomial-first: `coeff m p` becomes `p.coeff m`. Conditional lemmas use their new names, and the real-number import uses its new canonical owner. No mathematical hypotheses or conclusions are weakened.
- The six published PRs remain on their pre-upgrade bases. After #903 lands, compare its actual tree/pins with this preview, apply the relevant patch parts to T1 and T5, refresh each PR and the T5 stack, and rerun the final-head gates. Do not substitute this combined preflight for those checks.

The exact compatibility patch has SHA-256 `016ec923d14e879c04f66bcdebb697fe01609f9e4a0fc7a6c2d7f85bb5902b7e`. It is included here so the migration does not depend on a local worktree:

<details>
<summary>Compatibility patch for the six reviewed tranche revisions</summary>

```diff
diff --git a/ArkLib/Data/Finset/PairwiseIntersection.lean b/ArkLib/Data/Finset/PairwiseIntersection.lean
index 1aab97733..d81a710eb 100644
--- a/ArkLib/Data/Finset/PairwiseIntersection.lean
+++ b/ArkLib/Data/Finset/PairwiseIntersection.lean
@@ -7,7 +7,7 @@ module
 
 public import Mathlib.Algebra.BigOperators.Ring.Finset
 public import Mathlib.Algebra.Order.Chebyshev
-public import Mathlib.Data.Real.Basic
+public import Mathlib.Basic.Real.Basic
 public import Mathlib.Tactic.Linarith
 public import Mathlib.Tactic.NormNum
 public import Mathlib.Tactic.Positivity
diff --git a/ArkLib/Data/MvPolynomial/EvenAndOdd.lean b/ArkLib/Data/MvPolynomial/EvenAndOdd.lean
index 7b7cde6ec..5b786932b 100644
--- a/ArkLib/Data/MvPolynomial/EvenAndOdd.lean
+++ b/ArkLib/Data/MvPolynomial/EvenAndOdd.lean
@@ -282,9 +282,9 @@ lemma aeval_shift_mem_restrictDegree
   apply aeval_mem_restrictWeightedDegree (w := w) (v := Pi.single i 1)
   · intro j
     by_cases hj0 : j = 0
-    · rw [dif_pos hj0]
+    · rw [dite_eq_left hj0]
       exact (restrictWeightedDegree (R := R) (Pi.single i 1) (w j)).zero_mem
-    · rw [dif_neg hj0]
+    · rw [dite_eq_right hj0]
       apply X_mem_restrictWeightedDegree
       by_cases hjs : j = source
       · subst j
diff --git a/ArkLib/Data/MvPolynomial/WeightedDegree.lean b/ArkLib/Data/MvPolynomial/WeightedDegree.lean
index 731cd3180..39d8f54ee 100644
--- a/ArkLib/Data/MvPolynomial/WeightedDegree.lean
+++ b/ArkLib/Data/MvPolynomial/WeightedDegree.lean
@@ -163,7 +163,7 @@ theorem weightedTotalDegree_C (w : σ → ℕ) (r : R) :
 theorem weightedTotalDegree_monomial (w : σ → ℕ) (m : σ →₀ ℕ) (r : R) (hr : r ≠ 0) :
     weightedTotalDegree w (monomial m r) = weight w m := by
   classical
-  rw [weightedTotalDegree, support_monomial, if_neg hr]
+  rw [weightedTotalDegree, support_monomial, ite_eq_right hr]
   simp
 
 /-- Taking the `n`th power multiplies the weighted-total-degree upper bound by `n`. -/
@@ -213,12 +213,12 @@ theorem weightedTotalDegree_bind₁_le {τ : Type*} (v : τ → ℕ)
       weightedTotalDegree (fun i => weightedTotalDegree v (f i)) p := by
   conv_lhs => rw [p.as_sum, map_sum]
   calc
-    weightedTotalDegree v (∑ m ∈ p.support, bind₁ f (monomial m (coeff m p))) ≤
-        p.support.sup fun m => weightedTotalDegree v (bind₁ f (monomial m (coeff m p))) :=
+    weightedTotalDegree v (∑ m ∈ p.support, bind₁ f (monomial m (p.coeff m))) ≤
+        p.support.sup fun m => weightedTotalDegree v (bind₁ f (monomial m (p.coeff m))) :=
       AddMonoidAlgebra.supDegree_sum_le
     _ ≤ p.support.sup fun m => weight (fun i => weightedTotalDegree v (f i)) m :=
       Finset.sup_mono_fun fun m _ =>
-        weightedTotalDegree_bind₁_monomial_le v f m (coeff m p)
+        weightedTotalDegree_bind₁_monomial_le v f m (p.coeff m)
     _ = weightedTotalDegree (fun i => weightedTotalDegree v (f i)) p := rfl
 
 /-- Prescribed-weight substitution bound: if the image of source variable `i` has target weighted
@@ -300,7 +300,7 @@ theorem eq_zero_of_mem_restrictWeightedDegree_zero {w : σ → ℕ} (hw : ∀ i,
 /-- With positive weights, the weight-zero piece consists only of constants. -/
 theorem eq_C_coeff_zero_of_mem_restrictWeightedDegree_zero {w : σ → ℕ} (hw : ∀ i, w i ≠ 0)
     {p : MvPolynomial σ R} (hp : p ∈ restrictWeightedDegree (R := R) w 0) :
-    p = C (coeff 0 p) := by
+    p = C (p.coeff 0) := by
   ext m
   by_cases hm : m = 0
   · subst m
@@ -308,7 +308,7 @@ theorem eq_C_coeff_zero_of_mem_restrictWeightedDegree_zero {w : σ → ℕ} (hw
   · have hm_support : m ∉ p.support :=
       fun hmem => hm (eq_zero_of_mem_restrictWeightedDegree_zero hw hp hmem)
     rw [notMem_support_iff.mp hm_support]
-    exact (coeff_C_of_ne_zero (R := R) hm (coeff 0 p)).symm
+    exact (coeff_C_of_ne_zero (R := R) hm (p.coeff 0)).symm
 
 /-- The weight-zero bounded piece is a subalgebra.  This is the fixed-bound multiplication closure
 that remains valid without incorrectly claiming the same for a positive bound. -/
@@ -337,7 +337,7 @@ theorem basisRestrictWeightedDegree_repr_apply (w : σ → ℕ) (d : ℕ)
     (p : restrictWeightedDegree (R := R) w d)
     (m : {m : σ →₀ ℕ // m.weight w ≤ d}) :
     (basisRestrictWeightedDegree (R := R) w d).repr p m =
-      coeff m (p : MvPolynomial σ R) :=
+      (p : MvPolynomial σ R).coeff m :=
   rfl
 
 /-- Coefficient projection from a bounded weighted-degree submodule at an allowed monomial. -/
@@ -351,14 +351,14 @@ theorem restrictWeightedDegreeCoeff_apply (w : σ → ℕ) (d : ℕ)
     (m : {m : σ →₀ ℕ // m.weight w ≤ d})
     (p : restrictWeightedDegree (R := R) w d) :
     restrictWeightedDegreeCoeff (R := R) w d m p =
-      coeff m (p : MvPolynomial σ R) :=
+      (p : MvPolynomial σ R).coeff m :=
   rfl
 
 /-- Coefficients outside the weighted-degree bound vanish. -/
 theorem coeff_eq_zero_of_mem_restrictWeightedDegree {w : σ → ℕ} {d : ℕ}
     {p : MvPolynomial σ R} (hp : p ∈ restrictWeightedDegree (R := R) w d)
     {m : σ →₀ ℕ} (hm : d < m.weight w) :
-    coeff m p = 0 := by
+    p.coeff m = 0 := by
   rw [← notMem_support_iff]
   exact fun hmem => Nat.not_le_of_gt hm ((mem_restrictWeightedDegree.mp hp) m hmem)
 
```

</details>

## First tranche: assigned implementation

Statuses mean **planned → implementing → review → published → validated → merged**. “Validated” records the exact head and target; it does not imply approval or merge. All six units are assigned; none is marked complete at issue creation.

| ID | Unit and disposition | Dependencies / acceptance result | Status / PR |
|---|---|---|---|
| T1 | Refresh weighted support, substitution, and finite-dimensional API. Preserve #857's `EvenAndOdd` consumer and use the published source's module-form implementation. Move production acceptance canaries into `ArkLibTest`. | Current polynomial owners; zero weights remain allowed outside finite-dimensional results. No artificial no-zero-divisors premise on substitution bounds. | Published; #857 at `55ea6bad1515544e8a4714a33f400d4f77ffc12f`. Refreshed to base `a523e9e7`; full local gate passed on Lean 4.33.1. Hosted head CI passed; post-#903 validation pending. |
| T2 | Refresh fraction-field resultant certificates, preserving both actual-degree and padded forms. | Current resultant API; specialization may lower degrees. Retain the positive combined-degree guard. | Published; #877 at `417470c2fcb5941e8b629b849ad3e3ace95d906f`, base `a523e9e7`. Full local gate passed on Lean 4.33.1; hosted head CI passed; post-#903 validation pending. |
| T3 | Replace #855 with proved exact-list/candidate-filter specifications. Import the proofs of `filteredDecoder_isExact` and `filteredDecoder_card_le` from `ReedSolomon/ListSpecification.lean`. | Existing RS and agreement semantics. No old admitted headline, unused generic contracts, or added axiom debt. Choose the specification owner once and update its consumers. | Published as #908 at `fa98e2acaf5e530f79603b637bb15d6d03582d5d`, base `a523e9e7`. Full local gate passed on Lean 4.33.1; hosted head CI passed; post-#903 validation pending. #855 closed without merge. |
| T4 | Complete agreement-list finiteness and incidence counting from `AgreementList.lean`. | Depends only on #906 or its merged successor for the incidence-only extraction; no T3 dependency. Deliver `.Finite` and the bound `list.card * A.choose k ≤ n.choose k`, with actual message-degree/threshold hypotheses. | Published as #909 at `88544465a09fb5a254d51d4305486c5e6332b8d8`, base `68726031`. Full local gate passed on Lean 4.33.1; hosted head CI passed; post-#903 validation pending. |
| T5 | Extract elementary pairwise Johnson counting and the RS list theorem from `MutualCorrelatedAgreement/Johnson/WeightedCertificate.lean`. | T4 and existing polynomial uniqueness. The list theorem must not import geometric MCA machinery. Preserve the exact integral floor and positive denominator. | Published as #910 at `c1df20cec4868c11cfa828e643d10cf8f08b36a2`, targeting #909 head `88544465`. Full local gate passed on Lean 4.33.1. Explicit hosted head checks passed; post-#903/main integration validation pending. |
| T6 | Refresh exact weighted product/divisor accounting. Put complementary #875 material in a coherent separate owner such as `Data/MvPolynomial/WeightedDegree/Products.lean`. | Independent of T1 mathematically; preserve both APIs if imports are reorganized. Do not force it into the paper's dependency chain without a consumer. | Published; #875 at `867f68b0e049a2325b3cf4fd5963d0baba2bc5fe`, base `a523e9e7`. Full local gate passed on Lean 4.33.1; hosted head CI passed; post-#903 validation pending. |

All six PRs are published and independently source-reviewed. Their exact current heads passed full local `./scripts/validate.sh --axioms` on Lean 4.33.1, with no new axiom or admission taint. All six listed heads now have passing substantive hosted checks. For #910 these are explicit head-check runs; its non-main PR rollup itself shows only the summary job. For stacked #910, the explicitly dispatched checks are [CI](https://github.com/Verified-zkEVM/ArkLib/actions/runs/35537954974), [imports](https://github.com/Verified-zkEVM/ArkLib/actions/runs/35537956213), and [documentation integrity](https://github.com/Verified-zkEVM/ArkLib/actions/runs/35537957512), all at `c1df20cec4868c11cfa828e643d10cf8f08b36a2`. The remaining integration dependency is #903 landing. The reviewed Lean 4.34 compatibility patch is ready above; actual-main refresh and final-head gates must follow the landing. No first-tranche PR is merged or claimed accepted on Lean 4.34. A legacy auto-merge request on #877 was disabled; all six are verified outside the merge queue with auto-merge off, preserving the explicit landing gates.

The T4 extraction deliberately omits the source file's later general-index `agreeingPolynomials`, `agreeingPolynomials_antitone`, `exists_finset_polynomial_list`, and `agreeingPolynomials_eq_empty_of_card_lt`. These remain tracked for a separate specification-bridge slice depending on T3; it must reconcile the subtype-valued list and `closePolynomialSet` through the canonical agreement API. Do not mark all of source `AgreementList.lean` ported when only its incidence section is present. Independent review confirmed that no T3 definition is needed for the core T4 incidence proof.

Disposition: #855 was closed without merge after #908 was published and validated locally. Its preserved description links the proved specification replacement and keeps the unproved historical low-rate headline under #854; no baseline debt was imported. Do not resolve #857/#875's add/add collision by selecting one entire file. Preserve author and donor attribution.

## Mathematical targets and correspondence

The published inventory R1–R12 is the initial coverage contract. Record a destination declaration for every row; an import umbrella or matching theorem name is insufficient evidence.

| Target | Source declaration / owner | Required meaning |
|---|---|---|
| R1 Johnson lists | `closePolynomialSet_finite_and_ncard_le_johnsonPairwise`; `MCA/Johnson/WeightedCertificate` | Complete finite list over arbitrary fields; exact integral bound |
| R2 Johnson MCA | `exists_exceptional_johnson_lineMCA_allChar`, `exists_exceptional_weightedJohnsonMCA_fullAgreement` | All characteristic, one exceptional set, full agreement-set recovery |
| R3 First-order rate branches | `FirstOrder.firstOrderBranch_finiteLength_finiteSlack_bounds`, `..._rate_bounds`, `..._mcaError_le`; `MCA/FirstOrder/Branchwise` | Both rate branches; finite slack `eta + 1/n`; list and exceptional bounds with their characteristic guards |
| R4 Finite optimized curve certificates | `CurveCertificate.exists_exceptional_exact_powerAgreement_best[_optimized]`; `CurveCertificate.exists_exceptional_exact_powerAgreement_squarefree_sharp_optimized`; `FirstOrder/Squarefree/Sharp` retained-squarefree theorems | Actual recovery for optimized thresholds; comparison laws proving optimization cannot worsen the bound |
| R5–R6 Fixed-order lists and MCA | `exists_ratePartition_list_bound`, `exists_ratePartition_lineMCA_parameters`; respective `Capacity/RatePartition` owners | Strict `Gamma > 1` gate; constants chosen before field/code/word; `n^d` and `n^(d+1)` |
| R7–R8 Explicit fixed-rate order | `fixedRatePartitionOrder_list_bound[_selected]`, `fixedRatePartitionOrder_lineMCA`; `Capacity/FixedRateExplicitGate` | Explicit order and finite parameters; preserve floor/ceiling and rate hypotheses |
| R9 Uniform capacity lists | `HasCapacityLists`, `exists_rateCapacity_list`; `ListDecodability/Capacity` | Actual message dimension; first-order branch at gap `6/25`; current 300-based small-gap recipe |
| R10 Uniform capacity MCA | `HasSharpCapacityLineAgreement`, `sharpCapacity_lineAgreement`, `exists_sharpCapacity_lineAgreement`; `MCA/Capacity` | Constant-code branch and precise characteristic guard; one uniform exceptional set |
| R11 Affine and powers families | `sharpCapacity_affineAgreement_and_mcaError`, `sharpCapacity_powerBatchingAgreement`; `MCA/Capacity` | Keep line/affine/curve sampling and characteristic conditions distinct |
| R12 Interleaving and shared-level folds | `uniformExactInterleavedPowerAgreement_of_scalar_arbitrary`; `TensorMCA.tensorFoldBad_card_le`; `fullSetLevelWitness_interleaved_of_exactAgreement`; `interleavedRS_tensorFoldBad_card_le_heightThree` | Width-independent exceptional bound; full set-level witnesses; count each shared challenge level once |
| A1–A3 Applications | Source `ArkLibExamples/ReedSolomon/PaperGuide` and its ProveKit, ZisK, LambdaVM owners | Mathematical certificates and analytical/recorded-byte arithmetic, with empirical inputs and protocol assumptions explicit |
| D Decoder track | Separately pinned `ListDecoding/PaperAlgorithms`, `ExactOutput`, `CapacityDecoder` | Per-procedure correctness, then complete execution and the actually justified cost model; no automatic claim of the paper's fast decoder |

Here `MCA/` abbreviates source `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/`. It is a table abbreviation, not a proposed directory rename. R1–R12 are tracking IDs, never Lean declaration names.

## Later slices and dependency boundaries

Each row is a work package to split into narrowly reviewable PRs, not permission for a directory-sized dump. Before coding it, freeze the export/consumer manifest and exact predecessors. Adjacent units may be combined only when that makes a complete API easier to review; split when the interface or proof method changes.

| Package | Separate review units | Prerequisites and public payoff |
|---|---|---|
| P1 Polynomial and differential algebra | Differential types/basic laws; Hasse/Taylor/substitution bridges; local contact and derivative descent | T1 plus current polynomial owners. Keep ordinary derivatives and Hasse derivatives explicit; reusable differential laws have no coding-theory imports. |
| P2 Polynomial kernel bounds | Uniform degree-height bounds; primitive vectors; column budgets; shifted row/column budgets | Existing matrix/polynomial algebra. Expose nonzero kernel-vector theorems with degree and specialization invariants before RS specialization. |
| P3 Finite interpolation | Constraint maps; local rank bounds; dimension counts; concrete interpolation certificate and its constructor | P1/T1 and ordinary finite-dimensional algebra; P2 only for symbolic/height-controlled constructors. Bundle actual nonzero differential polynomial, degree bound, and constraints; derive satisfaction for agreeing candidates. |
| P4 Resultant regularity | T2-based padded nonvanishing; common-root specialization; bivariate degree budgets; ordinary factor/regularity application | T2 and main's `Data/Polynomial/ResultantDegree`. Preserve coefficient-domain and degree-drop cases. |
| P5 Counting geometry | Hilbert/degree interfaces; finite zero loci; principal opens/cuts; retained families; incidence product bounds | Generic algebra/geometry. Keep definitions meaningful without RS; introduce each layer with a proved consumer. |
| P6 Ordinary MCA | Ordinary interpolation/factor transfer; all-characteristic regularity; weighted Johnson and simple line endpoints | P3/P4 and required P5 subset. Delivers R2; R1 does not wait for this. |
| P7a Shared differential root counting | Rational Taylor charts; regular branch geometry; singular recursion; all-solution bounds | P1 and required P5 geometry. Preserve `IsBelowCharacteristic`, separate binomial nonvanishing, arbitrary-field finite-subset statements, and the characteristic-zero route. This common substrate precedes both first- and higher-order counting. |
| P7b First-order list theory | Specialized Taylor degree/bidegree counts; capped/hybrid counts; finite list certificates; rate-branch arithmetic | P3/P7a. The hybrid order-zero terminal route avoids differentiation; do not impose a blanket stronger characteristic guard. Deliver list results without depending on MCA endpoints. |
| P8 First-order MCA and curves | Symbolic transfer; line bounds; factorwise squarefree bounds; threshold optimization and endpoints | P6/P7b plus kernel heights. Deliver R3/R4 with a shared lower-level owner for genuinely shared list/MCA parameters. |
| P9 Higher-order support estimates | Discrete simplex counts; continuous moments; floor/lattice transfers; positive-surplus and parameter selection | T1 plus generic analysis/combinatorics. Expose the reusable estimates separately from the paper's parameter recipes. |
| P10 Higher-order lists | Support-dependent fixed-order interpolation/list bound; explicit fixed-rate selection; uniform capacity assembly | P3/P7a/P9; P7b only for the uniform first-order fallback. Deliver R5/R7/R9 in that order. |
| P11 Higher-order MCA | Symbolic interpolation/descent; fixed-order line bound; explicit selection; uniform all-rate assembly | Relevant P2/P5/P9/P10 owners. Deliver R6/R8/R10; audit constants chosen before field and word. |
| P12a Early generic transfers | Minimal exact-agreement contracts; line-to-affine/powers transfers where independent; subspace avoidance and interleaving projection; shared-level fold theorem | Lightweight agreement contracts and generic linear algebra/probability. Split definitions out of source construction files and remove incidental capacity imports before claiming independence. Conditional transfers alone do not complete R11/R12 applications. |
| P12b Concrete transfer endpoints | Capacity/interleaving list/probability endpoints; nested-powers and concrete RS fold specializations | P12a plus the selected scalar exact-agreement provider from R2/R3/R10/R11, with its threshold/characteristic hypotheses discharged. Record exactly which provider closes each concrete result. |
| P13 Application library | Register separate example target and validation coverage; common certificate wrappers; named application certificates | R4/R12 as needed. Avoid a reusable-library import of applications or measured data. |
| P14 Decoder procedures | Representation/exact outputs; arithmetic procedures; reconstruction procedures; candidate coverage; executor integration; cost composition | Separate source pin and declared backends. Maintain a separate obligations ledger; missing implementations are new work, not merely porting. |

The core dependency graph is acyclic after these extractions: differential algebra plus geometry gives common Taylor/root counting; finite support gives finite interpolation; polynomial kernels add symbolic height control; first- and higher-order counts share the counting substrate. Uniform capacity assembly may then consume the first-order fallback. Generic transfers become concrete applications only after their scalar provider is supplied.

### Canonical ownership and exposition

Use existing ArkLib owners before creating parallel representations. Generic polynomial results belong in `Data/Polynomial` or `Data/MvPolynomial`; Mathlib-shaped extensions can remain in existing `ToMathlib` families within ArkLib. No Mathlib or CSLib upstreaming is a prerequisite. Record every source-to-destination move; source folder names are not binding architecture.

Use `ReedSolomon/ListDecodability` for list bounds, `HiddenDerivative` for the interpolation/reconstruction method, and a single `MutualCorrelatedAgreement` hierarchy for MCA. Mathematical theorem entrypoints must not import executable decoders, cost models, or application examples. Shared parameter arithmetic belongs below both list and MCA results. Establish separate build/axiom/import coverage before introducing `ArkLibExamples`; that target exists in the source branch but is not established by current main's default checks.

Every main result family gets a dedicated, explicitly identified theorem module. A mathematically useful intermediate theorem deserves the same treatment when it is independently reusable. A module docstring must state the question, mathematical result/formula, assumptions, representations, principal declarations, proof idea, consumers, and sources. Main declaration docstrings must explain quantifier order, field/characteristic conditions, degree convention, constants, and precisely what is recovered. Use spaced inline comments before meaningful binder/conclusion groups, following the published reader guide; do not annotate every syntax line. Supporting implementation lemmas should not obscure the main theorem.

Names describe mathematics, not author/year, work-package IDs, draft chronology, or vague `New`/`Improved` suffixes. Source labels belong in citations and the correspondence ledger. Do not create redundant theorem wrappers merely to satisfy a file quota; a coherent theorem family can share its dedicated file.

### Intermediate results to expose as library results

These are required architecture investigations with concrete source evidence. Final names/paths are provisional until compared against the post-upgrade dependencies; keep the mathematical contracts even if the owner changes.

| Candidate | Source evidence | Canonical destination / invariant to preserve |
|---|---|---|
| Actual-row basis selection | `ToMathlib/LinearAlgebra/PolynomialKernelHeight.lean`, `exists_rows_fin_rank` | A matrix-rank owner, without a polynomial dependency for ordinary row-space theory. |
| Primitive and shifted polynomial kernels | `Matrix.exists_primitive_kernel_vector_preserving_zero` in `PrimitivePolynomialKernel.lean`; `Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT` in `ShiftedDegreeKernel.lean`; column-budget corollaries | Keep the generic linear-algebra family. Expose zero-coordinate preservation, unit-ideal span, nonvanishing after every field extension, and empty shifted slots. Derive column/uniform variants from the strongest appropriate owner; do not lose `degreeLT` information by replacing it with natural-degree inequalities. |
| Specialization counting and avoidance | `ToMathlib/Polynomial/SeparableResultant.lean`, `finite_polynomial_specializations_eq_zero_card_le`, `exists_map_evalRingHom_ne_zero_avoiding` | A generic polynomial specialization module, used by resultants. Preserve distinct field-counting and infinite-domain existence hypotheses. Move the substantive nonmonic-linear canary into tests. |
| Centered simplex moments | `HiddenDerivative/Interpolation/WeightedSupport/Moments.lean`, centered first/second/third moments and continuous integrability; generic raw moments already under `ToMathlib/Analysis/Simplex/Moments` | Generic `Analysis/Simplex/CenteredMoments` owner; RS moment inequalities consume it. Preserve normalization behavior, including totalized zero-scale cases; do not introduce an unnecessary positivity assumption. |
| Discrete-to-continuous simplex estimates | `WeightedSupport/CubeTransfer.lean`, cell inclusion, residual monotonicity, sum-to-integral bound | Generic simplex/lattice owner above floor cells and finite weighted tuples. Preserve enlargement by the sum of coordinate weights and the dimension shift; remove the incidental jet-coordinate import. |
| Algebraic total jet degree | `HiddenDerivative/RootFinding/Counting/TotalJetDegreeRootCount.lean`, degree definition, support characterization, separant decrease and partial-specialization monotonicity; interpolation already consumes it | `Data/Polynomial/Differential/JetDegree` or a minimal method-level owner. Both interpolation and counting import it. Exponent-tuple `totalJetDegree` and polynomial `jetTotalDegree` need a bridge, not deletion as supposed spelling duplicates. |
| Finite Taylor prefixes | `HiddenDerivative/RootFinding/Taylor/Numerator.lean`, centered prefix definition, coefficient/translation/degree/successor laws | Generic `Polynomial/TaylorPrefix` owner. Keep jet-specific adapters with differential polynomials and preserve the higher-level `TaylorExponentSufficient` parameter so improved first-order bounds remain expressible. |
| Finite-subspace avoidance | `Interleaved/PowerAgreement.lean`, `exists_vector_avoiding_submodules`; local padding helpers | Generic linear-algebra/submodule finite-union owner, with a separate existing finite-index owner for padding if needed. Preserve the sharp **at most field-cardinality** bound and nontrivial-space conditions; interleaved projection is a consumer. |

Representative pinned sources: [kernel bounds](https://github.com/quangvdao/ArkLib/blob/a5aa2677fee4e3a79d6bb05136631cce4a08587d/ArkLib/ToMathlib/LinearAlgebra/ShiftedDegreeKernel.lean), [simplex moments](https://github.com/quangvdao/ArkLib/blob/a5aa2677fee4e3a79d6bb05136631cce4a08587d/ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/Moments.lean), [jet-degree owner](https://github.com/quangvdao/ArkLib/blob/a5aa2677fee4e3a79d6bb05136631cce4a08587d/ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Counting/TotalJetDegreeRootCount.lean), [subspace avoidance](https://github.com/quangvdao/ArkLib/blob/a5aa2677fee4e3a79d6bb05136631cce4a08587d/ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/PowerAgreement.lean#L134).

Root-count integration also needs separate accounting for `Counting/TaylorAllSolutions`'s below-characteristic and binomial-nonvanishing hypotheses and the characteristic-zero route in `TaylorCharZeroSolutions`. Similar induction scripts are a review signal; consolidate only through an interface that preserves both statements.

### Decoder obligations: ported components versus new work

The separately pinned decoder uses the retained 100-based coordinate recipe, including `ceil(exp(2.7/delta))`, while the current mathematical headline uses the 300-based recipe and the `6/25` split. Keep separate parameter families and source correspondences until an actual proved bridge is supplied.

| Obligation | Status at decoder pin; acceptance for a later claim |
|---|---|
| Coordinate reference executor | Existing component to port. Bounds its returned primitive-work ledger; same-output machine refinement, scalar preparation, and control overhead remain separate obligations. |
| Complete `ExactHiddenDerivativeDecode` | No end-to-end run/exactness theorem in the cited guide. Completion needs an actual run, coverage of every qualifying polynomial, and canonical duplicate-free output. |
| First-order norm candidates and two-level recovery | Constructor/run/coverage/`ExactOutput` integration and the two-level tower consumer remain incomplete. Ported algebra does not discharge them. |
| Square-system decoder | `run_exact_of_torus_cover` assumes `TorusBackend` and `CoversTorusIsolatedRoots`. Preserve this conditional status until the backend and paper's direct affine/paired selection are supplied. |
| Paper procedures | Complete `FastRegularTaylorFamily`, `SplitZeroUnit`, and `PreprocessFiber` integrations remain explicit work. |
| Whole-decoder complexity | Requires cost composition and refinement for the same execution/output. Neither an existential list nor a primitive counter proves bit-RAM or native Lean runtime. |

Bounded-input list recovery is outside the pinned formalization scope. It requires a separately proposed extension, not an implicit completion claim for this port.

## Observed warning signs and required repairs

These are source findings or known integration risks, not claims that the entire formalization is wrong.

| Evidence | Risk | Required disposition |
|---|---|---|
| #855 has two admitted filter lemmas and an admitted old low-rate target; five geometric parameter fields do not constrain its abstract contracts | Green baseline checks can coexist with obsolete admitted mathematics and an interface that does not express the intended geometry | T3 ports the proved successor; concrete certificates arrive with constructors. No added `sorryAx` debt. |
| #857 and #875 independently add `WeightedDegree.lean` | Textual conflict can silently drop complementary APIs | Deliberate ownership reconciliation; check both downstream consumer families. |
| `ToMathlib/Polynomial/{SeparableResultant,PaddedDerivativeResultant}` repeat fraction-field padded nonvanishing; the general module imports the specialized one | Duplicate proof maintenance and reversed dependency direction | Generic kernel → general padded API → specialized API. Bridge resultant orientation explicitly. |
| `SeparableResultant` imports `CodingTheory/PolishchukSpielman/Resultant` for `ps_nat_degree_resultant_le`, already a wrapper over `Data/Polynomial/ResultantDegree` | Generic algebra acquires a coding-theory dependency unnecessarily | Import/call the generic owner directly; preserve attribution. |
| Pairwise Johnson list theorem and its private counting lemma live in `MCA/Johnson/WeightedCertificate` | An elementary list theorem imports the geometric MCA tree | T5 extracts generic counting and list specialization before MCA. |
| Source `Capacity` facades retain older recipes alongside current results; first-order `RateBounds` has weaker exponents than `Branchwise`; interleaving contracts import capacity constructions through `AgreementBounds`/`CodewordBound` | A plausible name can select the wrong paper theorem or silently worsen constants | Track exact declarations; preserve older results only for named consumers and document differences. Extract early transfer contracts from construction-heavy imports. |
| Local older source uses `CorrelatedAgreement` while published pin uses `MutualCorrelatedAgreement`; source and target dependency pins differ | Copying by directory/name can mix revisions and duplicate representations | Port pinned objects, maintain rename/owner map, search exact post-upgrade dependencies. |
| Decoder guide lists missing complete-run, backend, candidate-construction, and cost integration obligations | A finite-set theorem or conditional solver contract can be mistaken for a verified fast decoder | Separate decoder ledger; name remaining assumptions and match each complexity claim to the actual implemented procedure/model. |

Review probes for every affected slice: zero polynomial versus `natDegree`; `k=0`, `k=1`, empty/full code and threshold endpoints; characteristic versus field cardinality; physical rate `k/n` versus reduced degree `(k-1)/n`; natural subtraction and floor/ceiling losses; zero weights versus finite-dimensional support; nonzero/divisor hypotheses; finite sets versus totalized `Set.ncard`; one exceptional set selected before challenge/candidate; complete agreement-set equality versus a qualifying subset; line/affine/curve probability denominators; scalar versus extension-field message witnesses. These are obligations to inspect, not demands for one test per item.

## Acceptance contract for every PR

This project adds a strict no-new-admissions requirement to ArkLib's existing gates. Consult the actual target's [AGENTS.md](https://github.com/Verified-zkEVM/ArkLib/blob/main/AGENTS.md), [CONTRIBUTING.md](https://github.com/Verified-zkEVM/ArkLib/blob/main/CONTRIBUTING.md), [module guide](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/wiki/module-system.md), and [validation wrapper](https://github.com/Verified-zkEVM/ArkLib/blob/main/scripts/validate.sh) again after migration.

- **Statement review:** record source theorem, exported Lean type, exact hypotheses and conclusion, and whether the port is equivalent, generalized, specialized, or intentionally different. Explain every semantic change. Inspect transitive assumptions, not just theorem names or proof bodies.
- **Generalization review:** apply the required port objective above; record the most general useful contract, existing-API search, consumer interfaces, and the thin RS specialization. Unnecessary RS specialization is an acceptance defect even when the proof compiles.
- **Architecture review:** one canonical owner and representation, justified import direction, appropriately general universes/typeclasses, and a real consumer or self-contained mathematical specification. Search pinned dependencies before retaining helpers. Repeated casts, proof skeletons, wrappers, or broad imports trigger an owner/API review rather than automatic stylistic rejection.
- **Proof engineering review:** expose structural steps; use stable named lemmas across module boundaries; audit simp normal forms and private/exposed bodies through ordinary imports. Do not solve module migration with linter suppressions or blanket private-in-public switches. Profile before making performance claims or mechanically changing tactics.
- **Trust:** no new admissions, axioms, native/compiler trust, or baseline expansion to hide debt. Standard foundational axioms are not proof gaps. Do not newly taint a completed export through an existing admitted dependency. Audit the principal theorem dependency cones and source coverage, including examples/unimported files. An axiom baseline passing does not establish that a particular theorem is axiom-clean.
- **Validation:** stage new source/test paths; regenerate `ArkLib.lean` using the repository generator; run full `./scripts/validate.sh --axioms` before commit/push. Add `--docs` for API documentation work and `--site` when the blueprint/site changes. Record exact head, base/merge base, toolchain/dependency pins, command results, and excluded targets. A stopped build means later gates did not run.
- **Coverage beyond the default root:** current axiom sweep defaults to `ArkLib` only. Account separately for classic `ArkLibTest`, nondefault `ArkLibBlueprint`, and any new `ArkLibExamples` target. CI also runs `scripts/test-source-trust-audit.py` and `scripts/source-trust-audit.py`; inspect these results/coverage in addition to the kernel sweep. A new target needs build, warning, import-boundary, and trust coverage before it is called accepted.
- **Acceptance clients:** use `ArkLibTest`, ordinary imports, and the smallest meaningful coverage of public API/edge cases. Reject theorem-mirror examples unless they protect a named elaboration/import contract. Existing laws and production consumers count as evidence; no test quota.
- **Independent review:** a reviewer other than the implementer examines statements, ownership, proof/API quality, source correspondence, and validation. Resolve every actionable hosted review finding. A self-posted agent review is evidence, not a substitute for required GitHub approvals.
- **Stacked-PR CI coverage:** current CI, import, and documentation workflows trigger automatically for PRs targeting `main`, not arbitrary predecessor branches. A clean stacked PR can therefore have no substantive hosted validation. Publish a scoped upstream head branch and explicitly dispatch the applicable workflows at that head when needed; record the tested SHA. These head checks do not replace main/merge-queue integration checks after retargeting. Do not treat an empty check list or the summary bot as a pass.
- **Integration:** current required CI and merge-queue checks must pass on the relevant revision. Historical green checks, skipped publishing-only jobs, or successful unrelated jobs are not evidence for unrun validation. Do not use administrative bypass to evade the mathematical, trust, or integration requirements in this issue.

The first-tranche worker is authorized to prepare and publish scoped PRs, not merge them. Final landing is a separate maintainer action after these gates.

## Ledger, revisions, and completion

Every PR links this issue and records:

| Field | Required content |
|---|---|
| Source | Immutable revision, file, declarations, provenance/credits |
| Destination | Generic owner and public theorem, consumer-facing interfaces, RS specialization, rename/compatibility disposition |
| Dependencies | Exact base and predecessor PRs; required exported declarations |
| Mathematical contract | Assumptions, guarantee, quantifier order, changed hypotheses/constants |
| Evidence | Consumer or acceptance client, principal axiom cones, validation and independent review |
| State | Owner, PR URL/head, blocked reason if any, merge SHA when landed |

Keep this issue as the human-readable dashboard. Establish a small version-controlled port manifest/blueprint with the first published replacement/extraction PR, then extend it before each later package, so agents can work from a fresh clone without local notes. Its initial scope is T1–T6 source declarations, destination owners, predecessor interfaces, and deferred overlaps. Record all R1–R12, A1–A3, decoder obligations, and meaningful intermediate results; distinguish ported, supplied upstream, intentionally retired, and newly required work. Do not copy historical generated KB output or machine-specific paths.

Revise the plan when proof dependencies or better APIs require it: record the evidence, old/new owner/interface, affected slices, migration cost, and validation impact; obtain independent review before dependent slices rely on a changed contract. Recompute unique diffs and dependencies after squash merges. Avoid parallel edits to an owner file and avoid sharing writable build directories. Do not freeze a bad abstraction merely because this issue initially named it.

Completion means the declared mathematical targets are merged with source correspondence and clean principal axiom cones, useful intermediate results are discoverable, redundant source APIs are reconciled, and the reader guides build on current main. The mathematical milestone can finish separately. Close the overall tracking issue only when every application and decoder obligation is merged or explicitly moved to a linked, accepted follow-up with its scope disposition recorded. A deferred or unimplemented decoder obligation remains visible; it is not checked off by importing a conditional theorem.

Initial plan review: two independent Astra low source reviews checked architecture and acceptance/scope. Revisions pinned the paper artifact, corrected the finite-versus-symbolic interpolation dependencies, separated common root counting to remove a first-/higher-order package cycle, split conditional transfers from concrete endpoints, and made decoder/axiom coverage explicit. This review certifies the planning evidence only; no ported Lean build or mathematical whole-library audit is claimed.

First-tranche source review checkpoint: all six bounded extractions have independent source reviews. These found documentation/provenance corrections, the T4 dependency/deferred-bridge correction above, and a concrete T5 extraction defect: declaration-wide `open Classical in` had been lost, so proof-local `classical` did not supply the instance needed to elaborate the theorem statement. The scope was restored without adding a public hypothesis; the correction was re-reviewed. T4 also exposes its incidence bound directly for `closePolynomialSet.ncard`. All six reviewed extractions subsequently passed full local build/axiom gates at the exact pre-upgrade heads recorded in the tranche table; the table distinguishes published PRs from public preparation branches. T5 compilation also caught an invalid tactic import introduced during extraction; the generic owner now imports `Mathlib.Tactic.Linarith` and `Mathlib.Data.Real.Basic` explicitly, without changing the theorem. Hosted CI, post-upgrade validation, PR publication, and merge remain separate gates; later changes require delta review.

Final public-artifact review also corrected unit-specific provenance: T2/T6 use their immutable old-PR implementation donors, not direct extraction from the paper snapshot. Acceptance descriptions distinguish direct tests from transitive proof coverage; no extra tests are required merely to make a coverage count larger.














