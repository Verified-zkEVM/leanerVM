This issue tracks the interaction framework under `ArkLib/Interaction/` and the protocol proofs that use it.

**Updated 2026-09-26.** Run protocols in sequence, preserve the prover's private memory and the oracle state, and prove soundness under clearly stated assumptions.

## Start here

- [Design guide](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/design/README.md): reading order and document responsibilities.
- [Current implementation status](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/design/00-current-status.md): supported APIs and proved results.
- [Implementation roadmap](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/design/05-roadmap.md): the single plan, with dependencies and acceptance checks.
- [Documentation refactor #1230](https://github.com/Verified-zkEVM/ArkLib/pull/1230) is merged; the guide and roadmap above are current on `main`.

Architecture chapters own design decisions, the roadmap owns the implementation sequence, and these issues record progress. Update current status when a result lands.

## What is proved

- [x] Typed protocol trees, oracle access, virtual oracle substitution, claims, and closing using actual execution resources: #851–#871.
- [x] Logged execution, persistent runtime support, outcomes, and query phases: #880, #884, #886, #889.
- [x] Ordered execution of a specified sequence of reductions: #891, with Sumcheck clients #883 and #892.
- [x] Full native Sumcheck soundness and completeness for ordinary prover strategies, including private memory: #1214.
- [x] Shared direct strategy execution: #1216.
- [x] General native composition soundness with additive errors and an explicit error for intermediate inputs outside the next theorem's assumptions: #1218.

C5–C7 below add restricted-oracle composition and persistent-runtime bounds for native whole-prover execution under explicit assumptions about the actual joint distribution. They do not automatically transfer a bound to every persistent runtime. Ordered stage execution and arbitrary whole-prover execution are different claims. Legacy theorem admissions are not removed by the new native results.

## Composition milestones

Each C-number identifies a PR-sized result and its tracking issue.

- [x] C1 — Generalize native composition probability bounds: #1222, merged in #1231.
- [x] C2 — Preserve oracle paths and query access under composition: #1223, merged in #1232.
- [x] C3 — Compose restricted verifier strategies without changing execution order: #1224, merged in #1233.
- [x] C4 — Compose reductions through their exported oracle interfaces: #1225, merged in #1234.
- [x] C5 — Prove oracle composition soundness and use it for Sumcheck: #1226, merged in #1235.
- [x] C6 — Run native strategies through the existing persistent runtime: #1227, merged in #1236.
- [x] C7 — Prove composition with correlated prover memory and oracle state: #1228, merged in #1237.
- [x] C8 — Certify available oracle access and composed query budgets: #1229, merged in #1238.

C1–C8 are merged after full validation, independent Sol High review, and green CI. C8 includes canonical access, name-preservation and weighted route-cost proofs and both concrete resource-certified clients. All merges used squash; merged trees were checked against the reviewed commits. Work on the next step may overlap validation and CI, with merges in dependency order. C3 follows C2; C4 follows C3; C5 uses C1 and C4. C6 follows C4, C7 uses C1/C5/C6, and C8 completes the resource-certified application of C6/C7.

**First milestone:** C1–C5 let Sumcheck use reusable oracle composition proofs.
**Second milestone:** C6–C8 add persistent-world soundness and a concrete client with proved access and budget assumptions.

## Design contracts

- [Claims, oracle access, and composition](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/design/02-oracle-reduction-core.md): ordinary prover continuations, exported oracle interfaces, suffix shape, and effect order.
- [Execution and security](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/design/03-adversarial-oracle-execution.md): actual joint distributions, the prover's allowed view, and rejection/fault/missing-mass distinctions.
- [Naming and explanations](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/wiki/interaction-naming.md): standard cryptographic language in names, docstrings, and PR descriptions.

## Later work and related tracking

- [x] **Computable Sumcheck:** #1242 adds CompPoly round messages, shared native verification, exact whole-prover execution correspondence and soundness. #1243 adds direct CompPoly honest message generation, original-oracle evaluation, whole honest execution correspondence and completeness. Both are squash-merged after full local validation, compiled runtime checks, independent Sol High review and green CI. The merged trees were checked against the reviewed results. These are general finite-enumeration computations, not an optimized multilinear algorithm.
- **Priority update:** complete native Sumcheck before starting the FRI/Spartan migrations. C1–C8 complete the composition milestones, not the whole Sumcheck development. Computable CompPoly messages and general honest prover operations, with correspondence and soundness/completeness proofs, are now implemented in #1242 and #1243. Remaining Sumcheck work includes native round-by-round soundness; precise native knowledge/round-by-round knowledge games and their implications; and an explicit account of what is extracted when the original polynomial is an input oracle versus a hidden witness. The optimized multilinear implementation is a separate obligation from computability of the general protocol. FRI batching remains a researched later candidate, not the next implementation task.
- Knowledge soundness/extraction, state restoration, and compilation need separate theorems. Ordinary soundness composition does not settle them.
- #676 tracks remaining legacy composition/context-lifting gaps. Do not close it because a native theorem lands.
- #627 covers the BCS implementation-change design. It is not part of the first composition milestone.
- #480 concerns conceptual documentation of the legacy API; it is separate from this maintained framework plan.

## Historical context

The original checklist asked for legacy `OracleVerifier.append`, finite composition, and preservation of all security notions. Implementations and scoped completeness proofs now exist, but unrestricted legacy security claims still include admissions. The current plan above replaces that old implementation checklist without claiming those security gaps are solved.

The old prototype PRs are superseded. Their preserved branch is a reference source, not a development base. Earlier discussion and progress reports remain in this issue's comments.
