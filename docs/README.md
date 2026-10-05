# Documentation

This directory contains stable project and operating knowledge.

- [architecture.md](architecture.md): Lean layers, dependency direction, and criteria for
  adding native or acceleration code.
- [dependencies.md](dependencies.md): version pins and dependency update policy.
- [leanvm-target.md](leanvm-target.md): audited target revision, legacy comparison, and
  proof-obligation coverage.
- [leanisa-checker.md](leanisa-checker.md): proved exact and fuel-bounded checkers, trace
  adapters, filler validation, and the pinned Rust comparison lane.
- [development.md](development.md): local commands, module workflow, and testing guidance.
- [ci.md](ci.md): workflow responsibilities, required checks, and automation secrets.
- [roadmap/](roadmap/): one roadmap (what is wanted) and one status snapshot (where it stands)
  per formalization effort.
  - [leanisa-blueprint.md](roadmap/leanisa-blueprint.md): the leanISA roadmap — scope,
    dependency contracts, pinned conventions, the eleven layers, acceptance tests, and public
    interfaces.
  - [leanisa-status.md](roadmap/leanisa-status.md): where the leanISA roadmap stands — layer
    coverage, the frontier, pending decisions, open source findings, and the survey record.
  - [protocol-blueprint.md](roadmap/protocol-blueprint.md): the proof-system roadmap on
    ArkLib — scope, dependency contracts and the upstream ledger, pinned conventions, the spine
    and its holes, the fourteen layers from the M3 relation to the executable verifier,
    acceptance tests, public interfaces, and the decisions.
  - [protocol-status.md](roadmap/protocol-status.md): what of the proof system is on `main`,
    what the built work owes the blueprint, what can start now, and the upstream watch.
  - [leanth-reuse.md](roadmap/leanth-reuse.md): what the earlier leanVM-a formalization
    (private repository `leanth`) contains that the proof-system roadmap reuses — the catalog by
    layer, verdicts, credit, the port log, and the upstream candidates.
- [reviews/](reviews/): review documents handed off for implementation, one per reviewed piece
  of work, each an archive of the commit it describes; what was accepted from a proof-system
  review is text of its blueprint.
  - [leanisa-layer6-tables.md](reviews/leanisa-layer6-tables.md): the review of the Layer 6
    table contracts (2026-09-14), whose findings the tables now meet (status finding F8).
  - [leanisa-layer8-statement.md](reviews/leanisa-layer8-statement.md): the review of the
    Layer 8 constraint statement (2026-09-17), whose findings the statement now meets (the
    missing BLAKE2s validity conjunct, its finding A1).
  - [public-input-phase.md](reviews/public-input-phase.md): the review of the public-input
    phase (2026-09-29), whose findings the branch now meets (the two checks that are not
    equivalent, one output, the line's `sent` flag, the shared lemmas).
  - [protocol-spine.md](reviews/protocol-spine.md): the review of the proof-system spine
    (2026-09-28), whose findings the branch now meets (the degree bound at the bus seam, the
    named extractor, public lines, the strong Flock predicate).
  - [protocol-survey-record.md](reviews/protocol-survey-record.md): the proof system's survey
    log up to 2026-09-29, archived from its status file.
  - [protocol-layer1.md](reviews/protocol-layer1.md): the review of the proof system's Layer 1
    (2026-09-29), whose findings the branch now meets (a column claim as a weighted claim, the
    aligned layout in an instance's layout field, the bit order of the bytecode column stated
    at the oracle) or records for the roadmap (the order of equal-size blocks, the wall).
  - [protocol-gkr.md](reviews/protocol-gkr.md): the review of the grand-product GKR at the
    slot's schedule, definition and completeness (2026-10-02), whose findings the branch meets
    (the slot's verifier type through `Component.Front`, the generic modules' vocabulary and
    imports, the bus phase's prefix instances, the status's conditions on Layer 4's components)
    or records for the roadmap (the three blueprint asks), with the earlier review's findings
    and their fate.
  - [protocol-spine-revision.md](reviews/protocol-spine-revision.md): the review of the spine
    at the slots' schedules and errors (2026-10-02), whose findings the branch now meets (the
    Flock slot's two values, the generic schedule combinators, the refutation's core lemma, the
    citations) or records for the roadmap (the depth of the pull and count trees, the schedule
    bundle).
  - [protocol-gkr-security.md](reviews/protocol-gkr-security.md): the review of the
    grand-product GKR's knowledge soundness (2026-10-02), which found no theorem wrong, vacuous
    or tautological, and whose findings the branch meets (the security computes at `E`, the
    round refutation for every extractor and state function, the generic lemmas in their
    owners' modules, the private helpers, the documentation).
  - [protocol-gkr-security-second.md](reviews/protocol-gkr-security-second.md): an independent
    second review of the same work (2026-10-05), on the blueprint fit, the audit surface, the
    non-vacuity of the tests and readability, whose findings the branch meets (twelve lemmas
    private, the duplicated extraction and extractor gone, the unit lemma in the spine, the
    rider tests inhabited, one generic partial-point builder) but for one repeated raise kept.
  - [deployed-public-input.md](reviews/deployed-public-input.md): the review of the deployed
    check of the public-input phase (2026-10-05), whose findings the branch now meets (one
    completeness proof for both verifiers, two docstrings trimmed) or records for the adaptor
    (the two pools' agreement as a theorem).
  - [protocol-fingerprint.md](reviews/protocol-fingerprint.md): the review of the fingerprint
    and the collision bound (2026-10-05), whose findings the branch meets (a witness that the
    factor 4 is needed, the generic module free of the protocol, a smaller surface, citations).
  - [protocol-bus.md](reviews/protocol-bus.md): the review of the bus phase's definition and
    completeness (2026-10-05), whose findings the branch meets (the refutation of the check
    `R_c ≠ 0`, the lines rider documented and tested, a smaller surface, the status page) but
    for a by-hand run of the grand-product argument on the bus's leaves.

Design notes for substantive new components should be added only when there is a concrete
proposal to review. Reference files, generated sites, and report machinery should not be
created pre-emptively.
