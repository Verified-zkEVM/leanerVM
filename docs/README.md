# Documentation

This directory contains stable project and operating knowledge.

- [architecture.md](architecture.md): Lean layers, dependency direction, and criteria for
  adding native or acceleration code.
- [dependencies.md](dependencies.md): version pins and dependency update policy.
- [leanvm-target.md](leanvm-target.md): audited target revision, legacy comparison, and
  proof-obligation coverage.
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
    ArkLib — scope, dependency contracts and the ArkLib ledger, pinned conventions, the fourteen
    layers from the M3 relation to the executable verifier, acceptance tests, and public
    interfaces.
  - [protocol-status.md](roadmap/protocol-status.md): where the proof-system roadmap stands —
    layer coverage, the frontier, the upstream ledger, pending decisions, open findings, and the
    survey record.
- [reviews/](reviews/): review documents handed off for implementation, one per reviewed piece
  of work; the status file records how each finding was met.
  - [leanisa-layer6-tables.md](reviews/leanisa-layer6-tables.md): the review of the Layer 6
    table contracts (2026-09-14), whose findings the tables now meet (status finding F8).
- [design/](design/): design notes for substantive components, each a concrete proposal to
  review before its layers are built.
  - [blake2s-flock-boundary.md](design/blake2s-flock-boundary.md): how the `K`-valued `BLAKE2S`
    table, Flock's Boolean R1CS and ring switching are reconciled in Lean: the packing bijection,
    the circuit and its R1CS, the bridge to `Blake2sRelation`, the changes to the two roadmaps,
    the alternatives rejected, and the decisions requested.

Design notes for substantive new components should be added only when there is a concrete
proposal to review. Reference files, generated sites, and report machinery should not be
created pre-emptively.
