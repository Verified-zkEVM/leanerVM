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

Design notes for substantive new components should be added only when there is a concrete
proposal to review. Reference files, generated sites, and report machinery should not be
created pre-emptively.
