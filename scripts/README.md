# Scripts

- `validate.sh`: complete local gate and the command to run before handoff.
- `audit-lean.sh`: first-party lexical policy for trust-sensitive constructs and local
  option overrides.
- `audit-axioms.lean`: recursive axiom-closure audit of the production and test namespaces;
  `validate.sh` and CI run it after `lake test` through `test-axiom-audit.py`. Permits only
  `propext`, `Classical.choice` and `Quot.sound`. CI's lean-action audit independently covers
  the production namespace.
- `test-axiom-audit.py`: runs the real audit and verifies that a temporary foreign assumption
  is rejected through dependent declarations in both project namespaces. The negative
  fixture is never written into accepted source.
- `check-lean-options.py`: the audit's option scanner; recognizes whitespace, line comments,
  nested block comments and escaped option names. The lexical policy conservatively checks
  command-shaped text in comments, strings and syntax quotations too.
- `check-repository.sh`: rejects executable Lean sources, case-colliding paths, and
  trailing whitespace.
- `check-imports.sh`: verifies that `LeanerVM.lean` and `tests/LeanerVMTests.lean` list every
  production or test module exactly once and contain no stale imports.
- `check-layers.sh`: enforces the allowed Lean layer dependency direction and rejects unregistered
  production layers.
- `check-docs.py`: validates local Markdown links without third-party Python packages.
- `test-policy-checks.py`: plants isolated violations to exercise the source, aggregate-import,
  and layer gates.
- `build_timing.py`: records timed commands as JSONL and renders a Markdown summary.
- `test-build-timing.py`: exercises successful, failing, and reporting timing paths.
- `test-warning-policy.py`: checks that imported production and test leaves fail on Lean
  warnings while warning-free fixtures build under the root warning policy. Valid local overrides
  separated by line, block and nested comments build with planted warnings but fail the source audit,
  confirming why both gates are needed.
- `test-rust-contracts.py <leanVM checkout>`: archives the named Rust revision, runs its locked
  offline tests with test-only row exports, and checks actual exported fixtures in Lean. See
  [the checker guide](../docs/leanisa-checker.md) for scope and prerequisites.
- `check-upstreams.sh`: compares `upstreams.json` with current releases and branch heads;
  requires `gh`, `jq`, and network access.
- `dump-blake2s.py`: `constants` extracts the BLAKE2s `IV` and `SIGMA` tables from RFC 7693
  Appendix D for `LeanerVM/Parameters/Blake2s.lean`; `vectors` prints the `hashlib.blake2s`
  compression vectors, including the tree-mode `last_node` flag, used by
  `tests/LeanerVMTests/Semantics/Blake2s.lean`.
- `dump-blake2s-rust.sh <leanVM checkout>`: reproduces the BLAKE2S opcode cells of the pinned
  leanVM executor test `blake2s_computes_the_compression` through the executor's own
  `hash_flock` functions; requires `cargo` and a checkout at the pinned commit.
- `dump-mul-rust.sh <leanVM checkout>`: reproduces the operands and the `E` product of the
  pinned leanVM executor test `mul_192bit_word` through the executor's own `F192` arithmetic,
  as the words of `tests/LeanerVMTests/Semantics/Execution.lean`; same requirements.

Keep scripts small and deterministic. Add specialized tooling only with the feature or
artifact it validates.
