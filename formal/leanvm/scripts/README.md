# Scripts

- `validate.sh`: complete local gate and the command to run before handoff.
- `audit-lean.sh`: first-party lexical policy for trust-sensitive constructs and local
  option overrides.
- `audit-axioms.lean`: recursive axiom-closure audit of every declaration a first-party module
  defines, whatever its namespace;
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
The scripts that read leanVM read the repository they sit in. Those that cite an older leanVM
commit, whose crates have since been renamed, build that commit from a `git archive` of it, so
they need a clone with history; the others read the containing commit.

- `test-rust-contracts.py [leanVM clone]`: archives the named Rust revision, runs its locked
  offline tests with test-only row exports, and checks actual exported fixtures in Lean. See
  [the checker guide](../docs/leanisa-checker.md) for scope and prerequisites.
- `check-upstreams.sh`: compares `upstreams.json` with current releases and branch heads;
  requires `gh`, `jq`, and network access.
- `dump-blake2s.py`: `constants` extracts the BLAKE2s `IV` and `SIGMA` tables from RFC 7693
  Appendix D for `LeanerVM/Parameters/Blake2s.lean`; `vectors` prints the `hashlib.blake2s`
  compression vectors, including the tree-mode `last_node` flag, used by
  `tests/LeanerVMTests/Semantics/Blake2s.lean`.
- `dump-blake2s-rust.sh`: reproduces the BLAKE2S opcode cells of the leanVM executor test
  `blake2s_computes_the_compression` at `a386121f` through the executor's own `hash_flock`
  functions; requires `cargo`.
- `dump-mul-rust.sh`: reproduces the operands and the `E` product of the leanVM executor test
  `mul_192bit_word` at `a386121f` through the executor's own `F192` arithmetic, as the words of
  `tests/LeanerVMTests/Semantics/Execution.lean`; requires `cargo`.
- `dump-flock-column-rust.sh`: digests the Flock region the prover at `a386121f` commits for
  eight compressions (the executor test's, the RFC 7693 `"abc"` one and six padding blocks), for
  the differential check of the honest column in `tests/LeanerVMTests/Protocol/FlockSpec.lean`;
  requires `cargo`.
- `dump-flock-circuit-digest.py`: digests the rows of the Flock BLAKE2s circuit as the Python
  verifier's `blake2s_row_values` walks them, for the row-for-row comparison in
  `tests/LeanerVMTests/Protocol/Blake2sCircuit.lean`; requires only Python.
- `dump-leanisa-layout-rust.sh`: prints the stacked size and every column's offset in the stack
  the verifier at `a386121f` reconstructs for two announced size vectors, for the comparison in
  `tests/LeanerVMTests/Protocol/LeanIsa.lean`; requires `cargo`.

- `export-verifier-fixtures-rust.sh <out>`: proves small guest programs with the Rust prover and
  writes each proof as the four files `bytecode.bin`, `public_input.bin`, `stream.bin`,
  `merkle_openings.bin` (the fixtures of `tests/fixtures/verifier/`), each checked by the Rust
  verifier first; requires `cargo`.
- `rust-verifier-cli/`: the deployed Rust verifier (`crates/verifier`) on the same four files,
  one proof or a batch (see its `README.md`).
- `fuzz-verifier.py <fixtures>`: mutates the fixtures (structured and seeded random edits of
  every phase's scalars, roots, nonces, Merkle openings, public input and bytecode) and requires
  `lake exe leanvm-verify` and the Rust verifier to give the same verdict on every mutated proof;
  keeps any divergent case. CI runs it on `tests/fixtures/verifier`.

Keep scripts small and deterministic. Add specialized tooling only with the feature or
artifact it validates.
