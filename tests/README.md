# Tests

Lean tests live here and are run by `lake test`, which builds the `LeanerVMTests` library: every
test is a `#guard` (compiled evaluation) or an `example` (kernel check) that fails the build.
`Main.lean` imports the `LeanerVMTests.lean` aggregate, which imports every test module and
checks the production public module graph; `scripts/validate.sh` elaborates it with warnings as
errors. There is no test executable: a binary linking CompPoly's `BF64` module is killed at
startup evaluating its `Fintype BF64` instance (finding P3 in
[`docs/roadmap/leanisa-status.md`](../docs/roadmap/leanisa-status.md)).
`scripts/check-imports.sh` rejects missing, stale, or duplicate test imports. The aggregate and
`Main.lean` are plain files because `LeanerVM.lean` is one (see `CONTRIBUTING.md`); a test
module may be a `module` or plain, and a plain one can decide `E` arithmetic in the kernel,
which a `module` cannot.

As executable definitions arrive, add focused unit, differential, and mutation tests here.
Put their modules under `tests/LeanerVMTests/` and import each one from `LeanerVMTests.lean`.
Tests must not be imported by the production `LeanerVM/` library.

Implementation-validation tests should run identical versioned workloads through the Lean
reference and a pinned Rust leanVM revision, comparing decoding, state transitions, outputs,
traces, encodings, and rejection behavior as each surface becomes available. Optimized native,
Rust FFI, CUDA, and future compiled paths use the same fixtures. These tests establish observed
agreement, not a formal theorem about the foreign implementation.

The initial target suite should cover all six opcodes, write-once conflicts, invalid generator-
power addresses, branch state, BLAKE2s counter/finalization metadata, public-input encoding, and
prover-supplied cells. Guest-level fixtures should separately cover XMSS epoch groups, SPHINCS
`(key, message)` claims, overlaps, conflicting messages, omitted coverage, child mappings, and
deferred-claim rejection. Bind vectors to the revision in
[`docs/leanvm-target.md`](../docs/leanvm-target.md).
