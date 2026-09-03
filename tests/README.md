# Tests

Executable Lean tests live here and are run by `lake test`. `Main.lean` imports the
`LeanerVMTests.lean` aggregate, which imports every test module and checks the production public
module graph. `scripts/check-imports.sh` rejects missing, stale, or duplicate test imports.

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
