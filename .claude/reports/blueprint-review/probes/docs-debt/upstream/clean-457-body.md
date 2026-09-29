## Summary

- Upgrade Lean and Mathlib from v4.32.2 to v4.33.1, the newest stable release.
- Use the canonical scoped Lake dependency syntax and refresh the transitive manifest.
- Adapt explicit circuit metadata and proofs to Lean 4.33 while preserving semantic subcircuit boundaries.
- Simplify several proof paths, including Addition32Full, FemtoCairo, BLAKE3 ApplyRounds, and SHA-256, without raising resource limits.
- Add ArkLib's release-tag workflow so changes to `lean-toolchain` on `main` or `master` create the corresponding Lean release tag.

## Proof-regression guardrails

- No new sorry or admit declarations.
- No maxHeartbeats or maxRecDepth changes.
- Child gadgets remain bundled subcircuits; new abstraction boundaries use FormalCircuit or ElaboratedCircuit metadata.
- Existing test-only sorry fixtures are unchanged.

## Validation

- `lake build --wfail`
- `lake build CleanTests`
- `python3 scripts/check-consecutive-empty-lines.py`
- `cargo test --release -- --nocapture test_lean_circuit_end_to_end`
- `cargo test test_tampered_multiplicity`
- `cargo test --release test_tampered_multiplicity`
- `cargo test --release -- --nocapture test_femtocairo`
- `git diff origin/main --check`
