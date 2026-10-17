# Continuous integration

CI is the `leanvm-formalization` job of leanVM's Lean workflow,
[`.github/workflows/lean.yml`](../../../.github/workflows/lean.yml), beside the XMSS and SPHINCS
formalizations. It runs on a push to `main`, on a manual dispatch, and on a pull request that
changes this project, the workflow, or a leanVM source the project models: `crates/verifier`,
`python-verifier`, `crates/rec_aggregation/guests`, `crates/leanvm_core` and `crates/lean_da`.
A pull request that changes none of them skips it, which branch protection counts as passed, so
it can be a required check.

Its steps, each named so that a failure stays legible:

| Step | Responsibility |
| --- | --- |
| Source and repository policy | `audit-lean.sh`, `check-repository.sh`, and the planted violations of `test-policy-checks.py` |
| Imports and layers | `check-imports.sh` and `check-layers.sh`: the aggregate imports are complete and the architecture DAG holds |
| Documentation | `check-docs.py`: no broken or unsafe local Markdown link |
| Build and tests | lean-action's `lake build` and `lake test`, with its kernel axiom audit of `LeanerVM`, then `lake exe node-vectors`: the checks of the Rust vectors too costly to interpret |
| Axioms and warnings | `test-axiom-audit.py` with its negative control, `tests/Main.lean` elaborated with warnings as errors, and `test-warning-policy.py` |
| Rust-vs-Lean differential | `fuzz-verifier.py` on `tests/fixtures/verifier`: the Lean verifier and the containing commit's Rust verifier give the same verdict on every committed proof and on every mutation of it |

The differential is what ties the project to the containing commit: a change to the Rust
verifier's accepted language fails it until the Lean verifier follows. A change to the prover
that alters proofs leaves the committed fixtures as they are; regenerate them with
`scripts/export-verifier-fixtures-rust.sh` when it should.

`.lake` is cached without Mathlib's build, which `lake exe cache get` fetches; only `main` saves
the cache, and every branch restores it.

leanerVM's informational workflows (build timing, the automated PR summary and review, upstream
drift, and Dependabot) are not part of leanVM. `scripts/build_timing.py` and
`scripts/check-upstreams.sh` still run locally.

Project releases are milestone-driven. A Lean toolchain update is an ordinary reviewed dependency
change and does not create or move a release tag.

Native/FFI isolation, CUDA, generated-blueprint, and VM-runtime benchmark jobs are deliberately
absent. Add each only alongside the artifact it protects. Runtime benchmarks should follow the
contract in [../bench/README.md](../bench/README.md).
