# Development

## Python tooling

Install [uv](https://docs.astral.sh/uv/getting-started/installation/) for
all repository Python entry points, including validation scripts and CI.
CI uses uv 0.13.6. The uv commands below select Python
3.12; uv downloads it if needed. Run them from the repository root.
These checks use only the standard library. `--no-project` runs them without
installing a Python package or creating a project environment.

## Validation

Run the full local gate:

```sh
./scripts/validate.sh
```

Focused checks:

```sh
lake build
lake test
./scripts/audit-lean.sh
./scripts/check-repository.sh
./scripts/check-imports.sh
./scripts/check-layers.sh
uv run --no-project --python 3.12 python ./scripts/check-docs.py
uv run --no-project --python 3.12 python ./scripts/test-policy-checks.py
uv run --no-project --python 3.12 python ./scripts/test-build-timing.py
lake env lean -E warning tests/Main.lean
```

`scripts/check-upstreams.sh` additionally requires `gh`, `jq`, and network access.

The full local gate runs the production-and-test namespace axiom audit after `lake test`.
To run the audit and its negative control on their own:

```sh
uv run --no-project --python 3.12 python scripts/test-axiom-audit.py
```

This recursively inspects declaration dependencies and permits only `propext`,
`Classical.choice` and `Quot.sound`. It is distinct from `audit-lean.sh`'s lexical policy
and CI's independent production-only lean-action audit. The negative control checks
transitive rejection through production and test declarations in a temporary fixture.

## Adding a production module

1. Choose its owner layer using `docs/architecture.md`.
2. Use Lean's module syntax and a module docstring. Clean and ArkLib both use the module
   system; `CONTRIBUTING.md` describes visibility and the classic test convention.
3. Keep imports narrow and respect the CI-enforced layer DAG.
4. Add an `import` line to `LeanerVM.lean`.
5. Add executable or proof-regression coverage under `tests/LeanerVMTests/` and import it from
   `tests/LeanerVMTests.lean`.
6. Run the complete validator.

The production and test aggregate checks are intentionally dependency-free; they do not require
Mathlib's `mk_all` utility before Mathlib exists in the Lake graph.

`lake test` builds the `LeanerVMTests` library, so a test is anything that fails elaboration: a
compiled `#guard` or a kernel-checked `example` (see [`tests/README.md`](../tests/README.md) for
the module-system caveats). There is no test executable (finding P3 in
[`docs/roadmap/leanisa-status.md`](roadmap/leanisa-status.md)).

## Benchmarks

`lakefile.toml` declares the benchmark source `bench/LeanerVMBench.lean` twice: as the library
`LeanerVMBench`, a default target, so that `lake build` and the validator elaborate it without
linking, and as the executable `leanervm-bench`, which is not a default target, because linking an
executable compiles every transitive module, Mathlib's included, to C. Both are build targets of
this package, not dependencies, so adding or changing them needs none of the review in
[dependencies.md](dependencies.md).

```sh
lake build leanervm-bench
.lake/build/bin/leanervm-bench [percent] [arith|sumcheck|provers|all] [filter]
.lake/build/bin/leanervm-bench 1 protocol [bus|table|pub|flock|whole] [lm] [spec]
```

The object files land in each package's own `.lake/build`. A worktree that shares its
`.lake/packages` with another checkout should build the executable on a private copy of the
packages. See [`bench/README.md`](../bench/README.md) for the workloads and the recorded
timings.

## CI

Build/test, repository policy, architectural imports, and documentation links are separate
checks so branch protection and failures remain legible. Build timing is intentionally
informational. See [ci.md](ci.md) for the complete workflow inventory and repository setup.
