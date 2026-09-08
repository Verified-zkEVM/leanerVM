# Development

## Validation

Run the full local gate:

```sh
./scripts/validate.sh
```

Focused checks:

```sh
lake build --wfail
lake test
./scripts/audit-lean.sh
./scripts/check-repository.sh
./scripts/check-imports.sh
./scripts/check-layers.sh
python3 ./scripts/check-docs.py
python3 ./scripts/test-policy-checks.py
python3 ./scripts/test-build-timing.py
lake env lean -E warning tests/Main.lean
```

`scripts/check-upstreams.sh` additionally requires `gh`, `jq`, and network access.

## Adding a production module

1. Choose its owner layer using `docs/architecture.md`.
2. Use Lean's module syntax and a module docstring, unless the file imports Clean or a file
   that does; `CONTRIBUTING.md` explains when a file is plain instead.
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

## CI

Build/test, repository policy, architectural imports, and documentation links are separate
checks so branch protection and failures remain legible. Build timing is intentionally
informational. See [ci.md](ci.md) for the complete workflow inventory and repository setup.
