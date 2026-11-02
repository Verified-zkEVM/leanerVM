#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

./scripts/audit-lean.sh
./scripts/check-repository.sh
./scripts/check-imports.sh
./scripts/check-layers.sh
uv run --no-project --python 3.12 python ./scripts/check-docs.py
uv run --no-project --python 3.12 python ./scripts/test-policy-checks.py
uv run --no-project --python 3.12 python ./scripts/test-build-timing.py
uv run --no-project --python 3.12 python ./scripts/test-warning-policy.py
# Plain `lake build`, as in CI: no `--wfail`, so dependency release lookups may warn and
# Lake's caches stay enabled. Package-level `warningAsError` still rejects
# every first-party elaboration warning, including imported leaves. See docs/dependencies.md.
lake build
lake test
uv run --no-project --python 3.12 python ./scripts/test-axiom-audit.py
lake env lean -E warning tests/Main.lean
