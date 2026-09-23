#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

./scripts/audit-lean.sh
./scripts/check-repository.sh
./scripts/check-imports.sh
./scripts/check-layers.sh
python3 ./scripts/check-docs.py
python3 ./scripts/test-policy-checks.py
python3 ./scripts/test-build-timing.py
python3 ./scripts/test-warning-policy.py
# Plain `lake build`, as in CI: no `--wfail`, so CompPoly's release lookup may warn at its
# untagged pin and Lake's caches stay enabled. Package-level `warningAsError` still rejects
# every first-party elaboration warning, including imported leaves. See docs/dependencies.md.
lake build
lake test
python3 ./scripts/test-axiom-audit.py
lake env lean -E warning tests/Main.lean
