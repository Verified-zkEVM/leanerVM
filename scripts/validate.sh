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
# `--no-cache`: Lake's release lookup for CompPoly warns at an untagged pin and `--wfail`
# would fail a fresh checkout. See docs/dependencies.md.
lake build --wfail --no-cache
lake test
lake env lean -E warning tests/Main.lean
