#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

paths=(LeanerVM LeanerVM.lean tests)
pattern='\b(axiom|sorry|admit|unsafe|native_decide)\b'

if matches="$(rg --line-number --glob '*.lean' "$pattern" "${paths[@]}")"; then
  echo "Forbidden trust-sensitive Lean construct found:" >&2
  echo "$matches" >&2
  exit 1
else
  status=$?
  if [[ $status -ne 1 ]]; then
    exit "$status"
  fi
fi

# Lean also permits line comments and nested block comments between these tokens.
python3 ./scripts/check-lean-options.py "${paths[@]}"

echo "First-party Lean source policy passed."
