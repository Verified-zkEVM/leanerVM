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

if matches="$(rg --line-number --glob '*.lean' \
    'set_option (autoImplicit|relaxedAutoImplicit|linter\.|weak\.linter\.)' "${paths[@]}")"; then
  echo "Repository-wide Lean options must not be overridden in source files:" >&2
  echo "$matches" >&2
  exit 1
else
  status=$?
  if [[ $status -ne 1 ]]; then
    exit "$status"
  fi
fi

echo "First-party Lean source policy passed."
