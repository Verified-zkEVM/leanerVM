#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

status=0

executable_lean="$(git ls-files -s '*.lean' | awk '$1 == "100755" { print $4 }')"
if [[ -n "$executable_lean" ]]; then
  echo "Lean source files must not be executable:" >&2
  echo "$executable_lean" >&2
  status=1
fi

case_clashes="$(git ls-files | LC_ALL=C sort --ignore-case | uniq -D --ignore-case)"
if [[ -n "$case_clashes" ]]; then
  echo "Tracked paths with case-insensitive name collisions:" >&2
  echo "$case_clashes" >&2
  status=1
fi

if trailing="$(git grep --line-number --perl-regexp '[\t ]+$' -- \
    '*.lean' '*.md' '*.sh' '*.toml' '*.yml' '*.yaml' '*.json')"; then
  echo "Tracked text files contain trailing whitespace:" >&2
  echo "$trailing" >&2
  status=1
else
  grep_status=$?
  if [[ $grep_status -ne 1 ]]; then
    exit "$grep_status"
  fi
fi

if [[ $status -eq 0 ]]; then
  echo "Repository hygiene checks passed."
fi

exit "$status"
