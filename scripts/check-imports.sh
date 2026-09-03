#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

status=0

if ! rg --fixed-strings --line-regexp --quiet \
    "public import LeanerVMTests" tests/Main.lean; then
  echo "tests/Main.lean must import the LeanerVMTests aggregate" >&2
  status=1
fi

# Production modules must be reachable from the public library root.
while IFS= read -r file; do
  module="${file%.lean}"
  module="${module//\//.}"
  if ! rg --fixed-strings --line-regexp --quiet "public import $module" LeanerVM.lean; then
    echo "Missing from LeanerVM.lean: public import $module" >&2
    status=1
  fi
done < <(find LeanerVM -type f -name '*.lean' -print | LC_ALL=C sort)

while IFS= read -r module; do
  path="${module//./\/}.lean"
  if [[ ! -f "$path" ]]; then
    echo "Stale import in LeanerVM.lean: public import $module" >&2
    status=1
  fi
done < <(sed -n 's/^public import \([A-Za-z0-9_.]*\)$/\1/p' LeanerVM.lean)

duplicates="$(sed -n 's/^public import \([A-Za-z0-9_.]*\)$/\1/p' LeanerVM.lean | sort | uniq -d)"
if [[ -n "$duplicates" ]]; then
  echo "Duplicate public imports in LeanerVM.lean:" >&2
  echo "$duplicates" >&2
  status=1
fi

# Test modules must likewise be reachable from the configured test-library root. Lake builds the
# configured driver; it does not discover unrelated files under tests/.
while IFS= read -r file; do
  module="${file#tests/}"
  module="${module%.lean}"
  module="${module//\//.}"
  if ! rg --fixed-strings --line-regexp --quiet \
      "public import $module" tests/LeanerVMTests.lean; then
    echo "Missing from tests/LeanerVMTests.lean: public import $module" >&2
    status=1
  fi
done < <(find tests/LeanerVMTests -type f -name '*.lean' -print | LC_ALL=C sort)

while IFS= read -r module; do
  path="tests/${module//./\/}.lean"
  if [[ ! -f "$path" ]]; then
    echo "Stale import in tests/LeanerVMTests.lean: public import $module" >&2
    status=1
  fi
done < <(sed -n 's/^public import \([A-Za-z0-9_.]*\)$/\1/p' tests/LeanerVMTests.lean)

test_duplicates="$(sed -n 's/^public import \([A-Za-z0-9_.]*\)$/\1/p' \
  tests/LeanerVMTests.lean | sort | uniq -d)"
if [[ -n "$test_duplicates" ]]; then
  echo "Duplicate public imports in tests/LeanerVMTests.lean:" >&2
  echo "$test_duplicates" >&2
  status=1
fi

while IFS= read -r file; do
  echo "Test module is outside tests/LeanerVMTests/: $file" >&2
  status=1
done < <(find tests -type f -name '*.lean' \
  ! -path tests/Main.lean \
  ! -path tests/LeanerVMTests.lean \
  ! -path 'tests/LeanerVMTests/*' -print)

if [[ $status -eq 0 ]]; then
  echo "Production and test aggregate imports are complete."
fi

exit "$status"
