#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

status=0
import_prefix='^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import([[:space:]]+all)?[[:space:]]+'

check_forbidden() {
  local path="$1"
  local layers="$2"
  local label="$3"
  local pattern="${import_prefix}LeanerVM\.(${layers})(\.|$)"
  local matches

  if matches="$(rg --line-number --glob '*.lean' "$pattern" "$path")"; then
    echo "Forbidden $label dependency:" >&2
    echo "$matches" >&2
    status=1
  else
    local rg_status=$?
    if [[ $rg_status -ne 1 ]]; then
      exit "$rg_status"
    fi
  fi
}

check_forbidden LeanerVM/Parameters \
  'Semantics|Arithmetization|Applications|Protocol' 'Parameters'
check_forbidden LeanerVM/Semantics \
  'Arithmetization|Applications|Protocol' 'Semantics'
check_forbidden LeanerVM/Arithmetization \
  'Applications|Protocol' 'Arithmetization'

if [[ -d LeanerVM/Applications ]]; then
  check_forbidden LeanerVM/Applications \
    'Arithmetization|Protocol' 'Applications'
fi

allowed_layers='^(Applications|Arithmetization|Parameters|Protocol|Semantics)$'
while IFS= read -r entry; do
  name="${entry#LeanerVM/}"
  if [[ -d "$entry" ]]; then
    if [[ ! "$name" =~ $allowed_layers ]] && \
        find "$entry" -type f -name '*.lean' -print -quit | rg --quiet .; then
      echo "Unknown production layer containing Lean modules: $entry" >&2
      status=1
    fi
  elif [[ "$entry" == *.lean ]]; then
    echo "Production module must belong to a registered layer: $entry" >&2
    status=1
  fi
done < <(find LeanerVM -mindepth 1 -maxdepth 1 -print | LC_ALL=C sort)

if [[ $status -eq 0 ]]; then
  echo "Lean layer dependencies respect the architecture DAG."
fi

exit "$status"
