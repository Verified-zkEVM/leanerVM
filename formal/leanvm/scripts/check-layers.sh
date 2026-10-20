#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

status=0
import_prefix='^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import([[:space:]]+all)?[[:space:]]+'

# A layer's modules: its directory, and its root module `LeanerVM/<Layer>.lean` when there is one.
check_forbidden() {
  local path="$1"
  local layers="$2"
  local label="$3"
  local pattern="${import_prefix}LeanerVM\.(${layers})(\.|$)"
  local matches
  local paths=()

  [[ -e "$path" ]] && paths+=("$path")
  [[ -f "$path.lean" ]] && paths+=("$path.lean")
  [[ ${#paths[@]} -eq 0 ]] && return 0

  if matches="$(rg --line-number --glob '*.lean' "$pattern" "${paths[@]}")"; then
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

# The specification imports nothing of the rest of the repository: it is what a reviewer reads.
check_spec() {
  local pattern="${import_prefix}LeanerVM\.([A-Za-z]+)"
  local matches
  if matches="$(rg --line-number --glob '*.lean' "$pattern" LeanerVM/Spec)"; then
    while IFS= read -r match; do
      if [[ ! "$match" =~ import([[:space:]]+all)?[[:space:]]+LeanerVM\.Spec(\.|[[:space:]]|$) ]]; then
        echo "Forbidden Spec dependency outside LeanerVM/Spec: $match" >&2
        status=1
      fi
    done <<< "$matches"
  else
    local rg_status=$?
    if [[ $rg_status -ne 1 ]]; then
      exit "$rg_status"
    fi
  fi
}

if [[ -d LeanerVM/Spec ]]; then
  check_spec
fi

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

# The wall of the proof system: a module of the protocol layer is written over an abstract
# instance and imports nothing from the arithmetization, except the modules whose business the
# arithmetization is: the fixed columns, the adaptor, the compiled verifier and the base
# theorems, the end-to-end theorems under `EndToEnd/` among them.
check_wall() {
  local allowed='^LeanerVM/Protocol/(FixedColumns|LeanIsa(/[A-Za-z]+)?|EndToEnd(/[A-Za-z]+)+|Transcript|Proof|Compile|Verify|Soundness)\.lean$'
  local pattern="${import_prefix}LeanerVM\.Arithmetization(\.|$)"
  local matches

  if matches="$(rg --line-number --glob '*.lean' "$pattern" LeanerVM/Protocol)"; then
    while IFS= read -r match; do
      if [[ ! "${match%%:*}" =~ $allowed ]]; then
        echo "Forbidden Protocol dependency on the arithmetization (the wall): $match" >&2
        status=1
      fi
    done <<< "$matches"
  else
    local rg_status=$?
    if [[ $rg_status -ne 1 ]]; then
      exit "$rg_status"
    fi
  fi
}

if [[ -d LeanerVM/Protocol ]]; then
  check_wall
fi

allowed_layers='^(Applications|Arithmetization|Parameters|Protocol|Semantics|Spec)$'
while IFS= read -r entry; do
  name="${entry#LeanerVM/}"
  if [[ -d "$entry" ]]; then
    if [[ ! "$name" =~ $allowed_layers ]] && \
        find "$entry" -type f -name '*.lean' -print -quit | rg --quiet .; then
      echo "Unknown production layer containing Lean modules: $entry" >&2
      status=1
    fi
  elif [[ "$entry" == *.lean && ! "${name%.lean}" =~ $allowed_layers ]]; then
    echo "Production module must belong to a registered layer: $entry" >&2
    status=1
  fi
done < <(find LeanerVM -mindepth 1 -maxdepth 1 -print | LC_ALL=C sort)

if [[ $status -eq 0 ]]; then
  echo "Lean layer dependencies respect the architecture DAG."
fi

exit "$status"
