#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

outdated=0

while IFS=$'\t' read -r name repository tracking current_ref current_commit; do
  if [[ "$tracking" == "release" ]]; then
    latest_ref="$(gh api "repos/${repository}/releases/latest" --jq .tag_name)"
    if [[ "$latest_ref" != "$current_ref" ]]; then
      printf '%s: configured %s, latest release %s\n' "$name" "$current_ref" "$latest_ref"
      outdated=1
    else
      printf '%s: current at %s\n' "$name" "$current_ref"
    fi
  else
    latest_commit="$(gh api "repos/${repository}/commits/${current_ref}" --jq .sha)"
    if [[ "$latest_commit" != "$current_commit" ]]; then
      printf '%s: configured %.12s, %s is %.12s\n' \
        "$name" "$current_commit" "$current_ref" "$latest_commit"
      outdated=1
    else
      printf '%s: current at %.12s\n' "$name" "$current_commit"
    fi
  fi
done < <(jq -r \
  'to_entries[] | [.key, .value.repository, .value.tracking, .value.ref, .value.commit] | @tsv' \
  upstreams.json)

exit "$outdated"
