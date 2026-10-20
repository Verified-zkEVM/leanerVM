#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

paths=()
for path in LeanerVM LeanerVM.lean tests cli; do
  [[ -e "$path" ]] && paths+=("$path")
done
# Constructs that add axioms or bypass the kernel or the compiler's proved code: `decide +native`
# and `native_decide` trust the compiler, `implemented_by`/`extern` replace compiled code without a
# proof, `addDecl`-style metaprograms and `ofReduceBool`/`trustCompiler` sidestep the kernel.
pattern='\b(axiom|sorry|admit|unsafe|native_decide|implemented_by|extern|addDecl|addAndCompile|ofReduceBool|trustCompiler)\b|\+native\b'

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
