#!/usr/bin/env bash
# Checks out leanVM at the commit in `leanvm-rev` into `.leanvm/`, fetching that commit alone,
# with its `formal/lean_vm` a link to this repository's `lean_vm`: leanVM's Rust tests that
# check and rewrite the Lean data (`guest_bytecode_lean`, `guest_source_lean`,
# `node_spec_vectors`) then read and write the copy here, and lean_vm's scripts find the
# Rust and Python verifiers, the prover and the guests at `.leanvm/`. Idempotent; prints the tree.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
rev="$(tr -d '[:space:]' < "$root/leanvm-rev")"
tree="$root/.leanvm"

if [ ! -d "$tree/.git" ]; then
  git init -q "$tree"
  git -C "$tree" remote add origin https://github.com/leanEthereum/leanVM.git
fi
if [ "$(git -C "$tree" rev-parse -q --verify 'HEAD^{commit}' || true)" != "$rev" ]; then
  git -C "$tree" fetch -q --depth=1 origin "$rev"
  git -C "$tree" checkout -q --force --detach "$rev"
fi
# leanVM's own copy of the formalization gives way to this one.
if [ ! -L "$tree/formal/lean_vm" ]; then
  rm -rf "$tree/formal/lean_vm"
  ln -s ../../lean_vm "$tree/formal/lean_vm"
fi
echo "$tree"
