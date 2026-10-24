#!/usr/bin/env bash
# Builds and checks the four Lake projects as .github/workflows/lean.yml does, one after another,
# each in its own directory with its own manifest, then lean_vm against leanVM at `leanvm-rev`
# (`leanvm`, which needs cargo). `lake build` at the root runs it.
#
#   ./check-all.sh [lean_rpm] [lean_xmss] [lean_sphincs] [lean_da] [lean_vm] [leanvm]   (default: all six)
#
# The compiled checks and `lean` run under a virtual-memory cap of LEAN_VMEM_KB (default 40 GB);
# `lake` itself cannot, as it reserves about 1 GB of address space per job. WIDTH is passed to
# lean_vm/scripts/ci-build.py, the modules it builds at once (default 2).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
log=$(mktemp -d)
trap 'rm -rf "$log"' EXIT

step() { printf '\n==> %s\n' "$*"; }
fail() { echo "error: $*" >&2; exit 1; }
capped() { (ulimit -v "${LEAN_VMEM_KB:-40000000}"; exec "$@"); }

# No `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by` or `#exit` outside comments.
no_escapes() {
  step "$1: forbid proof escapes"
  if grep -rnE '\b(sorry|sorryAx|admit|native_decide|unsafe|implemented_by)\b|#exit' \
      --include='*.lean' --exclude-dir=.lake "$1" | grep -vE ':[0-9]+: *(--|/-)'; then
    fail "$1: proof escape"
  fi
}

# `lake build` in $1, then no deprecation warning from the modules matching $2. Lake replays a
# cached module's warnings, so the log lists every one.
build() {
  step "$1: lake build"
  (cd "$1" && lake build 2>&1) | tee "$log/build.txt"
  if grep -E "^warning: $2.*has been deprecated" "$log/build.txt"; then
    fail "$1: deprecated API"
  fi
}

# Each theorem after the module $2 depends on Lean's three axioms only, asked from outside.
axioms() {
  local dir=$1 module=$2 t; shift 2
  step "$dir: axiom footprint"
  { echo "import $module"; for t in "$@"; do echo "#print axioms $t"; done; } > "$log/axioms.lean"
  (cd "$dir" && capped lake env lean "$log/axioms.lean") | tee "$log/axioms.txt"
  for t in "$@"; do
    grep -qF "'$t' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log/axioms.txt" \
      || fail "$dir: $t depends on more axioms"
  done
}

lean_rpm() {
  no_escapes lean_rpm
  (cd lean_rpm && lake exe cache get)
  build lean_rpm 'LeanRpm'
  axioms lean_rpm LeanRpm LeanRpm.indifferentiability LeanRpm.transfer LeanRpm.transfer2 \
    LeanRpm.keccak256_indifferentiable LeanRpm.keccak256_transfer LeanRpm.keccak256_transfer2 \
    LeanRpm.SufCma.rpm_le_rom LeanRpm.SufCma.rpm_bound LeanRpm.SufCma.rpm_bound_perm \
    LeanRpm.Duplex.duplex_le
}

lean_xmss() {
  no_escapes lean_xmss
  (cd lean_xmss && lake exe cache get)
  build lean_xmss '(LeanXmss|XmssSecurity)'
  axioms lean_xmss XmssSecurity XmssSecurity.leanXmss_has_127_bits_of_classical_security \
    XmssSecurity.leanXmss_rpm_security XmssSecurity.leanXmss_rpm_security_calls
}

lean_sphincs() {
  no_escapes lean_sphincs
  (cd lean_sphincs && lake exe cache get)
  # The kernel-checked tables (`decide +kernel`) one at a time: the largest takes most of the memory.
  local m
  for m in Sphincs.H0FTab Sphincs.H0PTab Sphincs.H0NTab Sphincs.LifetimeCertificates; do
    step "lean_sphincs: lake build $m"
    (cd lean_sphincs && lake build "$m")
  done
  build lean_sphincs 'Sphincs(Fors|Base)?/'
  axioms lean_sphincs Sphincs Sphincs.Lifetimes.requestedSecurity \
    Sphincs.Lifetimes.requestedSecurityRpm Sphincs.Lifetimes.requestedSecurityRpmCalls
}

lean_da() {
  no_escapes lean_da
  (cd lean_da && lake exe cache get)
  build lean_da '(LeanDa|PqDas)'
  axioms lean_da LeanDa LeanDa.leanDa_perfectlyComplete LeanDa.leanDa_positionBinding \
    LeanDa.leanDa_codeBinding LeanDa.checker_sound LeanDa.commitCodewords_eq_commitCells \
    LeanDa.dualCodeword_eq_dual LeanDa.membershipVector_eq_dual \
    LeanDa.leanDa_positionBinding_rpm LeanDa.leanDa_codeBinding_rpm \
    LeanDa.leanDa_codeBinding_rpm_bound
}

lean_vm() {
  no_escapes lean_vm
  step "lean_vm: keep the specification apart from the proofs"
  if grep -rnE '^(public )?import LeanVM\.' lean_vm/LeanVM/Spec | grep -vE 'import LeanVM\.Spec\.'; then
    fail "lean_vm: LeanVM/Spec imports the proofs"
  fi
  (cd lean_vm && lake exe cache get)
  # Fails on any warning and on an axiom footprint beyond Lean's three (`LeanVM.lean`).
  step "lean_vm: build, a few modules at a time"
  (cd lean_vm && python3 -I scripts/ci-build.py)
  step "lean_vm: lake test"
  (cd lean_vm && lake test)
  step "lean_vm: the Rust vectors' costly checks, compiled"
  (cd lean_vm && lake build node-vectors guest-core guest-cert guest-memory && capped .lake/build/bin/node-vectors)
  step "lean_vm: the guest's core IR data is current"
  (cd lean_vm && capped .lake/build/bin/guest-core --check)
  step "lean_vm: the guest's certificates are current"
  (cd lean_vm && capped .lake/build/bin/guest-cert --check)
  step "lean_vm: the guest's memory-layer checks are current"
  (cd lean_vm && capped .lake/build/bin/guest-memory --check)
}

# Against leanVM at `leanvm-rev`, checked out by leanvm-tree.sh with its `formal/lean_vm` a link to
# lean_vm: the guest's data is the one leanVM's sources give, and the Lean and Rust verifiers agree
# on the fixtures and their mutations.
leanvm() {
  command -v cargo > /dev/null || fail "leanvm: needs cargo; name the other projects to skip it"
  local tree
  tree=$(./leanvm-tree.sh)
  step "leanvm: the guest's data is leanVM's"
  cargo build --release --manifest-path lean_vm/scripts/guest-export/Cargo.toml
  capped lean_vm/scripts/guest-export/target/release/guest-export lean_vm --check
  step "leanvm: the honest hints are the Rust's, and the guest runs on them (guest-diff)"
  local gd
  gd=$(mktemp -d)
  (cd lean_vm && LEANVM_GUEST_DIFF="$gd" cargo test --release \
    --manifest-path scripts/guest-export/Cargo.toml --lib guest_diff -- --ignored)
  (cd lean_vm && lake build guest-diff && capped .lake/build/bin/guest-diff "$gd"/*.txt)
  rm -rf "$gd"
  step "leanvm: Rust-vs-Lean differential"
  (cd lean_vm && lake build leanvm-verify)
  cargo build --release --manifest-path lean_vm/scripts/rust-verifier-cli/Cargo.toml
  (cd lean_vm && python3 -I scripts/fuzz-verifier.py tests/fixtures/verifier --jobs 4)
}

projects=("$@")
[ ${#projects[@]} -gt 0 ] || projects=(lean_rpm lean_xmss lean_sphincs lean_da lean_vm leanvm)
for p in "${projects[@]}"; do
  case $p in
    lean_rpm | lean_xmss | lean_sphincs | lean_da | lean_vm | leanvm) "$p" ;;
    *) fail "unknown project $p" ;;
  esac
done
step "all checks passed: ${projects[*]}"
