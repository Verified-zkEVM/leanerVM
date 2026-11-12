#!/usr/bin/env bash
# Write executions of compiled leanVM programs by the pinned Rust executor, one file per program,
# for `leanervm-witgen` (bench/LeanerVMWitgen.lean). The executor is the one `prove` runs
# (`Program::execute_to_floor`, its call in `prove` at crates/lean_vm/src/cpu/mod.rs:528 at
# a386121f84292f6fa663aaa3e570c15bc0240ea2), main run and fill blocks.
#
# The pinned source is unpacked with `git archive`, so the checkout's HEAD and tree are never
# touched; tests/rust/leanisa_execution.rs is added to it as the public module
# `lean_vm::cpu::leanisa_execution` (it reads the crate-private trace rows) and
# tests/rust/leanisa_execution_driver.rs as an example of `lean_compiler`. The driver compiles
# the division program of scripts/dump-proof-rust.sh, the BLAKE2s hash chain of
# crates/rec_aggregation/src/hash_chain.rs (8 compressions), every program of
# crates/lean_compiler/tests/programs with its annotated public input and witness streams, and
# Fibonacci in the exponent (crates/rec_aggregation/src/fibonacci.rs) for each `-f n`.
# With `-g`, one line is also added to `prove`, after its execution, that writes the execution
# when `LEANISA_EXECUTION_DIR` is set, and the guest test `aggregate_one_signer`
# (crates/rec_aggregation/src/aggregation.rs:3087, a leaf aggregating one XMSS signature, the
# real recursion guest crates/rec_aggregation/guests/aggregate.py) runs with it: its proof
# writes `guest_one_signer-0.exec`. No other line of the pinned source changes.
#
# The file format, one item per line: `leanisa-execution <pin> <name>`; `program <B>` and B
# instruction lines in the format of scripts/dump-proof-rust.sh (an operand is the exponent `j`
# of `g^j`); `program_hash <hex>` (the Rust bytecode digest); `filler <n>` and n lines
# `<pc> <size> <table>`; `public` and the six limbs of the two public words; `kappa <κ>` (memory
# 2^κ); `steps <n>` (main-run transitions to the sentinel, sum of `base_counts`); `cycles <n>`
# (rows including the fill); `mem_used <n>`; `unconstrained_reads <n>`; `min_log_committed <n>`
# (the prover's floor on the committed size, which the fill meets; 0 = none); `main <6 counts>`
# (`base_counts`); `rows <6 counts>` (rows per table after the fill); `memory <n>` and n lines
# `<index> <c0> <c1> <c2>`, the nonzero words of the final image, limbs in hexadecimal;
# `accessed <n>` and n cell indices some row accessed (an untrusted hint for the reader); for each
# table t = 0..5 in the order XOR, MUL, SET, DEREF, JUMP, BLAKE2S, `table <t> <n>` and its n rows
# `<pc> <fp>` as integers (the row's `g^pc`, `g^fp`), in row order; `end`. Files are compressed
# with `gzip -9 -n`.
#
# Usage: scripts/dump-execution-rust.sh [-f n]... [-g] <leanVM checkout> <output dir>
# The checkout must contain the pin. CARGO_TARGET_DIR is honoured (default: a directory beside
# the unpacked source); LEANISA_WORK names a directory to unpack into (default: a temporary one,
# removed on exit).
set -euo pipefail

pin="a386121f84292f6fa663aaa3e570c15bc0240ea2"
root="$(cd "$(dirname "$0")/.." && pwd)"
fib=()
guest=0
while getopts "f:g" opt; do
  case "$opt" in
    f) fib+=("$OPTARG") ;;
    g) guest=1 ;;
    *) echo "usage: $0 [-f n]... [-g] <leanVM checkout> <output dir>" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))
checkout="$(cd "${1:?usage: $0 [-f n]... [-g] <leanVM checkout> <output dir>}" && pwd)"
mkdir -p "${2:?usage: $0 [-f n]... [-g] <leanVM checkout> <output dir>}"
out="$(cd "$2" && pwd)"
git -C "$checkout" cat-file -e "$pin^{commit}"

if [[ -n "${LEANISA_WORK:-}" ]]; then
  work="$LEANISA_WORK"
  rm -rf "$work/source"
  mkdir -p "$work"
else
  work="$(mktemp -d)"
  trap 'rm -rf "$work"' EXIT
fi
mkdir "$work/source"
git -C "$checkout" archive --format=tar "$pin" | tar -x -C "$work/source"
src="$work/source"
lock="$(sha256sum "$src/Cargo.lock")"

cp "$root/tests/rust/leanisa_execution.rs" "$src/crates/lean_vm/src/cpu/leanisa_execution.rs"
printf '\npub mod leanisa_execution;\n' >> "$src/crates/lean_vm/src/cpu/mod.rs"
mkdir -p "$src/crates/lean_compiler/examples"
cp "$root/tests/rust/leanisa_execution_driver.rs" \
  "$src/crates/lean_compiler/examples/leanisa_execution_driver.rs"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$work/target}"

raw="$work/raw"
rm -rf "$raw"
mkdir -p "$raw"
(cd "$src" && cargo run --release --locked --offline -p lean_compiler \
  --example leanisa_execution_driver -- "$raw" ${fib[@]+"${fib[@]}"})

if [[ "$guest" == 1 ]]; then
  marker='let exec = crate::stage!("Execute program", || program.execute_to_floor(public_input));'
  grep -qF "$marker" "$src/crates/lean_vm/src/cpu/mod.rs"
  uv run --no-project --python 3.12 python - "$src/crates/lean_vm/src/cpu/mod.rs" "$marker" <<'EOF'
import sys
path, marker = sys.argv[1], sys.argv[2]
text = open(path).read()
assert text.count(marker) == 1
text = text.replace(marker, marker + "\n    leanisa_execution::hook(program, &exec, public_input);")
open(path, "w").write(text)
EOF
  (cd "$src" && LEANISA_EXECUTION_DIR="$raw" LEANISA_EXECUTION_NAME=guest_one_signer \
    cargo test --release --locked --offline -p rec_aggregation --lib \
    aggregation::tests::aggregate_one_signer -- --exact --test-threads=1)
fi

if [[ "$(sha256sum "$src/Cargo.lock")" != "$lock" ]]; then
  echo "The reference Cargo.lock changed" >&2
  exit 1
fi
for f in "$raw"/*.exec; do
  gzip -9 -n -c "$f" > "$out/$(basename "$f").gz"
  echo "$(basename "$f").gz $(stat -c %s "$f") bytes," \
    "$(stat -c %s "$out/$(basename "$f").gz") compressed"
done
