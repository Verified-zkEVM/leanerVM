#!/usr/bin/env bash
# Print the stack layout the pinned leanVM verifier reconstructs for two announced size vectors:
# the stacked size `mu` and, for every column in global order, its offset in the stack, or `V`
# for a virtual column (`lean_vm::cpu::layout`, crates/lean_vm/src/cpu/layout.rs and
# crates/lean_vm/src/witness.rs at a386121f84292f6fa663aaa3e570c15bc0240ea2). The program is four
# `XOR` instructions, so the bytecode's log-size is 2. The output is compared with the Lean
# layout in tests/LeanerVMTests/Protocol/LeanIsa.lean.
#
# Usage: scripts/dump-leanisa-layout-rust.sh <path to a leanVM checkout at the pin>
set -euo pipefail

pin="a386121f84292f6fa663aaa3e570c15bc0240ea2"
checkout="$(cd "${1:?usage: $0 <leanVM checkout>}" && pwd)"
head="$(git -C "$checkout" rev-parse HEAD)"
if [[ "$head" != "$pin" ]]; then
  echo "leanVM checkout is at $head, not the pin $pin" >&2
  exit 1
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/src"
cp "$checkout/Cargo.lock" "$work/Cargo.lock"

cat > "$work/Cargo.toml" <<EOF
[package]
name = "dump-leanisa-layout"
version = "0.0.0"
edition = "2024"

[dependencies]
lean_vm = { path = "$checkout/crates/lean_vm" }
primitives = { path = "$checkout/crates/primitives" }
EOF

cat > "$work/src/main.rs" <<'EOF'
use lean_vm::cpu::{layout, Op};
use primitives::field::F192;

fn main() {
    let prog = vec![Op::Xor { a: 0, b: 0, c: 0 }; 4];
    let pi = [F192::new(0, 0, 0), F192::new(0, 0, 0)];
    // A table as tall as the memory (the tie the order breaks by global index), and a mixed one.
    for (log_mem, taus) in [(16usize, [16usize, 3, 16, 4, 16, 16]), (18, [2, 18, 5, 0, 7, 3])] {
        let l = layout(&prog, log_mem, taus, pi);
        let cells: Vec<String> = l
            .placements
            .iter()
            .map(|p| if p.is_virtual() { "V".to_string() } else { p.offset.to_string() })
            .collect();
        println!("log_mem {log_mem} taus {taus:?} mu {}", l.shape.mu);
        println!("{}", cells.join(" "));
    }
}
EOF

cargo run --quiet --release --manifest-path "$work/Cargo.toml" --target-dir "$checkout/target"
