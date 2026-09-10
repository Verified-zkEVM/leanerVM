#!/usr/bin/env bash
# Dump the MUL_NATIVE vector of the pinned leanVM executor test `mul_192bit_word`
# (crates/lean_vm/src/cpu/mod.rs:981-998 at a386121f84292f6fa663aaa3e570c15bc0240ea2): the two
# 192-bit operands and their product in `E`, computed by the same `primitives::field::F192`
# arithmetic the executor uses, printed as the Lean words of
# tests/LeanerVMTests/Semantics/Execution.lean.
#
# Usage: scripts/dump-mul-rust.sh <path to a leanVM checkout at the pin>
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
name = "dump-mul"
version = "0.0.0"
edition = "2024"

[dependencies]
primitives = { path = "$checkout/crates/primitives" }
EOF

cat > "$work/src/main.rs" <<'EOF'
use primitives::field::F192;

fn lean_word(name: &str, x: F192) {
    println!("def {name} : E := E.ofLimbs 0x{:016x} 0x{:016x} 0x{:016x}", x.c0, x.c1, x.c2);
}

fn main() {
    // `mul_192bit_word`, verbatim operands (cpu/mod.rs:985-986).
    let x = F192::new(0x0123_4567_89ab_cdef, 0xfeed_face_dead_beef, 0x1111_2222_3333_4444);
    let y = F192::new(0x9999_aaaa_bbbb_cccc, 0x1357_9bdf_2468_ace0, 0x5555_6666_7777_8888);
    println!("-- scripts/dump-mul-rust.sh at leanVM a386121f");
    println!("-- operands and product of `mul_192bit_word` (cpu/mod.rs:981-998)");
    lean_word("mulX", x);
    lean_word("mulY", y);
    lean_word("mulXY", x * y);
}
EOF

cargo run --quiet --manifest-path "$work/Cargo.toml"
