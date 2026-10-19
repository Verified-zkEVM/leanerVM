#!/usr/bin/env bash
# Digest the committed Flock region the pinned leanVM prover builds for eight BLAKE2s compressions:
# the executor test's compression (`blake2s_computes_the_compression`, crates/lean_vm/src/cpu/mod.rs
# at a386121f84292f6fa663aaa3e570c15bc0240ea2), the RFC 7693 "abc" compression, and six of the
# prover's padding block (`flock::hash::padding_block`). The region is the first output of
# `flock::hash::generate_witness_with_ab_packed_and_lincheck`, which `build_qflock_prepared` copies
# word for word into `q_flock` (crates/lean_vm/src/hash_flock.rs:186-215). The digest
# `sum_u (word_u mod P) (u + 1) mod P`, `P = 2^64 - 59`, over its 2048 words, is compared with the
# Lean honest column in tests/LeanerVMTests/Protocol/FlockSpec.lean.
#
# Usage: scripts/dump-flock-column-rust.sh <path to a leanVM checkout at the pin>
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
name = "dump-flock-column"
version = "0.0.0"
edition = "2024"

[dependencies]
flock = { path = "$checkout/crates/flock" }
lean_vm = { path = "$checkout/crates/lean_vm" }
primitives = { path = "$checkout/crates/primitives" }
EOF

cat > "$work/src/main.rs" <<'EOF'
use flock::hash::{generate_witness_with_ab_packed_and_lincheck, padding_block, param_iv, Compression};
use lean_vm::hash_flock::{FINAL_FLAG, PINNED_T, compression, metadata};
use primitives::field::{F64, F192};

fn main() {
    // `blake2s_computes_the_compression`, verbatim inputs.
    let a: [F64; 4] = [
        F64(0x0123_4567_89ab_cdef),
        F64(0xfedc_ba98_7654_3210),
        F64(0x1111_2222_3333_4444),
        F64(0x5555_6666_7777_8888),
    ];
    let b: [F64; 4] = [
        F64(0xdead_beef_cafe_babe),
        F64(0x0badf00d_0badf00d),
        F64(0x9999_aaaa_bbbb_cccc),
        F64(0xdddd_eeee_ffff_0000),
    ];
    let pi = [F192::new(7, 0, 0), F192::new(11, 0, 0)];
    let cv = [F64(pi[0].c0), F64(pi[0].c1), F64(pi[1].c0), F64(pi[1].c1)];
    let executor = compression(a, b, cv, metadata(PINNED_T, FINAL_FLAG, 0));
    // RFC 7693 Appendix B: BLAKE2s-256("abc").
    let mut m = [0u32; 16];
    m[0] = 0x0063_6261;
    let abc: Compression = (param_iv(), m, 3, u32::MAX, 0);
    let mut blocks = vec![executor, abc];
    blocks.extend(std::iter::repeat_n(padding_block(), 6));
    let z = generate_witness_with_ab_packed_and_lincheck(&blocks, 3).0;
    let p: u128 = (1u128 << 64) - 59;
    let mut d: u128 = 0;
    for (u, &w) in z.iter().enumerate() {
        d = (d + (w as u128 % p) * (u as u128 + 1)) % p;
    }
    println!("words {}", z.len());
    println!("digest {d}");
    println!("padding h = {:08x?}", padding_block().0);
}
EOF

cargo run --quiet --release --manifest-path "$work/Cargo.toml"
