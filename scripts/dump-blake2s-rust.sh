#!/usr/bin/env bash
# Dump the BLAKE2S opcode vector of the pinned leanVM executor test
# `blake2s_computes_the_compression` (crates/lean_vm/src/cpu/mod.rs:889-917 at
# a386121f84292f6fa663aaa3e570c15bc0240ea2) by calling the same
# `lean_vm::hash_flock::{compression, digest, metadata}` the executor calls, and print it as the
# Lean cells used in tests/LeanerVMTests/Semantics/Blake2s.lean.
#
# Usage: scripts/dump-blake2s-rust.sh <path to a leanVM checkout at the pin>
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
name = "dump-blake2s"
version = "0.0.0"
edition = "2024"

[dependencies]
flock = { path = "$checkout/crates/flock" }
lean_vm = { path = "$checkout/crates/lean_vm" }
primitives = { path = "$checkout/crates/primitives" }
EOF

cat > "$work/src/main.rs" <<'EOF'
use lean_vm::hash_flock::{FINAL_FLAG, PINNED_T, compression, digest, metadata, unpack_metadata};
use primitives::field::{F64, F192};

/// Two flock lanes into the canonical BLAKE2s subspace of F192 (`cpu/mod.rs:826`, `cell`).
fn cell(lo: F64, hi: F64) -> F192 {
    F192::new(lo.0, hi.0, 0)
}

fn lean_cell(name: &str, x: F192) {
    println!("def {name} : E := E.ofLimbs 0x{:016x} 0x{:016x} 0x{:016x}", x.c0, x.c1, x.c2);
}

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
    let md = metadata(PINNED_T, FINAL_FLAG, 0);

    let block = compression(a, b, cv, md);
    let d = digest(&block);
    let (t, f0, f1) = unpack_metadata(md);

    println!("-- scripts/dump-blake2s-rust.sh at leanVM a386121f");
    println!("-- cells of `blake2s_computes_the_compression` (cpu/mod.rs:889-917)");
    lean_cell("rustM0", cell(a[0], a[1]));
    lean_cell("rustM1", cell(a[2], a[3]));
    lean_cell("rustM2", cell(b[0], b[1]));
    lean_cell("rustM3", cell(b[2], b[3]));
    lean_cell("rustCv0", pi[0]);
    lean_cell("rustCv1", pi[1]);
    lean_cell("rustMd", md);
    lean_cell("rustOut0", cell(d[0], d[1]));
    lean_cell("rustOut1", cell(d[2], d[3]));
    println!("-- the compression the executor ran on them (hash_flock.rs:162-185)");
    let words = |w: &[u32]| w.iter().map(|x| format!("0x{x:08x}")).collect::<Vec<_>>().join(", ");
    println!("-- h  = #v[{}]", words(&block.0));
    println!("-- m  = #v[{}]", words(&block.1));
    println!("-- t = {t}, f0 = 0x{f0:08x}, f1 = 0x{f1:08x}");
    println!("-- h' = #v[{}]", words(&flock::hash::blake2s_compress(
        &block.0, &block.1, block.2, block.3, block.4)));
}
EOF

cargo run --quiet --manifest-path "$work/Cargo.toml"
