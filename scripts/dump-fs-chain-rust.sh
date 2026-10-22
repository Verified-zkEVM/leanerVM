#!/usr/bin/env bash
# Print known-answer vectors of the pinned leanVM's Fiat-Shamir chain and proof transport, for
# tests/LeanerVMTests/Protocol/Transcript.lean: the
# statement seed of a four-instruction program and a public input (`lean_vm::cpu::fs_seed`,
# crates/lean_vm/src/cpu/mod.rs:82-106), the chain state after seeding, observes, samples and an
# 8-bit grind with its nonce and checks (crates/fiat_shamir/src/lib.rs:18-174), and a prover
# transcript with a scalar, a root, a plain and an `eq` round polynomial and a grind, read back by
# the verifier (crates/fiat_shamir/src/transcript.rs), at a386121f84292f6fa663aaa3e570c15bc0240ea2.
# A word is printed as 16 hexadecimal digits; an element of E as its three limbs `c0 c1 c2`.
#
# Usage: scripts/dump-fs-chain-rust.sh <path to a leanVM checkout at the pin>
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
name = "dump-fs-chain"
version = "0.0.0"
edition = "2024"

[dependencies]
fiat_shamir = { path = "$checkout/crates/fiat_shamir" }
lean_vm = { path = "$checkout/crates/lean_vm" }
primitives = { path = "$checkout/crates/primitives" }
EOF

cat > "$work/src/main.rs" <<'EOF'
use std::collections::HashMap;

use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use fiat_shamir::{FiatShamirState, compress};
use lean_vm::cpu::{DerefMode, Op, Program, bytecode_table, fs_seed};
use primitives::field::{F64, F192};

fn words(name: &str, w: [F64; 4]) {
    println!("{name} {:016x} {:016x} {:016x} {:016x}", w[0].0, w[1].0, w[2].0, w[3].0);
}

fn scalar(name: &str, x: F192) {
    println!("{name} {:016x} {:016x} {:016x}", x.c0, x.c1, x.c2);
}

/// `cpu/mod.rs:99-106`, `digest_words` (private there).
fn halves_words(h: &[F192; 2]) -> [F64; 4] {
    [F64(h[0].c0), F64(h[0].c1), F64(h[1].c0), F64(h[1].c1)]
}

fn main() {
    // The program: four instructions, every slot kind but BLAKE2S's.
    let prog = vec![
        Op::Xor { a: 1, b: 2, c: 3 },
        Op::Set { o: 4, k: F192::new(0x1111, 0x2222, 0x3333) },
        Op::Deref { o1: 5, o2: 6, o3: 7, mode: DerefMode::Pc },
        Op::Jump { oc: 8, od: 9, of: 10 },
    ];
    let table = bytecode_table(&prog);
    let bytes: Vec<u8> = table.iter().flat_map(|w| w.0.to_le_bytes()).collect();
    let bytecode_hash = primitives::hash::hash(&bytes);
    let program = Program::assemble(prog, HashMap::new(), 0);
    println!("-- scripts/dump-fs-chain-rust.sh at leanVM a386121f");
    println!("table_len {}", table.len());
    println!(
        "bytecode_hash {}",
        bytecode_hash.iter().map(|b| format!("{b:02x}")).collect::<String>()
    );
    let seed = fs_seed(&program);
    scalar("seed0", seed[0]);
    scalar("seed1", seed[1]);
    let iv = halves_words(&seed);
    let pi = [F192::new(7, 11, 0), F192::new(13, 17, 0)];
    let piw = halves_words(&pi);

    // The chain (`lib.rs`).
    let mut fs = FiatShamirState::new(iv, piw);
    words("state_new", fs.state());
    let x = F192::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x1111_2222_3333_4444);
    fs.observe(x);
    words("state_observe", fs.state());
    let c1 = fs.sample();
    scalar("sample1", c1);
    words("state_sample1", fs.state());
    fs.observe(F192::new(5, 0, 0));
    let c2 = fs.sample();
    scalar("sample2", c2);
    words("state_sample2", fs.state());
    words("pow_base", compress(fs.state(), [F64::ZERO, F64::ZERO, F64::ZERO, F64(3)]));
    let mut prover = fs.clone();
    let nonce = prover.grind_pow(8);
    println!("grind8_nonce {nonce}");
    words("state_grind8", prover.state());
    let mut verifier = fs.clone();
    println!("verify8_ok {}", verifier.verify_pow_field(F192::new(nonce, 0, 0), 8));
    words("state_verify8", verifier.state());
    let mut wrong = fs.clone();
    println!("verify8_next_ok {}", wrong.verify_pow_field(F192::new(nonce + 1, 0, 0), 8));
    let mut zero = fs.clone();
    println!("verify0_zero_ok {}", zero.verify_pow_field(F192::ZERO, 0));
    words("state_verify0", zero.state());
    let mut one = fs.clone();
    println!("verify0_one_ok {}", one.verify_pow_field(F192::ONE, 0));

    // The transport (`transcript.rs`).
    let root: [u8; 32] = std::array::from_fn(|i| (3 * i + 1) as u8);
    let plain = [F192::new(1, 2, 3), F192::new(4, 5, 6), F192::new(7, 8, 9), F192::new(10, 11, 12)];
    let eqp = [
        F192::new(21, 22, 23),
        F192::new(24, 25, 26),
        F192::new(27, 28, 29),
        F192::new(30, 31, 32),
        F192::new(33, 34, 35),
    ];
    let r = F192::new(0x99, 0x98, 0x97);
    let plain_claim = plain[1..].iter().fold(F192::ZERO, |a, &c| a + c);
    let eq_claim = eqp[0] + r * eqp[1..].iter().fold(F192::ZERO, |a, &c| a + c);
    scalar("plain_claim", plain_claim);
    scalar("eq_claim", eq_claim);
    let mut ps = ProverState::new(iv, piw);
    let p1 = ps.sample();
    ps.add_scalar(x);
    ps.add_root(&root);
    ps.add_round_poly(&plain, false);
    ps.add_round_poly(&eqp, true);
    ps.grind(8);
    let p2 = ps.sample();
    scalar("transcript_sample1", p1);
    scalar("transcript_sample2", p2);
    let proof = ps.into_proof();
    println!("stream_len {}", proof.stream.len());
    for (i, s) in proof.stream.iter().enumerate() {
        scalar(&format!("stream{i}"), *s);
    }
    let mut vs = VerifierState::new(iv, &proof, piw);
    assert_eq!(vs.sample(), p1);
    assert_eq!(vs.next_scalar().unwrap(), x);
    assert_eq!(vs.next_root().unwrap(), root);
    let dp = vs.next_round_poly(4, plain_claim, None).unwrap();
    let de = vs.next_round_poly(5, eq_claim, Some(r)).unwrap();
    assert_eq!(dp, plain);
    assert_eq!(de, eqp);
    assert!(vs.grind_check(8).is_ok());
    assert_eq!(vs.sample(), p2);
    assert!(vs.finish().is_ok());
    println!("verifier_reads_back true");
}
EOF

cargo run --quiet --release --manifest-path "$work/Cargo.toml" --target-dir "$checkout/target"
