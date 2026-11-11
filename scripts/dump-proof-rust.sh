#!/usr/bin/env bash
# Print the Lean module tests/LeanerVMTests/Protocol/RustProofData.lean, a proof of the pinned
# leanVM prover with its program and public input as one text string: a small compiled program
# and the hash of its bytecode table (`lean_vm::cpu::layout::bytecode_table`, the words
# `Program::assemble` hashes), the public input, the proof's scalar stream and its pruned Merkle
# opening phases (`fiat_shamir::transcript::Proof`, crates/fiat_shamir/src/transcript.rs:8-12;
# `PrunedMerklePaths`, crates/fiat_shamir/src/merkle.rs:88-92), at
# a386121f84292f6fa663aaa3e570c15bc0240ea2. The program is the division test of
# crates/lean_compiler/tests/suite/field_div.rs:15-31 with its fill blocks (`compile`; the prover
# rejects a program without them), proved at the test rate (`lean_vm::pcs::TEST_LOG_INV_RATE`)
# and checked by `lean_vm::cpu::verify` before it is printed. The program is printed instruction
# by instruction (`Op`, crates/lean_vm/src/cpu/isa.rs:6-56; an operand is the exponent `j` of
# `g^j`), followed by BLAKE2s-256 of its bytecode table, the program hash of the seed.
#
# A word is 16 hexadecimal digits; an element of E is its three limbs `c0 c1 c2`; a digest is its
# 32 bytes as 64 hexadecimal digits. With a second argument, the script also writes there the
# four files the Python verifier reads (python-verifier/verifier.py:1418-1433).
#
# Usage: scripts/dump-proof-rust.sh <path to a leanVM checkout at the pin> [python-input-dir]
set -euo pipefail

pin="a386121f84292f6fa663aaa3e570c15bc0240ea2"
checkout="$(cd "${1:?usage: $0 <leanVM checkout> [python-input-dir]}" && pwd)"
pydir="${2:-}"
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
name = "dump-proof"
version = "0.0.0"
edition = "2024"

[dependencies]
fiat_shamir = { path = "$checkout/crates/fiat_shamir" }
lean_compiler = { path = "$checkout/crates/lean_compiler" }
lean_vm = { path = "$checkout/crates/lean_vm" }
primitives = { path = "$checkout/crates/primitives" }
EOF

cat > "$work/src/main.rs" <<'EOF'
use lean_compiler::{compile, parse};
use lean_vm::cpu::{DerefMode, Op};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};
use std::path::Path;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn main() {
    // crates/lean_compiler/tests/suite/field_div.rs:15-31.
    let src = "\
def main():
    a = GEN ** 20
    b = GEN ** 7
    q = a / b
    r = 1 / b
    p = 1
    p[1] = q * b
    p[GEN] = r * b
    return
";
    let program = compile(&parse(src).expect("parse"));
    let public_input = [F192::from(g_pow(20)), F192::from(F64::ONE)];
    let rate = lean_vm::pcs::TEST_LOG_INV_RATE;
    let (proof, _) = prove(&program, public_input, rate);
    let raw = verify(&program, &public_input, &proof).expect("honest proof verifies").raw;
    let table = lean_vm::cpu::layout::bytecode_table(&program.prog);

    println!("leanvm-proof {}", "a386121f84292f6fa663aaa3e570c15bc0240ea2");
    println!("rate {rate}");
    println!("program {}", program.prog.len());
    for op in &program.prog {
        match *op {
            Op::Xor { a, b, c } => println!("xor {a} {b} {c}"),
            Op::Mul { a, b, c } => println!("mul {a} {b} {c}"),
            Op::Set { o, k } => println!("set {o} {:016x} {:016x} {:016x}", k.c0, k.c1, k.c2),
            Op::Deref { o1, o2, o3, mode } => {
                let m = match mode {
                    DerefMode::Cell => "cell",
                    DerefMode::Pc => "pc",
                    DerefMode::Fp => "fp",
                };
                println!("deref {o1} {o2} {o3} {m}")
            }
            Op::Jump { oc, od, of } => println!("jump {oc} {od} {of}"),
            Op::Blake2s { ins, cv, out, md } => {
                println!("blake2s {} {} {} {} {cv} {out} {md}", ins[0], ins[1], ins[2], ins[3])
            }
        }
    }
    let table_bytes: Vec<u8> = table.iter().flat_map(|w| w.0.to_le_bytes()).collect();
    println!("program_hash {}", hex(&primitives::hash::hash(&table_bytes)));
    println!(
        "public {:016x} {:016x} {:016x} {:016x} {:016x} {:016x}",
        public_input[0].c0, public_input[0].c1, public_input[0].c2,
        public_input[1].c0, public_input[1].c1, public_input[1].c2
    );
    println!("stream {}", proof.stream.len());
    for x in &proof.stream {
        println!("{:016x} {:016x} {:016x}", x.c0, x.c1, x.c2);
    }
    println!("merkle {}", proof.merkle.len());
    for phase in &proof.merkle {
        println!("phase {} {}", phase.leaf_data.len(), phase.sibling_hashes.len());
        for row in &phase.leaf_data {
            let words: Vec<String> = row.iter().map(|w| format!("{:016x}", w.0)).collect();
            println!("row {} {}", row.len(), words.join(" "));
        }
        for h in &phase.sibling_hashes {
            println!("sibling {}", hex(h));
        }
    }
    println!("end");

    if let Some(dir) = std::env::args().nth(1) {
        let dir = Path::new(&dir);
        std::fs::create_dir_all(dir).expect("create python input directory");
        let bytecode: Vec<u8> = table.iter().flat_map(|w| w.0.to_le_bytes()).collect();
        std::fs::write(dir.join("bytecode.bin"), bytecode).expect("write bytecode");
        let pi: Vec<u8> = public_input
            .iter()
            .flat_map(|v| [v.c0.to_le_bytes(), v.c1.to_le_bytes()].concat())
            .collect();
        std::fs::write(dir.join("public_input.bin"), pi).expect("write public input");
        let mut stream = Vec::new();
        for x in &raw.stream {
            for limb in [x.c0, x.c1, x.c2] {
                stream.extend(limb.to_le_bytes());
            }
        }
        std::fs::write(dir.join("stream.bin"), stream).expect("write stream");
        let mut openings = Vec::new();
        for opening in &raw.merkle {
            for word in &opening.leaf_data {
                openings.extend(word.0.to_le_bytes());
            }
            for digest in &opening.path {
                openings.extend(digest);
            }
        }
        std::fs::write(dir.join("merkle_openings.bin"), openings).expect("write openings");
    }
}
EOF

text="$(cargo run --quiet --release --manifest-path "$work/Cargo.toml" --target-dir "$checkout/target" -- $pydir)"
printf '%s\n' "/-" "  LeanerVMTests.Protocol.RustProofData" "" \
  "  Generated by scripts/dump-proof-rust.sh from leanVM" "  $pin; do not edit." "-/" "" \
  "namespace LeanerVMTests.Protocol.RustProofData" "" \
  "/-- A proof of the pinned Rust prover with its program and public input, as text. -/" \
  "def rustProofText : String := \""
printf '%s\n' "$text"
printf '%s\n' "\"" "" "end LeanerVMTests.Protocol.RustProofData"
