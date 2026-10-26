#!/usr/bin/env bash
# The traces of small guest programs, for the Lean prover's differential test
# (`lake exe leanvm-prove`, `scripts/prover-diff.py`): the programs and public inputs of
# `export-verifier-fixtures-rust.sh` (the chain of crates/leanvm_core/tests/verifiers/
# python_verifier.rs at several loop counts, fibonacci.py, and with `--corpus` every suite
# program that declares its public input), each executed by the leanVM Rust interpreter
# (`Program::execute`) and proved by the Rust prover at the rate in its name, at the leanVM
# commit in `../leanvm-rev`. Per case directory:
#
#   bytecode.bin          the bytecode table, little-endian 64-bit words (as the fixtures);
#   public_input.bin      the public input's two halves, 16 bytes each;
#   memory.bin            the execution's memory, 24 bytes per cell (three limbs, little-endian);
#   trace.txt             `<log2 cells> <instructions executed> <rate>`;
#   rust.txt              the Rust prover's wall time in seconds;
#   stream.bin, merkle_openings.bin   the Rust prover's proof (the fixtures' format).
#
# Usage: scripts/export-prover-traces-rust.sh <output dir> [--corpus]
set -euo pipefail

checkout="$("$(dirname "${BASH_SOURCE[0]}")/../../leanvm-tree.sh")"
out="${1:?usage: $0 <output dir> [--corpus]}"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/src" "$out"
out="$(cd "$out" && pwd)"
cp "$checkout/Cargo.lock" "$work/Cargo.lock"
# The workspace's `target-cpu=native`, so that the prover runs its vectorized kernels.
mkdir -p "$work/.cargo"
cp "$checkout/.cargo/config.toml" "$work/.cargo/config.toml"

cat > "$work/Cargo.toml" <<EOF
[package]
name = "export-prover-traces"
version = "0.0.0"
edition = "2024"

[workspace]

[dependencies]
leanvm_core = { path = "$checkout/crates/leanvm_core" }
lean_compiler = { path = "$checkout/crates/lean_compiler" }
primitives = { path = "$checkout/crates/primitives" }
verifier = { path = "$checkout/crates/verifier" }

[profile.release]
lto = "thin"
codegen-units = 1
EOF

cat > "$work/src/main.rs" <<'EOF'
use lean_compiler::{compile, parse, parse_const, parse_with_replacements};
use leanvm_core::cpu::{Program, prove, public_input_bytes, verify};
use primitives::field::{F192, g_pow};
use std::collections::BTreeMap;
use std::path::Path;

// The program of crates/leanvm_core/tests/verifiers/python_verifier.rs, its loop count a parameter.
const CHAIN: &str = r#"
from snark_lib import *

LOOP_STEPS = LOOP_STEPS_PLACEHOLDER

def mix(value, tag):
    # A JUMP condition is K-valued (a g-power here), never an arbitrary word.
    if tag == 0:
        return value
    return value * GEN + value

def main():
    # 160 bytes: two blocks, the second read in the odd layout.
    digest = StackBuf(2)
    keccak_cells([5, 7, 5, 7, 5, 7, 5, 7, 5, 7], digest)

    chain = HeapBuf(LOOP_STEPS + 1)
    chain[1] = digest[0]
    for index in mul_range(1, GEN ** LOOP_STEPS):
        chain[index * GEN] = mix(chain[index] + index, index) + index

    public = GEN ** 0
    public[1] = chain[GEN ** LOOP_STEPS]
    public[GEN] = mix(digest[1], GEN ** 0)
    return
"#;

// The public input the program computes (python_verifier.rs, `public_input`).
fn chain_public_input(loop_steps: usize) -> [F192; 2] {
    let message: Vec<u8> = [5u64, 7]
        .repeat(5)
        .into_iter()
        .flat_map(|v| [v, 0])
        .flat_map(u64::to_le_bytes)
        .collect();
    let digest = primitives::hash::hash(&message);
    let word = |i: usize| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap());
    let digest = [F192::new(word(0), word(1), 0), F192::new(word(2), word(3), 0)];
    let mut value = digest[0];
    let mut index = F192::ONE;
    let generator = F192::from(g_pow(1));
    for _ in 0..loop_steps {
        let candidate = value + index;
        let product = candidate * generator;
        value = (if product == F192::ZERO {
            candidate
        } else {
            product + candidate
        }) + index;
        index *= generator;
    }
    [value, digest[1] * generator + digest[1]]
}

fn chain(loop_steps: usize) -> (Program, [F192; 2]) {
    let replacements = BTreeMap::from([("LOOP_STEPS_PLACEHOLDER".to_string(), loop_steps.to_string())]);
    let ast = parse_with_replacements(CHAIN, &replacements).expect("parse zkDSL program");
    (compile(&ast), chain_public_input(loop_steps))
}

// crates/lean_compiler/tests/programs/fibonacci.py, whose header gives its public input.
fn fibonacci(checkout: &Path) -> (Program, [F192; 2]) {
    let source = std::fs::read_to_string(checkout.join("crates/lean_compiler/tests/programs/fibonacci.py"))
        .expect("read fibonacci.py");
    assert!(source.contains("# public_input: GEN ** 89, GEN ** 89"));
    let ast = parse_with_replacements(&source, &BTreeMap::new()).expect("parse zkDSL program");
    let out = F192::from(g_pow(89));
    (compile(&ast), [out, out])
}

// A program of crates/lean_compiler/tests/programs with its `# public_input:` and `# witness`
// annotations, read as crates/lean_compiler/tests/suite/py_source.rs reads them; `None` for a
// program without a declared public input.
fn suite_program(path: &Path) -> Option<(Program, [F192; 2])> {
    let source = std::fs::read_to_string(path).expect("read suite program");
    let header = source.lines().find_map(|line| line.trim().strip_prefix("# public_input:"))?;
    let parts: Vec<&str> = header.split(',').collect();
    assert_eq!(parts.len(), 2, "public input of {}", path.display());
    let public_input = [parse_const(parts[0]).expect("public input"), parse_const(parts[1]).expect("public input")];
    let ast = parse(&source).expect("parse suite program");
    let mut program = compile(&ast);
    let mut streams: BTreeMap<String, Vec<Vec<F192>>> = BTreeMap::new();
    for rest in source.lines().filter_map(|line| line.trim().strip_prefix("# witness ")) {
        let (name, values) = rest.split_once(':').expect("`# witness` needs `name: values`");
        let entry = values.split(',').map(|v| parse_const(v).expect("witness value")).collect();
        streams.entry(name.trim().to_string()).or_default().push(entry);
    }
    for (stream, entries) in streams {
        program.set_witness(stream, entries);
    }
    Some((program, public_input))
}

// The corpus: every suite program with a declared public input, and the chain at three sizes, each
// at the four rates.
fn corpus(checkout: &Path) -> Vec<(String, (Program, [F192; 2]), usize)> {
    let mut programs: Vec<(String, Box<dyn Fn() -> (Program, [F192; 2])>)> = Vec::new();
    let directory = checkout.join("crates/lean_compiler/tests/programs");
    let mut paths: Vec<_> = std::fs::read_dir(&directory)
        .expect("suite programs")
        .map(|entry| entry.expect("directory entry").path())
        .filter(|path| path.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    for path in paths {
        if suite_program(&path).is_some() {
            let name = path.file_stem().unwrap().to_string_lossy().replace('_', "-");
            programs.push((name, Box::new(move || suite_program(&path).unwrap())));
        }
    }
    for steps in [16usize, 1000, 5000] {
        programs.push((format!("chain{steps}"), Box::new(move || chain(steps))));
    }
    let mut fixtures = Vec::new();
    for (name, make) in &programs {
        for rate in 1..=4usize {
            fixtures.push((format!("{name}-rate{rate}"), make(), rate));
        }
    }
    fixtures
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let checkout = Path::new(&args[1]);
    let out = Path::new(&args[2]);
    let fixtures = if args.get(3).is_some_and(|flag| flag == "--corpus") {
        corpus(checkout)
    } else {
        vec![
            ("chain4-rate1".to_string(), chain(4), 1usize),
            ("chain4-rate4".to_string(), chain(4), 4),
            ("chain300-rate2".to_string(), chain(300), 2),
            ("fibonacci-rate4".to_string(), fibonacci(checkout), 4),
        ]
    };
    for (name, (program, public_input), log_inv_rate) in fixtures {
        let directory = out.join(&name);
        std::fs::create_dir_all(&directory).expect("create case directory");
        let exec = match program.execute(public_input) {
            Ok(exec) => exec,
            Err(_) => { println!("{name}: no execution, skipped"); continue; }
        };
        let start = std::time::Instant::now();
        let (proof, stats) = match prove(&program, public_input, log_inv_rate) {
            Ok(r) => r,
            Err(_) => { println!("{name}: the Rust prover refuses it, skipped"); continue; }
        };
        let seconds = start.elapsed().as_secs_f64();
        let summary = verify(&program, &public_input, &proof).expect("honest proof verifies");
        let table: Vec<u8> = leanvm_core::cpu::layout::bytecode_table(&program.prog)
            .iter()
            .flat_map(|w| w.0.to_le_bytes())
            .collect();
        std::fs::write(directory.join("bytecode.bin"), &table).expect("write bytecode");
        std::fs::write(directory.join("public_input.bin"), public_input_bytes(&public_input))
            .expect("write public input");
        let mut memory = Vec::with_capacity(24 * exec.mem.len());
        for i in 0..exec.mem.len() {
            let w = exec.mem.word(i);
            for limb in [w.c0, w.c1, w.c2] {
                memory.extend_from_slice(&limb.to_le_bytes());
            }
        }
        std::fs::write(directory.join("memory.bin"), memory).expect("write memory");
        let log_mem = exec.mem.len().trailing_zeros();
        std::fs::write(directory.join("trace.txt"), format!("{log_mem} {} {log_inv_rate}\n", exec.cycles))
            .expect("write trace");
        std::fs::write(directory.join("rust.txt"), format!("{seconds}\n")).expect("write time");
        let stream: Vec<u8> = proof
            .stream
            .iter()
            .flat_map(|scalar| [scalar.c0, scalar.c1, scalar.c2])
            .flat_map(u64::to_le_bytes)
            .collect();
        let mut openings = Vec::new();
        for path in &summary.merkle_paths {
            openings.extend(path.leaf.iter().flat_map(|word| word.to_bytes()));
            openings.extend(path.siblings.iter().flatten());
        }
        std::fs::write(directory.join("stream.bin"), stream).expect("write scalar stream");
        std::fs::write(directory.join("merkle_openings.bin"), openings).expect("write Merkle openings");
        println!(
            "{name}: {} instructions, 2^{log_mem} cells, {} cycles, Rust prover {seconds:.3} s",
            program.prog.len(),
            stats.cycles,
        );
    }
}
EOF

cargo run --quiet --release --manifest-path "$work/Cargo.toml" --target-dir "$checkout/target" \
  -- "$checkout" "$out" ${2:+"$2"}
