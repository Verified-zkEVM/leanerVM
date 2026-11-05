// Copied by scripts/dump-execution-rust.sh into the pinned source as an example of
// `lean_compiler`: compiles a few programs, runs each as `prove` would, and writes each execution
// with `lean_vm::cpu::leanisa_execution` (tests/rust/leanisa_execution.rs).
//
// Usage: leanisa_execution_driver <output dir> [fibonacci n ...]
use lean_compiler::{compile, parse, parse_const};
use lean_vm::cpu::leanisa_execution::execute_and_write;
use lean_vm::vmhash::compress;
use primitives::field::{F64, F192, g_pow};
use std::collections::HashMap;
use std::path::Path;

/// crates/lean_compiler/tests/suite/field_div.rs:15-31, the program of scripts/dump-proof-rust.sh.
fn field_div() -> (String, [F192; 2]) {
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
    (src.into(), [F192::from(g_pow(20)), F192::from(F64::ONE)])
}

/// crates/rec_aggregation/src/hash_chain.rs:20-60 (`chain_source`) and its public input (:66-82).
fn hash_chain(steps: usize, unroll: usize) -> (String, [F192; 2]) {
    assert!(unroll >= 1 && steps.is_multiple_of(unroll));
    let blocks = steps / unroll;
    let result_cell = 2 * blocks;
    let mut body = String::new();
    body.push_str("        b = i * i\n");
    body.push_str("        h0 = StackBuf(2)\n");
    body.push_str("        h0[0] = buff[b]\n");
    body.push_str("        h0[1] = buff[b * GEN]\n");
    for step in 1..=unroll {
        body.push_str(&format!("        h{step} = StackBuf(2)\n"));
        body.push_str(&format!("        blake2s(h{previous}, h{previous}, h{step})\n", previous = step - 1));
    }
    for word in 0..2 {
        body.push_str(&format!("        buff[b * GEN ** {}] = h{unroll}[{word}]\n", 2 + word));
    }
    let src = format!(
        "def main():\n\
        \x20   buff = HeapBuf({size})\n\
        \x20   buff[1] = 0\n\
        \x20   buff[GEN] = 0\n\
        \x20   for i in mul_range(1, GEN ** {blocks}):\n\
        {body}\
        \x20   output = 1\n\
        \x20   output[1] = buff[GEN ** {result_cell}]\n\
        \x20   output[GEN] = buff[GEN ** {next_cell}]\n\
        \x20   return\n",
        size = result_cell + 2,
        next_cell = result_cell + 1,
    );
    let mut digest = [F64::ZERO; 4];
    for _ in 0..steps {
        digest = compress(digest, digest);
    }
    let pi = [F192::new(digest[0].0, digest[1].0, 0), F192::new(digest[2].0, digest[3].0, 0)];
    (src, pi)
}

/// crates/rec_aggregation/src/fibonacci.rs:59-104 (`fibonacci_program`).
fn fibonacci(fib_n: usize) -> (String, [F192; 2]) {
    const UNROLL: usize = 1000;
    assert!(fib_n >= UNROLL && fib_n.is_multiple_of(UNROLL));
    let blocks = fib_n / UNROLL;
    let (mut previous, mut current) = (F64::ONE, g_pow(1));
    for _ in 1..=fib_n {
        let next = previous * current;
        previous = current;
        current = next;
    }
    let pi = [F192::from(previous), F192::ZERO];
    let mut body = String::from("        b = x * x\n        f0 = buff[b]\n        f1 = buff[b * GEN]\n");
    for j in 2..=UNROLL + 1 {
        body.push_str(&format!("        f{j} = f{} * f{}\n", j - 2, j - 1));
    }
    body.push_str(&format!("        buff[b * GEN ** 2] = f{UNROLL}\n"));
    body.push_str(&format!("        buff[b * GEN ** 3] = f{}\n", UNROLL + 1));
    let publish = format!("    p = 1\n    p[1] = buff[GEN ** {}]\n", 2 * blocks);
    let src = format!(
        "def main():\n\
        \x20   buff = HeapBuf({size})\n\
        \x20   buff[1] = 1\n\
        \x20   buff[GEN] = GEN\n\
        \x20   for x in mul_range(1, GEN ** {blocks}):\n\
        {body}\
        {publish}\
        \x20   return\n",
        size = 2 * blocks + 2,
    );
    (src, pi)
}

/// The annotations of crates/lean_compiler/tests/suite/py_source.rs:21-50.
fn annotations(src: &str) -> ([F192; 2], HashMap<String, Vec<Vec<F192>>>) {
    let mut pi = [F192::ZERO; 2];
    for line in src.lines() {
        if let Some(rest) = line.trim().strip_prefix("# public_input:") {
            let parts: Vec<&str> = rest.split(',').collect();
            pi = [parse_const(parts[0]).unwrap(), parse_const(parts[1]).unwrap()];
        }
    }
    let mut streams: HashMap<String, Vec<Vec<F192>>> = HashMap::new();
    for rest in src.lines().filter_map(|l| l.trim().strip_prefix("# witness ")) {
        let (name, vals) = rest.split_once(':').unwrap();
        let entry = vals.split(',').map(|s| parse_const(s).unwrap()).collect();
        streams.entry(name.trim().to_string()).or_default().push(entry);
    }
    (pi, streams)
}

fn run(dir: &Path, name: &str, src: &str, pi: [F192; 2], witness: HashMap<String, Vec<Vec<F192>>>) {
    let mut program = compile(&parse(src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
    for (stream, entries) in witness {
        program.set_witness(stream, entries);
    }
    execute_and_write(name, &program, pi, &dir.join(format!("{name}.exec")));
    println!("{name}: written");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = Path::new(&args[1]);
    std::fs::create_dir_all(dir).unwrap();
    let (src, pi) = field_div();
    run(dir, "field_div", &src, pi, HashMap::new());
    let (src, pi) = hash_chain(8, 4);
    run(dir, "hash_chain_8", &src, pi, HashMap::new());
    let programs = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut paths: Vec<_> = std::fs::read_dir(programs)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    for path in paths {
        let src = std::fs::read_to_string(&path).unwrap();
        let (pi, witness) = annotations(&src);
        let name = format!("py_{}", path.file_stem().unwrap().to_string_lossy());
        run(dir, &name, &src, pi, witness);
    }
    for n in args[2..].iter().map(|a| a.parse::<usize>().unwrap()) {
        let (src, pi) = fibonacci(n);
        run(dir, &format!("fibonacci_{n}"), &src, pi, HashMap::new());
    }
}
