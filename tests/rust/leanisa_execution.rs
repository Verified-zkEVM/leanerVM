// Loaded by scripts/dump-execution-rust.sh as a public child of `cpu` in a temporary archive of
// the pinned source; it only reads an execution. Writes one run of the interpreter in the text
// format read by bench/LeanerVMWitgen.lean.
use super::{DerefMode, Execution, Op, Program};
use primitives::field::F192;
use std::fmt::Write;

/// Run the program as `prove` does (`execute_to_floor`, its call in `prove` at cpu/mod.rs:528)
/// and write the execution to `path`.
pub fn execute_and_write(
    name: &str,
    program: &Program,
    public_input: [F192; 2],
    path: &std::path::Path,
) {
    let exec = program.execute_to_floor(public_input);
    write(name, program, &exec, public_input, path);
}

/// The hook `prove` calls when the dump script patched it in: write the execution to
/// `$LEANISA_EXECUTION_DIR/$LEANISA_EXECUTION_NAME-<n>.exec`, nothing if the directory is unset.
pub fn hook(program: &Program, exec: &Execution, public_input: [F192; 2]) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNT: AtomicUsize = AtomicUsize::new(0);
    let Some(directory) = std::env::var_os("LEANISA_EXECUTION_DIR") else {
        return;
    };
    let base = std::env::var("LEANISA_EXECUTION_NAME").unwrap_or_else(|_| "prove".into());
    let name = format!("{base}-{}", COUNT.fetch_add(1, Ordering::SeqCst));
    let path = std::path::Path::new(&directory).join(format!("{name}.exec"));
    write(&name, program, exec, public_input, &path);
}

fn op_line(op: &Op) -> String {
    match *op {
        Op::Xor { a, b, c } => format!("xor {a} {b} {c}"),
        Op::Mul { a, b, c } => format!("mul {a} {b} {c}"),
        Op::Set { o, k } => format!("set {o} {:016x} {:016x} {:016x}", k.c0, k.c1, k.c2),
        Op::Deref { o1, o2, o3, mode } => {
            let m = match mode {
                DerefMode::Cell => "cell",
                DerefMode::Pc => "pc",
                DerefMode::Fp => "fp",
            };
            format!("deref {o1} {o2} {o3} {m}")
        }
        Op::Jump { oc, od, of } => format!("jump {oc} {od} {of}"),
        Op::Blake2s { ins, cv, out, md } => {
            format!("blake2s {} {} {} {} {cv} {out} {md}", ins[0], ins[1], ins[2], ins[3])
        }
    }
}

fn counts(ns: &[usize]) -> String {
    ns.iter().map(usize::to_string).collect::<Vec<_>>().join(" ")
}

fn write(
    name: &str,
    program: &Program,
    exec: &Execution,
    public_input: [F192; 2],
    path: &std::path::Path,
) {
    let pin = "a386121f84292f6fa663aaa3e570c15bc0240ea2";
    let mut out = String::new();
    writeln!(out, "leanisa-execution {pin} {name}").unwrap();
    writeln!(out, "program {}", program.prog.len()).unwrap();
    for op in &program.prog {
        writeln!(out, "{}", op_line(op)).unwrap();
    }
    let hash: String = program.bytecode_hash.iter().map(|b| format!("{b:02x}")).collect();
    writeln!(out, "program_hash {hash}").unwrap();
    writeln!(out, "filler {}", program.filler.len()).unwrap();
    for b in &program.filler {
        writeln!(out, "{} {} {}", b.pc, b.size, b.table).unwrap();
    }
    writeln!(
        out,
        "public {:016x} {:016x} {:016x} {:016x} {:016x} {:016x}",
        public_input[0].c0, public_input[0].c1, public_input[0].c2,
        public_input[1].c0, public_input[1].c1, public_input[1].c2
    )
    .unwrap();
    let log_mem = exec.mem.len().trailing_zeros();
    assert_eq!(exec.mem.len(), 1 << log_mem, "memory is padded to a power of two");
    writeln!(out, "kappa {log_mem}").unwrap();
    writeln!(out, "steps {}", exec.base_counts.iter().sum::<usize>()).unwrap();
    writeln!(out, "cycles {}", exec.cycles).unwrap();
    writeln!(out, "mem_used {}", exec.mem_used).unwrap();
    writeln!(out, "unconstrained_reads {}", exec.unconstrained_reads.len()).unwrap();
    writeln!(out, "min_log_committed {}", program.min_log_committed).unwrap();
    writeln!(out, "main {}", counts(&exec.base_counts)).unwrap();
    writeln!(out, "rows {}", counts(&exec.trace.row_counts())).unwrap();
    let cells: Vec<_> = exec.mem.iter().enumerate().filter(|(_, v)| **v != F192::ZERO).collect();
    writeln!(out, "memory {}", cells.len()).unwrap();
    for (i, v) in cells {
        writeln!(out, "{i} {:x} {:x} {:x}", v.c0, v.c1, v.c2).unwrap();
    }
    let t = &exec.trace;
    // The cells some row accessed (final count not g^0), the hint list of
    // tests/rust/leanisa_contracts.rs; untrusted, a reader's speedup only.
    let accessed: Vec<_> = t
        .mem_count
        .iter()
        .enumerate()
        .filter(|(_, c)| c.0 != 1)
        .map(|(i, _)| i)
        .collect();
    writeln!(out, "accessed {}", accessed.len()).unwrap();
    for i in accessed {
        writeln!(out, "{i}").unwrap();
    }
    let tables: [Vec<(u32, u32)>; 6] = [
        t.xor.iter().map(|r| (r.pc, r.fp)).collect(),
        t.mul.iter().map(|r| (r.pc, r.fp)).collect(),
        t.set.iter().map(|r| (r.pc, r.fp)).collect(),
        t.deref.iter().map(|r| (r.pc, r.fp)).collect(),
        t.jump.iter().map(|r| (r.pc, r.fp)).collect(),
        t.blake2s.iter().map(|r| (r.pc, r.fp)).collect(),
    ];
    for (i, rows) in tables.iter().enumerate() {
        writeln!(out, "table {i} {}", rows.len()).unwrap();
        for (pc, fp) in rows {
            writeln!(out, "{pc} {fp}").unwrap();
        }
    }
    out.push_str("end\n");
    std::fs::write(path, out).unwrap();
}
