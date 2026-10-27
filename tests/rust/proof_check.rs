//! Verify proof files with the pinned leanVM verifier (`lean_vm::cpu::verify`,
//! crates/lean_vm/src/cpu/mod.rs:711 at a386121f84292f6fa663aaa3e570c15bc0240ea2). Built by
//! scripts/check-proofs-rust.py. A file is a proof in the text format of
//! scripts/dump-proof-rust.sh, plain or gzip-compressed.
//!
//! `proof-check <file>...` prints `<file>: ACCEPT` or `<file>: REJECT <reason>` per file and exits
//! nonzero unless every file is accepted; a file whose program hash is not its program's is
//! rejected before `verify` runs.
//!
//! `proof-check serve` reads paths from standard input, one per line, and prints per path
//! `<file>\t<verdict>\t<detail>\t<microseconds>`, flushing after each: the verdict is `ACCEPT`,
//! `REJECT` (the detail is the verifier's error), `PARSEFAIL` (the loader refuses the file) or
//! `PANIC` (the detail is the panic's message); a program hash that is not the program's appends
//! `;hashmismatch` to the detail and `verify` still runs. It exits `0`; the lines carry the
//! verdicts. This is the Rust side of tests/differential/fuzz.py.
//!
//! Both modes refuse a program with an operand exponent above `2^24` (environment variable
//! `PROOF_CHECK_MAX_OPERAND` to change it) before assembling it: `bytecode_columns`
//! (crates/lean_vm/src/cpu/layout.rs:229-241), run by `Program::assemble` and by `verify`,
//! allocates `g^0, ..., g^m` for the largest exponent `m`, 32 GiB at `2^32 - 1`.

use fiat_shamir::merkle::PrunedMerklePaths;
use lean_vm::cpu::{DerefMode, Op, Program, Proof, verify};
use primitives::field::{F64, F192};
use std::collections::HashMap;
use std::io::{BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Instant;

/// What a dump holds, less its rate line: `verify` reads the rate from the stream.
struct Dump {
    ops: Vec<Op>,
    program_hash: [u8; 32],
    public: [F192; 2],
    proof: Proof,
}

/// The file's bytes, gunzipped when they start with the gzip magic.
fn read_text(path: &str) -> Result<String, String> {
    let mut bytes = std::fs::read(path).map_err(|e| format!("read: {e}"))?;
    if bytes.starts_with(&[0x1f, 0x8b]) {
        let out = std::process::Command::new("gzip")
            .args(["-dc", path])
            .output()
            .map_err(|e| format!("gzip: {e}"))?;
        if !out.status.success() {
            return Err("gzip -dc failed".into());
        }
        bytes = out.stdout;
    }
    String::from_utf8(bytes).map_err(|_| "not UTF-8".into())
}

fn word(s: &str) -> Result<u64, String> {
    u64::from_str_radix(s, 16).map_err(|_| format!("bad word `{s}`"))
}

fn scalar(c0: &str, c1: &str, c2: &str) -> Result<F192, String> {
    Ok(F192::new(word(c0)?, word(c1)?, word(c2)?))
}

fn digest(s: &str) -> Result<[u8; 32], String> {
    let mut out = [0u8; 32];
    if s.len() != 64 {
        return Err(format!("bad digest `{s}`"));
    }
    for (i, b) in out.iter_mut().enumerate() {
        *b = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|_| format!("bad digest `{s}`"))?;
    }
    Ok(out)
}

fn num<T: std::str::FromStr>(s: &str) -> Result<T, String> {
    s.parse().map_err(|_| format!("bad number `{s}`"))
}

/// One instruction (`Op`, crates/lean_vm/src/cpu/isa.rs:6-56); an operand is its exponent of `g`.
fn instr(ws: &[&str]) -> Result<Op, String> {
    let o = |s: &str| num::<u32>(s);
    Ok(match ws {
        ["xor", a, b, c] => Op::Xor { a: o(a)?, b: o(b)?, c: o(c)? },
        ["mul", a, b, c] => Op::Mul { a: o(a)?, b: o(b)?, c: o(c)? },
        ["set", d, k0, k1, k2] => Op::Set { o: o(d)?, k: scalar(k0, k1, k2)? },
        ["deref", o1, o2, o3, m] => {
            let mode = match *m {
                "cell" => DerefMode::Cell,
                "pc" => DerefMode::Pc,
                "fp" => DerefMode::Fp,
                _ => return Err(format!("bad deref mode `{m}`")),
            };
            Op::Deref { o1: o(o1)?, o2: o(o2)?, o3: o(o3)?, mode }
        }
        ["jump", c, d, f] => Op::Jump { oc: o(c)?, od: o(d)?, of: o(f)? },
        ["blake2s", i0, i1, i2, i3, cv, out, md] => Op::Blake2s {
            ins: [o(i0)?, o(i1)?, o(i2)?, o(i3)?],
            cv: o(cv)?,
            out: o(out)?,
            md: o(md)?,
        },
        _ => return Err(format!("bad instruction `{}`", ws.join(" "))),
    })
}

/// Read a dump: the lines the dump script prints, in its order, blank lines skipped.
fn load(text: &str) -> Result<Dump, String> {
    let mut lines = text
        .split('\n')
        .map(|l| l.split(' ').filter(|t| !t.is_empty()).collect::<Vec<_>>())
        .filter(|l| !l.is_empty());
    let mut next = |what: &str| lines.next().ok_or_else(|| format!("missing {what}"));
    let bad = |l: &[&str]| format!("unexpected line `{}`", l.join(" "));
    if !matches!(next("header")?[..], ["leanvm-proof", _]) {
        return Err("missing header".into());
    }
    if !matches!(next("rate")?[..], ["rate", _]) {
        return Err("missing rate".into());
    }
    let n = match next("program")?[..] {
        ["program", n] => num::<usize>(n)?,
        ref l => return Err(bad(l)),
    };
    if !n.is_power_of_two() {
        return Err(format!("a program of {n} instructions"));
    }
    let ops = (0..n).map(|_| instr(&next("instruction")?)).collect::<Result<Vec<_>, _>>()?;
    let program_hash = match next("program_hash")?[..] {
        ["program_hash", h] => digest(h)?,
        ref l => return Err(bad(l)),
    };
    // Every limb as written, the third included: the verifier's check on it is under test.
    let public = match next("public")?[..] {
        ["public", a0, a1, a2, b0, b1, b2] => [scalar(a0, a1, a2)?, scalar(b0, b1, b2)?],
        ref l => return Err(bad(l)),
    };
    let n = match next("stream")?[..] {
        ["stream", n] => num::<usize>(n)?,
        ref l => return Err(bad(l)),
    };
    let mut stream = Vec::new();
    for _ in 0..n {
        match next("scalar")?[..] {
            [c0, c1, c2] => stream.push(scalar(c0, c1, c2)?),
            ref l => return Err(bad(l)),
        }
    }
    let p = match next("merkle")?[..] {
        ["merkle", p] => num::<usize>(p)?,
        ref l => return Err(bad(l)),
    };
    let mut merkle = Vec::new();
    for _ in 0..p {
        let (r, s) = match next("phase")?[..] {
            ["phase", r, s] => (num::<usize>(r)?, num::<usize>(s)?),
            ref l => return Err(bad(l)),
        };
        let mut leaf_data = Vec::new();
        for _ in 0..r {
            match next("row")?[..] {
                ["row", w, ref ws @ ..] if num::<usize>(w)? == ws.len() => {
                    leaf_data.push(ws.iter().map(|w| word(w).map(F64)).collect::<Result<_, _>>()?)
                }
                ref l => return Err(bad(l)),
            }
        }
        let mut sibling_hashes = Vec::new();
        for _ in 0..s {
            match next("sibling")?[..] {
                ["sibling", h] => sibling_hashes.push(digest(h)?),
                ref l => return Err(bad(l)),
            }
        }
        merkle.push(PrunedMerklePaths { leaf_data, sibling_hashes });
    }
    if !matches!(next("end")?[..], ["end"]) {
        return Err("missing end".into());
    }
    if let Some(l) = lines.next() {
        return Err(bad(&l));
    }
    Ok(Dump { ops, program_hash, public, proof: Proof { stream, merkle } })
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The largest operand exponent a program may have, `2^24` unless `PROOF_CHECK_MAX_OPERAND` says.
fn operand_cap() -> u64 {
    std::env::var("PROOF_CHECK_MAX_OPERAND").ok().and_then(|v| v.parse().ok()).unwrap_or(1 << 24)
}

/// The largest operand exponent of an instruction, as `bytecode_columns` reads it.
fn max_operand(op: &Op) -> u32 {
    match *op {
        Op::Xor { a, b, c } | Op::Mul { a, b, c } => a.max(b).max(c),
        Op::Set { o, .. } => o,
        Op::Deref { o1, o2, o3, .. } => o1.max(o2).max(o3),
        Op::Jump { oc, od, of } => oc.max(od).max(of),
        Op::Blake2s { ins, cv, out, md } => ins.into_iter().fold(cv.max(out).max(md), u32::max),
    }
}

enum Verdict {
    Accept,
    Reject(String),
    ParseFail(String),
    Panic(String),
}

/// The verdict on one file, whether its program hash is its program's, and `verify`'s time.
struct Checked {
    verdict: Verdict,
    hash_mismatch: bool,
    micros: u128,
}

fn panic_message(e: &(dyn std::any::Any + Send)) -> String {
    match (e.downcast_ref::<&str>(), e.downcast_ref::<String>()) {
        (Some(s), _) => (*s).to_string(),
        (_, Some(s)) => s.clone(),
        _ => "a panic without a message".into(),
    }
}

/// Check one file. With `strict`, a program hash that is not the program's rejects the file
/// before `verify` runs; otherwise it is noted and `verify` runs.
fn check(path: &str, strict: bool) -> Checked {
    let done = |verdict| Checked { verdict, hash_mismatch: false, micros: 0 };
    let dump = match read_text(path).and_then(|text| load(&text)) {
        Ok(dump) => dump,
        Err(e) => return done(Verdict::ParseFail(e)),
    };
    let cap = operand_cap();
    let max = dump.ops.iter().map(max_operand).max().unwrap_or(0);
    if u64::from(max) > cap {
        return done(Verdict::ParseFail(format!(
            "operand exponent {max} above the cap {cap}: `bytecode_columns` would allocate \
             {max} + 1 powers of g (layout.rs:229-241); raise PROOF_CHECK_MAX_OPERAND to run it"
        )));
    }
    let assembled = catch_unwind(AssertUnwindSafe(|| {
        let program = Program::assemble(dump.ops, HashMap::new(), 0);
        // The program hash as the dump script computes it: BLAKE2s of the bytecode table's
        // words, as `Program::assemble` hashes them (crates/lean_vm/src/cpu/mod.rs:237-243).
        let table = lean_vm::cpu::layout::bytecode_table(&program.prog);
        let bytes: Vec<u8> = table.iter().flat_map(|w| w.0.to_le_bytes()).collect();
        (program, primitives::hash::hash(&bytes))
    }));
    let (program, hash) = match assembled {
        Ok(x) => x,
        Err(e) => return done(Verdict::Panic(format!("assemble: {}", panic_message(&*e)))),
    };
    let hash_mismatch = hash != dump.program_hash;
    if strict && hash_mismatch {
        return done(Verdict::Reject(format!(
            "program_hash {} but the program hashes to {}",
            hex(&dump.program_hash),
            hex(&hash)
        )));
    }
    let t = Instant::now();
    let r = catch_unwind(AssertUnwindSafe(|| verify(&program, &dump.public, &dump.proof)));
    let micros = t.elapsed().as_micros();
    let verdict = match r {
        Ok(Ok(_)) => Verdict::Accept,
        Ok(Err(e)) => Verdict::Reject(format!("{e:?}")),
        Err(e) => Verdict::Panic(panic_message(&*e)),
    };
    Checked { verdict, hash_mismatch, micros }
}

/// One field of a `serve` line: no tab or line break inside.
fn field(s: &str) -> String {
    s.replace(['\t', '\n', '\r'], " ")
}

/// The `serve` line of one file.
fn serve_line(path: &str) -> String {
    let c = check(path, false);
    let (verdict, detail) = match c.verdict {
        Verdict::Accept => ("ACCEPT", "accepted".to_string()),
        Verdict::Reject(e) => ("REJECT", e),
        Verdict::ParseFail(e) => ("PARSEFAIL", e),
        Verdict::Panic(e) => ("PANIC", e),
    };
    let note = if c.hash_mismatch { ";hashmismatch" } else { "" };
    format!("{}\t{verdict}\t{}{note}\t{}", field(path), field(&detail), c.micros)
}

fn serve() {
    let mut out = std::io::stdout().lock();
    for line in std::io::stdin().lock().lines() {
        let Ok(line) = line else { break };
        let path = line.trim_end_matches('\r');
        if !path.is_empty() {
            let _ = writeln!(out, "{}", serve_line(path));
            let _ = out.flush();
        }
    }
}

fn main() {
    // Panics are caught and reported per file; the default hook would print each to stderr.
    std::panic::set_hook(Box::new(|_| {}));
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() == 1 && args[0] == "serve" {
        serve();
        return;
    }
    if args.is_empty() {
        eprintln!("usage: proof-check <proof file>... | proof-check serve");
        std::process::exit(2);
    }
    let mut all = true;
    for f in &args {
        match check(f, true).verdict {
            Verdict::Accept => println!("{f}: ACCEPT"),
            Verdict::Reject(e) | Verdict::ParseFail(e) => {
                all = false;
                println!("{f}: REJECT {e}");
            }
            Verdict::Panic(e) => {
                all = false;
                println!("{f}: REJECT panic: {e}");
            }
        }
    }
    std::process::exit(if all { 0 } else { 1 });
}
