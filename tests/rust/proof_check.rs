//! Verify proof files with the pinned leanVM verifier (`lean_vm::cpu::verify`,
//! crates/lean_vm/src/cpu/mod.rs:711 at a386121f84292f6fa663aaa3e570c15bc0240ea2). Built and run
//! by scripts/check-proofs-rust.py. A file is a proof in the text format of
//! scripts/dump-proof-rust.sh, plain or gzip-compressed. Prints one line per file and exits
//! nonzero unless every file is accepted.

use fiat_shamir::merkle::PrunedMerklePaths;
use lean_vm::cpu::{DerefMode, Op, Program, Proof, verify};
use primitives::field::{F64, F192};
use std::collections::HashMap;
use std::panic::{AssertUnwindSafe, catch_unwind};

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

/// The verdict on one file: `Ok` if `verify` accepts it.
fn check(path: &str) -> Result<(), String> {
    let dump = load(&read_text(path)?)?;
    let program = Program::assemble(dump.ops, HashMap::new(), 0);
    // The program hash as the dump script computes it: BLAKE2s of the bytecode table's words, as
    // `Program::assemble` hashes them (crates/lean_vm/src/cpu/mod.rs:237-243).
    let table = lean_vm::cpu::layout::bytecode_table(&program.prog);
    let bytes: Vec<u8> = table.iter().flat_map(|w| w.0.to_le_bytes()).collect();
    let hash = primitives::hash::hash(&bytes);
    if hash != dump.program_hash {
        return Err(format!(
            "program_hash {} but the program hashes to {}",
            hex(&dump.program_hash),
            hex(&hash)
        ));
    }
    verify(&program, &dump.public, &dump.proof).map(|_| ()).map_err(|e| format!("{e:?}"))
}

fn main() {
    let files: Vec<String> = std::env::args().skip(1).collect();
    if files.is_empty() {
        eprintln!("usage: proof-check <proof file>...");
        std::process::exit(2);
    }
    let mut all = true;
    for f in &files {
        match catch_unwind(AssertUnwindSafe(|| check(f))).unwrap_or(Err("panic".into())) {
            Ok(()) => println!("{f}: ACCEPT"),
            Err(e) => {
                all = false;
                println!("{f}: REJECT {e}");
            }
        }
    }
    std::process::exit(if all { 0 } else { 1 });
}
