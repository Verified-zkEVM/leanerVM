// Loaded as a test-only child of cpu in a temporary archive of the pinned source.
use crate::cpu::{filler, DerefMode, Execution, Op, Program};
use primitives::field::{g_pow, F192};
use std::collections::HashMap;
use std::fmt::Write;

#[test]
fn blake2s_distinct_non_boolean_flag_words() {
    // leanVM a386121f: flock::hash::blake2s_compress consumes both raw u32 words.
    // The corresponding Lean vector is in Semantics/Blake2s.lean.
    let h = [7, 0, 0, 0, 11, 0, 0, 0];
    let m = [
        0x89abcdef, 0x01234567, 0x76543210, 0xfedcba98, 0x33334444, 0x11112222, 0x77778888,
        0x55556666, 0xcafebabe, 0xdeadbeef, 0x0badf00d, 0x0badf00d, 0xbbbbcccc, 0x9999aaaa,
        0xffff0000, 0xddddeeee,
    ];
    assert_eq!(
        flock::hash::blake2s_compress(&h, &m, 64, 0x12345678, 0x9abcdef0),
        [
            0xe9a85163, 0xd16af0a6, 0x2edb90ff, 0xba5be325, 0xbdc018d2, 0x3ce6b68f, 0xbea90143,
            0x8c0e7b0b
        ]
    );
}

#[test]
fn main_steps_exclude_disconnected_fillers() {
    let mut code = vec![Op::Jump {
        oc: 0,
        od: 1,
        of: 0,
    }];
    let mut blocks = Vec::new();
    let dummies = [
        Op::Xor { a: 4, b: 4, c: 4 },
        Op::Mul { a: 4, b: 4, c: 4 },
        Op::Set {
            o: 4,
            k: F192::ZERO,
        },
        Op::Deref {
            o1: 2,
            o2: 0,
            o3: 4,
            mode: DerefMode::Cell,
        },
        Op::Jump {
            oc: 3,
            od: 3,
            of: 3,
        },
        Op::Blake2s {
            ins: [8, 9, 10, 11],
            cv: 4,
            out: 6,
            md: 3,
        },
    ];
    for (table, dummy) in dummies.into_iter().enumerate() {
        for size in filler::SIZES {
            blocks.push(filler::Block {
                pc: code.len() as u32,
                size: size as u32,
                table: table as u8,
            });
            code.extend(std::iter::repeat_n(dummy, size));
            code.push(Op::Jump {
                oc: 0,
                od: 0,
                of: 1,
            });
        }
    }
    code.resize(
        (code.len() + 1).next_power_of_two(),
        Op::Set {
            o: 0,
            k: F192::ZERO,
        },
    );
    let sentinel = code.len() - 1;
    let mut p = Program::assemble(code, HashMap::new(), 8);
    p.filler = blocks;
    let e = p.execute([F192::ONE, F192::from(g_pow(sentinel))]);
    let main_steps: usize = e.base_counts.iter().sum();
    assert_eq!(main_steps, 1);
    assert!(e.cycles > main_steps);
    assert!(e.unconstrained_reads.is_empty());
    assert_eq!(e.cycles, 20);
    assert_eq!(e.mem.len(), 1 << 17);
    emit_fixture(
        "fillers",
        &p,
        &e,
        [F192::ONE, F192::from(g_pow(sentinel))],
        true,
    );
}

fn program(ops: Vec<Op>) -> Program {
    Program::assemble(ops, HashMap::new(), 8)
}

#[test]
fn zero_step_main_does_not_execute_sentinel() {
    let p = program(vec![Op::Set { o: 0, k: F192::ONE }]);
    let e = p.execute([F192::ZERO; 2]);
    assert_eq!(e.cycles, 0);
    assert_eq!(e.base_counts.iter().sum::<usize>(), 0);
    assert_eq!(e.mem[0], F192::ZERO);
    emit_fixture("zero", &p, &e, [F192::ZERO; 2], true);
}

// A revision-specific regression for the known witness-generation mismatch, not a
// desired ISA behavior: the Lean checker must reject this final image.
#[test]
fn returned_image_can_violate_an_earlier_xor() {
    let p = program(vec![
        Op::Xor { a: 2, b: 0, c: 3 },
        Op::Set { o: 2, k: F192::ONE },
        Op::Set {
            o: 4,
            k: F192::ZERO,
        },
        Op::Set { o: 0, k: F192::ONE },
    ]);
    let e = p.execute([F192::ZERO; 2]);
    assert_eq!(e.cycles, 3);
    assert_eq!(e.base_counts, [1, 0, 2, 0, 0, 0]);
    assert!(e.unconstrained_reads.is_empty());
    assert_ne!(e.mem[3], e.mem[2] + e.mem[0]);
    emit_fixture("stale", &p, &e, [F192::ZERO; 2], false);
}

#[test]
fn unwritten_zero_operands_can_match_the_final_image() {
    let p = program(vec![
        Op::Xor { a: 2, b: 3, c: 4 },
        Op::Set { o: 0, k: F192::ONE },
    ]);
    let input = [F192::ZERO; 2];
    let e = p.execute(input);
    assert_eq!(e.base_counts, [1, 0, 0, 0, 0, 0]);
    assert_eq!(e.unconstrained_reads, [2, 3]);
    assert_eq!(e.mem[4], e.mem[2] + e.mem[3]);
    emit_fixture("unwritten_zero", &p, &e, input, true);
}

#[test]
fn later_xor_operand_changes_can_cancel() {
    let p = program(vec![
        Op::Xor { a: 2, b: 3, c: 4 },
        Op::Set { o: 2, k: F192::ONE },
        Op::Set { o: 3, k: F192::ONE },
        Op::Set { o: 0, k: F192::ONE },
    ]);
    let input = [F192::ZERO; 2];
    let e = p.execute(input);
    assert_eq!(e.base_counts, [1, 0, 2, 0, 0, 0]);
    assert!(e.unconstrained_reads.is_empty());
    assert_eq!(e.mem[4], e.mem[2] + e.mem[3]);
    emit_fixture("xor_cancellation", &p, &e, input, true);
}

#[test]
fn returned_image_can_violate_an_earlier_mul() {
    let p = program(vec![
        Op::Mul { a: 2, b: 3, c: 4 },
        Op::Set { o: 2, k: F192::ONE },
        Op::Set { o: 3, k: F192::ONE },
        Op::Set { o: 0, k: F192::ONE },
    ]);
    let input = [F192::ZERO; 2];
    let e = p.execute(input);
    assert_eq!(e.base_counts, [0, 1, 2, 0, 0, 0]);
    assert!(e.unconstrained_reads.is_empty());
    assert_ne!(e.mem[4], e.mem[2] * e.mem[3]);
    emit_fixture("stale_mul", &p, &e, input, false);
}

#[test]
fn untaken_jump_checks_upper_limbs() {
    let p = program(vec![
        Op::Jump {
            oc: 0,
            od: 1,
            of: 0,
        },
        Op::Set { o: 0, k: F192::ONE },
    ]);
    assert!(std::panic::catch_unwind(|| p.execute([F192::ZERO, F192::new(0, 1, 0)])).is_err());
}

#[test]
fn sentinel_with_wrong_frame_is_rejected() {
    let p = program(vec![
        Op::Jump {
            oc: 0,
            od: 1,
            of: 0,
        },
        Op::Set { o: 0, k: F192::ONE },
    ]);
    let g = F192::from(g_pow(1));
    assert!(std::panic::catch_unwind(|| p.execute([g, g])).is_err());
}

fn word(v: F192) -> String {
    format!("(E.ofLimbs {} {} {})", v.c0, v.c1, v.c2)
}

fn instruction(op: Op) -> String {
    let address = |i: u32| format!("({} : K)", g_pow(i as usize).0);
    match op {
        Op::Xor { a, b, c } => format!(".xor {} {} {}", address(a), address(b), address(c)),
        Op::Mul { a, b, c } => format!(".mulNative {} {} {}", address(a), address(b), address(c)),
        Op::Set { o, k } => format!(".setConstant {} {}", address(o), word(k)),
        Op::Deref { o1, o2, o3, mode } => {
            let mode = match mode {
                DerefMode::Cell => "cell",
                DerefMode::Pc => "pc",
                DerefMode::Fp => "fp",
            };
            format!(
                ".deref {} {} {} .{mode}",
                address(o1),
                address(o2),
                address(o3)
            )
        }
        Op::Jump { oc, od, of } => format!(".jump {} {} {}", address(oc), address(od), address(of)),
        Op::Blake2s { ins, cv, out, md } => format!(
            ".blake2s ![{}, {}, {}, {}] {} {} {}",
            address(ins[0]),
            address(ins[1]),
            address(ins[2]),
            address(ins[3]),
            address(cv),
            address(out),
            address(md)
        ),
    }
}

// Serialize data, never results of Lean checking. Zero memory words and adjacent repeated
// instructions are losslessly compressed; every field element is its raw 64-bit bit pattern.
fn emit_fixture(name: &str, p: &Program, e: &Execution, public_input: [F192; 2], valid: bool) {
    let Some(directory) = std::env::var_os("LEANISA_EXPORT_DIR") else {
        return;
    };
    let mut out = String::from("import LeanerVMTests.Semantics.RustExport\n\nopen LeanerVM.Parameters LeanerVM.Semantics\nopen LeanerVMTests.Semantics.RustExport\n\n");
    let encoded: Vec<_> = p.prog.iter().map(|op| instruction(*op)).collect();
    let mut blocks = Vec::new();
    let mut start = 0;
    while start < encoded.len() {
        let mut end = start + 1;
        while end < encoded.len() && encoded[end] == encoded[start] {
            end += 1;
        }
        blocks.push(format!("({}, ({}))", end - start, encoded[start]));
        start = end;
    }
    writeln!(
        out,
        "def codeBlocks : Array (Nat × Instr) := #[{}]",
        blocks.join(",\n  ")
    )
    .unwrap();
    out.push_str(
        "def code : Array Instr := codeBlocks.foldl (fun a b ↦ a ++ Array.replicate b.1 b.2) #[]\n",
    );
    writeln!(out, "#guard code.size = {}", p.prog.len()).unwrap();
    writeln!(
        out,
        "def prog : Program := ⟨{}, by decide, fun i ↦ code[i.val]?.getD (.setConstant 1 0)⟩",
        p.prog.len().ilog2()
    )
    .unwrap();
    out.push_str("#guard SentinelSafe prog\n");
    let cells: Vec<_> = e
        .mem
        .iter()
        .enumerate()
        .filter(|(_, v)| **v != F192::ZERO)
        .map(|(i, v)| format!("({i}, {})", word(*v)))
        .collect();
    writeln!(
        out,
        "def memoryCells : Array (Nat × E) := #[{}]",
        cells.join(",\n  ")
    )
    .unwrap();
    writeln!(out, "def memory : Array E := memoryCells.foldl (fun a b ↦ a.set! b.1 b.2) (Array.replicate {} 0)", e.mem.len()).unwrap();
    let numbers = |ns: &[usize]| {
        ns.iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    };
    writeln!(
        out,
        "def input : TraceInput := ⟨memory, #v[{}], #v[{}], {}⟩",
        numbers(&e.base_counts),
        numbers(&e.trace.row_counts()),
        e.cycles
    )
    .unwrap();
    writeln!(
        out,
        "def publicInput : PublicInput := ⟨![{}, {}, {}, {}]⟩",
        public_input[0].c0, public_input[0].c1, public_input[1].c0, public_input[1].c1
    )
    .unwrap();
    assert_eq!(public_input[0].c2, 0);
    assert_eq!(public_input[1].c2, 0);
    let regs = |pc: u32, fp: u32| format!("⟨{}, {}⟩", g_pow(pc as usize).0, g_pow(fp as usize).0);
    let rows = [
        e.trace
            .xor
            .iter()
            .map(|r| regs(r.pc, r.fp))
            .collect::<Vec<_>>(),
        e.trace
            .mul
            .iter()
            .map(|r| regs(r.pc, r.fp))
            .collect::<Vec<_>>(),
        e.trace
            .set
            .iter()
            .map(|r| regs(r.pc, r.fp))
            .collect::<Vec<_>>(),
        e.trace
            .deref
            .iter()
            .map(|r| regs(r.pc, r.fp))
            .collect::<Vec<_>>(),
        e.trace
            .jump
            .iter()
            .map(|r| regs(r.pc, r.fp))
            .collect::<Vec<_>>(),
        e.trace
            .blake2s
            .iter()
            .map(|r| regs(r.pc, r.fp))
            .collect::<Vec<_>>(),
    ];
    writeln!(
        out,
        "def rows : Vector (Array (Regs K)) 6 := #v[{}]",
        rows.iter()
            .map(|rs| format!("#[{}]", rs.join(", ")))
            .collect::<Vec<_>>()
            .join(",\n  ")
    )
    .unwrap();
    // Hints affect performance only. Lean verifies every hit and searches fully on a miss.
    let mut hints: Vec<_> = e
        .trace
        .mem_count
        .iter()
        .enumerate()
        .filter(|(_, count)| count.0 != 1)
        .map(|(i, _)| i)
        .collect();
    hints.extend(e.trace.xor.iter().map(|r| r.pc as usize));
    hints.extend(e.trace.mul.iter().map(|r| r.pc as usize));
    hints.extend(e.trace.set.iter().map(|r| r.pc as usize));
    hints.extend(e.trace.deref.iter().map(|r| r.pc as usize));
    hints.extend(e.trace.jump.iter().map(|r| r.pc as usize));
    hints.extend(e.trace.blake2s.iter().map(|r| r.pc as usize));
    hints.sort_unstable();
    hints.dedup();
    writeln!(out, "def hints : List Nat := [{}]", numbers(&hints)).unwrap();
    writeln!(
        out,
        "#guard (input.adapt prog).map (·.steps) = some {}",
        e.base_counts.iter().sum::<usize>()
    )
    .unwrap();
    writeln!(
        out,
        "#guard {}validateInput prog publicInput input",
        if valid { "" } else { "!" }
    )
    .unwrap();
    writeln!(
        out,
        "#guard {}checkExport prog publicInput input rows hints",
        if valid { "" } else { "!" }
    )
    .unwrap();
    if name == "fillers" {
        out.push_str(
            "#guard !validateInput prog publicInput { input with mainCounts := input.rowCounts }\n",
        );
        out.push_str("def missingJumpRows := rows.set 4 (rows[4].eraseIdx 1)\n");
        out.push_str("def missingJumpInput := { input with rowCounts := input.rowCounts.set 4 (input.rowCounts[4] - 1), cycles := input.cycles - 1 }\n");
        out.push_str("#guard validateInput prog publicInput missingJumpInput\n");
        out.push_str(
            "#guard !checkExport prog publicInput missingJumpInput missingJumpRows hints\n",
        );
        out.push_str(
            "#guard !checkExport prog publicInput { input with cycles := input.cycles + 1 } rows hints\n",
        );
    }
    std::fs::write(
        std::path::Path::new(&directory).join(format!("{name}.lean")),
        out,
    )
    .unwrap();
}

#[test]
fn nonempty_main_without_fillers() {
    let p = program(vec![
        Op::Set {
            o: 0,
            k: F192::ZERO,
        },
        Op::Set { o: 0, k: F192::ONE },
    ]);
    let input = [F192::ZERO; 2];
    let e = p.execute(input);
    assert_eq!(e.cycles, 1);
    assert_eq!(e.base_counts, [0, 0, 1, 0, 0, 0]);
    assert_eq!(e.trace.row_counts(), e.base_counts);
    emit_fixture("plain", &p, &e, input, true);
}
