# leanISA semantic source and coverage ledger

Review date: 2026-09-23. The normative source for these Lean definitions is leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2` (the **semantic pin**). Paths and line
numbers in the source column refer to that commit. The maintained Rust comparison lane
archives `48a904208d682848dac0e18ef8b01ebfc40df9ad` (the **comparison pin**). This
ledger records each semantic choice and a distinguishing control; passing a checker equivalence
proof alone cannot establish fidelity to either external source.

| Clause and pinned source | Adopted typed ISA behavior | Distinguishing evidence |
| --- | --- | --- |
| Fields, generator: `doc/leanvm/body/02-vm-specification.tex:4-12`; `crates/primitives/src/field/gf2_64.rs:19-28` | `K = GF(2^64)`, `E = K[y]/(y³+y+1)`, `g` is the raw bit pattern `0x2` representing `x`, and the first index is `g^0 = 1`. The field's natural-number cast of two is zero; it must not replace the raw encoding. | `Parameters/Field`, `Generator`; generator order and bit-pattern tests in `tests/LeanerVMTests/Parameters/Generator.lean`. |
| Image, addresses, public words: specification `:16-24,37-52`; Rust `crates/lean_vm/src/cpu/execute.rs:173-177`, `crates/lean_vm/src/cpu/mod.rs:139-143` | `MemImage κ` is one fixed, total, `2^κ`-cell image. A read succeeds exactly at an effective address `g^i` with `i < 2^κ`; address zero and out-of-range addresses fail. The first two cells contain the four public 64-bit lanes, with zero top limbs. `16 ≤ κ ≤ 32` is a valid-execution boundary. The ISA does not impose Rust host-index bounds on each register or operand; only effective reads and fetches must be valid. | `Semantics/Memory`, `Execution`, `Executable`; `tests/LeanerVMTests/Semantics/Memory.lean` checks zero/end addresses and each public lane. `Checker.lean` checks size and public-word rejection. The stale-read Rust export is rejected against its final image. |
| Typed instructions and fetch: specification `:16,22,54-68`; Rust `crates/lean_vm/src/cpu/isa.rs:6-66`, `crates/lean_vm/src/cpu/mod.rs:158-159` | A `Program` has exactly `2^logSize` typed instructions, `logSize ≤ 32`. Fetch maps a field counter `g^i` to instruction `i` and rejects other counters. It does not decode raw bytecode. | `Semantics/Instruction`; `tests/LeanerVMTests/Semantics/Instruction.lean` checks first/last and invalid counters. Canonical encoding and the eight-coordinate entry decoder are in `Arithmetization/Bytecode`; its sixteen-slot encoder and round trips have separate tests. |
| XOR, MUL_NATIVE, SET_CONSTANT: specification `:60-62`; tables `doc/leanvm/body/07-instruction-tables.tex:8-66`; Rust `crates/lean_vm/src/cpu/execute.rs:585-643` | The fixed image must satisfy the `E` sum, product, or exact three-limb immediate at the addressed output. Aliases remain equality constraints. A failed input/output read or false equality rejects the step. | `Semantics/Step`, `Executable`; `Execution.lean` checks a three-step multiplication run and its final image, `Checker.lean` checks XOR aliases, wrong MUL/SET results and failed reads. The Rust stale-read export distinguishes the fixed-image check from generator success. |
| DEREF: specification `:71-81`; `doc/leanvm/body/07-instruction-tables.tex:68-90`; Rust `crates/lean_vm/src/cpu/execute.rs:644-744` | The pointer must lie in `K`. All three cells are read in every mode, including the local cell in `.pc` and `.fp`. The target equals the local cell, `g²·pc`, or `fp` respectively; failed reads and a false equality reject. §2 alone does not mention the unconditional local read, so §7.4's three memory interactions decide this point. | Direct success for `.cell`, `.pc`, `.fp` and wrong-target/local-out-of-range rejection in `Execution.lean`; matching `stepChecked` cases in `Checker.lean`. The all-mode table controls remain separate. |
| JUMP: specification `:86`; table `doc/leanvm/body/07-instruction-tables.tex:94-110`; Rust `crates/lean_vm/src/cpu/execute.rs:745-777` | Read condition, destination, and frame cells and require all three in `K` on **both** branches. Nonzero condition jumps to their low limbs; zero falls through to `(g·pc, fp)`. A destination or frame may be outside the Rust runner's host-index search while still being a `K` value; effective later accesses decide ISA validity. | `Execution.lean` checks taken and untaken successors and an untaken branch with a non-`K` destination; `Checker.lean` checks the same. The maintained Rust lane checks the untaken rejection. |
| BLAKE2S: specification `:90-93`; table `doc/leanvm/body/07-instruction-tables.tex:114-136`; Rust `crates/lean_vm/src/cpu/execute.rs:779-812`, `crates/lean_vm/src/hash_flock.rs:117-139,162-185`, `crates/flock/src/hash.rs:191-231` | Four independent message cells, two consecutive chaining-value cells, two consecutive output cells, and one metadata cell must be canonical 128-bit embeddings. Metadata packs a 64-bit counter and two **full** `UInt32` flag words; both words enter compression unchanged. The two outputs must equal the exact ten-round compression. | `Semantics/Blake2s` and `Step`; `tests/LeanerVMTests/Semantics/Blake2s.lean` checks RFC/hashlib, pinned executor data, a distinct non-Boolean two-flag vector, top-limb/output/metadata mutations. `tests/rust/leanisa_contracts.rs` checks the same raw-flag output against the comparison pin. `Execution.lean` and `Checker.lean` check an opcode step. |
| Halting and final registers: specification `:26-35`; bus `doc/leanvm/body/06-bus-interactions.tex:6-8`; Rust `crates/lean_vm/src/cpu/execute.rs:361-371` | The ISA tests for the sentinel **before** fetch. The sentinel instruction is never executed; a one-slot program has a zero-step execution. A successful run ends at `(g^(Nprog-1), 1)`. §2 writes its test after execute and omits the final `fp`; the Rust runner and the bus boundary settle those two discrepancies. `SentinelSafe` is a separate current constraint-soundness premise. | `Semantics/Execution`, `Checker`; `Execution.lean` checks zero-step and early-stop cases, the wrong final frame, and a valid one-slot **JUMP** sentinel that fails `SentinelSafe`. `Checker.lean` checks exact/fuel-bound behavior and the JUMP sentinel. Rust lane checks zero-step and wrong-frame cases. |

## Revision delta affecting the comparison

The two pins differ. The source review compared their relevant paths from committed Git objects,
including the whole diff of `crates/lean_vm/src/cpu/execute.rs`,
`crates/lean_vm/src/cpu/mod.rs`, `crates/lean_vm/src/cpu/hints.rs`,
`crates/lean_vm/src/cpu/layout.rs`, `crates/lean_vm/src/hash_flock.rs`,
`crates/flock/src/hash.rs`, `crates/lean_vm/src/tables.rs`,
`crates/lean_vm/src/constraints.rs`, and the §2 specification.
`crates/lean_vm/src/cpu/isa.rs`, `crates/primitives/src/hash.rs`,
`doc/leanvm/body/07-instruction-tables.tex`, and the compression core at
`crates/flock/src/hash.rs:191-231` are unchanged. The comparison pin adds three execution hints
(`ResolveDeref`, `FrameAddress`, `AllocFrames`) before opcode dispatch; they can change the
constructed image and a runner's success domain, so the Rust lane is evidence at its own pin.
The opcode arms, pre-fetch halt, and flag-word compression are unchanged. The §2 delta adds the
bit-encoding explanation. `crates/lean_vm/src/hash_flock.rs` changes setup caching, while
`crates/lean_vm/src/tables.rs` and `crates/lean_vm/src/constraints.rs` change the quadratic-part
interface used by sumcheck; the full row constraints
remain a different call (`quadratic = false`). These are relevant to later witness/protocol
correspondence and cannot be inferred from the ISA checker proof.

The typed ISA scope excludes arbitrary raw verifier bytecode. `Program.fetch` never runs the
entry decoder. The verifier's broader raw-array input and invalid DEREF flag pairs remain an
explicit T1/verifier binding gap, as recorded in
[status](../roadmap/leanisa-status.md#open-findings-against-the-sources) (R27). No claim that
the actual verifier rejects those arrays follows from the canonical decoder. Similarly,
fixed-image validation and comparison vectors do not prove that every successful Rust runner
result is valid: the maintained stale-read case is a counterexample to that unrestricted claim.

This ledger supports an ISA specification PR over typed programs and canonical encoding. It
does not close the Rust source correspondence, raw verifier-input coverage, T1 completeness,
Flock enforcement, or executable verifier binding.
