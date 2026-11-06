# Intermediate representation route

This note answers one question from the project lead. Can leanVM's Rust verifier be compiled to
an intermediate representation (IR) that has a mechanised semantics, is shared by several
languages, and leaves less of the compiler in the trusted base, so that a proof of the IR program
against leanerVM's Lean `verify` is easier and more trustworthy? It is a proposal for review.
Nothing it describes is built in this repository.

It extends [the Rust verifier correspondence note](rust-verifier-correspondence.md) (the
companion note) and assumes its statement, its target and its routes. The statement is one
inclusion: whenever the Rust verifier accepts, `verify` accepts. The target is the portable
verifier crate backported to the leanVM pin (backport commit `48614e15`). This note was written on
2026-11-06. A figure is either measured in this survey (see [evidence](#evidence)) or cited to a
dated external source.

## Answer in brief

- **Such IRs exist, but none gives everything at once.** WebAssembly has the best mechanised
  semantics and runs the standard-library build of our verifier unchanged. RISC-V machine code
  takes the whole compiler out of the trusted base. C with CompCert has the only verified back
  end, but the one Rust-to-C compiler tried failed. LLVM IR and Cranelift IR are not ready.
- **Two rules decide what an IR is worth.** First, the trust cut moves down to the lowest
  representation tied to the shipped artefact by proof: built from the proved program by a
  verified step, or linked to it by a per-build check. Second, whatever executes that
  representation, and the fidelity of its semantics, set the trusted base that remains.
- **Proving at an IR is not easier than proving at source.** Below the source, memory is one flat
  byte array and the standard library is compiled into the program. Those costs dominate, so a
  whole-program IR proof costs about as much as a machine-code proof. The gain is trust and
  portability, not proof effort.
- **Recommendation.** Keep the companion note's source-level proof as the primary route. Tie the
  shipped Wasm module to its model by a per-build check, which moves the trust cut to the module.
  RISC-V removes the whole compiler. leanISA is the IR of a different verifier, the recursion
  guest.

## Terms

The *trusted base* of a claim is everything it assumes without a machine-checked proof: tools,
models, compilers and hardware. Lean's kernel and leanerVM's specification are in every trusted
base, and the lists below omit them. The other terms are:

- *Front end* and *back end*: the compiler stages before and after the IR.
- *Translation validation*, or a *per-build check*: an automatic check, on each build, that one
  compiler output is equivalent to its input, in place of a proof that the compiler is correct.
- *Program logic*: proof rules, in a proof assistant such as Lean, Rocq (formerly Coq), Isabelle
  or HOL4, for showing that a program meets a specification. *Separation logic* is one for code
  over a shared mutable memory. *Partial correctness* proves the result right if the program
  stops, not that it stops.
- *SMT solver*: an automatic decision procedure for formulas over bit vectors and arithmetic.
- *JIT*: a just-in-time compiler, run by a Wasm engine on the host each time it loads a module.
- *Wasm* (WebAssembly): a portable, sandboxed stack-machine bytecode run by browsers and engines.
- *LLVM IR*: the typed, single-assignment IR that rustc, Clang, Swift and Zig pass to LLVM.
- *Cranelift*: the code generator of the Wasmtime engine, also a rustc back end.
- *CompCert*: a C compiler written in Rocq and proved to preserve the semantics of the program.
- *Sail*: a language for instruction-set specifications, in which the official RISC-V model is
  written and then translated to Lean, Rocq and Isabelle.
- *WasmCert*: mechanised Wasm semantics in Rocq (WasmCert-Coq) and Isabelle, each with a proved
  interpreter extracted from the proof assistant.
- *Talos*: an executable Lean 4 Wasm semantics with a program logic for compiled modules (Cajal
  Technologies, started 2026-05-21).
- *xv6iris*: a proof of the GCC-compiled kernel of the xv6 teaching operating system against
  the Sail RISC-V model.
- *zkDSL*: leanVM's language for guest programs, compiled to leanISA bytecode.

## Where the proof sits

```text
Rust source
    |  rustc front end, LLVM middle end        <- leaves the trusted base
    v
IR program   == proved against Lean `verify` under a mechanised IR semantics
    |  back end, JIT, interpreter or hardware  <- stays trusted: the executor
    v
verdict

Also trusted: the IR semantics' fidelity, the decoder into the proof assistant, the host interface.
```

A proof about the IR program itself turns a front-end bug into a failed proof instead of a hidden
one.

## Rule 1: the trust cut moves to the lowest representation tied to the artefact by proof

A proof about one representation of the verifier extends down a chain of links. Each link builds
the next representation by a verified step, or checks it on every build against the one above.
The trust cut sits at the lowest representation the chain reaches, and the shipped artefact must
be that representation or be built from it. The stages above the cut leave the trusted base. The
unverified build stages below it stay.

Verification tools such as Kani, SAW's Crucible, KMIR (rustc's mid-level IR, MIR, in the K
framework), MiniRust and Charon (for Aeneas) translate Rust into IRs of their own, which the
deployed binary never passes through. A proof there, with no link to the artefact, is about a
model, and rustc and LLVM stay fully trusted, as in the companion note's source-level route. Hence
the per-build check in the recommendation.

Without such a check only an IR on the build path can move the cut: LLVM IR, Cranelift IR, C, Wasm,
or machine code such as RISC-V. Rust, C and C++, Zig and Go all reach Wasm and RISC-V. For LLVM IR
the link also needs a reproducible build, because the IR is a transient file. A Wasm module is the
shipped bytes themselves.

The proof covers only the artefact the chain reaches, so the deployment must ship that artefact.
A proof about the Wasm module says nothing about the native x86-64 binary that rustc builds from
the same source. Whether leanVM ships a Wasm or RISC-V verifier is a product decision.

## Rule 2: the executor and the semantics' fidelity set what remains

Whatever runs the IR, and the fidelity of the mechanised semantics to it, take the compiler's
place in the trusted base. The host interface and the decoder into the proof assistant are always
in it. There are four kinds of executor:

- **A verified back end.** Only C has one: CompCert 3.18 (released 2026-08-31). No Wasm-to-native
  compiler is proved to preserve semantics. vWasm proves sandbox safety only (USENIX Security
  2022). LLVM's back end is unverified. For Cranelift only the instruction-selection rules are
  verified, by an SMT solver, for aarch64, in Wasmtime's CI since 2026-08-27 (PR #14207).
- **A mechanised interpreter.** WasmCert-Coq's extracted interpreter matched the native verdicts
  and digests on ten proofs, at 124 s against 20 ms native, about 6,000 times slower (measured). Its
  trusted base is Rocq extraction, the OCaml toolchain, 31 parameters about persistent arrays
  with their OCaml implementation, the numeric shims and an unverified binary parser.
- **Hardware.** For RISC-V machine code the trusted base is the chip, the Sail model's fidelity
  to it, Sail's translation to Lean, the loader and entry state, and the proof's environment
  assumptions (privilege mode, alignment, no interrupts). xv6iris found a bug in both the model
  and the translation.
- **A zkVM.** For leanISA bytecode, leanerVM's headline theorem (knowledge soundness under a named
  BLAKE2s hypothesis) covers execution.

**Corollary.** An interpreter compiled by Lean's compiler, such as Talos's runner or the Sail
Lean emulator, puts Lean's compiler in the trusted base. Shipping the compiled Lean `verify` (the
companion note's [route 2](rust-verifier-correspondence.md#2-the-lean-verifier-as-a-second-check))
has the same trusted base, needs no decoder and is likely faster (inferred: Talos's runner was not
built). Such an IR route buys nothing over route 2.

## Is proving at the IR easier?

Against machine code, partly. Wasm has structured control flow and typed locals, and LLVM IR has
single-assignment values. Neither has registers or calling-convention plumbing.

Against source, no. Two costs appear at every level below the front end:

- **Memory and erased types.** `Vec`, iterators and `BTreeMap` become pointer arithmetic over one
  flat memory, which in Wasm holds both the heap and the stack of the compiled code. Aeneas gets
  ownership and non-aliasing from the Rust types. At an IR a separation logic must rebuild them.
- **The standard library is compiled in**: `BTreeMap`, sort, destructors and the allocator. One
  crate-only O3 LLVM build has 157 defined functions, 63 of them from the standard library. The
  Wasm module has 240 to 280 functions and 146,000 to 150,000 instructions, with the dlmalloc
  allocator inside (measured). Aeneas takes 101 standard-library items as axioms. At an IR they
  are proved at the pointer level: a gain for trust and a loss for effort.

Precedents give the effort a scale:

- Talos needed 17,977 Lean lines (302 generated) for a module of 56 functions and 7.9 KB of code,
  compiled from a 38-line mergesort with a `Vec`-based driver and a 147-line bump allocator (Talos
  `d7c84ac`, 2026-11-02). At that rate our 337 KB module needs of the order of 10^6 lines.
- xv6iris proved 8,725 instructions of GCC-compiled kernel against Sail RISC-V in about
  1.6 million Rocq lines, a fifth of them generated, in 102 days with AI agents (arXiv 2609.04043
  v3, 2026-10-12), later ported to about 755,000 Lean lines. At that rate our verifier needs of
  the order of 10^7 lines. The two precedents differ tenfold, so they fix a scale only.
- Our verifier is about 135,000 instructions as a whole RISC-V program (75,000 on the panic-free
  call graph) and 150,000 Wasm operators (measured), 15 to 17 times the xv6 kernel text.
- At source, the companion note estimates 20,000 to 36,000 proof lines, with 101 library items
  axiomatised. Its loop pilot took about 40 lines per loop, with callee specifications assumed.
- Cheaper precedents do not transfer. EquiVM/Stele proved 35 production EVM contracts against
  Lean models, compiler untrusted, with AI agents (arXiv 2607.26306 v2, 2026-10-20), but EVM
  bytecode carries no allocator or compiled standard library. SAW proved AWS-LC's SHA-384, HMAC
  and AES-GCM at LLVM bitcode against Cryptol, by SMT for bounded input sizes over an unverified
  semantics, which cannot cover our input-dependent loops.

A whole-program IR proof therefore costs about as much as a machine-code proof. What the IR adds
is trust, since the front end leaves the trusted base, and portability across languages and
engines.

## The candidates

| IR | Reached by | Mechanised semantics | Program proofs at scale | Executor and its trust | Verdict |
|---|---|---|---|---|---|
| Wasm | Rust, C and C++, Zig, Go | WasmCert in Rocq and Isabelle. Talos in Lean 4, with a program logic, young, AGPL-3.0. All executable | small: Talos's mergesort and gcd | JIT, unverified, 1.0 to 1.2 times native on V8 and Wasmtime. Mechanised interpreter, 6,000 times native (both measured) | best IR for semantics and execution. No verified native back end |
| RISC-V machine code | rustc, Clang, GCC, Go, Zig | official Sail model, in Lean, Rocq and Isabelle | xv6iris, a whole binary; two of our kernels, including a memory kernel (measured) | hardware or a zkVM. The chip, the model and its Lean translation, the loader and the environment assumptions; no compiler | removes the whole compiler. Machine-code effort |
| C with CompCert | Rust via `rustc_codegen_clr` (failed, measured); mrustc, Eurydice, llvm-cbe (untested) | CompCert's C semantics and the VST program logic, in Rocq. Lean has a prototype C semantics only | VST proof of SHA-256: 235 C lines, 6,539 proof lines (2015) | CompCert, verified | not recommended: no tested Rust path |
| LLVM IR | Rust, C and C++, Swift, Zig | Vellvm in Rocq, missing 7 of the 18 intrinsics rustc emits here. VeIR in Lean, executable, no program logic | compiler correctness only | LLVM back end, unverified. Poison and undefined behaviour | not recommended |
| Cranelift IR | Rust, Wasm engines | none for the whole language | none | lowering rules verified by an SMT solver, aarch64 only | not yet |
| Own-language verified compilers: Pancake and Flapjack, CakeML, Bedrock2, Jasmin | their own languages | yes, in their proof assistants. Flapjack in Lean | yes, outside Lean: fiat-crypto, libjade, CakeML proof checkers | verified compiler to machine code | requires a rewrite of the verifier. Flapjack is too young |
| leanISA bytecode | the zkDSL only | leanerVM's own `step` | none: no program logic | leanVM's proof system, covered by leanerVM's headline theorem | for a different verifier, the recursion guest, not the Rust one |

### WebAssembly

Wasm is the closest fit to the lead's description. Its semantics is mechanised in Rocq,
Isabelle and Lean, and all three mechanisations are executable. Rust supports it officially
(Tier 2). Our crate's standard-library build runs unchanged, as a module with no imports, no
floating point and no SIMD. The `wasm32v1-none` build needs a no-standard-library patch of 68
changed lines and then validates as the original Wasm 1.0 core (measured).

Seven engine configurations (V8, Wasmtime, three Wasmer back ends, wasmi and wasm3), two versions
of the official reference interpreter (2.0.2 on six of the ten cases) and WasmCert-Coq returned
the native verdicts on one honest proof and nine tampered ones. V8 and Wasmtime ran the 30-proof
corpus at 1.0 to 1.2 times native time (measured).

Its weak points are the executor (Rule 2) and the Lean semantics. Talos is under six months old and
proves partial correctness only. Its semantics is tested (64,769 testsuite assertions pass), not
proved against the official specification, and its validator is incomplete. It is AGPL-3.0 on Lean
v4.35.0; leanerVM is Apache-2.0 on v4.34.1. The official SpecTec specification's Lean back end is
one unmerged branch that leaves the bitwise operations opaque.

### RISC-V machine code

A proof about the RISC-V binary removes the whole compiler from the trusted base. The official
Sail model is in Lean, and xv6iris shows that a whole compiled binary can be proved against it.
Both are RV64, so the proof target would be the companion note's `riscv64gc` build. Our
`riscv32im` build is execution evidence only: after the same no-standard-library patch it has
134,529 static instructions in 201 functions, and under QEMU it gives the native verdict on the
honest proof and all 18 tamper runs, at 172 million instructions per verification (measured).

Two gaps are known. The Lean model of the riscv-zkvm project (Verified-zkEVM, v0.3.1, an RV64IM
model proved equal to the Sail model instruction by instruction, with a program logic) lacks most
RV64 32-bit word operations, such as `ADDW`. Our RV64 build has about 900 of them, for `u32`
arithmetic like BLAKE2s (measured). Running on RISC-V hardware or a RISC-V zkVM is also a
deployment change from today's x86-64 and AArch64.

A pilot on that program logic closed the case on which the companion note's x86 pilot with
Kraken had failed (measured in this survey):

- **The BLAKE2s mixing step is proved** from its object-file bytes: 31 rustc `-O3` RV64
  instructions, 4 loads and 4 stores, including the return, in about 3 minutes of checking and
  60 hand-written proof lines. Kraken had stopped on the same kernel's second store after 23
  minutes.
- **The carry-less multiply core is proved** too: 72 instructions, with stack spills, a constant
  loaded from read-only data and the restoration of the callee-saved registers. It took about 7
  minutes and 3.4 GB. Kraken's x86 proof had covered the function body only.
- **What it took.** The one missing word operation, `SRLIW`, was added to a local copy of the
  model in about 50 lines, with its equality to Sail proved in 3. A tactic fix was backported
  from the project's main branch, and four register-aliasing lemmas were added.
- **Scaling.** Checking time grows faster than linearly in block length: 0.14 s, 0.72 s, 7.2 s and
  67 s for 4, 8, 16 and 31 instructions. It also grows with the number of memory cells in scope.
  A proof must be cut into blocks of 10 to 30 instructions, and a single block of 72 did not
  finish in 30 minutes.
- **Still trusted or missing.** The theorems are about the project's model, tied to Sail one
  instruction at a time. Lifting a whole run to a Sail run is not yet done. The bytes are decoded
  by the project's own decoder, which is not tied to Sail. Both proofs use `bv_decide`'s
  certificate axioms (the companion note's obstruction 5).

So machine-code proofs of memory kernels are practical on RISC-V today, at minutes per kernel. The
whole verifier is still about 135,000 instructions.

### C with CompCert

C is the only IR with a verified executor, CompCert. The Rust-to-C front is untested beyond one
tool. `rustc_codegen_clr`'s C
mode stopped with an internal compiler error in the standard library before it reached the
verifier (measured). `rustc_codegen_c` handles toy examples only. mrustc, llvm-cbe and Eurydice
were not tried. A VST proof of the C would be in Rocq, with `verify` restated there by hand, an
unproved link between two specifications.

Eurydice compiles Charon's export, which already covers the crate, to C. One export could then
feed both the Aeneas proof and a CompCert build, with no per-build check, trusting Charon, the two
translations and CompCert's unverified front instead of LLVM. Eurydice's tests barely use `Vec`
and never `BTreeMap`, so the collections would probably have to become arrays first.

### LLVM IR and Cranelift IR

A proof of rustc's optimized LLVM IR takes rustc and LLVM's optimizer out of the trusted base, but
the LLVM back end stays. Its semantics adds poison values (LLVM's marker for the result of an
invalid operation) and undefined behaviour, and neither Vellvm nor VeIR can carry a proof of our
crate today. Cranelift IR is cleaner, but no proof assistant has a semantics for the whole language,
and Rust on Cranelift is a debug-build back end.

### Languages with their own verified compiler

Pancake, CakeML, Bedrock2 and Jasmin each pair a source language with a compiler verified down to
machine code, so using one means rewriting the verifier. Only Flapjack, a Lean 4 port of Pancake's
compiler, keeps the proof in Lean. It started on 2026-09-04, its compiler theorem targets a RISC-V
model whose link to Sail covers 37 instructions and is not composed with the theorem, and its README
says the theorem "might not mean anything" yet. The others would need `verify` restated in HOL4,
Rocq or EasyCrypt.

### leanISA bytecode

leanISA answers a different question. For recursion the verifier that matters is not the Rust
one but the zkDSL guest `aggregate.py`, compiled to leanISA bytecode. Its semantics is the one
leanerVM's headline theorem already uses, so no new model enters the trusted base. The guest is a
checker with prover hints, so the theorem reads "if some hints make the guest execution valid,
then `verify` accepts". It needs a program logic over leanISA `step` (the companion note's route
[6](rust-verifier-correspondence.md#6-the-recursion-guest-over-leanisa)).

## Recommendation

1. **Do not move the primary route to an IR.** Keep the companion note's Charon and Aeneas proof.
   An IR proof costs machine-code effort, and a per-build check from the source model aims at the
   same trust gain for less.
2. **Use Wasm as the target of the per-build check.** Prove once at source that the Aeneas model
   implies `verify`. Then check, for each build, that the shipped Wasm module refines the model
   under Talos's semantics: the companion note's
   [route 5](rust-verifier-correspondence.md#5-hybrid-source-proofs-with-a-per-build-machine-code-check)
   moved to Wasm. By Rule 1 rustc, LLVM, Charon and Aeneas then leave the trusted base. The module
   must be built from the revision the model came from, the rewritten crate. No such checker
   exists, and three parts are hard. The module is inlined (240 functions against the model's 795
   definitions), so the check relates compositions of model functions to module functions. The
   compiled standard library and allocator need a one-off hand proof against the model's library
   definitions. Nothing yet relates Aeneas values to linear memory. Talos's closest precedent
   relates unoptimized and optimized builds of two programs, over the same memory, not a typed
   model to a module. Building on Talos is also a licence and toolchain decision.

   Under Wasmtime, Talos's semantics and decoder and the JIT replace the compiler. The JIT is
   smaller than LLVM but runs at every load on every host, so a miscompile reaches every
   verifier. Its verified rules cover aarch64 only, and the critical aarch64 miscompile
   CVE-2026-34971 (2026-04-09) arose where their model lagged the sources. Under V8 no rule is
   verified. Compiling ahead of time (`wasmtime compile`) makes the output testable once.
3. **To remove the whole compiler, target RISC-V.** On hardware the trusted base is the one Rule 2
   lists, with no compiler in it, at machine-code proof effort: minutes of checking per kernel in
   the pilot, for a program of about 135,000 instructions.
4. **For recursion, use leanISA**, for the zkDSL guest rather than the Rust verifier. It needs a
   program logic.
5. **Collect cheap evidence now.** Add the Wasm build to the companion note's differential
   harness. Keep WasmCert-Coq as an independent mechanised
   oracle for offline spot checks, at minutes per proof. Try translating the module to C with
   wasm2c or w2c2 and compiling it with the installed CompCert 3.18: a verified back end for Wasm,
   trusting the translator and its runtime macros.

## Evidence

The probes and reports of this survey are under `/home/devops/scratch/leanerVM-rustfv/ir/`,
outside the repository: the reports in `reports/` and the measurements in `probes/`. The
companion note lists the earlier probes, including the RV64 binary census.

| Probe | What it measured |
|---|---|
| Wasm builds | sizes, functions, instruction mix and feature use of four modules: `wasm32-unknown-unknown` and `wasm32v1-none`, each with and without overflow checks |
| Engines | verdicts and result digests on one honest proof and nine single-byte tampers, on ten engine configurations. The 30-proof corpus on V8 and Wasmtime. Timings and operator counts |
| WasmCert-Coq | a build from source, and 16 runs of the extracted interpreter |
| LLVM IR | whole-program census after link-time optimization, at O0 and O3, for wasm32, x86-64 and riscv64gc |
| C | an attempt with `rustc_codegen_clr` in C mode (45-minute time box) |
| RISC-V | a `riscv32im` bare-metal build, its census, and 18 tamper runs under QEMU. The RV64 word instructions of the earlier `riscv64gc` build |
| Literature | reports on Wasm, compiler IRs and low-level instruction sets, and a fact-check of them against cloned repositories and papers |

| Item | Revision or version |
|---|---|
| Target | leanVM backport `48614e15` on the local branch `rustfv/portable-verifier-at-pin`, not pushed |
| Rust | rustc 1.99.0 stable, release profile with thin link-time optimization and one codegen unit; nightly-2025-10-15 for `rustc_codegen_clr` `a9aa553` |
| Wasm tooling and engines | wasm-tools 1.263.0, Wasmtime 50.0.1, Node 26.12.1 (V8 14.6), Wasmer 7.5.0 (three back ends), wasmi 2.0.0, wasm3 `28ecb9a`, reference interpreter 3.0.0 (spec `859d3232`) and 2.0.2 |
| WasmCert-Coq | `58a3d3f`, on Rocq 9.2.0 and OCaml 5.3.0 |
| RISC-V | qemu-riscv32 10.2.1 |
| Read, not built | Talos `d7c84ac` (2026-11-02), Vellvm, VeIR, xv6iris (fork `d4f2082`), riscv-zkvm `6810fc1`, Flapjack, Eurydice `08b84e0`, CompCert 3.18 |
