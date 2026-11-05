# Rust verifier correspondence

This note surveys how to prove that leanVM's Rust verifier is correct with respect to leanerVM's
executable Lean verifier, and it recommends a route. It is a proposal for review. Nothing it
describes is built in this repository.

It was written on 2026-11-05 against three revisions:

- leanerVM `ca9c3be5cbe349708709aa4dac4968e96e480d73`, the head of PR #185
  (`feat/headline-execution`);
- leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`, the revision leanerVM pins (the pin);
- leanVM `8c31abd7`, which adds the portable verifier crate `crates/verifier`.

A number is either measured in this survey (the probes listed in the
[evidence appendix](#evidence-appendix)) or cited to a dated external source. Effort figures are
estimates and are marked as such.

## Summary and recommendation

**The claim.** Knowledge soundness of a Rust verifier follows from one inclusion: whenever the
Rust verifier returns `Ok`, Lean's `verify` returns `true` on the same statement and proof. This
is a one-directional refinement under partial correctness. A Rust panic, abort, hang or extra
rejection does not weaken it. leanerVM's BLAKE2s headline theorems mention `verify` only in their
acceptance event, so the inclusion carries them over unchanged.

**The target.** Verify the portable Rust verifier crate, backported to the pin's protocol. The
crate has 2,352 lines of code, no dependencies, no `unsafe`, no threads and no floating point. The
backport adds 20 lines and removes 11. It agrees with the pin's verifier on a 30-proof corpus
and on 24,865 mutated or tampered proofs, with no divergence (measured in this survey). The pin's
own verifier shares its crates with the prover, runs a thread pool and derives parameters in
floating point. It is the wrong target.

Nothing deploys the backport today. The theorem is about the pin's protocol, which leanerVM
formalizes. It covers a deployed binary only if leanVM ships the portable crate for that
protocol, or after leanerVM moves its pin to the revision that ships the crate (now with
Keccak-256) and the proof moves with it. Against the pin's own verifier the only link is the
differential evidence below.

**The route.** Translate the crate into Lean with Charon and Aeneas, and prove the inclusion
against `verify` in Lean. State the deployment conditions in the theorem: the caller uses the
verifying entry point with pruned openings, and the verifier is built with
`overflow-checks = true`, by the pinned compiler, for the stated target. Of the routes with a
usable toolchain today, this is the only one that states a theorem about the Rust source against
the existing Lean specification. A proof about the whole machine-code binary is not feasible in
2026. A hybrid that adds an automatic machine-code check per build is the long-term way to
remove the Rust compiler from the trusted base.

**Meanwhile.** Keep the differential tests in CI. Where 0.8 s per verification is acceptable,
deploy the compiled Lean verifier next to the Rust one, and accept a proof only if both accept.

**The cost (estimate).** The crate needs about 80 source rewrites before Aeneas translates it
(measured). A proof then needs about 100 standard-library models and 128 loop invariants
(measured counts), and a few lemmas where the Rust and Lean algorithms differ (listed in
[the plan](#recommended-plan)). By the proof-to-code ratios of the nearest precedent, that is
20,000 to 36,000 proof lines. At an assumed 3,000 proof lines per person-month with agent
assistance, it is 6 to 12 person-months for a first proof. The rate is judgement. A pilot proved
10 of the 128 loops at a median of about 40 proof lines each, which puts the loops near the low
end; [route 3](#3-source-level-charon-and-aeneas) says what would move the figure threefold. After that, an upstream change costs the re-proof of the functions it
touches.

## What has to be proved

### The Lean side

[`verify`](../../LeanerVM/Protocol/Verify.lean) has the type
`Program → PublicInput → Proof PrunedMerklePaths → Bool`. It is total and computable, by
structural recursion without fuel, and a malformed proof gives `false`. It is the BLAKE2s-256
instance of `verifyWith H`, which is generic in the hash `H` and its monad. The statement has two
parts. The program maps an index set of size `2^k` to instructions whose operands lie in
`K = GF(2^64)`. The public input is four `K` lanes, 32 bytes. The proof is a stream of
`E = GF(2^192)` scalars and the pruned Merkle openings. Its stream mirrors the Rust
`Proof::stream`, and its openings are the Rust `MerkleOpenings::Pruned` arm. The crate also
accepts `MerkleOpenings::Raw`, every path expanded, which `Proof::load` produces and which Lean
has no counterpart for. Compiled, `verify` accepts the Rust fixture proof in 0.76 to 0.81 s
([bench/README.md](../../bench/README.md), 2026-10-25).

### One inclusion suffices

A *refinement* proof shows that every behaviour of an implementation is allowed by its
specification. Here only one behaviour matters, acceptance, and only in one direction. In outline,
the theorem has this shape. It is a sketch, not code in the repository:

```lean
-- `rustVerify` is the Aeneas model of `verifier::verify_execution`. `ok` means the model
-- returned without a panic and terminated. `tableOf`, `bytesOf` and `proofOf` are encodings;
-- `proofOf` is defined on proofs with `Pruned` openings (see the deployment conditions).
theorem rustVerify_sound (prog : Program) (input : PublicInput) (p : RustProof) (s : Summary)
    (h : rustVerify (tableOf prog) (bytesOf input) p = ok (.Ok s)) :
    verify prog input (proofOf p) = true
```

The headline `baseVerifier_extractsExecution` in
[Headline.lean](../../LeanerVM/Protocol/Headline.lean), with its adaptive and randomized forms,
has this shape. With BLAKE2s answering the hash, the probability that `verify` accepts the
adversary's proof while the extractor finds no valid execution is at most δ. Here δ is the
probability of the named hypothesis that BLAKE2s misbehaves on the run. The event is monotone in
the verdict. Suppose that Rust acceptance implies `verify` acceptance. Then the event with Rust
acceptance is a subset of the event with `verify`. It has the same bound, with the same game,
extractor and hypothesis. An adversary that outputs a program, a public input and a Rust proof is
a Lean adversary followed by the pure map `proofOf` on its proof (`isQueryBound_map_iff` keeps
its query bound). The theorem covers it, with the named hypothesis stated at that composed
adversary. The Rust game must take the program, not the table: `tableOf` is not onto, so a table
the caller did not compute from a program is outside every theorem here.

Proving only this direction makes every route cheaper:

- no termination proof and no resource bound is needed;
- a panic, out-of-memory abort or hang is a rejection;
- an error path needs only the fact that it does not return `Ok`.

### What does not transfer

**Completeness.** The converse inclusion says that Lean acceptance implies Rust acceptance with
termination. It is an availability property. With `prove_complete`, it gives "the Rust verifier
accepts every proof that Lean's `prove` returns". It says nothing about proofs from the Rust
prover, which differs from `prove` in its witness and opening order
([leanvm-target.md](../leanvm-target.md)). In total form it is false for the deployed entry
points and untested for the crate (see [the obstructions](#obstructions)), so it needs a resource
hypothesis. Differential tests cover it in the near term.

**The random-oracle theorems.** Their event concerns `verifyWith H` at an arbitrary oracle `H`. A
Rust model with BLAKE2s built in equals `verify` only at `H = BLAKE2s`. Transfer would need a
model with the hash as a parameter. It is not needed for deployment. The BLAKE2s headline is the
deployed claim, and the theorem that supports its hypothesis concerns the Lean game, which the
Rust verifier does not change.

### The interface of the statement

The portable crate takes the *stacked bytecode table* (`&[u64]`, prepared once by
`Bytecode::new`), 32 public-input bytes and a `Proof` structure or its bytes. It does not take
the program. A statement can be made at three levels:

| Level | Needs, beyond the crate | Cost |
|---|---|---|
| Table | the Lean encoder `bytecodeColumn`, which `verify` already uses; the statement stays quantified over programs | cheapest |
| Program | the program-to-table encoder (about 60 Rust lines in `leanvm_core`, inferred from the pin's code), modelled or defined in Lean; the caller's rejection of a nonzero third public-input limb | small |
| Bytes | a Lean model of `Proof::load` (24-byte little-endian scalars), and a conversion of raw openings to pruned ones, since `Proof::load` produces only `Raw` | small; the parser need not be injective |

Lean's `PublicInput` cannot express a nonzero third limb, so the encoding covers only inputs the
Rust caller does not reject. The recommended first statement is at the program level over proofs
with pruned openings. The `Raw` arm waits for the conversion of the Bytes level. Upstream's own
caller builds the `Pruned` form from the prover's output (`scalar_proof`, `cpu/mod.rs:656-667`
at `8c31abd7`), as does this survey's harness; `Proof::load` reads the Python verifier's byte
format.

## Which Rust verifier

### The pin's verifier is the wrong target

At the pin, `lean_vm::cpu::verify` spans seven crates that also hold the prover. After link-time
optimization, its call graph has 625 functions and 105,000 x86-64 instructions. These come from
1,647 first-party source lines and 2,363 standard-library lines (measured). It uses `unsafe`,
static caches behind mutexes and `&dyn` calls. It runs a thread pool by default, with 31 workers
active during one verification (measured with `strace`). It derives the WHIR parameters with `f64`
arithmetic and `libm` at run time. Every one of these features enlarges the model a proof needs.
Its field code also picks hardware or software arithmetic by compile-time configuration (`cfg`),
and Charon translates one configuration per run (measured). On this survey's machine, which has
AES instructions but no `PCLMULQDQ`, Charon selected the software multiply; with `PCLMULQDQ`
enabled it left the intrinsics as axioms. A proof would cover one configuration only.

### The portable crate, backported to the pin

Upstream commit `8c31abd7` (leanVM PR #635) adds `crates/verifier`, a port of the Python
verifier. Its commit message says that the dropped fuzz tests "will be superseded by formal
verification". The crate has 3,091 lines with tests, and 2,352 lines of code. It has no
dependencies, `#![forbid(unsafe_code)]`, one thread, no floating point (a query table replaces
the `f64` search), no `cfg` outside its tests, and BLAKE2s. Its call graph is about 154 functions
(measured). Later upstream commits replace BLAKE2s by Keccak-256 (`4af2cddd`, #636), so the crate
at a later revision checks a different protocol.

Between the pin and `8c31abd7` lie 79 commits. Three of them change which proofs are accepted:

1. **Public-input binding** (`9084d317`, #322): the prover no longer sends two public-input
   scalars; the verifier computes each limb's claim.
2. **WHIR query counts** (`b977f5fa`, #370): 25 of the 56 table entries drop by 1 to 3 queries.
3. **GKR combiner schedule** (`40bdeac6`): the bus GKR samples its combiner at a different time,
   which shifts every later challenge.

The backport reverses exactly these three changes, in 20 added and 11 removed lines in three files.
The [appendix](#the-backport-diff) gives the diff. Its validation (measured in this survey):

| Test | Cases | Result |
|---|---:|---|
| Corpus: 29 Rust proofs and one Lean proof | 30 | backport and pin both accept all 30 |
| Negative control: the unchanged crate on the corpus | 30 | rejects all 30 |
| Mutations of proof, sizes, Merkle data, public input and program | 24,000 | all agree, no panic |
| Tampered proofs with a consistent transcript, from a patched prover | 865 | all agree, both reject |

The negative control shows that the backport is not a no-op. The three changes were each
identified by reading the 79 commits, not by removing them one at a time. Agreement on the corpus
and the mutants shows no fourth change on the tested shapes. On the corpus, the backport verifies
a proof in 14 to 38 ms and the pin in 0.43 to 0.61 s, on a loaded machine. The earlier
differential fuzz work for leanerVM PR #161 compared Lean's `verify` with the pin's verifier on
about 47,000 proofs, with no divergence (2026-10-27). The evidence that the backport agrees with
Lean is therefore mostly indirect, through the pin: 24,865 cases backport against pin, about
47,000 cases pin against Lean, and the 30-proof corpus on all three. These tests cover the corpus
shapes only: memory of size 2^17 and 2^20, all four rates and bytecode of size 2^11. WHIR table
rows for other shapes are copied from the pin's Python table, which upstream CI ties to the Rust
search.

### SIMD is not an obstruction

The portable crate has no intrinsics. Even the pin's verifier compiles without them for a
baseline target: its `riscv64gc` archive has no vector instructions, and its x86-64 baseline
build has only compiler-generated SSE2 (measured). Lean 4 has no SIMD types and no carry-less
multiply primitive (v4.35.0), but this blocks no route. A source-level model treats an intrinsic
as an opaque function on bit vectors with a stated specification, as SymCrypt does for
`PCLMULQDQ` ([arXiv 2609.15648](https://arxiv.org/abs/2609.15648), 2026-09-14). At machine level
the gap is instruction coverage: Kraken has no `PCLMULQDQ` and no AArch64 NEON
([Kraken](https://github.com/AeneasVerif/kraken) `e211eaf`, 2026-11-04).

## The routes

The *trusted base* of a route is everything its conclusion assumes without a machine-checked
proof: tools, models, compilers and hardware. Every route also trusts Lean's kernel and the
statements of leanerVM's specification and headline theorems. The descriptions below omit these.

### 1. Differential testing

Run the Rust and Lean verifiers on the same inputs and compare the verdicts. This proves nothing,
so everything is trusted. It is the baseline and the regression net for every other route. About
47,000 cases pin against Lean and 24,865 backport against pin have shown no divergence. The same
work found that a program with a huge operand makes the Rust verifier allocate without bound
([leanVM#647](https://github.com/leanEthereum/leanVM/issues/647)). The effort is spent. Keep it
in CI on the backport.

### 2. The Lean verifier as a second check

Deploy the compiled Lean `verify` beside the Rust verifier and accept a proof only if both accept.
A false acceptance then needs both verifiers to be wrong on the same proof. Soundness needs only
the compiled Lean code to be correct, and no Rust tool is trusted. The trusted base is the Lean
compiler (unverified, from its intermediate representations to C), the Lean runtime and its
bignum library, the C compiler, the `@[extern]` primitives written in C, and the proof encoder
between the two verifiers (today a text dump and leanerVM's loader). turbo-lean, a one-developer
Lean-to-LLVM compiler with a self-reported proof of its lowering against its own LLVM model, is
the only project found that could shrink this base; LLVM below that model stays trusted. The
fast `@[csimp]` replacements that make `verify` run in 0.8 s are proved equal to the
specification forms in the kernel. Integration is days of work (estimate), through a
foreign-function interface or a subprocess. The cost is latency: 0.8 s per proof against 14 to
38 ms for the backport. This suits aggregation and offline checks, not hot paths.

### 3. Source level: Charon and Aeneas

*Charon* is a rustc plug-in that exports a crate's MIR, rustc's mid-level intermediate
representation, as structured code. *Aeneas* translates that code into one pure Lean function per
Rust function, in a monad whose outcomes are success, failure (panic) and divergence. The
[inclusion](#one-inclusion-suffices) is then an ordinary Lean theorem about the generated
functions. *hax*, Cryspen's Rust verification front end, has run its Lean backend through Charon
and Aeneas since version 0.4.0 (2026-09-07). The two are one pipeline, and hax adds its own
models of the core library.

**Trusted base.** It has six parts:

- Charon, with the rustc nightly it is built on;
- the Aeneas translation, which has no soundness proof: the ICFP 2024 paper proves its
  borrow-checking semantics on paper and leaves the translation to future work
  ([arXiv 2404.02680](https://arxiv.org/abs/2404.02680)), and a Rocq formalization of that
  paper reports a flaw in some of its fundamental lemmas (Verimag seminar, 2026-01-19).
  Translation bugs are still being found, for example user `Drop` implementations that never run
  ([Aeneas#1410](https://github.com/AeneasVerif/aeneas/issues/1410), 2026-10-09). No test
  exercises the translated code until the model is executable;
- the hand-written models of the Rust standard library, in which several soundness bugs were
  reported in October and November 2026, for example `Cell::set` modelled as pure
  ([Aeneas#1525](https://github.com/AeneasVerif/aeneas/issues/1525)) and `array::repeat`
  skipping `clone` ([Aeneas#1526](https://github.com/AeneasVerif/aeneas/issues/1526));
- the rustc and LLVM that build the deployed binary, a different compiler from Charon's;
- the Lean encoders that stand in for the caller's Rust (`tableOf`, `bytesOf`, `proofOf`),
  unless the caller is translated too;
- the deployment conditions of the theorem.

The compiler gap is real but rarely hit by accident. rust-lang/rust has 94 issues labelled
`I-miscompile` from 2025-11-01 to 2026-11-05. One study reproduced 48 of 88 known rustc and LLVM
miscompilations inside SP1 guests, yet the buggy and fixed compilers produced byte-identical guest
binaries in 447 of 552 cases ([arXiv 2611.04701](https://arxiv.org/abs/2611.04701), 2026-11-03).

**Evidence (measured in this survey).**

- Charon translates the unchanged crate in 7 s. Aeneas stops with an internal error and writes no
  Lean. The causes are `Iterator::copied`, `Box<dyn Fn>`, early returns inside nested loops, and
  mutable iterators combined with `zip`.
- After about 80 source rewrites in 15 categories (17 commits, +1,139/−582 lines), the whole crate
  translates. The model has 18,394 lines with 795 definitions and 128 loops. It leaves 101
  standard-library items as axioms to be modelled.
- Elaboration of the whole model stops at 4 errors, from bugs in Aeneas or its library. Two more
  source changes are expected to clear them, but this was not run. The field module elaborates in
  41 s.
- The rewritten crate passes its unit tests and upstream's integration tests. These test honest
  proofs only. No rejection test was run against the rewrite.
- Pilot proofs on the generated model: two field helpers never panic (2 lines each), and both
  equal independent bit-level definitions (6 and 7 lines, with `step*`, Aeneas's tactic that
  steps through the generated code, and `bv_decide`). One reference is long division, a
  different algorithm from the Rust. Both helpers are loop-free.
- The hax probe (cargo-hax 0.4.2, which pins Lean v4.31.0) reached the same wall. After six
  rounds of rewrites, 5 of 12 modules translated. It proved the field reduction equal to a
  bit-vector reference, with no panic and no divergence, in about 45 minutes.

**Effort (estimate).** SymCrypt, the closest precedent, verified Rust SHA-3 and ML-KEM with
Aeneas and Lean against FIPS specifications; its code ships in Windows Insider builds (Microsoft
Research blog, 2026-07-13). The estimate has three inputs of different standing:

- *Measured here:* the counts above, four loop-free pilot lemmas of 2 to 7 lines, and a loop
  pilot. The pilot proved that 10 loops of the generated model return without failure and equal
  `List` functions. They are `dot`, `eq_eval`, `index_mle`, the Merkle path root, both loops of
  `multilinear_eval` and of `eq_kernel`, the transcript's scalar reads (an early exit), and a
  BLAKE2s round, checked against RFC 7693. Each took 16 to 74 proof lines (median about 40) on a
  shared layer of about 156 lines of generic iterator lemmas. That layer covers 108 of the 128
  loops by iterator kind. Each loop took 1 to 26 minutes of agent time. Regenerating the model
  four times broke no proof. Extrapolated, the loops need 6,000 to 15,000 proof lines. Most of
  these theorems take their callees' specifications as hypotheses (the `E` product, the hashes).
  Only the BLAKE2s round is closed. So the loops are not the main cost. The main costs are the
  callee and library models, and the step from these Rust-shaped references to leanerVM's
  mathematics.
- *Measured elsewhere:* SymCrypt's ratio of specification and proof lines to Rust lines,
  computed from Figure 4 of [arXiv 2609.15648](https://arxiv.org/abs/2609.15648), is 8.4 for
  SHA-3, 15.5 for ML-KEM and 10.6 overall. At those ratios, 2,352 lines need 20,000 to 36,000
  proof lines. The ratio transfers only roughly: SymCrypt's specifications follow the standard's
  pseudocode, close to the Rust, while `verify` follows the oracle reductions.
- *Assumed:* about 3,000 proof lines per person-month with agent assistance, which turns the
  line range into 6 to 12 person-months. The rate is judgement. SymCrypt states none: it reports
  that its first NTT layer took about six months and that a further algorithm now takes about a
  week of agent work and a few days of human review, and it declines to quantify productivity.
  Those two figures bracket the pace loosely; they do not fix a rate.

The figure falls threefold, to 2 to 4 person-months, if the loop pilot's generic layer keeps
the remaining loops routine (it already covers 108 of 128 by kind), and agents reach SymCrypt's
later pace, about a week per phase. It rises
threefold, to 18 to 36, if each loop needs its own invariant over iterator state, if the
hand-written tables and BLAKE2s circuit (see [the plan](#recommended-plan)) must be matched gate
by gate, or if tool churn and translation bugs force repeated repairs.

**Fragility.** A source change breaks the proofs of the functions it touches; a hash change
touches the transcript and Merkle modules. The crate must stay in the subset Aeneas accepts, which
needs upstream cooperation or a maintained fork. Aeneas releases nightly. Its library is on Lean
v4.35.0 and leanerVM on v4.34.1, so one side must move.

### 4. Machine code alone

Prove the compiled binary against `verify`, using a Lean model of the instruction set. *Kraken*
(Lean FRO, Google and Inria) proves facts about x86-64 and AArch64 assembly text, with hand-written
instruction semantics tested against hardware. The RISC-V model generated by *Sail*, an ISA
specification language, is official and has a Lean backend (`LeanRV64D`, 173,614 lines,
[opencompl/sail-riscv-lean](https://github.com/opencompl/sail-riscv-lean) `51c635c`, 2026-08-20).

This removes rustc and LLVM from the trusted base. In their place it trusts the ISA model, the
assembler and loader (Kraken has no decoder), the calling convention, and contracts for the
allocator, `memcpy`-style routines and panics.

The backport's binary is 35,000 to 75,000 instructions in about 154 functions, by target and
optimization level (measured). It has about 1,000 allocator call sites, 130 to 200 calls to
`mem*` routines, 500 panic sites and, on x86-64, about 220 indirect calls. No binary-level proof of
any SNARK or STARK verifier was found (search, 2026-11-05). The state of the art is s2n-bignum in
HOL Light, which needed 63,159 proof lines for eight Arm AES-GCM routines
([s2n-bignum](https://github.com/awslabs/s2n-bignum), 2026-10-22 to 2026-11-03).
[LNSym](https://github.com/leanprover/LNSym), the Lean Armv8 effort, has had no commit on its
main branch since 2024-12-09.

Evidence from the Kraken pilot (measured in this survey, Kraken `e211eaf`):

- Proved: the `K` addition, the field reduction (16 instructions, 4.45 s) and the 68-instruction
  carry-less multiply core with 16 integer multiplies (10 lines, 45.6 s with cold imports).
- Not proved: one BLAKE2s mixing step, 22 instructions with 4 loads and 4 stores. Five of its
  eight memory accesses were discharged. The goal that the second store leaves the rest of
  memory unchanged exceeded Lean's per-proof work limit (its heartbeat limit) after 23 minutes.
- Not proved: the full `K` multiply, 210 instructions. It steps completely in about 90 s, but the
  closing `bv_decide` call hit the solver's 600 s timeout. Closing it by associative-commutative
  normalization, as for the multiply core, was not tried.
- Kraken's main branch has four gaps on rustc output, each with a small workaround
  ([appendix](#probes)). Memory automation exists only on a fork, which was not built.
- The proofs cover function bodies run straight-line, without the calling convention. They target
  transcriptions of the Rust. The step from those to field arithmetic is a separate source-level
  lemma.

**Verdict.** Not feasible for the whole verifier in 2026. Feasible for register-only kernels.
Memory kernels wait on automation.

### 5. Hybrid: source proofs with a per-build machine-code check

Keep the hand proofs at source level (route 3), where they survive recompilation. For each build,
prove automatically that each machine-code function equals its Aeneas model function. This is
*translation validation*: one compiler output is checked against its input, instead of proving
the compiler. The trusted base is route 4's without rustc and LLVM, and no hand proof is redone
per build.

One register-only kernel suggests that this is the easy direction. The machine code and the Rust
share structure. `ac_rfl`, which normalizes associative and commutative operators, closed the
carry-less multiply core against a transcription of the Rust. The same function against the
mathematical specification needed 57 s of SAT solving, and the full 64-bit multiply timed out at
600 s (measured in this survey). Two things are missing. Kraken's main branch has no automation for
loops, calls and memory. Nothing yet relates the Aeneas model's data (vectors, slices) to the
machine's memory layout and calling convention. This is the right long-term target, with
research-grade tools today.

### 6. The recursion guest over leanISA

For recursion, the verifier that matters runs inside leanVM. It is the zkDSL guest
`aggregate.py` (3,538 lines at the pin), compiled to leanISA bytecode. leanerVM already trusts
leanISA semantics, so a proof of the guest bytecode against `verify` adds no new ISA model. It
also removes the zkDSL compiler from the trusted base. The guest is a checker with prover hints,
so the theorem reads "if some hints make the guest execution valid, then `verify` accepts". It
also checks raw (expanded) Merkle paths and defers its bytecode claims. A proof needs a program
logic over leanISA `step`, which leanerVM does not have. This belongs to the recursion target of
the [target map](../leanvm-target.md), with the same specification and the same direction of
statement.

### 7. LLVM intermediate representation

No Lean semantics of whole LLVM-IR programs exists. Lean-MLIR verifies individual lowering
patterns (158 at EuroLLVM, 2026-04-14), not programs. turbo-lean compiles Lean to LLVM, the
opposite direction. Not viable.

### Routes not taken

Verus, Creusot and Prusti prove Rust against specifications in their own logics, so the link to
the Lean specification would be an unproved restatement. SAW needs Cryptol specifications and
bounded inputs. rocq-of-rust works in Rocq, where the specification would have to be
retranscribed. Kani, a bounded model checker, cannot prove the inclusion for every proof length,
but it checks panic-freedom on bounded inputs cheaply ([obstruction 2](#obstructions)).

### Comparison

| Route | What is proved, about what | Trusted, beyond Lean's kernel and the specification | Evidence in this survey | Effort (estimate) | Fragility | Maturity |
|---|---|---|---|---|---|---|
| 1. Differential testing | nothing; agreement on the tested inputs | everything | about 47,000 cases pin against Lean, 24,865 backport against pin, no divergence; found leanVM#647 | done | none | built (draft PR #161) |
| 2. Lean verifier as second check | the deployed check is as sound as compiled `verify` | Lean compiler, runtime and bignum library, C compiler, `@[extern]` primitives, proof encoder | compiled `verify` accepts the fixture in 0.8 s | days | none | usable |
| 3. Charon and Aeneas | the inclusion, for the Aeneas model of the crate | Charon and its rustc, the Aeneas translation, library models, deployed rustc and LLVM, the caller's encoders | whole crate translates after about 80 rewrites; four kernel lemmas and ten loops proved | 6 to 12 person-months, threefold either way | breaks at changed functions; crate must stay in the Aeneas subset | production precedent; tools change monthly |
| 4. Machine code alone | one binary against the specification | ISA model, assembler and loader, ABI, allocator and panic contracts | three small register-only kernels proved; the full `K` multiply and one memory kernel not | not feasible for the whole verifier | per build and per flag set | no verifier precedent |
| 5. Hybrid | route 3, plus each built function equals its model | route 4's, without rustc and LLVM | one 68-instruction kernel equals its Rust-shaped reference by `ac_rfl` | route 3 plus unknown tooling | automatic re-check per build | research-grade |
| 6. Recursion guest | some hints make the guest valid ⇒ `verify` accepts | leanISA semantics (already trusted), the bytecode dump | none; source reading only | not estimated; needs a program logic | per compiled guest | nothing in leanerVM |
| 7. LLVM IR | none | none | none | not viable | none | no program semantics in Lean |

## Obstructions

Each item is a negative result that any plan must respect.

1. **Total equivalence is false for the deployed entry points.** At the pin, `cpu::verify`
   builds the bytecode columns by allocating a table of generator powers up to the largest
   operand; at `8c31abd7` the caller's encoder `layout::bytecode_table` does the same. A huge
   operand makes the Rust verifier hang or run out of memory
   ([leanVM#647](https://github.com/leanEthereum/leanVM/issues/647)), while `verify` is total.
   Upstream fixed the encoder in `05931b78` (2026-10-27). For the crate alone, which takes the
   table, total equivalence is untested, not known to be false. Consequence: the theorem must be
   partial correctness. The soundness inclusion needs nothing more.
2. **The model and the release binary disagree on overflow.** Aeneas and hax models fail on
   integer overflow and on shifts by at least the width, as a debug build does. A release build
   wraps and masks. For example, `MerklePath::root` shifts the leaf index by the level, which
   fails in the model from 64 siblings on and masks in release. Read from the source, both
   openings readers build exactly `height ≤ 32` siblings, so this example cannot occur; the
   general gap remains. "Model `Ok` implies `verify`" says nothing about inputs where the model
   fails and the binary continues. Consequence: build the deployed verifier with
   `overflow-checks = true`, so that the binary panics where the model fails. For the crate that
   suffices: its ten `wrapping_*` operations wrap in both, it has no `debug_assert!`, and `as`
   casts truncate in both, provided the model's `usize` has the target's 64 bits. Proving
   panic-freedom closes the gap as well. Do both; Kani can check it on bounded inputs.
3. **Allocation failure is not modelled.** In the Aeneas model, `Vec::with_capacity` cannot fail.
   In the binary, running out of memory aborts the process, which is a rejection. Consequence:
   harmless for soundness, but no availability claim follows from the model alone.
4. **SAT solving does not scale to 64-bit carry-less multiplication** (measured in this survey).
   `bv_decide` is Lean's tactic that turns a bit-vector goal into a SAT problem and checks the
   solver's certificate. It proves the shift-and-xor multiply at 64 bits in 276 s with 7.8 GB of
   memory. It times out (600 s) on the BearSSL-style multiply the crate uses and on the full
   `K` product. leanerVM's own Karatsuba multiply times out at 16 bits (300 s cap). A 121-line
   proof by loop invariant proves the pin's multiply at every width in about 1 s. Consequence:
   give field kernels structured, algebraic proofs, and use SAT only for linear or
   add-rotate-xor pieces (reductions take 7 s, a BLAKE2s mixing step under 0.1 s).
5. **`bv_decide` adds an axiom that leanerVM's audit rejects.** A theorem closed by `bv_decide`
   depends on an auxiliary axiom `<theorem>._native.bv_decide.ax_*` for the compiled certificate
   check, created by the same mechanism as `native_decide`'s (measured with `#print axioms`).
   `scripts/audit-axioms.lean` allows only `propext`, `Classical.choice` and `Quot.sound`, so it
   rejects it. Consequence: use structured proofs for accepted code. leanerVM already has
   SAT-free reduction lemmas (`BF64Fast.toPoly_reduceWords`). The alternative is a policy
   exception scoped to the correspondence proof, which is the maintainers' decision.
6. **Data structures break before arithmetic.** Evaluating one BLAKE2s round on the Rust's
   16-word vector by `rfl` was killed after 9.5 minutes. `simp` normal forms such as `List.set`
   with coerced indices are opaque to `bv_decide` (measured in this survey). The Aeneas model
   carries iterator state through 128 loops. Per-step lemmas composed by rewriting do scale, as
   leanerVM's [`Blake2sFast`](../../LeanerVM/Semantics/Blake2sFast.lean) shows. Consequence: in
   every route, the main cost is the plumbing of loops and data, not bit arithmetic.
7. **"The binary" is not one object.** The pin's `.cargo/config.toml` sets
   `target-cpu=native`, so a build inside the leanVM workspace depends on the build host. Cargo
   does not read that file when the crate is built as a dependency (measured). The optimization
   level changes the program: moving from `-O3` to `-O2` halves the instruction count and turns the
   BLAKE2s rounds into a loop with bounds checks. An LLVM one year older gave byte-identical
   kernels at `-O3` (measured). Consequence: a binary proof is about one artefact built with
   pinned flags.

## Recommended plan

### Milestones

The milestones follow route 3. The order puts cheap, independent parts first.

1. **Crate in the Aeneas subset.** Apply the 17-commit rewrite series to the backport (it needed
   two backport-only fixes through round 9; rounds 10 and 11 are not yet translated there), plus
   the two changes expected to clear elaboration. Keep the differential harness green, and add
   rejection tests for the rewritten crate. Commit the generated Lean beside the Rust. Report the
   Aeneas crash on `Iterator::copied` to its maintainers, with the one-line reproducer.
2. **One toolchain.** Put leanerVM and the Aeneas library on one Lean release (v4.35.0 against
   v4.34.1 at the time of writing). A separate Lake package that imports leanerVM would keep
   Aeneas out of the production layers (proposal).
3. **Library models.** Give each of the 101 axioms a Lean definition and a specification, or
   remove its use from the Rust. leanerVM's axiom audit rejects the model until this is done.
   The models then join the trusted base as definitions.
4. **Executable model.** Run Aeneas with `-all-computable`, give the externals executable
   models, and run the model on the corpus and the mutation harness. A disagreement with the
   binary is a translation or model bug. It is the one cheap check on the translation.
5. **Kernels.** Prove the `K` product, the `E` product and the BLAKE2s compression equal to
   leanerVM's definitions by structured lemmas, reusing
   [`BF64Fast`](../../LeanerVM/Parameters/ToCompPoly/BF64Fast.lean) and `Blake2sFast`. The
   BearSSL-style multiply is estimated at 2 to 4 days, the compression at 1 to 2 days (estimates
   from the bit-level pilot on hand transcriptions of the Rust, not on the Aeneas model).
6. **Cheap phases.** Transcript, Fiat–Shamir seed, setup checks, public input and Merkle
   openings.
7. **Middle phases.** Layout and tables, bus and GKR, table sumcheck and Flock.
8. **WHIR.** The loop over levels and the glued weights; no new lemma.
9. **Composition and audit.** Compose the phases into the inclusion and run `#print axioms` over
   the whole environment.

The structural distance between the crate and `verify` sets the cost of milestones 6 to 8. This
table reads the crate at the backport (`crates/verifier/src/` at `48614e15`) beside `verify`
(under `LeanerVM/Protocol/`). It is inferred from reading, not attempted. *Representation* means
the same algorithm over different data; *lemma*, a different algorithm that needs one.

| Phase | Distance | Where (crate; Lean) | Cost |
|---|---|---|---|
| Transcript and seed | representation: four `u64` words against an eight-word digest | `transcript.rs:38-123`, `bytecode.rs:45-49`; `Transcript.lean:82-306` | cheap |
| Setup | same checks; Lean makes them before any hash | `lib.rs:211-224`, `layout.rs:386-395`; `Verify/Setup.lean:68-87` | cheap |
| Layout and tables | representation: the crate writes the six tables' bus flushes, constraints and stack placements by hand; Lean derives them from the leanISA arithmetization | `layout.rs:131-475`, `multilinear.rs:104-137`; `LeanIsa.lean:542`, `ToCompPoly/Stacking.lean:303` | medium to large: one equality per table, quantified over the announced sizes; the largest refinement |
| Bus and GKR | same GKR; the framework tuples hard-coded in the crate (representation); both evaluate the bytecode multilinear, the crate by bucketing its words (lemma, which the crate's unit test `evaluate_matches_the_fold` states; no share identity is needed) | `bus.rs:12-161`, `bytecode.rs:100-144`; `Verify/Bus.lean:113-276` | medium |
| Table sumcheck | same, over the summand of the layout row | `bus.rs:212-261`; `Verify/Tables.lean:93-102` | cheap, given the layout |
| Public input | same combined check | `lib.rs:255-263`; `PublicInput.lean:161-165` | cheap |
| Flock | same zerocheck, lincheck and terminal; the BLAKE2s circuit walk written separately (representation); one shared Lagrange denominator against per-node inverses, and closed-form ring-switch coefficients against an expanded term list (two small lemmas) | `flock.rs:46-65, 80-172, 265-335, 379-386`; `Verify/Flock.lean:108-130`, `Verify/Blake2sWalk.lean:41`, `ToCompPoly/Interpolation.lean:53`, `ToArkLib/Flock/FrobeniusMap.lean:51` | large in volume, shallow |
| Merkle | representation: `Vec` and index maps against lists; the crate also reads the `Raw` arm | `merkle.rs:77-144`, `transcript.rs:137-184`; `Merkle.lean:90-135` | medium |
| WHIR | representation: the terminal weight is the same per-query closed form in both (equal in characteristic 2), glued with the same powers; a flat list of closures against nested weights | `whir.rs:88-264`; `Verify/Whir.lean:277-315`, `NovelBasis.lean:97-127, 301`, `Whir/Glue.lean:221` | medium |
| Order of checks | the crate checks each phase as it reads it and opens each WHIR level inside the walk; Lean reads everything, opens, then checks | `whir.rs:200`; `Verify.lean:167-186` | a commutation argument per phase, the crate failing early where Lean fails late; the existing `walkChain_rel` relates the two walks' reads |

The documentation of `Verify/Whir.lean` calls the Rust's terminal weight a different algorithm
from the glued weight. The two agree factor by factor: the pin's
`induce_sumcheck_evaluate_at_residual`, the crate's `induced_weight` and the `mle` of
`Whir.gluedWeight` all evaluate a level's query batch as `Σ_q λ^q ∏_k (1 + r_k (1 + Ŵ_k(x_q)))`
(Lean writes the factor `(1 - r_k) + r_k Ŵ_k(x_q)`, the same in characteristic 2) and glue the
levels with the same powers. The difference is representation, as the row says.

Not on the verification path, and outside the theorem: `replay_unchecked`, `verify_flock_batch`
and the `da` and `deferred` modules.

### Deployment conditions

State these in the theorem's docstring. The theorem says nothing about a deployment that breaks
one of them:

- The caller calls `verify_execution`, not `replay_unchecked` or `verify_flock_batch`, and
  treats its `Ok` as the only acceptance; every other outcome, including a caught panic and an
  abort, is a rejection.
- The caller passes proofs whose openings are `MerkleOpenings::Pruned`, as upstream's
  `scalar_proof` does; the theorem does not cover the `Raw` arm that `Proof::load` produces.
- The caller encodes the statement from a program, with the encoder in the theorem.
- The verifier is built with `overflow-checks = true`, by the stated rustc, for a 64-bit target
  (the model fixes `usize` at 64 bits), with no `cfg` changes.

### What to ask upstream

- Keep `crates/verifier` inside the Aeneas subset: no `.copied()`, closures as enums instead of
  `Box<dyn Fn>`, no `?` inside nested loops, no `BTreeMap` or string-named columns.
- Set `overflow-checks = true` in the profile that builds the deployed verifier.
- Optionally move the program-to-table encoder into the crate, so a program-level theorem covers
  only crate code.

### Later

- Prove the converse inclusion with a resource hypothesis, for availability.
- Add the hybrid check of route 5 once Kraken's loop, call and memory automation is on its main
  branch.
- Pursue the recursion guest of route 6 in the recursion track, with the same specification and
  the same shape of statement.
- Make the model generic in the hash if the random-oracle theorems must transfer.

### What not to do

- Do not attempt a whole-binary proof against the specification (route 4 alone).
- Do not build on LLVM-IR semantics (route 7).
- Do not run a second translation through hax's legacy Lean engine or its F* backend.
- Do not aim for total equivalence (obstruction 1).

## Evidence appendix

The probes and reports of this survey live under `/home/devops/scratch/leanerVM-rustfv/`. They
are not in the repository.

### Revisions and tools

| Item | Revision or version |
|---|---|
| leanerVM | `ca9c3be5cbe349708709aa4dac4968e96e480d73` (PR #185 head). The Lean reading was done at `44e745ee`; `Verify.lean` is the same at both, and the description of `Headline.lean` was re-read at `ca9c3be5`. The crate-to-Lean distance table was read at `ca9c3be5`. |
| leanVM pin | `a386121f84292f6fa663aaa3e570c15bc0240ea2` |
| Portable crate | leanVM `8c31abd7` (#635) |
| Backport | local branch `rustfv/portable-verifier-at-pin`: `8027523a` (unchanged copy), `48614e15` (backport); not pushed |
| Rust (binary census, Kraken pilot) | rustc 1.99.0 stable (`b940084d7` of 2026-09-28, released 2026-10-01), LLVM 23.1.1; rustc nightly-2025-11-08 for the LLVM comparison |
| Aeneas | `nightly-2026.11.05-c2d2343` (git `c2d23438`, 2026-11-04); Charon 0.1.308 (`a58d1592`) on rustc nightly-2026-09-17; Lean library on Lean v4.35.0 and Mathlib v4.35.0 |
| hax | cargo-hax 0.4.2 (2026-10-01): Aeneas fork `build-183e4f0`, Charon nightly-2026.09.02, Lean v4.31.0, hax-lean v0.3.30 |
| Kraken | AeneasVerif/kraken `e211eaf` (2026-11-04), Lean nightly-2026-09-21 |
| Bit-level pilot | Lean v4.34.1 (leanerVM's) |

### Probes

| Probe | What it measured | Location |
|---|---|---|
| Rust anatomy and SIMD | builds for six targets, disassembly, call-graph census, `strace` of the thread pool | `probes/simd-pin/`, `probes/callgraph/`, `probes/portable-size/` |
| Drift | classification of the 79 commits | `probes/drift/`, `reports/10b-protocol-drift.md` |
| Backport and harness | the backport, corpus, 24,000 mutations, 865 tampers, the negative control | `probes/leanVM-pin/`, `probes/backport-diff/`, `probes/backport-diff-verbatim/` |
| Binary size | 2 targets × 5 profiles of the backport | `probes/backport-size/` |
| Aeneas | translation of the crate, 17 patches, elaboration, pilot proofs | `probes/aeneas-target/`, `probes/aeneas-patches/`, `probes/aeneas-lean/`, `probes/aeneas-micro/`, `probes/aeneas-pin/` |
| Aeneas loops | ten loops of the generated model proved against `List` functions, generic iterator lemmas, classification of all 128 loops | `probes/aeneas-loop-pilot/` |
| hax | translation, six rounds of rewrites, field-module build, pilot proof, F* comparison | `probes/hax-target-patched/`, `probes/hax-micro/`, `probes/hax-logs/` |
| Bit-level automation | `bv_decide`, `decide`, `rfl` and structured proofs on the kernels | `probes/bv-pilot/` |
| Kraken | assembly of seven kernels, proofs, codegen variants; four gaps of Kraken's main branch on rustc output, each worked around: the parser rejects tabs and one LLVM addressing form, the stepper stalls at shifts by an immediate, the prologue tactic fails at 210 instructions, final goals hold forms opaque to `bv_decide` | `probes/kraken-pilot/` |
| Earlier differential fuzz (2026-10-26 and 27, for PR #161) | Lean `verify` against the pin's verifier on about 47,000 proofs | `/home/devops/scratch/leanerVM-fuzz/`, outside this survey's directory |

The reports are `reports/10-rust-anatomy.md` to `reports/40-synthesis.md` in the same directory.
Every Lean run in the probes ran under a shared lock with a memory cap and a timeout.

### The backport diff

`git diff 8027523a 48614e15` on the backport branch:

```diff
diff --git a/crates/verifier/src/bus.rs b/crates/verifier/src/bus.rs
index 341a9c2c..8f545c01 100644
--- a/crates/verifier/src/bus.rs
+++ b/crates/verifier/src/bus.rs
@@ -13,12 +13,12 @@ fn verify_gkr_grand_products(depth: usize, transcript: &mut Transcript) -> Resul
     let (shared, count) = (transcript.next_scalar()?, transcript.next_scalar()?);
     let mut point: Vec<E> = Vec::new();
     let mut values = vec![shared, shared, count]; // 3 grand product GKR are batched together: push, pull, count
+    let mut combiner = transcript.sample();
 
     let mut layer = depth;
     while layer > 0 {
         // Two levels a step. An odd depth starts with one.
         let step = if layer % 2 == 1 { 1 } else { 2 };
-        let combiner = transcript.sample();
         let claim = poly_eval(&values, combiner);
         // The product is degree 2^step, so one more coefficient than that per round.
         let equalities: Vec<Option<E>> = point.iter().copied().map(Some).collect();
@@ -41,6 +41,7 @@ fn verify_gkr_grand_products(depth: usize, transcript: &mut Transcript) -> Resul
         for child in &children {
             values.push(multilinear_eval(child, &y)?);
         }
+        combiner = transcript.sample();
         point = [y, x].concat();
         layer -= step;
     }
diff --git a/crates/verifier/src/lib.rs b/crates/verifier/src/lib.rs
index 91154fb4..97551286 100644
--- a/crates/verifier/src/lib.rs
+++ b/crates/verifier/src/lib.rs
@@ -36,7 +36,7 @@ use layout::{
     BLAKE2S_R1CS_LOG_SIZE, FLOCK_K_SKIP, MAX_STACKED_LOG, MEMORY_0, MEMORY_1, MEMORY_2, MIN_STACKED_LOG, N_TABLES,
     OP_BLAKE2S, QFLOCK, build_layout,
 };
-use multilinear::{dot, multilinear_eval};
+use multilinear::{dot, multilinear_eval, poly_eval};
 use transcript::Transcript;
 use whir::verify_whir;
 
@@ -69,6 +69,7 @@ pub enum VerifierError {
     AnnouncedHighLimb,
     PcsInverseRate,
     CommittedSize,
+    PublicInputCheck,
 }
 
 impl std::fmt::Display for VerifierError {
@@ -99,6 +100,7 @@ impl std::fmt::Display for VerifierError {
             Self::AnnouncedHighLimb => "announced size has a nonzero high limb",
             Self::PcsInverseRate => "invalid PCS inverse rate",
             Self::CommittedSize => "committed size outside the PCS window",
+            Self::PublicInputCheck => "public input check failed",
         };
         f.write_str(message)
     }
@@ -248,18 +250,24 @@ fn walk(bytecode: &Bytecode, public_input: &[u8; 32], proof: &Proof, checked: bo
     let mut claims = bus.claims;
     claims.extend(table_sumcheck_claims);
 
-    // 5] binding the public input: each memory limb's claim is that limb's public line at the challenge, which the verifier
-    // evaluates itself, so the prover sends nothing. Both public words are 128-bit, so the top limb's claim is zero.
+    // 5] binding the public input: the prover sends the low two memory limbs' claims, which must sit on the
+    // public line at the challenge, the top limb's being zero.
     let public_challenge = transcript.sample();
+    let public_limbs = [transcript.next_scalar()?, transcript.next_scalar()?, ZERO];
     let (first, second) = public_input.halves();
+    if transcript.checked() {
+        require(
+            poly_eval(&public_limbs, E::new(0, 1, 0)) == multilinear_eval(&[first, second], &[public_challenge])?,
+            VerifierError::PublicInputCheck,
+        )?;
+    }
     let mut public_point = vec![ZERO; layout.placements[MEMORY_0].variables];
     public_point[0] = public_challenge;
-    let public_pairs = [(first.c0, second.c0), (first.c1, second.c1), (first.c2, second.c2)];
-    for (column, (low, high)) in [MEMORY_0, MEMORY_1, MEMORY_2].into_iter().zip(public_pairs) {
+    for (column, value) in [MEMORY_0, MEMORY_1, MEMORY_2].into_iter().zip(public_limbs) {
         claims.push(ColumnClaim {
             column,
             point: public_point.clone(),
-            value: multilinear_eval(&[K(low), K(high)], &[public_challenge])?,
+            value,
         });
     }
 
diff --git a/crates/verifier/src/whir.rs b/crates/verifier/src/whir.rs
index 8f17b937..b2d68999 100644
--- a/crates/verifier/src/whir.rs
+++ b/crates/verifier/src/whir.rs
@@ -16,10 +16,10 @@ const QUERY_GRINDING_BITS: u32 = 17;
 
 #[rustfmt::skip]
 const WHIR_QUERIES: [[&[usize]; 14]; 4] = [
-    [&[222,55], &[223,56,30], &[223,56,31], &[223,56,32], &[223,56,32], &[223,56,32,22], &[223,56,32,22], &[224,56,32,23], &[224,56,32,23], &[224,56,32,23,17], &[224,56,32,23,17], &[224,56,32,23,18], &[225,56,32,23,18], &[225,56,32,23,18,14]],
-    [&[111,45], &[112,45,27], &[112,45,28], &[112,45,28], &[112,45,28], &[112,45,28,20], &[112,45,28,20], &[112,45,28,21], &[112,45,28,21], &[112,45,28,21,16], &[112,45,28,21,16], &[112,45,28,21,16], &[112,45,28,21,16], &[112,45,28,21,16,13]],
-    [&[75,37], &[75,37,24], &[75,37,25], &[75,38,25], &[75,38,25], &[75,38,25,18], &[75,38,25,19], &[75,38,25,19], &[75,38,25,19], &[75,38,25,19,15], &[75,38,25,19,15], &[75,38,25,19,15], &[75,38,25,19,15], &[75,38,25,19,15,13]],
-    [&[56,32], &[56,32,22], &[56,32,22], &[56,32,23], &[56,32,23], &[56,32,23,17], &[56,32,23,17], &[56,32,23,18], &[56,32,23,18], &[56,32,23,18,14], &[56,32,23,18,14], &[56,32,23,18,14], &[56,32,23,18,15], &[56,32,23,18,15,12]],
+    [&[223,55], &[223,56,30], &[223,56,31], &[224,56,32], &[224,56,32], &[224,56,32,22], &[224,56,32,22], &[225,56,32,23], &[225,56,32,23], &[225,56,32,23,17], &[226,56,32,23,17], &[226,56,32,23,18], &[227,56,32,23,18], &[228,56,32,23,18,14]],
+    [&[112,45], &[112,45,27], &[112,45,28], &[112,45,28], &[112,45,28], &[112,45,28,20], &[112,45,28,20], &[112,45,28,21], &[112,45,28,21], &[113,45,28,21,16], &[113,45,28,21,16], &[113,45,28,21,16], &[113,45,28,21,16], &[113,45,28,21,17,13]],
+    [&[75,37], &[75,37,24], &[75,38,25], &[75,38,25], &[75,38,25], &[75,38,25,18], &[75,38,25,19], &[75,38,25,19], &[75,38,25,19], &[75,38,25,19,15], &[75,38,25,19,15], &[75,38,25,19,15], &[75,38,25,19,15], &[76,38,25,19,16,13]],
+    [&[56,32], &[56,32,22], &[56,32,22], &[56,32,23], &[56,32,23], &[56,32,23,17], &[56,32,23,17], &[56,32,23,18], &[56,32,23,18], &[57,32,23,18,14], &[57,32,23,18,14], &[57,32,23,18,15], &[57,33,23,18,15], &[57,33,23,18,15,12]],
 ];
 
 struct WhirConfig {
```

The `bus.rs` hunk restores the pin's combiner schedule. The `lib.rs` hunk restores the two
public-input scalars and their check, with a new error variant. The `whir.rs` hunk replaces the
query table with the pin's Python table (`verifier.py:910` at the pin).

### Corrections from the fact-check

An independent check of the two literature surveys against primary sources changed these claims.
The text above uses the corrected forms:

- SymCrypt's proof-to-code ratios are 8.4 (SHA-3) and 15.5 (ML-KEM) from the September 2026
  paper. The July README figures, 9.2 and 17.9, are a different count. The paper's totals include
  five experimental components that are not distributed.
- SymCrypt also verifies AES-GCM in Lean with `PCLMULQDQ` as an opaque shim. A Lean precedent for
  carry-less multiply kernels therefore exists at source level. The state of the art in HOL Light
  holds only at machine level.
- hax 0.4.0 was released on 2026-09-07, not 2026-10-01. hax kept its own Lean engine as
  `legacy-lean`.
- Aeneas has 236 open issues (not 337) and about 474 standard-library model attributes (not 160).
- The rustc miscompilation counts are correct, but accidental impact is rare: 447 of 552 buggy and
  fixed compiler pairs gave byte-identical guest binaries.
- The LNSym `sorry` equates two bit-vector carry-less products. It is not a bridge to a polynomial
  ring.
- The Sail-generated Arm model in Lean (`sail-arm-lean`) never built. It did not stop building in
  2025-11.

A second check, for the review of this note, corrected the rustc release date, the LNSym branch,
the Aeneas issue examples and the miscompilation pool; the text above uses those forms too.
