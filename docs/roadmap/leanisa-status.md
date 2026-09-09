# Status: leanISA semantics and M3 constraints

This file records where the [leanISA roadmap](leanisa-blueprint.md) stands as of branch
`feat/leanisa-bytecode-encoding`, which lands Layer 4 on top of the merged Layer 2 (`main` at
`46c5f83`, PR #8) on 2026-09-09. It is a hand-maintained snapshot, rewritten whole when a layer
lands or a decision is taken; the roadmap is the authority on what is wanted, and the tracking
issue [#4](https://github.com/Verified-zkEVM/leanerVM/issues/4) mirrors the coverage table
below.

## Where this roadmap stands

**At a glance.** Layers 0, 1, 2 and 4 are built. `LeanerVM/Parameters/Field.lean` and
`LeanerVM/Parameters/Generator.lean` define `K`, `E`, `y`, `ofK`, `E.limb`, `E.ofLimbs`,
`IsInK`, `IsCanonical128`, `g`, and `gpow`, and prove `orderOf_g` and `gpow_injOn` from the
seven `decide +kernel` checks; Clean's `FiniteField K` instance is `instFiniteFieldK` in the
plain file `LeanerVM/Parameters/CleanField.lean`. `LeanerVM/Parameters/Blake2s.lean` and
`LeanerVM/Semantics/Blake2s.lean` define `iv`, `sigma`, the two-flag `compress`, the cell
encoding (`cellWords`, `wordsCell`, `unpackMetadata`), and `CompressCells`, each pinned by
kernel-checked vectors from RFC 7693, from CPython's `hashlib.blake2s`, and from the pinned Rust
executor. `LeanerVM/Parameters/Isa.lean` defines `Opcode`, `Opcode.code` (`g^0 … g^5`), and the
five caps; `LeanerVM/Semantics/Memory.lean` defines `gLog?` (noncomputable, the index by
`Classical.choose`), `MemImage`, `MemImage.read`, and `PublicInput` with `word0`/`word1`, and
proves `gLog?_spec`, the one statement through which the bounded logarithm is trusted, with
`gLog?_eq_none_iff` and `gLog?_gpow_eq_none` on the failure side;
`LeanerVM/Semantics/Instruction.lean` defines `DerefMode`, `Instr`, `Instr.opcode`, `Program`,
and `Program.fetch`. `LeanerVM/Arithmetization/Bytecode.lean` defines `derefFlags`, the bus
entry `entry`, the sixteen slots `encodeSlots`, and the decoder `decode` (with `opcode?` and
`derefMode?`), and proves `decode_entry`, `decode_eq_some_iff` (the decoder is the exact inverse
of the entry), `entry_injective`, and `encodeSlots_getElem`. `./scripts/validate.sh` is green,
the axiom closure of every declaration is `propext, Classical.choice, Quot.sound`, and the
kernel axiom audit is enabled in CI
(`axiom-audit-root: LeanerVM`). Clean is consumed from plain files and the aggregates are plain
(finding C8, now the roadmap's module-system convention); kernel-`decide` over `E` arithmetic
works from plain files but not from `module`s (P1); `lake test` builds the test library because
no executable may link the field module (P3). `Bytecode.lean` is the first non-empty
Arithmetization module; it imports no Clean and is a `module`.

### Roadmap coverage

| Layer | Status | Notes |
| --- | --- | --- |
| 0 — fields, limbs, generator | landed (PR #6) | `instFiniteFieldK` lives in the plain `CleanField.lean` (C8); `E` arithmetic not kernel-reducible from `module` files (P1) |
| 1 — BLAKE2s | landed (PR #7) | flags are 32-bit words, not `Bool` (decision 6); vectors kernel-checked from a `module` file (L1) |
| 2 — instructions, image, public input | landed (PR #8) | `gLog?` is noncomputable behind `gLog?_spec`, hypothesis `κ < 64`; `MemImage` is an `abbrev`; `Instr.opcode` added (see the frontier) |
| 3 — `step`, `ValidExecution` | untouched; needs Layers 1 and 2 | Category A; write from specification §2 first; fixtures are proofs through the fetch and read lemmas (decision 4) |
| 4 — bytecode encoding | built, awaiting review | `decode` is exact (`decode_eq_some_iff`): a nonzero spare slot is no instruction; `derefFlags` added for Layer 6; a `module`, no Clean |
| 5 — channels | untouched; consumes Clean | plain files (C8) |
| 6 — six tables | untouched; consumes Clean | plain files (C8) |
| 7 — boundary blocks | untouched; consumes Clean | plain files (C8) |
| 8 — statement | untouched; consumes Clean | plain files (C8) |
| 9 — bus soundness | untouched; consumes a Clean change | statements land as block comments with Layer 8 |
| 10 — T1 | untouched; consumes Layer 9 | |

### The frontier

- **Layer 2** landed as PR #8. Every Layer 2 target of the roadmap is present; the roadmap's
  pinned shapes were adjusted in four places, each recorded in the roadmap itself or here:
  - `gLog?` is `noncomputable` (2026-09-09, next bullet), and with it `MemImage.read` and
    `Program.fetch`; the roadmap's Layer 2 and Layer 3 text now say so.
  - `gLog?_spec` takes `κ < 64` rather than `κ ≤ maxLogMem`. The condition the proof uses is
    `2^κ ≤ orderOf g = 2^64 - 1`, and both caps (`maxLogMem`, `maxLogBytecode`) satisfy it, so
    `Program.fetch` discharges it from `logSize_le` without identifying the two caps. The
    roadmap's Layer 2 signature now says so.
  - `MemImage` is an `abbrev`, not a `def`: the roadmap applies an image to an index
    (`t.image ⟨0, _⟩`), which needs the unfolding.
  - `Instr.opcode : Instr → Opcode` is added as the link Layer 4's `entry` and Layer 8's
    `CountsNonzero` need; it is one screen line.
- **Layer 4** awaits review as `feat(arithmetization): leanISA Layer 4 — bytecode encoding`
  (branch `feat/leanisa-bytecode-encoding`). Its reviewer reading list is
  `LeanerVM/Arithmetization/Bytecode.lean`, `tests/LeanerVMTests/Arithmetization/Bytecode.lean`,
  and the roadmap's Layer 4 section. Every Layer 4 target of the roadmap is present; the
  roadmap's Layer 4 text now records two things the build settled:
  - `decode` is exact (`decode_eq_some_iff : decode v = some i ↔ v = entry i`), so a nonzero
    spare slot is no instruction, not only the flag pair `(1, 1)` and an unknown opcode. The
    reason is completeness: every table's bytecode tuple carries literal zeros in its spare
    coordinates (R24), so no row can pull such an entry, and a semantics that fetched an
    instruction there would execute programs the constraints cannot.
  - `derefFlags : DerefMode → K × K` names the flag pair `(f_pc, f_fp)` of `isa.rs:69-78`, which
    Layer 6's `DEREF` table reads; `derefMode?` inverts it.
  The decoder reads coordinates and never compares whole vectors, so it needs no
  `DecidableEq (Vector K 8)` (L1): the tests decide `decode` on literal vectors and slot reads
  in the kernel from a `module` file, and state vector equalities on word lists.
- **`gLog?` is noncomputable** (2026-09-09). Its index is `Classical.choose` of
  `∃ i : Fin (2^κ), a = gpow i`, so `MemImage.read`, `Program.fetch`, and Layer 3's `step` are
  specifications that cannot be run, by construction rather than by cost; its body is still not
  exposed, so a `module` importer reasons through `gLog?_spec` (`MemImage.read`,
  `Program.fetch`, and their lemmas are exposed). It replaced a fuel-bounded scan of
  `g^0, g^1, …` that ran at about 50 µs per `K` multiplication (E4) and would have made every
  read of a running execution a discrete logarithm; the `mulG` fast-path idea went with it. The
  scan's two induction helpers became a `split_ifs` on the choice, and the failure side gained
  `gLog?_eq_none_iff` (no size bound) and `gLog?_gpow_eq_none` (a power past the end), which
  Layer 3's out-of-range test needs. The Layer 2 tests apply the lemmas to concrete addresses
  instead of evaluating; the one evaluated addressing fact (`g + 1` is no power below `g^4`) is
  `fin_cases` and `decide +kernel` at `κ = 2`. For the back of the mind only, not planned: if a
  runnable machine is ever wanted, it is a computable carrier bridged to this specification in
  the CompPoly shape, with exponent-indexed state and a memoized reverse index `g^j ↦ j` as the
  Rust executor has (`cpu/hints.rs:30-58`); nothing here anticipates it.
- **Clean is consumed from plain files** (C8, settled 2026-09-08). Lean `v4.33.1` rejects
  `import` of a non-`module` from a `module`, so the roadmap's module-system convention makes
  the Clean-facing files plain and everything importing them plain too: today
  `Parameters/CleanField.lean`, `LeanerVM.lean`, and the test aggregate; Layers 5–10 will be
  plain files. Clean adopting `module` upstream would let the boundary move back down.
- **CompPoly's `Ext` arithmetic does not reduce in the kernel from a `module` file** (P1), and
  neither does any `Vector` or `E` equality (L1). Layer 1 shows what does reduce: a `module`
  test decides a full compression and `CompressCells` on literal cells with `decide +kernel` in
  about a second each, because `compress` and `E.ofLimbs` avoid `Vector.ofFn` and every vector
  equality is decided on its word list. The Layer 3 fixtures (proofs unfolding `run`, whose
  per-step `E` equalities must reduce in the kernel) still need a plain test file, where the
  kernel sees every body, or an upstream fix; the Layer 6 per-table row tests can also use
  compiled evaluation (`#guard` under `meta import`). Decision 4 below.
- **Layer 3** can start now: it needs `CompressCells` for the `BLAKE2S` arm and everything else
  from Layer 2. Layer 5 needs Layers 3 and 4 and is the first Clean-consuming, plain, file.
- **The Rust vectors.** Layer 1's (`blake2s_computes_the_compression`) is reproduced by
  `scripts/dump-blake2s-rust.sh`; Layer 3's (`mul_192bit_word`, `cpu/mod.rs:985`) is not yet
  dumped; the dump command goes under `scripts/` with the fixture.
- **Clean's bus** is the remaining external item for Layers 9–10. The contract is stated in the
  roadmap's dependency table; no upstream issue exists yet for the direction tag, and Clean
  [#452](https://github.com/Verified-zkEVM/clean/issues/452) covers only the side-condition
  half of the balance change. Filing the combined request is the first action of the docs stage.
- **Clean PR [#446](https://github.com/Verified-zkEVM/clean/pull/446)** removes the three named
  hypotheses of Layer 8 when it lands; until then they stay in `SatisfiedBy`.

## Decisions pending

Confirm before Layer 3 is opened:

1. `DEREF` reads `fp·o3` in every mode (roadmap acceptance test 6); the semantics follows the
   table (specification §7.4), not the prose of §2.
2. `constraintCompleteness` carries `HasFillBlocks prog` (acceptance test 15): a change to the
   target statement in `docs/architecture.md`, not a leanerVM workaround.
3. The bytecode interaction stays on the bus, transcribed like memory, rather than becoming a
   Clean `StaticTable` lookup, which would be characteristic-safe today but would change the
   constraint system the theorems are about.
4. **Executable tests versus kernel `decide`** (P1, L1, E4). Either the roadmap's "by `decide`"
   tests for Layers 3 and 6 live in plain test files (the test aggregate already is one), or
   they are restated as compiled `#guard`s, or CompPoly makes `Ext.ofFn` and
   `Ext.instDecidableEq` kernel-reducible under the module system (a literal-vector or
   `List.ofFn`-free construction, since the blocker is core's unexposed `Array.ofFn`; a
   list-comparing `DecidableEq E`, since core's `Vector` equality is unexposed too), which is a
   CompPoly pin bump. `E.ofLimbs` is already a literal vector so the predicates on literal words
   decide in the kernel today, and Layer 1's `Decidable (CompressCells …)` compares word lists
   for the same reason. Since `gLog?` is noncomputable (2026-09-09), `ValidExecution` is
   neither kernel-decidable nor compilable at any `κ`; a Layer 3 fixture is a proof that
   unfolds `run` through `Program.fetch_gpow` and `MemImage.read_gpow` and decides each step's
   equality on literal words in the kernel, which P1 confines to plain test files until the
   upstream fix.
5. **Restoring a test executable** (P3). The library test driver is a workaround. If the
   roadmap's executable fixtures, the differential tests against the pinned Rust, or the native
   execution target need a real binary, CompPoly must first stop threading `[Fintype F]` through
   `Ext`'s runtime signature and make `Fintype BF64` noncomputable (P3, a pin bump), after which
   `tests/Main.lean` can be an executable again; linking it will additionally need native
   objects for the Mathlib closure, which the Mathlib cache does not ship.
6. **BLAKE2s flags are words.** The roadmap's Layer 1 types the two finalization flags as
   `Bool` (`compress … (f0 f1 : Bool)`, `unpackMetadata : E → UInt64 × Bool × Bool`). The
   built Layer 1 types them as `UInt32`: the pinned Rust (`crates/flock/src/hash.rs:207-215`)
   XORs the two 32-bit halves of limb 1 of the metadata cell into `v[14]` and `v[15]` whatever
   their values, and the Flock relation takes them as free 32-bit inputs (§7), so a metadata
   cell with a flag word other than `0` or `0xFFFFFFFF` satisfies the constraints and
   `CompressCells` must accept it too, or `constraintSoundness` is false for that witness. The
   RFC's Boolean `f` is the word `0xFFFFFFFF`. Either the roadmap's signatures move to `UInt32`
   or a Boolean wrapper is added for documentation; the tests
   (`tests/LeanerVMTests/Semantics/Blake2s.lean`, acceptance tests 10–11) hold either way.

## Open findings against the sources

Numbered for citation from pull requests and `docs/leanvm-target.md`. **S** = internal to the
specification document; **R** = Rust versus specification; **C** = Clean versus leanISA; **P** =
CompPoly versus leanISA; **L** = Lean core versus the roadmap's expectations; **E** = the Lean
environment. The roadmap's acceptance tests already encode the ones that bind a definition.

**Specification.** S1 halting is tested after execution in §2 but before the fetch in the Rust
and the bus (acceptance test 5). S2 final `fp = g^0` is required by §6.1 and the Rust, not by
§2 (test 4). S3 `DEREF` reads `fp·o3` unconditionally in §7.4, unstated in §2 (test 6). S4 the
generator value is not in the specification; Layer 0 binds it to the Rust and the Python
verifier. S5 `02-vm-specification.tex` line 75 annotates `o_3 ∈ K` where the cell value is
meant. S6 §8.4 Fiat–Shamir is `TODO`. S7 §2 calls `BLAKE2S` "the standard BLAKE2s compression"
and names both flags in the metadata cell without saying that the flag *words* enter the state
unchanged (decision 6). S8 the BLAKE2S table floor (`τ_BLAKE2S ≥ 3`) is enforced by the
verifier (`cpu/mod.rs:166`) and the filler (`filler.rs:43`) but appears in no section of the
specification; Layer 2 binds `minLogRowsBlake2s` to the Rust and to Flock's `min_n_blocks_log`
(`crates/flock/src/hash.rs:283-286`).

**Rust executor** (`crates/lean_vm/src/cpu/execute.rs`), all witness-generation behaviour, none
a second meaning of the machine (test 19): R1 registers and operands are `u32` exponents
(Layer 2's operands are `K` elements; a non-`g`-power operand is expressible and names no valid
cell). R2 an equal rewrite of a set cell is accepted, a differing one panics. R3 an unset cell
reads as zero with a diagnostic. R4 memory grows on demand; no range check at access. R5
`κ_mem` is a post-run high-water mark. R6 `DEREF` in `cell` mode fills the unset side, asserts
when both are set, defers when neither is, and zero-fills leftovers. R7 `MUL` back-solves one
unset operand; `XOR` does not. R8 ten `RHint` advice kinds run before each instruction. R9 a
taken `JUMP` needs small g-powers. R10 a `DEREF` pointer must be a small g-power. R11 the
canonical check covers the seven read cells only (test 12; pinned by the output-cell mutation
in the Layer 1 tests). R12 metadata split confirmed (test 11). R13 flag booleanity is not an AIR
constraint (test 18). R14 halt asserts `fp = 0` (test 4). R15 step cap `10^8`. R16 the filler
phase executes fill blocks after halt and can raise `κ_mem` (test 15). R17 `g = 0x2` (test 1;
Layer 0 `g`, certified). R18 `SET`'s immediate is one `F192` (Layer 2 `setConstant (o : K)
(k : E)`). R19 slot packing matches §8.1 (test 16; Layer 4's `entry` and `encodeSlots` transcribe
`layout.rs:229-290`). R20 `cpu/mod.rs` cites a stale `.tex`
filename. R21 the repository holds two BLAKE2s compressions: `flock::hash::blake2s_compress`
(two flag words; the opcode) and `primitives::hash::compress` (last-block flag only; the byte
hasher). Layer 1 transcribes the former. R22 the opcode's IV, sigma, rotations and round count
agree with RFC 7693 (`crates/primitives/src/hash.rs:19-62`), so no leanVM-specific compression
exists. R23 the verifier rejects a public input with a nonzero top limb
(`cpu/mod.rs:139-143`); Layer 2's `PublicInput` cannot express one, so the check is a type, not
a hypothesis. R24 a table's bytecode tuple passes five operand coordinates (`tables.rs:486-491`,
`:553-558`, `:636`, `:742-747`), seven for `BLAKE2S` (`:876-889`), and relies on the bus's zero
padding to `m = 16` slots (`05-arithmetization.tex:12`) to match the seed's eight public columns
(`layout.rs:385-395`); Layer 6 emits all seven explicitly, as the roadmap's `XOR` template does,
because Clean messages are typed, and Layer 4's `decode` rejects a nonzero spare slot for the
same reason.

**Clean** (`93c9d1ef`): C1 direction is the sign of the multiplicity (test 13). C2 balance is a
field sum with a characteristic side condition (test 14). C3 a component cannot see its row
index (Layer 8 hypothesis; PR #446). C4 `ProverData` is untied from committed columns (Layer 8
hypotheses; PR #446). C5 no degree bound on `Expression`. C6 no prover-chosen heights. C7 the
channel-based VM example (`FibonacciWithChannels.lean`) installs `Fact (ringChar F ≠ 2)`, and
`FemtoCairo` is `InductiveTable`-based with prime-field address arithmetic; both are proof-style
templates only. **C8 Clean does not use Lean's module system**: no file under `Clean/` is a
`module`, and `Lean.Environment.importModulesCore` in `v4.33.1` throws
``cannot import non-`module` Clean.Utils.FiniteField from `module` `` for any `import` or
`public import` from a `module` file. Settled 2026-09-08 by the roadmap's module-system
convention: Clean is consumed from plain (non-`module`) files, and every file importing one is
plain; `instFiniteFieldK` landed in `Parameters/CleanField.lean` with its `Field K` CompPoly's
by `rfl`, and `LeanerVM.lean` and the test aggregate are plain. C9 `Clean/Specs/BLAKE3.lean` is
a BLAKE3 specification over `ℕ` words; it shares BLAKE2s's IV and `G` but not its schedule or
finalization, and is not consumed.

**CompPoly** (`3468b38c`): **P1 `Ext` arithmetic is not kernel-reducible from a `module`
file.** `Ext.ofFn` is `Vector.ofFn`, which is core's `Array.ofFn`
(`Init/Data/Array/Basic.lean:331`), not `@[expose]`d; a `module` importer sees only exposed
bodies, so `decide` and `decide +kernel` get stuck on `Ext.ofBase`, `Ext.gen`, `+`, `*`, and on
`Ext.instDecidableEq` (through `Vector`'s `decEq`, L1). `Ext.ofVector` of a literal, `Ext.coeff`,
and all `BF64` arithmetic reduce; plain files are unaffected (the `CleanField` test file
decides `y ^ 3 = E.ofLimbs 1 1 0` in the kernel); compiled evaluation (`#eval`, `#guard` under
`meta import`) works throughout. Decision 4. **P2** `x ^ n` on `BF64`
elaborates to `BF64.instPowNat` while Mathlib's lemmas use `Monoid.npow`; the two unify, but a
goal mentioning `Fintype.card K` makes the elaborator enumerate `K` (`maxRecDepth`), so
hypotheses are rewritten with `simp only` rather than the goal with `rw` (`g_pow_card_sub_one`).
**P3 `instance : Fintype BF64` is evaluated at executable startup.** `BF64/Impl.lean:391`
defines it as `Fintype.ofEquiv _ equivFin.symm`, a zero-arity computable definition, so any
executable linking `CompPoly.Fields.Binary.BF64.Impl` runs its initializer, which is
`List.finRange (2^64)`; the process is OOM-killed (9 GB resident, backtrace through
`_init_lp_CompPoly_BF64_instFintype___closed__3` and `List.ofFn`). The former `leanerVMTests`
executable was killed this way as soon as `LeanerVM` imported the module, so the Lake test
driver is now the test library and the tests are compile-time `#guard`s and `example`s. Nothing
computes with the instance, but it cannot simply be made `noncomputable`: `ExtensionParams F`
takes `[Fintype F]` as a structure parameter, so every `Ext` operation carries the instance as a
runtime argument, and a noncomputable base instance makes `Ext3` multiplication, inversion, and
`#eval` fail to compile (checked on a wrapper type). The upstream fix is to drop `[Fintype F]`
from the runtime signature of `ExtensionParams`/`Ext` (for instance `card_eq : Nat.card F = q`,
with `[Fintype F]` only on the cardinality theorems) and then make `Fintype BF64`
noncomputable; `BF128Ghash` and `BTF₃` have the same eager instance shape. It is a CompPoly pin
bump here. Until then no leanerVM executable may link the field module. Linking one is costly
before it is fatal: the executable's import closure reaches Mathlib, whose cache ships `.c` for
its 8322 modules but no objects, so `lake` compiles all of them first (observed while Layer 1
was built, OOM-killed on a 16 GB machine).

**Lean core** (`v4.33.1`, module system): **L1 core's `DecidableEq` for `Vector` and `Array` is
not exposed** (`Init/Data/Array/DecidableEq.lean` is a `public section` without `@[expose]`, and
the derived `Vector` instance goes through it), so from a `module` file neither `decide` nor the
kernel reduces a `Vector` equality, nor `DecidableEq E`, while `List` equality, `Vector`
indexing, `Fin` and `UInt32` equality, and `Nat.decidableForallFin` all reduce. Layer 1's
`Decidable (CompressCells …)` therefore compares word lists, its tests decide vector equalities
through `Vector.toList_inj`, and `E` equalities in tests go through `E.ext` or a theorem. L2
`Fin.foldl` is well-founded recursion and does not reduce; `compress` folds `Vector.foldl` over
`sigma`, which does. L3 `#guard` in a `module` file is a `meta` definition and needs a
`meta import` of the module it evaluates (`Lean/Compiler/LCNF/Visibility.lean`, `checkMeta`).

**Environment** (Lean `v4.33.1`, Mathlib at the pin). **E1** the elaborator's `decide` exhausts
`maxRecDepth` on `K` powers, even `g ^ 5`, when the decision goes through instance search on a
finite type (`Function.Injective Opcode.code` with a derived `Fintype`); `decide +kernel` after a
`cases` split proves the same in two seconds and is what `Opcode.code_injective` uses. **E2**
`deriving Fintype` (Mathlib's handler) fails inside a `module` file: the generated `Finset`
term does not typecheck under the module system ("declaration has metavariables"). Enumerations
that need a `Fintype` instance write it by hand or avoid it; Layer 2 avoids it. **E3** a
non-exposed `def` in a `public section` (`gLog?`) is visible to importers by name and opaque in
the kernel, as intended, but non-exposure hides a body from proofs only: while `gLog?` was a
computable scan, `#guard` under `meta import` still evaluated it and a plain test file could
`decide +kernel` it, which is why making the specification unrunnable took `noncomputable`,
not exposure. **E4** compile-time evaluation runs in the IR interpreter: one `K` multiplication
(`carryLessMul` then `reduce`) costs about 50 µs, and one kernel `K` multiplication tens of
milliseconds, which sizes every evaluated test (the `cases` of `Opcode.code_injective`, the
`g + 1` non-power check, the per-step kernel equalities of Layer 3 fixtures).

**Targets.** F1 constraint completeness as phrased in `docs/architecture.md` is false without a
program-shape hypothesis (test 15). F2 the `2^64 - 1` read bound is derivable from the caps.
F3 the BLAKE2S value limbs are virtual columns in Flock's stack in the Rust; ordinary columns
here. F4 whether the Rust's nonzero-count product also covers the finalize counts is to be
checked when `layout.rs:410-412` is transcribed; `CountsNonzero` covers read pulls.

## Survey record

Kept so the searches are not repeated.

- **BLAKE2s in Lean** (2026-09-08): no Lean 4 BLAKE2s with the tree-mode flag exists. Lean core,
  Batteries and Mathlib have none; Verified-zkEVM's Clean has BLAKE3 only (C9) and `evm-asm` the
  BLAKE2b `F` of EIP-152; `reilabs/lampe` (`Lampe/Crypto/Blake2s.lean`, Apache-2.0, Lean
  `v4.29.1`) has a single-flag, `Array`-based `compress` inside a Noir-semantics library;
  `kim-em/lean-crypto-hash` has SHA-2/SHA-3/HMAC only. Layer 1 therefore transcribes RFC 7693
  (§2.1, §2.6–§2.7, §3.1–§3.2, Appendix D) and takes `v[15] ^= f1` from the BLAKE2 paper §2.4
  and `blake2s-ref.c`; HACL*'s `Spec.Blake2.fst` is the second formal witness for the two-flag
  form. Vectors: RFC 7693 Appendix B (`"abc"`, with the working vector per round),
  `hashlib.blake2s` with `last_node` (`scripts/dump-blake2s.py vectors`), and the executor test
  `blake2s_computes_the_compression` (`scripts/dump-blake2s-rust.sh`).
- **leanVM**: the local checkout `../../leanEthereum/leanVM` is exactly `a386121f`. The
  specification's §2 matches `02-vm-specification.tex` at the pin clause by clause (S5 is the
  only nit). Executor arms `execute.rs:584-831`; `BLAKE2S` arm 779–812; filler loop 353–410;
  deferred `DEREF` 884–901; `κ_mem` 914–920; public-input seeding 173–177; `as_addr` 36–40.
  Tables `tables.rs:436-908`; `BLAKE2S` flushes 890–907 and addresses 373–386; `FlushBuilder`
  126–183; `TOWER_LANES` 44–49; `jump_identity` 63–78; opcode constants 95–100. Caps
  `cpu/mod.rs:51-64`, checked in `read_public` at 158–166, with the third-limb rejection at
  139–143. ISA `cpu/isa.rs:6-66`. Boundary blocks `layout.rs:355-395`; bytecode columns
  229–290 (slot packing 252–290) and the bytecode seed and finalize blocks 385–395;
  count blocks 410–412. Cell packing `hash_flock.rs:117-139, 162-185`; the compression
  `flock/src/hash.rs:191-231` with constants in `primitives/src/hash.rs:19-62`. BLAKE2S floor:
  `filler.rs:43` (`MIN_ROWS`) and `crates/flock/src/hash.rs:283-286` (`min_n_blocks_log`,
  `max(8)`). No checked-in fixtures; no textual bytecode format. Smallest executor tests:
  `mul_192bit_word` (`cpu/mod.rs:985`), `blake2s_computes_the_compression` (`:893`),
  `blake2s_self_hash_aliased_operands` (`:938`), `blake2s_requires_zero_third_limb` (`:922`).
  The executor bodies were read while writing the roadmap and, for Layer 2, its seeding and
  address decoding were read before `Memory.lean` was written (recorded in its docstring);
  Layer 3 must still be authored from §2 first and diffed afterwards. Layer 0 cites
  `gf2_64.rs:19-22` (bit encoding), `:28` (`F64::G`), and `python-verifier/verifier.py:177`
  (`E.__repr__`), `:182` (`GEN`).
- **CompPoly**: the working checkout `../CompPoly` (`40bac6e4`) is byte-identical to the pin on
  every field module. No generator, no order lemma, no `IsScalarTower`, no `{1, y, y²}` basis
  (Layer 0 adds `E.eq_sum_limbs`); no multiply-by-`x` lemma on `BF64` (a runnable carrier, if
  ever built, could use one); the MLE representation (`CMlPolynomialEval`, `eqPolynomial`)
  exists, sumcheck does not. Every CompPoly file is a `module` with `@[expose] public section`;
  P1 is inherited from core, not from CompPoly's own exposure. `Ext P` is a `def` over
  `Vector F P.d`; `Ext.ofVector`, `Ext.coeff`, `Ext.ext` and `Ext.coeff_ofFn` are the API
  Layer 0 wraps.
- **Clean**: surveyed at `93c9d1ef` on an extracted tree: `Clean/Utils/FiniteField`,
  `Clean/Circuit/{Channel,Formal,Operations,Lookup}`, all of `Clean/Air/`,
  `Clean/Examples/{FemtoCairo,FibonacciWithChannels}`, `Clean/Utils/OfflineMemory`. Exactly
  three declarations carry `[Fact (ringChar F ≠ 2)]` (`Balance.lean:259, 292, 551`) and the
  `Vm.lean` theorems inherit it; `exists_push_of_pull` and `consistent_of_normal` are
  degenerate without a marker; `BalancedInteractions` is unsatisfiable over `K` beyond one
  interaction. Core `Air`/`Table` files never consume `FiniteField.val`. The 22 commits since
  `1e0933cf` are the Lean 4.33.1 migration only, and none introduces `module`. Open Clean work
  checked: PRs #446, #454 (by this repository's author), #415, #453; issues #452, #154.
- **Environment**: `lake update Clean` added only Clean to the manifest; `lake build` of
  `Clean.Utils.FiniteField`, `Clean.Circuit.{Formal,Channel,WitnessGeneration}`,
  `Clean.Air.{Balance,FlatComponent,FlatEnsemble,OrderedChannel,Vm}`,
  `Clean.Examples.FemtoCairo.FemtoCairo`, `Clean.Table.Inductive` took 2m44s. In a
  non-`module` probe, `instance : FiniteField BF64` elaborates,
  `(@FiniteField.toField BF64 _ : Field BF64) = inferInstance` by `rfl`, and `assertZero` and
  `Channel.push` typecheck over `BF64`; from a `module` file the import itself is rejected
  (C8). `#eval` on `BF64`/`Ext3` works. Layer 0 timings on the author's machine: the seven
  `decide +kernel` order checks take 18–36 s together in `LeanerVM.Parameters.Generator`
  (`/3` about 6 s, `/5` about 9 s); `g^(2^64-1) = 1` by `decide +kernel` took 27 s and was
  replaced by Lagrange; the two test modules take about 10 s; plain `decide` exhausts
  `maxRecDepth` on every large power. Layer 1: the kernel decides one BLAKE2s compression in
  about a second (`decide +kernel`); the elaborator's `decide` manages one in about three
  seconds and exhausts its recursion budget on `CompressCells`; the Layer 1 test module builds
  in under a minute. Layer 2: each production module builds in one to two seconds, each test
  module in one to three; the `g + 1` non-power check by `fin_cases` and `decide +kernel` at
  `κ = 2` is within that (the former scan to `g^4000` at `κ = 16` was a fifth of a second).
  Layer 4: the production module builds in about three seconds and the test module in two;
  `decode` on a literal vector and a slot read decide in the kernel from a `module` test file,
  since they touch only `K` equality and vector indexing (L1).
  A git worktree has no `.lake/`; symlinking or copying `.lake/packages` from the main checkout
  reuses the built dependencies. On a fresh checkout `lake build --wfail` fails at
  `CompPoly:extraDep`: CompPoly's `preferReleaseBuild` finds no release tag at `3468b38c` and
  warns. CI and `validate.sh` therefore build without `--wfail` and with Lake's caches enabled,
  and CI fetches Mathlib's oleans with `lake exe cache get` before building; without them the
  job compiled Mathlib from source and hit its time limit (`docs/dependencies.md`).
