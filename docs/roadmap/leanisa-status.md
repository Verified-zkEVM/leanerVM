# Status: leanISA semantics and M3 constraints

This file records where the [leanISA roadmap](leanisa-blueprint.md) stands as of the branch
landing Layer 1 on top of Layer 0 (`main` at `8926f92`) on 2026-09-08. It is a hand-maintained
snapshot, rewritten whole when a layer lands or a decision is taken; the roadmap is the
authority on what is wanted, and the tracking issue
[#4](https://github.com/Verified-zkEVM/leanerVM/issues/4) mirrors the coverage table below.

## Where this roadmap stands

**At a glance.** Layers 0 and 1 are built. `LeanerVM/Parameters/Field.lean` and
`LeanerVM/Parameters/Generator.lean` define `K`, `E`, `y`, `ofK`, `E.limb`, `E.ofLimbs`,
`IsInK`, `IsCanonical128`, `g`, and `gpow`, and prove `orderOf_g` and `gpow_injOn` from the
seven `decide +kernel` checks; Clean's `FiniteField K` instance is `instFiniteFieldK` in the
plain file `LeanerVM/Parameters/CleanField.lean`. `LeanerVM/Parameters/Blake2s.lean` and
`LeanerVM/Semantics/Blake2s.lean` define `iv`, `sigma`, the two-flag `compress`, the cell
encoding (`cellWords`, `wordsCell`, `unpackMetadata`), and `CompressCells`, each pinned by
kernel-checked vectors from RFC 7693, from CPython's `hashlib.blake2s`, and from the pinned Rust
executor. `./scripts/validate.sh` is green, the axiom closure of every declaration is
`propext, Classical.choice, Quot.sound`, and the kernel axiom audit is enabled in CI
(`axiom-audit-root: LeanerVM`). Clean is consumed from plain files and the aggregates are plain
(finding C8, now the roadmap's module-system convention); kernel-`decide` over `E` arithmetic
works from plain files but not from `module`s (P1); `lake test` builds the test library because
no executable may link the field module (P3). Nothing under `LeanerVM/Arithmetization/` is
non-empty yet.

### Roadmap coverage

| Layer | Status | Notes |
| --- | --- | --- |
| 0 — fields, limbs, generator | built | complete; `instFiniteFieldK` lives in the plain `CleanField.lean` (C8); `E` arithmetic not kernel-reducible from `module` files (P1) |
| 1 — BLAKE2s | built, awaiting review | complete; flags are 32-bit words, not `Bool` (decision 6); vectors kernel-checked from a `module` file (L1) |
| 2 — instructions, image, public input | untouched | can start on Layer 0 |
| 3 — `step`, `ValidExecution` | untouched | Category A; write from specification §2 first; "decidable by `decide`" tests depend on P1 and L1 |
| 4 — bytecode encoding | untouched | |
| 5 — channels | untouched; consumes Clean | plain files (C8) |
| 6 — six tables | untouched; consumes Clean | plain files (C8) |
| 7 — boundary blocks | untouched; consumes Clean | plain files (C8) |
| 8 — statement | untouched; consumes Clean | plain files (C8) |
| 9 — bus soundness | untouched; consumes a Clean change | statements land as block comments with Layer 8 |
| 10 — T1 | untouched; consumes Layer 9 | |

### The frontier

- **Layer 1** awaits review as `feat(blake2s): leanISA Layer 1`. Its reviewer reading list is
  the two production files, the two test files, the two dump scripts, and decision 6; the
  roadmap's Layer 1 targets are all present, with `UInt32` where the roadmap writes `Bool`.
- **Clean is consumed from plain files** (C8, settled 2026-09-08). Lean `v4.33.1` rejects
  `import` of a non-`module` from a `module`, so the roadmap's module-system convention makes
  the Clean-facing files plain and everything importing them plain too: today
  `Parameters/CleanField.lean`, `LeanerVM.lean`, and the test aggregate; Layers 5–10 will be
  plain files. Clean adopting `module` upstream would let the boundary move back down.
- **CompPoly's `Ext` arithmetic does not reduce in the kernel from a `module` file** (P1), and
  neither does any `Vector` or `E` equality (L1). Layer 1 shows what does reduce: a `module`
  test decides a full compression and `CompressCells` on literal cells with `decide +kernel` in
  about a second each, because `compress` and `E.ofLimbs` avoid `Vector.ofFn` and every vector
  equality is decided on its word list. The roadmap's Layer 3 tests ("`ValidExecution` by
  `decide`") and the Layer 6 per-table row tests still need one of: compiled evaluation
  (`#guard` under `meta import`), a plain test file, or an upstream fix. Decision 4 below.
- **Layers 2 and 4** can start now. Layer 2 builds on Layer 0.
- **The Rust vectors.** Layer 1's (`blake2s_computes_the_compression`) is reproduced by
  `scripts/dump-blake2s-rust.sh`; Layer 3's (`mul_192bit_word`) is not yet dumped; the dump
  command goes under `scripts/` with the fixture.
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
4. **Executable tests versus kernel `decide`** (P1, L1). Either the roadmap's "by `decide`"
   tests for Layers 3 and 6 live in plain test files (the test aggregate already is one), or
   they are restated as compiled `#guard`s, or CompPoly makes `Ext.ofFn` and
   `Ext.instDecidableEq` kernel-reducible under the module system (a literal-vector or
   `List.ofFn`-free construction, since the blocker is core's unexposed `Array.ofFn`; a
   list-comparing `DecidableEq E`, since core's `Vector` equality is unexposed too), which is a
   CompPoly pin bump. `E.ofLimbs` is already a literal vector so the predicates on literal words
   decide in the kernel today, and Layer 1's `Decidable (CompressCells …)` compares word lists
   for the same reason.
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
CompPoly versus leanISA; **L** = Lean core versus the roadmap's expectations. The roadmap's
acceptance tests already encode the ones that bind a definition.

**Specification.** S1 halting is tested after execution in §2 but before the fetch in the Rust
and the bus (acceptance test 5). S2 final `fp = g^0` is required by §6.1 and the Rust, not by
§2 (test 4). S3 `DEREF` reads `fp·o3` unconditionally in §7.4, unstated in §2 (test 6). S4 the
generator value is not in the specification; Layer 0 binds it to the Rust and the Python
verifier. S5 `02-vm-specification.tex` line 75 annotates `o_3 ∈ K` where the cell value is
meant. S6 §8.4 Fiat–Shamir is `TODO`. S7 §2 calls `BLAKE2S` "the standard BLAKE2s compression"
and names both flags in the metadata cell without saying that the flag *words* enter the state
unchanged (decision 6).

**Rust executor** (`crates/lean_vm/src/cpu/execute.rs`), all witness-generation behaviour, none
a second meaning of the machine (test 19): R1 registers and operands are `u32` exponents. R2 an
equal rewrite of a set cell is accepted, a differing one panics. R3 an unset cell reads as zero
with a diagnostic. R4 memory grows on demand; no range check at access. R5 `κ_mem` is a
post-run high-water mark. R6 `DEREF` in `cell` mode fills the unset side, asserts when both are
set, defers when neither is, and zero-fills leftovers. R7 `MUL` back-solves one unset operand;
`XOR` does not. R8 ten `RHint` advice kinds run before each instruction. R9 a taken `JUMP` needs
small g-powers. R10 a `DEREF` pointer must be a small g-power. R11 the canonical check covers the
seven read cells only (test 12; pinned by the output-cell mutation in the Layer 1 tests). R12
metadata split confirmed (test 11). R13 flag booleanity is not an AIR constraint (test 18). R14
halt asserts `fp = 0` (test 4). R15 step cap `10^8`. R16 the filler phase executes fill blocks
after halt and can raise `κ_mem` (test 15). R17 `g = 0x2` (test 1; Layer 0 `g`, certified). R18
`SET`'s immediate is one `F192`. R19 slot packing matches §8.1 (test 16). R20 `cpu/mod.rs` cites
a stale `.tex` filename. R21 the repository holds two BLAKE2s compressions:
`flock::hash::blake2s_compress` (two flag words; the opcode) and `primitives::hash::compress`
(last-block flag only; the byte hasher). Layer 1 transcribes the former. R22 the opcode's IV,
sigma, rotations and round count agree with RFC 7693 (`crates/primitives/src/hash.rs:19-62`), so
no leanVM-specific compression exists.

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
  deferred `DEREF` 884–901; `κ_mem` 914–920. Tables `tables.rs:436-908`; `BLAKE2S` flushes
  890–907 and addresses 373–386; `FlushBuilder` 126–183; `TOWER_LANES` 44–49; `jump_identity`
  63–78. Boundary blocks `layout.rs:355-395`; slot packing 252–290; count blocks 410–412. Cell
  packing `hash_flock.rs:117-139, 162-185`; the compression `flock/src/hash.rs:191-231` with
  constants in `primitives/src/hash.rs:19-62`. No checked-in fixtures; no textual bytecode
  format. Smallest executor tests: `mul_192bit_word` (`cpu/mod.rs:985`),
  `blake2s_computes_the_compression` (`:889`), `blake2s_self_hash_aliased_operands` (`:933`),
  `blake2s_requires_zero_third_limb` (`:919`). The executor bodies were read while writing the
  roadmap; Layer 3 must still be authored from §2 first and diffed afterwards. Layer 0 cites
  `gf2_64.rs:19-22` (bit encoding), `:28` (`F64::G`), and `python-verifier/verifier.py:177`
  (`E.__repr__`), `:182` (`GEN`).
- **CompPoly**: the working checkout `../CompPoly` (`40bac6e4`) is byte-identical to the pin on
  every field module. No generator, no order lemma, no `IsScalarTower`, no `{1, y, y²}` basis
  (Layer 0 adds `E.eq_sum_limbs`); the MLE representation (`CMlPolynomialEval`,
  `eqPolynomial`) exists, sumcheck does not. Every CompPoly file is a `module` with
  `@[expose] public section`; P1 is inherited from core, not from CompPoly's own exposure.
  `Ext P` is a `def` over `Vector F P.d`; `Ext.ofVector`, `Ext.coeff`, `Ext.ext` and
  `Ext.coeff_ofFn` are the API Layer 0 wraps.
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
  in under a minute. A git worktree has no `.lake/`; symlinking or copying `.lake/packages`
  from the main checkout reuses the built dependencies.
