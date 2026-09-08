# Status: leanISA semantics and M3 constraints

This file records where the [leanISA roadmap](leanisa-blueprint.md) stands as of the Layer 0
working tree on branch `feat/leanisa-orders-of-g` on 2026-09-08, built and validated locally but
not yet merged. It is a hand-maintained snapshot, rewritten whole when a layer lands or a
decision is taken; the roadmap is the authority on what is wanted, and the tracking issue
[#4](https://github.com/Verified-zkEVM/leanerVM/issues/4) mirrors the coverage table below.

## Where this roadmap stands

**At a glance.** Layer 0 is built. `LeanerVM/Parameters/Field.lean` and
`LeanerVM/Parameters/Generator.lean` define `K`, `E`, `y`, `ofK`, `E.limb`, `E.ofLimbs`,
`IsInK`, `IsCanonical128`, `g`, and `gpow`, and prove `orderOf_g` and `gpow_injOn` from the
seven `decide +kernel` checks; `./scripts/validate.sh` is green and the axiom closure of every
declaration is `propext, Classical.choice, Quot.sound`. The kernel axiom audit is enabled in CI
(`axiom-audit-root: LeanerVM`). Clean's `FiniteField K` instance is `instFiniteFieldK` in the
plain file `LeanerVM/Parameters/CleanField.lean`: Clean is not a `module`, so Clean is consumed
from plain files and the aggregates are plain (finding C8, now the roadmap's module-system
convention). Kernel-`decide` over `E` arithmetic works from plain files but not from `module`s
(finding P1). A third finding changed the repository's test
mechanism: an executable linking CompPoly's `BF64` module is OOM-killed at startup (P3), so
`lake test` now builds the test library instead of running an executable. Nothing under
`LeanerVM/Semantics/` or `LeanerVM/Arithmetization/` is non-empty yet.

### Roadmap coverage

| Layer | Status | Notes |
| --- | --- | --- |
| 0 — fields, limbs, generator | built, awaiting review | complete; `instFiniteFieldK` lives in the plain `CleanField.lean` (C8); `E` arithmetic not kernel-reducible from `module` files (P1) |
| 1 — BLAKE2s | untouched | needs the Rust word-order vector |
| 2 — instructions, image, public input | untouched | can start on Layer 0 |
| 3 — `step`, `ValidExecution` | untouched | Category A; write from specification §2 first; "decidable by `decide`" tests depend on P1 |
| 4 — bytecode encoding | untouched | |
| 5 — channels | untouched; consumes Clean | plain files (C8) |
| 6 — six tables | untouched; consumes Clean | plain files (C8) |
| 7 — boundary blocks | untouched; consumes Clean | plain files (C8) |
| 8 — statement | untouched; consumes Clean | plain files (C8) |
| 9 — bus soundness | untouched; consumes a Clean change | statements land as block comments with Layer 8 |
| 10 — T1 | untouched; consumes Layer 9 | |

### The frontier

- **Layer 0** awaits review as `feat(parameters): leanISA Layer 0 — fields, limbs, generator`.
  Its reviewer reading list is the three production files, the three test files, the policy
  change in `CONTRIBUTING.md`, and the CI change; the roadmap's Layer 0 targets are all present.
- **Clean is consumed from plain files** (C8, settled 2026-09-08). Lean `v4.33.1` rejects
  `import` of a non-`module` from a `module`, so the roadmap's module-system convention makes
  the Clean-facing files plain and everything importing them plain too: today
  `Parameters/CleanField.lean`, `LeanerVM.lean`, and the test aggregate; Layers 5–10 will be
  plain files. Clean adopting `module` upstream would let the boundary move back down.
- **CompPoly's `Ext` arithmetic does not reduce in the kernel from a `module` file** (P1). The
  roadmap's Layer 3 tests ("`ValidExecution` by `decide`") and the Layer 6 per-table row tests
  need compiled evaluation (`#guard` under `meta import`), a plain test file, where the kernel
  sees every body, or an upstream fix. Decision 4 below.
- **Layers 1, 2, 4** can start now. Layer 2 builds on Layer 0.
- **The Rust vectors** for Layer 1 (`blake2s_computes_the_compression`) and Layer 3
  (`mul_192bit_word`) are not yet dumped; the dump command goes under `scripts/` with the
  fixture.
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
4. **Executable tests versus kernel `decide`** (P1). Either the roadmap's "by `decide`" tests
   for Layers 3 and 6 live in plain test files (the test aggregate already is one), or they are
   restated as compiled `#guard`s, or CompPoly makes `Ext.ofFn` and
   `Ext.instDecidableEq` kernel-reducible under the module system (a literal-vector or
   `List.ofFn`-free construction, since the blocker is core's unexposed `Array.ofFn`), which is a
   CompPoly pin bump. `E.ofLimbs` is already a literal vector so the predicates on literal words
   decide in the kernel today.
5. **Restoring a test executable** (P3). The library test driver is a workaround. If the
   roadmap's executable fixtures, the differential tests against the pinned Rust, or the native
   execution target need a real binary, CompPoly must first stop threading `[Fintype F]` through
   `Ext`'s runtime signature and make `Fintype BF64` noncomputable (P3, a pin bump), after which
   `tests/Main.lean` can be an executable again.

## Open findings against the sources

Numbered for citation from pull requests and `docs/leanvm-target.md`. **S** = internal to the
specification document; **R** = Rust versus specification; **C** = Clean versus leanISA; **P** =
CompPoly versus leanISA. The roadmap's acceptance tests already encode the ones that bind a
definition.

**Specification.** S1 halting is tested after execution in §2 but before the fetch in the Rust
and the bus (acceptance test 5). S2 final `fp = g^0` is required by §6.1 and the Rust, not by
§2 (test 4). S3 `DEREF` reads `fp·o3` unconditionally in §7.4, unstated in §2 (test 6). S4 the
generator value is not in the specification; Layer 0 binds it to the Rust and the Python
verifier. S5 `02-vm-specification.tex` line 75 annotates `o_3 ∈ K` where the cell value is
meant. S6 §8.4 Fiat–Shamir is `TODO`.

**Rust executor** (`crates/lean_vm/src/cpu/execute.rs`), all witness-generation behaviour, none
a second meaning of the machine (test 19): R1 registers and operands are `u32` exponents. R2 an
equal rewrite of a set cell is accepted, a differing one panics. R3 an unset cell reads as zero
with a diagnostic. R4 memory grows on demand; no range check at access. R5 `κ_mem` is a
post-run high-water mark. R6 `DEREF` in `cell` mode fills the unset side, asserts when both are
set, defers when neither is, and zero-fills leftovers. R7 `MUL` back-solves one unset operand;
`XOR` does not. R8 ten `RHint` advice kinds run before each instruction. R9 a taken `JUMP` needs
small g-powers. R10 a `DEREF` pointer must be a small g-power. R11 the canonical check covers the
seven read cells only (test 12). R12 metadata split confirmed (test 11). R13 flag booleanity is
not an AIR constraint (test 18). R14 halt asserts `fp = 0` (test 4). R15 step cap `10^8`. R16
the filler phase executes fill blocks after halt and can raise `κ_mem` (test 15). R17
`g = 0x2` (test 1; Layer 0 `g`, certified). R18 `SET`'s immediate is one `F192`. R19 slot
packing matches §8.1 (test 16). R20 `cpu/mod.rs` cites a stale `.tex` filename.

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
by `rfl`, and `LeanerVM.lean` and the test aggregate are plain.

**CompPoly** (`3468b38c`): **P1 `Ext` arithmetic is not kernel-reducible from a `module`
file.** `Ext.ofFn` is `Vector.ofFn`, which is core's `Array.ofFn`
(`Init/Data/Array/Basic.lean:331`), not `@[expose]`d; a `module` importer sees only exposed
bodies, so `decide` and `decide +kernel` get stuck on `Ext.ofBase`, `Ext.gen`, `+`, `*`, and on
`Ext.instDecidableEq` (through `Vector`'s `decEq`). `Ext.ofVector` of a literal, `Ext.coeff`,
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
bump here. Until then no leanerVM executable may link the field module.

**Targets.** F1 constraint completeness as phrased in `docs/architecture.md` is false without a
program-shape hypothesis (test 15). F2 the `2^64 - 1` read bound is derivable from the caps.
F3 the BLAKE2S value limbs are virtual columns in Flock's stack in the Rust; ordinary columns
here. F4 whether the Rust's nonzero-count product also covers the finalize counts is to be
checked when `layout.rs:410-412` is transcribed; `CountsNonzero` covers read pulls.

## Survey record

Kept so the searches are not repeated.

- **leanVM**: the local checkout `../../leanEthereum/leanVM` is exactly `a386121f`. The
  specification's §2 matches `02-vm-specification.tex` at the pin clause by clause (S5 is the
  only nit). Executor arms `execute.rs:584-831`; filler loop 353–410; deferred `DEREF` 884–901;
  `κ_mem` 914–920. Tables `tables.rs:436-908`; `FlushBuilder` 126–183; `TOWER_LANES` 44–49;
  `jump_identity` 63–78. Boundary blocks `layout.rs:355-395`; slot packing 252–290; count blocks
  410–412. No checked-in fixtures; no textual bytecode format. Smallest executor tests:
  `mul_192bit_word` (`cpu/mod.rs:985`), `blake2s_computes_the_compression` (`:893`),
  `blake2s_self_hash_aliased_operands` (`:938`), `blake2s_requires_zero_third_limb` (`:922`).
  The executor bodies were read while writing the roadmap; Layer 3 must still be authored from
  §2 first and diffed afterwards. Layer 0 cites `gf2_64.rs:19-22` (bit encoding), `:28`
  (`F64::G`), and `python-verifier/verifier.py:177` (`E.__repr__`), `:182` (`GEN`).
- **CompPoly**: the working checkout `../CompPoly` (`40bac6e4`) is byte-identical to the pin on
  every field module. No generator, no order lemma, no `IsScalarTower`, no `{1, y, y²}` basis
  (Layer 0 adds `E.eq_sum_limbs`); the MLE representation (`CMlPolynomialEval`,
  `eqPolynomial`) exists, sumcheck does not. Every CompPoly file is a `module` with
  `@[expose] public section`; P1 is inherited from core, not from CompPoly's own exposure.
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
  `maxRecDepth` on every large power. A git worktree has no `.lake/`; symlinking
  `.lake/packages` to the main checkout's reuses the built dependencies. On a fresh checkout
  `lake build --wfail` fails at `CompPoly:extraDep`: CompPoly's `preferReleaseBuild` finds no
  release tag at `3468b38c` and warns, so CI and `validate.sh` pass `--no-cache`
  (`docs/dependencies.md`).
