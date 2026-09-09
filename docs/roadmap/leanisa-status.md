# Status: leanISA semantics and M3 constraints

This file records where the [leanISA roadmap](leanisa-blueprint.md) stands as of the Layer 2
working tree, built on `main` at `c66d8a0` (Layer 0, PR #6) on 2026-09-08 and revised on
2026-09-09 (`gLog?` made noncomputable), validated locally but not yet merged. Layer 1 is in flight on a sibling branch (`feat/leanisa-blake2s-semantics`) with
its own rewrite of this file; whichever lands second re-merges the two. This is a hand-maintained
snapshot, rewritten whole when a layer lands or a decision is taken; the roadmap is the authority
on what is wanted, and the tracking issue
[#4](https://github.com/Verified-zkEVM/leanerVM/issues/4) mirrors the coverage table below.

## Where this roadmap stands

**At a glance.** Layers 0 and 2 are built on this branch. `LeanerVM/Parameters/Field.lean` and
`LeanerVM/Parameters/Generator.lean` define `K`, `E`, `y`, `ofK`, `E.limb`, `E.ofLimbs`,
`IsInK`, `IsCanonical128`, `g`, and `gpow`, and prove `orderOf_g` and `gpow_injOn` from the
seven `decide +kernel` checks; Clean's `FiniteField K` instance is `instFiniteFieldK` in the
plain file `LeanerVM/Parameters/CleanField.lean`. `LeanerVM/Parameters/Isa.lean` defines
`Opcode`, `Opcode.code` (`g^0 … g^5`), and the five caps; `LeanerVM/Semantics/Memory.lean`
defines `gLog?` (noncomputable, the index by `Classical.choose`), `MemImage`, `MemImage.read`,
and `PublicInput` with `word0`/`word1`, and proves `gLog?_spec`, the one statement through which
the bounded logarithm is trusted, with `gLog?_eq_none_iff` and `gLog?_gpow_eq_none` on the
failure side;
`LeanerVM/Semantics/Instruction.lean` defines `DerefMode`, `Instr`, `Instr.opcode`, `Program`,
and `Program.fetch`. `./scripts/validate.sh` is green and the axiom closure of every declaration
is `propext, Classical.choice, Quot.sound`; the kernel axiom audit is enabled in CI
(`axiom-audit-root: LeanerVM`). Clean is consumed from plain files and the aggregates are plain
(finding C8, the roadmap's module-system convention); kernel-`decide` over `E` arithmetic works
from plain files but not from `module`s (P1); `lake test` builds the test library because no
executable may link the field module (P3). Nothing under `LeanerVM/Arithmetization/` is
non-empty yet.

### Roadmap coverage

| Layer | Status | Notes |
| --- | --- | --- |
| 0 — fields, limbs, generator | landed (PR #6) | `instFiniteFieldK` lives in the plain `CleanField.lean` (C8); `E` arithmetic not kernel-reducible from `module` files (P1) |
| 1 — BLAKE2s | in flight on `feat/leanisa-blake2s-semantics` | not on this branch |
| 2 — instructions, image, public input | built, awaiting review | `gLog?` is noncomputable behind `gLog?_spec`, hypothesis `κ < 64`; `MemImage` is an `abbrev`; `Instr.opcode` added (see the frontier) |
| 3 — `step`, `ValidExecution` | untouched; needs Layers 1 and 2 | Category A; write from specification §2 first; fixtures are proofs through the fetch and read lemmas (decision 4) |
| 4 — bytecode encoding | untouched; needs Layer 2 | `Instr.opcode` supplies slot 3 |
| 5 — channels | untouched; consumes Clean | plain files (C8) |
| 6 — six tables | untouched; consumes Clean | plain files (C8) |
| 7 — boundary blocks | untouched; consumes Clean | plain files (C8) |
| 8 — statement | untouched; consumes Clean | plain files (C8) |
| 9 — bus soundness | untouched; consumes a Clean change | statements land as block comments with Layer 8 |
| 10 — T1 | untouched; consumes Layer 9 | |

### The frontier

- **Layer 2** awaits review as `feat(semantics): leanISA Layer 2 — instructions, image, public
  input`. Its reviewer reading list is the three production files, the three test files, and the
  roadmap changes below. Every Layer 2 target of the roadmap is present; the roadmap's pinned
  shapes were adjusted in four places, each recorded in the roadmap itself or here:
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
- **CompPoly's `Ext` arithmetic does not reduce in the kernel from a `module` file** (P1). The
  Layer 3 fixtures (proofs unfolding `run`, whose per-step `E` equalities must reduce in the
  kernel) need a plain test file, where the kernel sees every body, or an upstream fix; the
  Layer 6 per-table row tests can also use compiled evaluation (`#guard` under `meta import`).
  Decision 4 below.
- **Layer 3** can start once Layer 1 lands: it needs `CompressCells` for the `BLAKE2S` arm and
  everything else from Layer 2. Layer 4 can start now.
- **The Rust vector** for Layer 3 (`mul_192bit_word`, `cpu/mod.rs:985`) is not yet dumped; the
  dump command goes under `scripts/` with the fixture.
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
4. **Executable tests versus kernel `decide`** (P1, E4). Either the roadmap's "by `decide`"
   tests for Layers 3 and 6 live in plain test files (the test aggregate already is one), or
   they are restated as compiled `#guard`s, or CompPoly makes `Ext.ofFn` and
   `Ext.instDecidableEq` kernel-reducible under the module system (a literal-vector or
   `List.ofFn`-free construction, since the blocker is core's unexposed `Array.ofFn`), which is a
   CompPoly pin bump. `E.ofLimbs` is already a literal vector so the predicates on literal words
   decide in the kernel today. Since `gLog?` is noncomputable (2026-09-09), `ValidExecution`
   is neither kernel-decidable nor compilable at any `κ`; a Layer 3 fixture is a proof that
   unfolds `run` through `Program.fetch_gpow` and `MemImage.read_gpow` and decides each step's
   equality on literal words in the kernel, which P1 confines to plain test files until the
   upstream fix.
5. **Restoring a test executable** (P3). The library test driver is a workaround. If the
   roadmap's executable fixtures, the differential tests against the pinned Rust, or the native
   execution target need a real binary, CompPoly must first stop threading `[Fintype F]` through
   `Ext`'s runtime signature and make `Fintype BF64` noncomputable (P3, a pin bump), after which
   `tests/Main.lean` can be an executable again.

## Open findings against the sources

Numbered for citation from pull requests and `docs/leanvm-target.md`. **S** = internal to the
specification document; **R** = Rust versus specification; **C** = Clean versus leanISA; **P** =
CompPoly versus leanISA; **E** = the Lean environment. The roadmap's acceptance tests already
encode the ones that bind a definition.

**Specification.** S1 halting is tested after execution in §2 but before the fetch in the Rust
and the bus (acceptance test 5). S2 final `fp = g^0` is required by §6.1 and the Rust, not by
§2 (test 4). S3 `DEREF` reads `fp·o3` unconditionally in §7.4, unstated in §2 (test 6). S4 the
generator value is not in the specification; Layer 0 binds it to the Rust and the Python
verifier. S5 `02-vm-specification.tex` line 75 annotates `o_3 ∈ K` where the cell value is
meant. S6 §8.4 Fiat–Shamir is `TODO`. S7 the BLAKE2S table floor (`τ_BLAKE2S ≥ 3`) is enforced
by the verifier (`cpu/mod.rs:166`) and the filler (`filler.rs:43`) but appears in no section of
the specification; Layer 2 binds `minLogRowsBlake2s` to the Rust and to Flock's
`min_n_blocks_log` (`crates/flock/src/hash.rs:283-286`).

**Rust executor** (`crates/lean_vm/src/cpu/execute.rs`), all witness-generation behaviour, none
a second meaning of the machine (test 19): R1 registers and operands are `u32` exponents
(Layer 2's operands are `K` elements; a non-`g`-power operand is expressible and names no valid
cell). R2 an equal rewrite of a set cell is accepted, a differing one panics. R3 an unset cell
reads as zero with a diagnostic. R4 memory grows on demand; no range check at access. R5
`κ_mem` is a post-run high-water mark. R6 `DEREF` in `cell` mode fills the unset side, asserts
when both are set, defers when neither is, and zero-fills leftovers. R7 `MUL` back-solves one
unset operand; `XOR` does not. R8 ten `RHint` advice kinds run before each instruction. R9 a
taken `JUMP` needs small g-powers. R10 a `DEREF` pointer must be a small g-power. R11 the
canonical check covers the seven read cells only (test 12). R12 metadata split confirmed
(test 11). R13 flag booleanity is not an AIR constraint (test 18). R14 halt asserts `fp = 0`
(test 4). R15 step cap `10^8`. R16 the filler phase executes fill blocks after halt and can
raise `κ_mem` (test 15). R17 `g = 0x2` (test 1; Layer 0 `g`, certified). R18 `SET`'s immediate
is one `F192` (Layer 2 `setConstant (o : K) (k : E)`). R19 slot packing matches §8.1 (test 16).
R20 `cpu/mod.rs` cites a stale `.tex` filename. R21 the verifier rejects a public input with a
nonzero top limb (`cpu/mod.rs:139-143`); Layer 2's `PublicInput` cannot express one, so the
check is a type, not a hypothesis.

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

- **leanVM**: the local checkout `../../leanEthereum/leanVM` is exactly `a386121f`. The
  specification's §2 matches `02-vm-specification.tex` at the pin clause by clause (S5 is the
  only nit). Executor arms `execute.rs:584-831`; filler loop 353–410; deferred `DEREF` 884–901;
  `κ_mem` 914–920; public-input seeding 173–177; `as_addr` 36–40. Tables `tables.rs:436-908`;
  `FlushBuilder` 126–183; `TOWER_LANES` 44–49; `jump_identity` 63–78; opcode constants 95–100.
  Caps `cpu/mod.rs:51-64`, checked in `read_public` at 158–166, with the third-limb rejection at
  139–143. ISA `cpu/isa.rs:6-66`. Boundary blocks `layout.rs:355-395`; slot packing 252–290;
  count blocks 410–412. BLAKE2S floor: `filler.rs:43` (`MIN_ROWS`) and
  `crates/flock/src/hash.rs:283-286` (`min_n_blocks_log`, `max(8)`). No checked-in fixtures; no
  textual bytecode format. Smallest executor tests: `mul_192bit_word` (`cpu/mod.rs:985`),
  `blake2s_computes_the_compression` (`:893`), `blake2s_self_hash_aliased_operands` (`:938`),
  `blake2s_requires_zero_third_limb` (`:922`). The executor bodies were read while writing the
  roadmap and, for Layer 2, its seeding and address decoding were read before `Memory.lean`
  was written (recorded in its docstring); Layer 3 must still be authored from §2 first and
  diffed afterwards. Layer 0 cites `gf2_64.rs:19-22` (bit encoding), `:28` (`F64::G`), and
  `python-verifier/verifier.py:177` (`E.__repr__`), `:182` (`GEN`).
- **CompPoly**: the working checkout `../CompPoly` (`40bac6e4`) is byte-identical to the pin on
  every field module. No generator, no order lemma, no `IsScalarTower`, no `{1, y, y²}` basis
  (Layer 0 adds `E.eq_sum_limbs`); no multiply-by-`x` lemma on `BF64` (a runnable carrier, if
  ever built, could use one); the MLE representation (`CMlPolynomialEval`, `eqPolynomial`)
  exists, sumcheck does not. Every CompPoly file is a `module` with `@[expose] public section`;
  P1 is inherited from core, not from CompPoly's own exposure.
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
  `maxRecDepth` on every large power. Layer 2 timings: each production module builds in one to
  two seconds, each test module in one to three; the `g + 1` non-power check by `fin_cases` and
  `decide +kernel` at `κ = 2` is within that (the former scan to `g^4000` at `κ = 16` was a
  fifth of a second). A git worktree has no `.lake/`; symlinking `.lake/packages` to the main
  checkout's reuses the built dependencies. On a fresh checkout `lake build --wfail` fails at
  `CompPoly:extraDep`: CompPoly's `preferReleaseBuild` finds no release tag at `3468b38c` and
  warns, so CI and `validate.sh` pass `--no-cache` (`docs/dependencies.md`).
