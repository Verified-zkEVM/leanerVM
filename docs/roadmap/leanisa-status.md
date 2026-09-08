# Status: leanISA semantics and M3 constraints

This file records where the [leanISA roadmap](leanisa-blueprint.md) stands as of the branch
`scaraven/leanISA-blueprint` on 2026-09-08, before any layer has landed. It is a hand-maintained
snapshot, rewritten whole when a layer lands or a decision is taken; the roadmap is the
authority on what is wanted, and the tracking issue
[#4](https://github.com/Verified-zkEVM/leanerVM/issues/4) mirrors the coverage table below.

## Where this roadmap stands

**At a glance.** No layer has landed. The dependencies are in place: Clean `93c9d1ef` is a Lake
dependency alongside CompPoly `3468b38c` with one shared Mathlib, its circuit and Air modules
build under Lean `v4.33.1`, and a `FiniteField K` instance elaborates with its field structure
definitionally CompPoly's. The generator `0x2` has been checked to have full order. Nothing under
`LeanerVM/` is non-empty yet.

### Roadmap coverage

| Layer | Status | Notes |
| --- | --- | --- |
| 0 — fields, limbs, generator | untouched | `FiniteField K` instance and the seven order checks verified in a probe, not landed |
| 1 — BLAKE2s | untouched | needs the Rust word-order vector |
| 2 — instructions, image, public input | untouched | |
| 3 — `step`, `ValidExecution` | untouched | Category A; write from specification §2 first |
| 4 — bytecode encoding | untouched | |
| 5 — channels | untouched | |
| 6 — six tables | untouched | |
| 7 — boundary blocks | untouched | |
| 8 — statement | untouched | |
| 9 — bus soundness | untouched; consumes a Clean change | statements land as block comments with Layer 8 |
| 10 — T1 | untouched; consumes Layer 9 | |

### The frontier

- **Layers 0, 1, 4** can start now and are independent. Layer 0 is the first production
  declaration and enables the kernel axiom audit.
- **The Rust vectors** for Layer 1 (`blake2s_computes_the_compression`) and Layer 3
  (`mul_192bit_word`) are not yet dumped; the dump command goes under `scripts/` with the
  fixture.
- **Clean's bus** is the only external item on the critical path (Layers 9–10). The contract
  is stated in the roadmap's dependency table; no upstream issue exists yet for the direction
  tag, and Clean [#452](https://github.com/Verified-zkEVM/clean/issues/452) covers only the
  side-condition half of the balance change. Filing the combined request is the first action
  of the docs stage.
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

## Open findings against the sources

Numbered for citation from pull requests and `docs/leanvm-target.md`. **S** = internal to the
specification document; **R** = Rust versus specification; **C** = Clean versus leanISA. The
roadmap's acceptance tests already encode the ones that bind a definition.

**Specification.** S1 halting is tested after execution in §2 but before the fetch in the Rust
and the bus (acceptance test 5). S2 final `fp = g^0` is required by §6.1 and the Rust, not by
§2 (test 4). S3 `DEREF` reads `fp·o3` unconditionally in §7.4, unstated in §2 (test 6). S4 the
generator value is not in the specification. S5 `02-vm-specification.tex` line 75 annotates
`o_3 ∈ K` where the cell value is meant. S6 §8.4 Fiat–Shamir is `TODO`.

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
`g = 0x2` (test 1). R18 `SET`'s immediate is one `F192`. R19 slot packing matches §8.1
(test 16). R20 `cpu/mod.rs` cites a stale `.tex` filename.

**Clean** (`93c9d1ef`): C1 direction is the sign of the multiplicity (test 13). C2 balance is a
field sum with a characteristic side condition (test 14). C3 a component cannot see its row
index (Layer 8 hypothesis; PR #446). C4 `ProverData` is untied from committed columns (Layer 8
hypotheses; PR #446). C5 no degree bound on `Expression`. C6 no prover-chosen heights. C7 the
channel-based VM example (`FibonacciWithChannels.lean`) installs `Fact (ringChar F ≠ 2)`, and
`FemtoCairo` is `InductiveTable`-based with prime-field address arithmetic; both are proof-style
templates only.

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
  §2 first and diffed afterwards.
- **CompPoly**: the working checkout `../CompPoly` (`40bac6e4`) is byte-identical to the pin on
  every field module. No generator, no order lemma, no `IsScalarTower`, no `{1, y, y²}` basis;
  the MLE representation (`CMlPolynomialEval`, `eqPolynomial`) exists, sumcheck does not.
- **Clean**: surveyed at `93c9d1ef` on an extracted tree: `Clean/Utils/FiniteField`,
  `Clean/Circuit/{Channel,Formal,Operations,Lookup}`, all of `Clean/Air/`,
  `Clean/Examples/{FemtoCairo,FibonacciWithChannels}`, `Clean/Utils/OfflineMemory`. Exactly
  three declarations carry `[Fact (ringChar F ≠ 2)]` (`Balance.lean:259, 292, 551`) and the
  `Vm.lean` theorems inherit it; `exists_push_of_pull` and `consistent_of_normal` are
  degenerate without a marker; `BalancedInteractions` is unsatisfiable over `K` beyond one
  interaction. Core `Air`/`Table` files never consume `FiniteField.val`. The 22 commits since
  `1e0933cf` are the Lean 4.33.1 migration only. Open Clean work checked: PRs #446, #454 (by
  this repository's author), #415, #453; issues #452, #154.
- **Environment**: `lake update Clean` added only Clean to the manifest; `lake build` of
  `Clean.Utils.FiniteField`, `Clean.Circuit.{Formal,Channel,WitnessGeneration}`,
  `Clean.Air.{Balance,FlatComponent,FlatEnsemble,OrderedChannel,Vm}`,
  `Clean.Examples.FemtoCairo.FemtoCairo`, `Clean.Table.Inductive` took 2m44s;
  `./scripts/validate.sh` passes. `instance : FiniteField BF64` elaborates;
  `(@FiniteField.toField BF64 _ : Field BF64) = inferInstance` by `rfl`; `assertZero` and
  `Channel.push` typecheck over `BF64`. `#eval` on `BF64`/`Ext3` works. `decide +kernel` proves
  `g ^ ((2^64-1)/3) ≠ 1`, `g ^ ((2^64-1)/641) ≠ 1`, and `g ^ (2^64-1) = 1` in seconds each;
  plain `decide` exhausts `maxRecDepth`; `norm_num` proves `Nat.Prime 6700417`.
  `lake build CompPoly.Fields.Binary.BF64` was needed once because no first-party module
  imports it yet.
