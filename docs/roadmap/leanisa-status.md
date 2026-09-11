# Status: leanISA semantics and M3 constraints

This file records where the [leanISA roadmap](leanisa-blueprint.md) stands as of Layer 6
(the branch `worktree-leanisa-task-6` on top of `main` at `849806e`, Layer 5 merged as PR #17
on 2026-09-11), together with the two findings that build records: the roadmap's bytecode
guarantee was too weak for the `DEREF` table (F7, below, a Layer 5 change) and core's `BitVec`
simprocs misread numerals of `K` (E6). It is a hand-maintained snapshot, rewritten whole when a
layer lands or a decision is taken; the roadmap is the authority on what is wanted, and the
tracking issue [#4](https://github.com/Verified-zkEVM/leanerVM/issues/4) mirrors the coverage
table below.

## Where this roadmap stands

**At a glance.** Layers 0 to 5 are landed and Layer 6 is built and fully proved on its branch,
awaiting its pull request. `LeanerVM/Parameters/Field.lean` and `LeanerVM/Parameters/Generator.lean`
define `K`, `E`, `y`, `ofK`, `E.limb`, `E.ofLimbs`, `IsInK`, `IsCanonical128`, `g`, and `gpow`,
and prove `orderOf_g` and `gpow_injOn` from the seven `decide +kernel` checks; Clean's
`FiniteField K` instance is `instFiniteFieldK` in the plain file
`LeanerVM/Parameters/CleanField.lean`. `LeanerVM/Parameters/Blake2s.lean` and
`LeanerVM/Semantics/Blake2s.lean` define `iv`, `sigma`, the two-flag `compress`, the cell encoding
(`cellWords`, `wordsCell`, `unpackMetadata`), and `CompressCells`, each pinned by kernel-checked
vectors from RFC 7693, from CPython's `hashlib.blake2s`, and from the pinned Rust executor.
`LeanerVM/Parameters/Isa.lean` defines `Opcode`, `Opcode.code` (`g^0 … g^5`), and the five caps;
`LeanerVM/Semantics/Memory.lean` defines `gLog?` (noncomputable, the index by `Classical.choose`),
`MemImage`, `MemImage.read`, and `PublicInput` with `word0`/`word1`, and proves `gLog?_spec`, the
one statement through which the bounded logarithm is trusted, with `gLog?_eq_none_iff` and
`gLog?_gpow_eq_none` on the failure side; `LeanerVM/Semantics/Instruction.lean` defines `DerefMode`,
`Instr`, `Instr.opcode`, `Program`, and `Program.fetch`. `LeanerVM/Semantics/Step.lean` defines
`Regs`, `Regs.next`, `derefSource`, `execute` (the six arms of specification §2's table) and `step =
fetch >>= execute`; `LeanerVM/Semantics/Execution.lean` defines `Regs.initial`, `Program.finalPc`,
`Regs.final`, `run` (the loop, with the halting test before each fetch), `Trace`,
`HasPublicBoundary`, `ValidExecution`, and `Trace.regs`, and proves `run_add`, `run_prefix`,
`run_intermediate` (no state before the last is at the sentinel) and `Trace.regs_length`; the plain
test file `tests/LeanerVMTests/Semantics/Execution.lean` proves the executor test `mul_192bit_word`
a `ValidExecution` and the executor's `BLAKE2S` row a step, rejects the wrong readings of acceptance
tests 2–7 and 12, and exhibits the `JUMP` sentinel of acceptance test 20.
`LeanerVM/Arithmetization/Bytecode.lean` defines `derefFlags`, the bus entry `entry`, the sixteen
slots `encodeSlots`, and the decoder `decode` (with `opcode?` and `derefMode?`), and proves
`decode_entry`, `decode_eq_some_iff` (the decoder is the exact inverse of the entry),
`entry_injective`, and `encodeSlots_getElem`. `LeanerVM/Arithmetization/Channels.lean`, the first
Clean-consuming production file and therefore plain, defines the two lookup messages `MemMsg`
and `BytecodeMsg` (`deriving ProvableStruct`) and makes Layer 3's `Regs`, parametric in the
field, the state message (`deriving instance ProvableStruct for Regs`); the prover-data tables
`memDataName`, `bytecodeDataName` with their rows `memRows`, `bytecodeRows`, the readings
`imageOf` and `programOf`, and the shape `WellShapedData` under which they drop no row; the six
channels `StatePull` … `BytecodePush` (guarantees on the memory and bytecode pulls only, the
bytecode guarantee naming the fetched instruction on both sides since Layer 6); the gadgets
`memRead` and `bytecodeRead` (`Channel.pull` then `Channel.push`, the count advanced by `g`); and
the bus data `Direction`, `channelDir`, `channelSep`, `busTuple`. It proves the three
`toElements` lemmas, `busTuple_getElem`, `wellShapedData_iff`, `imageOf_apply`, and
`programOf_code`. `LeanerVM/Arithmetization/Tables/{Xor,MulNative,SetConstant,Deref,Jump,Blake2s}.lean`
define the six rows `XorRow` … `Blake2sRow` (`deriving ProvableStruct`, columns in the Rust's
order) and the six tables `xorTable` … `blake2sTable`, each a `GeneralFormalCircuit K Row Regs`
whose `main` is the specification §7 entry and returns the state it pushes, whose `Spec` is
`step (programOf data) (imageOf data).2 ⟨pc, fp⟩ = some next`, and whose soundness and
completeness are proved; the named assumption `Blake2sRelation` (`CompressCells` on the row's
nine cells) is the `Assumptions` field of `blake2sTable`. They prove `add_limbs`, `mul_limbs`
(the twelve-product coordinates are the product in `E`), `storeCoords_eval` (the `DEREF` store
coordinates are `derefSource` at each flag setting), `flags_sound` and `flags_complete` (the two
`JUMP` residuals force the indicator), and the six `*_entry` lemmas tying each table's bytecode
tuple to Layer 4's `entry`. `./scripts/validate.sh` is green, the axiom closure of every
declaration is `propext, Classical.choice, Quot.sound`, and the kernel axiom audit is enabled in
CI (`axiom-audit-root: LeanerVM`). Clean is consumed from plain files and the aggregates are plain
(finding C8, now the roadmap's module-system convention); kernel-`decide` over `E` arithmetic
works from plain files but not from `module`s (P1); a derived `DecidableEq` on a `K`-valued
structure does not decide in the kernel (E5); core's `BitVec` simprocs fire on `K` numerals (E6,
new with Layer 6); `lake test` builds the test library because no executable may link the field
module (P3).

### Roadmap coverage

| Layer | Status | Notes |
| --- | --- | --- |
| 0 — fields, limbs, generator | landed (PR #6) | `instFiniteFieldK` lives in the plain `CleanField.lean` (C8); `E` arithmetic not kernel-reducible from `module` files (P1) |
| 1 — BLAKE2s | landed (PR #7) | flags are 32-bit words, not `Bool` (decision 6); vectors kernel-checked from a `module` file (L1) |
| 2 — instructions, image, public input | landed (PR #8) | `gLog?` is noncomputable behind `gLog?_spec`, hypothesis `κ < 64`; `MemImage` is an `abbrev`; `Instr.opcode` added (see the frontier) |
| 3 — `step`, `ValidExecution` | landed (PR #11) | Category A, written from §2 first and diffed against `execute.rs` afterwards (no new divergence); `Regs` equality by hand (E5); fixtures in a plain test file (decision 4); unchanged by F6, whose hypothesis sits on Layer 10; `Regs` made parametric in the field by PR #17 |
| 4 — bytecode encoding | landed (PR #9) | `decode` is exact (`decode_eq_some_iff`): a nonzero spare slot is no instruction; `derefFlags` added for Layer 6; a `module`, no Clean |
| 5 — channels | landed (PR #17) | plain file (C8); the state pull carries no guarantee (decision 7); each channel names its separator and direction, `busTuple` and the `toElements` lemmas (decision 8); gadgets emit through `Channel.pull`/`Channel.push`, never `emit` (C10); the image and program are read off `ProverData` by table name; `BytecodePull.Guarantees` strengthened by Layer 6 to name the fetched instruction on both sides (F7) |
| 6 — six tables | built and proved on `worktree-leanisa-task-6`; pull request pending | plain files (C8); each table returns the state it pushes (`GeneralFormalCircuit K Row Regs`) so that `Spec` reads `step … = some next` for `JUMP` too; push channels listed as `channelsWithRequirements`; `Blake2sRelation` is the one named assumption; row tests are kernel checks against `E.ofLimbs` words (decision 4, settled) |
| 7 — boundary blocks | untouched; consumes Clean | plain files (C8) |
| 8 — statement | untouched; consumes Clean | plain files (C8); `Caps` requires power-of-two heights and the bytecode length (decision 8) |
| 9 — bus soundness | untouched; consumes a Clean change | statements land as block comments with Layer 8; `exists_run_of_balanced` and `no_row_at_sentinel` under `WellFormedBytecode` (decisions 7 and 9) |
| 10 — T1 | untouched; consumes Layer 9 | both theorems take `WellFormedBytecode prog` (decision 9, F6) |

### The frontier

- **Layer 6 is built** on the branch `worktree-leanisa-task-6`. Its reading list is the six
  files under `LeanerVM/Arithmetization/Tables/`, `tests/LeanerVMTests/Arithmetization/Tables.lean`,
  the two-line change to `BytecodePull` in `LeanerVM/Arithmetization/Channels.lean`, and the
  roadmap's Layer 6 section, which shows the built shapes. Every Layer 6 target of the roadmap
  is present and proved. The roadmap's sketch was adjusted in four places, each written into the
  roadmap:
  - Each table is a `GeneralFormalCircuit K Row Regs`, not `… unit`: `main` returns the state
    it pushes and `Spec r next data` is `step … ⟨r.pc, r.fp⟩ = some next`. The `JUMP` successor
    `(b·v_pc + b·(g·pc) + g·pc, b·v_fp + b·fp + fp)` is a function of the witness `b`, which a
    `Spec` over the row cannot name; returning the pushed state makes the statement "the row's
    registers step exactly to the pushed state" uniform over the six tables, and Clean's
    `Air.Flat.Component` accepts any output type.
  - The bytecode guarantee names the instruction on both sides (F7, below): Layer 5's
    `BytecodePull.Guarantees` is now `∃ ins, fetch pc = some ins ∧ decode entry = some ins`.
  - `channelsWithRequirements` lists the three push channels: Clean's
    `RequirementsChannelsLawful` requires every channel a circuit interacts with to be in its
    guarantee list or its requirement list, and the push channels are in neither by default.
    Their requirements are vacuous (guarantee `True`); the obligation is `Spec`, as Layer 5
    says. The lawfulness proof is supplied by hand because Clean's default tactic dies on `K`
    (E6).
  - `ProverAssumptions` is the honest row in full: the fetched instruction with the row's
    operands (for `DEREF`, the mode whose flags the row carries) and every read, the derived
    result included, as the image's word; completeness discharges each pull's guarantee from
    it. `mul_limbs` is proved by the fold `y^3 = y + 1` (`ofLimbs_eq`, `linear_combination`
    against `y_pow_three`) rather than by `Ext.coeff_mul`: `E.limb` is an abbreviation, and
    CompPoly's `Ext.coeff_*` simp lemmas do not fire through it (they are usable as terms,
    `limb_add`, `limb_zero`).
  Tests: one prover data (a thirty-two-word image, an eight-slot program with one instruction
  per opcode) read through `imageOf_apply`/`programOf_code` at literal indices; per table the
  honest row's `ProverAssumptions` and `Spec` in the kernel, the `XOR` row pushed literally
  through `completeness` (`ConstraintsHold.Completeness` on the row's environment), the two
  honest `JUMP` witnesses checked against the residuals in the kernel, and one mutated row
  rejected through its pull guarantee or its residual. The `JUMP` row cannot be pushed through
  `completeness` the same way: its witness obligation is stated through Clean's witness-IR
  evaluator, which neither the kernel reduces nor `simp` normalises within budget. The `MUL_NATIVE` row reproduces the executor's product from the twelve
  coordinates (acceptance test 9).
- **Core's `BitVec` simprocs fire on `K`** (E6, 2026-09-11, with Layer 6). `K` is an `abbrev`
  for `BitVec 64`, so a numeral `(1 : K)` elaborates through `BitVec.instOfNat`, and core's
  simprocs treat `K` terms as bit vectors regardless of the instance: `simp` proves
  `(-1 : K) = 18446744073709551615#64`, which the kernel rejects (the field's `-1` is `1`), and
  this is exactly what Clean's default `requirementsChannelsLawful` tactic runs into through
  `Channel.toRaw_ext_iff`; a default `simp` also rewrites `0 : K` into a literal that lemmas
  stated with numerals (`isInK_ofLimbs`, `mul_one`) no longer match, while `simp only` with
  named lemmas does fire. The roadmap's conventions now carry the rule; the tables supply
  `requirementsChannelsLawful` with `-BitVec.reduceNeg` and use `simp only` throughout.
- **Layer 5 landed** as PR #17 on 2026-09-11. Its reading list is
  `LeanerVM/Arithmetization/Channels.lean`, `tests/LeanerVMTests/Arithmetization/Channels.lean`,
  and the roadmap's Layer 5 section. Nothing in the layer is vacuous, and the tests state, as
  theorems, the three facts about Clean's bus over `K` that the roadmap's channel pairs work
  around (C10). The review of 2026-09-11 settled three points, each written into the roadmap:
  the state message is Layer 3's `Regs`, made parametric in the field, rather than a second
  structure; the two prover-data tables have named accessors `memRows` and `bytecodeRows`; and
  the floor-logarithm normalisation of `imageOf`/`programOf` is explicit as `WellShapedData`, a
  conjunct of Layer 8's `Caps`. `channelSep`/`channelDir` stay, with the note that `Direction`
  and `channelDir` are deleted for Clean's direction tag once #16 is upstreamed. The sketch was
  adjusted in five further places, each in the roadmap: `memRead`/`bytecodeRead` emit through
  `Channel.pull` and `Channel.push`, not `Channel.emit 1` (`emit` never sets `assumeGuarantees`,
  `Clean/Circuit/Basic.lean:124-127`); the three `toElements` lemmas are stated on `.toList`;
  `BytecodePull.Guarantees` writes the entry as `#v[b.opcode] ++ b.op`; `imageOf` and
  `programOf` read the `"mem"` and `"bytecode"` tables of `ProverData` at the floor logarithm
  of the row count, capped; `channelSep` returns `0` and `channelDir` `.push` on a foreign
  channel.
- **Clean's bus over `K`, exhibited** (C10, 2026-09-10, with Layer 5). Three facts are
  kernel-checked theorems in `tests/LeanerVMTests/Arithmetization/Channels.lean`: `(-1 : K) = 1`;
  `MemPull.toRaw.Guarantees 1 v data ↔ MemPull.Guarantees (fromElements v) data`, so
  `Channel.toRaw` grants the typed guarantee at the multiplicity of a push, and
  `MemPull.toRaw.Requirements m v data` holds for `m ∈ {0, 1}`; and `¬ BalancedInteractions
  (i :: j :: rest)` for any two interactions, since `ringChar K = 2`. Layers 5 and 6 are stated
  so as not to depend on any of the three; Layer 8 balances through `BalancedPair`, and Layer 9
  is blocked on the Clean change of the roadmap's dependency table, requested upstream through
  [#16](https://github.com/Verified-zkEVM/leanerVM/issues/16).
- **Layers 0 to 4 were reviewed on 2026-09-10** (the `leanerVM-review` skill's three passes on
  `main` at `2a84f9b`, every changed module read in full, the pinned sources read first for the
  Category B content). Specification pass: every theorem inhabited, every load-bearing condition
  with a negative test, one finding against the target (F6, below). Fidelity pass: the moduli and
  limb order, the generator, the six codes, the caps, the six rows of the §8.1 slot table, the
  three flag pairs, the BLAKE2s constants, mixing function, initial state and finalization, the
  cell and metadata encodings, and the two executor vectors all match the pin; the one declared
  deviation (flags as words) is licensed by `flock/src/hash.rs:206-214`.
- **Layer 3** landed as PR #11 on 2026-09-10; its sketch was adjusted in six places, each in the
  roadmap: `step` is `prog.fetch r.pc >>= execute L r`; the halting test is in `run`, not in
  `step`; `HasPublicBoundary` states the public words through `MemImage.read`; `BLAKE2S` reads
  its four message cells as four `let`s; `Regs` has a hand-written `DecidableEq` (E5);
  `Trace.regs` is the `filterMap` of `run`. It was written from §2 first and diffed against the
  executor (`execute.rs:540-584`, `:584-831`) afterwards: no divergence beyond R1–R24.
- **Closed walks and the state pull** (F5, decision 7, issue
  [#10](https://github.com/Verified-zkEVM/leanerVM/issues/10), settled 2026-09-10): the state
  pull carries no guarantee and Proposition 6.1 is stated once, as `exists_run_of_balanced`.
- **A `JUMP` sentinel executes** (F6, decision 9, 2026-09-10): both T1 theorems take
  `WellFormedBytecode prog`; Layer 9 gains `no_row_at_sentinel`; Layer 3 is unchanged.
- **Bus data on the channels and power-of-two heights** (decision 8, issue
  [#13](https://github.com/Verified-zkEVM/leanerVM/issues/13), settled 2026-09-10).
- **Kernel-decided fixtures** are written in one shape: `step_of_fetch_eq_some (r := …)` at the
  literal state, `simp only [execute, one_mul, read lemmas …]` to rewrite every read at a
  literal index, then `decide +kernel` on the residual closed term; runs peel `run_succ_of_ne`.
  Layer 6's row tests use the same shape on prover data, through `readAt`/`read_lit`/`fetch_at`
  built on `imageOf_apply`, `programOf_code`, `MemImage.read_gpow` and `Program.fetch_gpow`;
  `r` is given explicitly, since leaving it implicit makes the elaborator unfold `gpow k`.
- **Layer 2** landed as PR #8 and **Layer 4** as PR #9; `gLog?` is noncomputable (2026-09-09),
  `gLog?_spec` takes `κ < 64`, `MemImage` is an `abbrev`, `Instr.opcode` was added; `decode` is
  exact and `derefFlags` names the flag pair (see the roadmap).
- **Clean is consumed from plain files** (C8, settled 2026-09-08): Lean `v4.33.1` rejects
  `import` of a non-`module` from a `module`, so the Clean-facing files and everything importing
  them are plain; Layers 5 to 10 are plain files.
- **CompPoly's `Ext` arithmetic does not reduce in the kernel from a `module` file** (P1), and
  neither does any `Vector` or `E` equality (L1); the Layer 3 and Layer 6 fixtures are plain
  test files (decision 4, settled).
- **Layer 7** can start on this branch: the boundary blocks reuse the six channels, the read
  gadgets, and the table template (`Tables/Xor.lean`), with `channelsWithRequirements` listing
  the channels they push on and the lawfulness proof supplied by hand (E6).
- **The Rust vectors.** Layer 1's (`blake2s_computes_the_compression`) is reproduced by
  `scripts/dump-blake2s-rust.sh`; Layer 3's and Layer 6's (`mul_192bit_word`,
  `cpu/mod.rs:981-998`) by `scripts/dump-mul-rust.sh`, whose product CompPoly reproduces in the
  kernel (`mulX * mulY = mulXY`, acceptance test 9), and which the `MUL_NATIVE` row reproduces
  from the twelve coordinates.
- **Clean's bus** is the remaining external item for Layers 9–10 (#16, whose action is a pull
  request to Clean; Clean [#452](https://github.com/Verified-zkEVM/clean/issues/452) covers
  half). **Clean PR [#446](https://github.com/Verified-zkEVM/clean/pull/446)** removes the three
  named hypotheses of Layer 8 when it lands.

## Decisions pending

Numbers are stable because the findings cite them; a settled item keeps its number and one
line.

1. Settled 2026-09-10 by the Layer 3 review: `DEREF` reads `fp·o3` in every mode (roadmap
   pinned convention, acceptance test 6; `execute`'s `deref` arm).
2. Settled 2026-09-10 with decision 9: both T1 theorems carry `WellFormedBytecode prog`
   (acceptance tests 15 and 20); `docs/architecture.md` states T1 for well-formed programs.
3. The bytecode interaction stays on the bus, transcribed like memory, rather than becoming a
   Clean `StaticTable` lookup, which would be characteristic-safe today but would change the
   constraint system the theorems are about.
4. Settled 2026-09-11 for Layer 6 (and 2026-09-10 for Layer 3): executable tests versus kernel
   `decide` (P1, L1, E4, E5). Fixtures are proofs in plain test files that rewrite each fetch
   and read at a literal index and decide the residual closed term in the kernel; Layer 6's
   row tests read the prover data through `imageOf_apply` and `programOf_code`. A CompPoly pin
   bump making `Ext.ofFn` and `Ext.instDecidableEq` kernel-reducible under the module system
   would let them move to `module` files. Since `gLog?` is noncomputable, `ValidExecution` is
   neither kernel-decidable nor compilable at any `κ`.
5. **Restoring a test executable** (P3). The library test driver is a workaround. If the
   roadmap's executable fixtures, the differential tests against the pinned Rust, or the native
   execution target need a real binary, CompPoly must first stop threading `[Fintype F]` through
   `Ext`'s runtime signature and make `Fintype BF64` noncomputable (P3, a pin bump), after which
   `tests/Main.lean` can be an executable again; linking it will additionally need native
   objects for the Mathlib closure, which the Mathlib cache does not ship.
6. Settled 2026-09-10: the roadmap's Layer 1 types the two finalization flags as `UInt32`
   words, as the built Layer 1 does (roadmap acceptance test 10 records why).
7. Settled 2026-09-10 (issue #10): the state pull carries no guarantee, and Layer 9 states
   Proposition 6.1 as `exists_run_of_balanced` (roadmap Layer 5, Layer 9, acceptance test 21).
8. Settled 2026-09-10 (issue #13): `Caps` requires power-of-two heights and the bytecode length;
   each Layer 5 channel names its separator, direction and sixteen-slot tuple.
9. Settled 2026-09-10 (F6): both T1 theorems take `WellFormedBytecode prog`, a structure with
   the fields `sentinelHalts` and `hasFillBlocks`; further program-shape conditions the Clean
   proofs need join it as fields (roadmap Layer 10, acceptance test 20).
10. Settled 2026-09-11 (Layer 6): the six tables return the state they push
    (`GeneralFormalCircuit K Row Regs`), so that every `Spec` is `step … = some next`, the
    `JUMP` successor being a function of its witness `b` (roadmap Layer 6).

## Open findings against the sources

Numbered for citation from pull requests and `docs/leanvm-target.md`. **S** = internal to the
specification document; **R** = Rust versus specification; **C** = Clean versus leanISA; **P** =
CompPoly versus leanISA; **L** = Lean core versus the roadmap's expectations; **E** = the Lean
environment; **F** = the roadmap's or the architecture's targets. The roadmap's acceptance
tests already encode the ones that bind a definition.

**Specification.** S1 halting is tested after execution in §2 but before the fetch in the Rust
and the bus (acceptance test 5; Layer 3's `run` tests before the fetch). S2 final `fp = g^0` is
required by §6.1 and the Rust, not by §2 (test 4; Layer 3's `Regs.final`). S3 `DEREF` reads
`fp·o3` unconditionally in §7.4, unstated in §2 (test 6; Layer 3's `deref` arm; Layer 6's
`derefTable` reads it unconditionally). S4 the generator value is not in the specification;
Layer 0 binds it to the Rust and the Python verifier. S5 `02-vm-specification.tex` line 75
annotates `o_3 ∈ K` where the cell value is meant. S6 §8.4 Fiat–Shamir is `TODO`. S7 §2 calls
`BLAKE2S` "the standard BLAKE2s compression" and names both flags in the metadata cell without
saying that the flag *words* enter the state unchanged (decision 6). S8 the BLAKE2S table floor
(`τ_BLAKE2S ≥ 3`) is enforced by the verifier (`cpu/mod.rs:166`) and the filler (`filler.rs:43`)
but appears in no section of the specification; Layer 2 binds `minLogRowsBlake2s` to the Rust
and to Flock's `min_n_blocks_log` (`crates/flock/src/hash.rs:283-286`). S9 §7.4 lists the
`DEREF` memory flushes as pointer, local, target while `tables.rs:645-650` emits pointer,
target, local; Layer 6 follows §7.4, the order of a row's interactions being immaterial to
balance.

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
in the Layer 1 tests, by the Layer 3 step mutation, and by the Layer 6 `BLAKE2S` mutated row).
R12 metadata split confirmed (test 11). R13 flag booleanity is not an AIR constraint (test 18;
Layer 6's `derefTable` has none). R14 halt asserts `fp = 0` (test 4). R15 step cap `10^8`. R16
the filler phase executes fill blocks after halt and can raise `κ_mem` (test 15). R17
`g = 0x2` (test 1; Layer 0 `g`, certified). R18 `SET`'s immediate is one `F192` (Layer 2
`setConstant (o : K) (k : E)`). R19 slot packing matches §8.1 (test 16; Layer 4's `entry` and
`encodeSlots` transcribe `layout.rs:229-290`). R20 `cpu/mod.rs` cites a stale `.tex` filename.
R21 the repository holds two BLAKE2s compressions: `flock::hash::blake2s_compress` (two flag
words; the opcode) and `primitives::hash::compress` (last-block flag only; the byte hasher).
Layer 1 transcribes the former. R22 the opcode's IV, sigma, rotations and round count agree with
RFC 7693 (`crates/primitives/src/hash.rs:19-62`), so no leanVM-specific compression exists. R23
the verifier rejects a public input with a nonzero top limb (`cpu/mod.rs:139-143`); Layer 2's
`PublicInput` cannot express one, so the check is a type, not a hypothesis. R24 a table's
bytecode tuple passes five operand coordinates (`tables.rs:486-491`, `:553-558`, `:636`,
`:742-747`), seven for `BLAKE2S` (`:876-889`), and relies on the bus's zero padding to `m = 16`
slots (`05-arithmetization.tex:12`) to match the seed's eight public columns
(`layout.rs:385-395`); Layer 6 emits all seven explicitly, because Clean messages are typed,
and Layer 4's `decode` rejects a nonzero spare slot for the same reason. R25
`Program::from_bytecode(prog, main_frame)` (`cpu/mod.rs:289-296`) starts at exponents `(0, 0)`
and `main_frame` is a frame-allocation hint for the prover, not part of the machine; the Layer 3
fixtures transcribe only `prog`. R26 the `JUMP` table commits `w` and `b` as columns
(`tables.rs:707-711`, "local witness columns"); Layer 6 has them as Clean `witness` operations,
local to the component, with the honest generators the Rust's batched inversion computes
(`tables.rs:781-806`).

**Clean** (`93c9d1ef`): C1 direction is the sign of the multiplicity (test 13). C2 balance is a
field sum with a characteristic side condition (test 14). C3 a component cannot see its row
index (Layer 8 hypothesis; PR #446). C4 `ProverData` is untied from committed columns (Layer 8
hypotheses; PR #446). C5 no degree bound on `Expression`. C6 no prover-chosen heights. C7 the
channel-based VM example (`FibonacciWithChannels.lean`) installs `Fact (ringChar F ≠ 2)`, and
`FemtoCairo` is `InductiveTable`-based with prime-field address arithmetic; both are proof-style
templates only. **C10 Clean's raw channels and balance are degenerate over `K`** (2026-09-10,
Layer 5): `Channel.toRaw` (`Clean/Circuit/Channel.lean:35-45`) grants `Guarantees` at `mult = -1`
and demands `Requirements` at `mult ∉ {-1, 0}`, and `Channel.emit` (`Clean/Circuit/Basic.lean:124`)
never sets `assumeGuarantees`; over `K`, `-1 = 1`, so a push-multiplicity interaction is granted
the guarantee and every requirement holds, and `BalancedInteractions` (`Clean/Air/Balance.lean:24`)
requires `length < ringChar F = 2`, and `Normal`, `Consistent`, and the VM-channel theorems
(`Balance.lean:193-260, 292, 551`; `Clean/Air/Vm.lean:703, 859`) carry `[Fact (ringChar F ≠ 2)]`.
Kernel-checked in `tests/LeanerVMTests/Arithmetization/Channels.lean`;
worked around by the channel pairs, `Channel.pull`/`Channel.push`, `Spec`-side push obligations,
and `BalancedPair`; removed by the Clean change of the roadmap's dependency table (#16).
C11 `RequirementsChannelsLawful` (`Clean/Circuit/Operations.lean:1145-1165`) requires every
channel a circuit interacts with to be in `channelsWithGuarantees` or
`channelsWithRequirements`; a push channel is in neither by default, so Layer 6 lists the three
push channels as requirement channels, and Clean's default proof of the field runs `simp` with
`Channel.toRaw_ext_iff`, which over `K` meets E6 and is replaced by a hand-supplied proof.
**C8 Clean does not use Lean's module system**: no file under `Clean/` is a
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
was built, OOM-killed on a 16 GB machine). **P4** `Ext`'s `DecidableEq` is the derived
`Vector` instance, so a kernel `E` equality has the E5 hazard: it decides only against a word
in `E.ofLimbs` form with literal limbs, or between syntactically identical terms. A
list-comparing instance (as decision 4 already asks for L1) would remove it. P5 `Ext.coeff_add`,
`Ext.coeff_mul`, `Ext.coeff_zero` are `simp` lemmas keyed on `Ext.coeff`, and leanISA's
`E.limb` is an `abbrev` of it, so they never fire on `E.limb` terms; Layer 6 states the needed
instances as terms (`limb_add`, `limb_zero`) and proves `mul_limbs` by the fold `y^3 = y + 1`.

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
`cases` split proves the same in two seconds and is what `Opcode.code_injective` uses; the same
overflow appears when a `rw` with `step_of_fetch_eq_some` is left to infer `r` from a goal at
`gpow k`, `k ≥ 2`, so the fixtures give `r` explicitly. **E2**
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
`g + 1` non-power check, the per-step kernel equalities of Layer 3 fixtures). **E5 a derived
`DecidableEq` on a structure over `K` does not decide in the kernel** (found with Layer 3,
2026-09-09). The derive handler decides the second field under `h ▸` for the first
(`if h : a = b then h ▸ if h : a₁ = b₁ then isTrue … else …`); reducing that `Eq.rec` is
K-like, so the kernel checks `a ≡ b` by definitional unfolding rather than by evaluating the
two values, and `decide +kernel` on `(⟨g * 1, 1⟩ : Regs) = ⟨g ^ 1, 1⟩` never returned (seven
minutes, 3 GB) while `⟨g * 1, 1⟩ = ⟨g, 1⟩`, `⟨g, 1⟩ = ⟨g ^ 1, 1⟩`, the bare `g * 1 = g ^ 1`, and
the same pair as a `Prod` each decide in under three seconds: with a literal on one side the
kernel evaluates the other. `Regs` therefore carries the hand-written instance
`decidable_of_iff (x.pc = y.pc ∧ x.fp = y.fp) …`. The hazard is inherited by anything whose
`DecidableEq` is derived, `Instr` (Layer 2, not kernel-compared anywhere yet) and CompPoly's
`Ext` (P4) included; the Layer 3 tests rewrite `derefSource`'s `ofK` word into `E.ofLimbs`
form (`ofK_eq_ofLimbs`) before the kernel compares it. **E6 core's `BitVec` simprocs fire on
numerals of `K`** (found with Layer 6, 2026-09-11). `K` is an `abbrev` for `BitVec 64`, a
numeral `(1 : K)` elaborates to `@OfNat.ofNat K 1 BitVec.instOfNat`, and core's simprocs match
`Neg.neg`, `OfNat.ofNat` and the arithmetic on any `BitVec 64` term whatever the instance: `by
simp` proves `(-1 : K) = 18446744073709551615#64`, rejected by the kernel since the field's
`-1` is `1`, which is what Clean's default `requirementsChannelsLawful` tactic runs into through
`Channel.toRaw_ext_iff` on every table over `K`; and a default `simp` rewrites `0 : K` into a
literal form that lemmas stated with numerals (`mul_one`, `isInK_ofLimbs`) no longer match,
while `simp only [mul_one]` does match. Layer 6 supplies the lawfulness proofs with
`-BitVec.reduceNeg`, uses `simp only` with named lemmas on every `K` goal, and the roadmap's
conventions carry the rule ("Numerals over `K`"). A numeral `2 : K` is the literal `x`, never
`1 + 1 = 0`, so characteristic-two facts go through `CharTwo.add_self_eq_zero`, never `ring`
with a `2`.

**Targets.** F1 constraint completeness as phrased in `docs/architecture.md` was false without a
program-shape hypothesis (test 15); since 2026-09-10 the architecture states T1 for well-formed
programs (decision 2). F2 the `2^64 - 1` read bound is derivable from the caps.
F3 the BLAKE2S value limbs are virtual columns in Flock's stack in the Rust; ordinary columns
here. F4 answered 2026-09-10: the count blocks are built from the tables' count columns only
(`layout.rs:412-414`), so the nonzero-count product does not cover the finalize counts, as §6.2
says ("Nothing checks the finalize counts"); `CountsNonzero` covers read pulls, as stated. F5
the roadmap's former state pull guarantee was stronger than Proposition 6.1 (2026-09-10, issue
[#10](https://github.com/Verified-zkEVM/leanerVM/issues/10)): it said every pulled state is
`run`-reachable from `(1, 1)`, but the proposition only splits a balanced channel into one walk
and closed walks, and §8.3's fill blocks are closed walks disjoint from the run, so every padded
honest witness refuted it (decision 7, settled). **F6 the constraints let a `JUMP` sentinel
execute** (2026-09-10, the review of Layers 0–4): §7 places no condition on a row's `pc`, so a
walk may pass through `(g^(N_prog - 1), fp)` with `fp ≠ 1` and continue through the sentinel
row to `(g^(N_prog - 1), 1)` exactly when the sentinel slot holds a `JUMP`, while §2 and the
executor never execute the sentinel; `constraintSoundness` without a program-shape hypothesis
was false (decision 9, settled; roadmap acceptance test 20; `docs/leanvm-target.md`). **F7 the
roadmap's bytecode guarantee was too weak for the `DEREF` table** (2026-09-11, Layer 6). Layer
5's `BytecodePull.Guarantees b data := fetch b.pc = decode entry` is satisfied by a counter that
fetches nothing paired with an entry that decodes to nothing, so a `DEREF` row at such a
counter with the flag pair `(1, 1)` satisfies every guarantee while `step` executes nothing,
and `derefTable`'s soundness (`Spec` = `step … = some next`) was false under it; the other five
tables were unaffected, their entries decoding unconditionally. The guarantee now names the
instruction on both sides, `∃ ins, fetch b.pc = some ins ∧ decode entry = some ins`, which is
what Theorem 6.4 gives Layer 9 from balance with the bytecode seed rows; the Layer 5 test file
gains the rejection of a `DEREF` tuple with the flag pair `(1, 1)` at the counter `0`.

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
  only nit); Proposition 6.1 and its proof are `06-bus-interactions.tex:9-31`, the closed-walk
  filling `08-end-to-end-protocol.tex:35-42` (F5). Executor loop head `execute.rs:540-584`
  (hints, g-power index growth, bytecode count bump, op load); arms `:584-831`; `BLAKE2S` arm
  779–812; filler loop 353–410; deferred `DEREF` 884–901; `κ_mem` 914–920; public-input
  seeding 173–177; `as_addr` 36–40. Tables `tables.rs:436-960`: `mod arith` 436–455 and
  `arith_result` 470–480 (`XOR`, `MUL`), `mod set` 532–543, `mod deref` 590–613 and
  `deref_store` 615–627, `mod jump` 690–712 with the batched inversion 781–806, `mod blake2st`
  846–882; `FlushBuilder` 126–183 (`memory_k` 172–174, `memory_128` 180–182); `TOWER_LANES`
  44–49; `jump_identity` 63–78; opcode constants 95–100. Caps `cpu/mod.rs:51-64`, checked in
  `read_public` at 158–166, with the third-limb rejection at 139–143. ISA `cpu/isa.rs:6-66`.
  `Program::from_bytecode` `cpu/mod.rs:289-296` (R25); executor tests `mul_192bit_word`
  `:981-998`, `blake2s_program` `:855-887`. Boundary blocks `layout.rs:355-395`; bytecode
  columns 229–290 (slot packing 252–290) and the bytecode seed and finalize blocks 385–395;
  count blocks 410–412. Cell packing `hash_flock.rs:117-139, 162-185`; the compression
  `flock/src/hash.rs:191-231` with constants in `primitives/src/hash.rs:19-62`; `F192` limb
  order `c0, c1, c2` in `primitives/src/field/gf2_64x3.rs:34-47` (`E.ofLimbs` order). BLAKE2S
  floor: `filler.rs:43` (`MIN_ROWS`) and `crates/flock/src/hash.rs:283-286` (`min_n_blocks_log`,
  `max(8)`). No checked-in fixtures; no textual bytecode format. Smallest executor tests:
  `mul_192bit_word` (`cpu/mod.rs:985`), `blake2s_computes_the_compression` (`:893`),
  `blake2s_self_hash_aliased_operands` (`:938`), `blake2s_requires_zero_third_limb` (`:922`).
  The executor bodies were read while writing the roadmap and, for Layer 2, its seeding and
  address decoding were read before `Memory.lean` was written (recorded in its docstring);
  Layer 3 was authored from §2 first and the arms diffed afterwards (the frontier). Layer 0
  cites `gf2_64.rs:19-22` (bit encoding), `:28` (`F64::G`), and `python-verifier/verifier.py:177`
  (`E.__repr__`), `:182` (`GEN`). Layer 6 transcribed §7 (`07-instruction-tables.tex:9-141`) and
  `tables.rs:436-960` side by side, column list, identities and flushes per table.
- **CompPoly**: the working checkout `../CompPoly` (`40bac6e4`) is byte-identical to the pin on
  every field module. No generator, no order lemma, no `IsScalarTower`, no `{1, y, y²}` basis
  (Layer 0 adds `E.eq_sum_limbs`); no multiply-by-`x` lemma on `BF64` (a runnable carrier, if
  ever built, could use one); the MLE representation (`CMlPolynomialEval`, `eqPolynomial`)
  exists, sumcheck does not. Every CompPoly file is a `module` with `@[expose] public section`;
  P1 is inherited from core, not from CompPoly's own exposure. `Ext P` is a `def` over
  `Vector F P.d`; `Ext.ofVector`, `Ext.coeff`, `Ext.ext` and `Ext.coeff_ofFn` are the API
  Layer 0 wraps; `Ext.coeff_add`, `Ext.coeff_mul` (a double sum over `monomialMod`) and
  `algebraMap K E = Ext.ofBase` by `rfl` are what Layer 6's limb lemmas use (P5). `BF64`'s `Mul`
  is `reduce (carryLessMul …)` (`BF64/Impl.lean:70`) and its `Pow` is `npowBinRec` (`:169`), both
  kernel-evaluable on literals; its `OfNat` is `BitVec.instOfNat` (E6).
- **Clean**: surveyed at `93c9d1ef` on an extracted tree: `Clean/Utils/FiniteField`,
  `Clean/Circuit/{Channel,Formal,Operations,Lookup,Basic,Explicit}`, all of `Clean/Air/`,
  `Clean/Examples/{FemtoCairo,FibonacciWithChannels}`, `Clean/Gadgets/IsZeroField`,
  `Clean/Utils/OfflineMemory`, `Clean/Utils/Tactics/CircuitProofStart`. Exactly
  three declarations carry `[Fact (ringChar F ≠ 2)]` (`Balance.lean:259, 292, 551`) and the
  `Vm.lean` theorems inherit it; `exists_push_of_pull` and `consistent_of_normal` are
  degenerate without a marker; `BalancedInteractions` is unsatisfiable over `K` beyond one
  interaction. Core `Air`/`Table` files never consume `FiniteField.val`. `Air.Flat.Component`
  wraps a `GeneralFormalCircuit F Input Output` with any `Output`; `Component.Spec` applies the
  circuit's `Spec` to the evaluated output (decision 10). `circuit_proof_start` introduces
  `i₀ env input_var input h_input h_assumptions h_holds` (soundness) and `h_env` (completeness)
  and normalises with `circuit_norm`; `Channel.pull` contributes its channel to the inferred
  `channelsWithGuarantees`, `Channel.push` nothing (C11); `witness` on a field takes a
  witness-IR `FExpr` (`.ite (x =? 0) 0 x⁻¹`, `IsZeroField.lean`). The 22 commits since
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
  Layer 3: the two production modules build in about a second each; the plain test module
  elaborates in about seven seconds, of which the kernel `E` product of `mul_192bit_word` and
  each of the two `BLAKE2S` step checks take about a second; a `K` product against a `K`
  power inside a hand-decided `Regs` equality takes under a second (E5). A hanging `lake
  build` prints nothing until the module finishes; bisecting a test file is done by running
  `lake env lean` on growing prefixes with a per-run timeout. Layer 4: the production module
  builds in about three seconds and the test module in two; `decode` on a literal vector and a
  slot read decide in the kernel from a `module` test file, since they touch only `K` equality
  and vector indexing (L1). Layer 5: the production file builds in about three seconds and the
  test file in two; `deriving ProvableStruct` needs `Clean.Utils.Tactics.ProvableStructDeriving`
  imported (it is not reached through `Clean.Circuit.Basic`), and `deriving instance
  ProvableStruct for Regs` derives it from a plain file for a structure declared in a `module`;
  a `Vector`-field message's `toElements` is rewritten to its append form with `change` and
  then `Vector.toList_append` by `rw` (a `simp` set does not fire on the `combinedSize'`-indexed
  appends); the channels are computable even though `MemPull.Guarantees` mentions the
  noncomputable `MemImage.read`, since a `Prop`-valued field is erased; a prover-data fixture
  that matches on table *names* exhausts the elaborator's `decide` on the string comparison,
  and so does unifying an indexed row with an `entry`, so the kernel-decided fixture matches on
  arity, the name-sensitive one is checked by `#guard`, and the decoded row is a `decide
  +kernel` fact. Layer 6: the six table files build in 10 s (`XOR`, `SET_CONSTANT`), 11 s
  (`MUL_NATIVE`), 12 s (`DEREF`), 17 s (`JUMP`) and 21 s (`BLAKE2S`), of which the
  `elaborate_circuit` derivation and the `circuit_proof_start` normalisation are the bulk; the
  test file elaborates in about a minute, its kernel work being the twelve-product check of
  acceptance test 9, the `BLAKE2S` compression of the honest row, and the `1⁻¹` of the `JUMP`
  witnesses. Field docstrings are not accepted inside a structure instance (`where` block); a
  `-` pattern in `obtain` on the conjuncts of `h_input` also cleared hypotheses obtained from
  `h_holds` beforehand, so the proofs keep them with `_`. A git worktree has no `.lake/`;
  symlinking or copying `.lake/packages` from the main checkout reuses the built dependencies.
  On a fresh checkout `lake build --wfail` fails at `CompPoly:extraDep`: CompPoly's
  `preferReleaseBuild` finds no release tag at `3468b38c` and warns. CI and `validate.sh`
  therefore build without `--wfail` and with Lake's caches enabled, and CI fetches Mathlib's
  oleans with `lake exe cache get` before building; without them the job compiled Mathlib from
  source and hit its time limit (`docs/dependencies.md`).
