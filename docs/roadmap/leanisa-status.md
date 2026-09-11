# Status: leanISA semantics and M3 constraints

This file records where the [leanISA roadmap](leanisa-blueprint.md) stands as of Layer 5
(PR #17, a draft on top of `main` at `4b95a60`, the review of Layers 0 to 4 merged 2026-09-10),
together with the finding that PR records against Clean's bus (C10, below) and the upstream
request it files ([#16](https://github.com/Verified-zkEVM/leanerVM/issues/16)). It is a
hand-maintained snapshot, rewritten whole when a layer lands or a decision is taken; the roadmap
is the authority on what is wanted, and the tracking issue
[#4](https://github.com/Verified-zkEVM/leanerVM/issues/4) mirrors the coverage table below.

## Where this roadmap stands

**At a glance.** Layers 0, 1, 2, 3 and 4 are landed and reviewed; Layer 5 is built, fully proved,
and held as a draft pull request (PR #17) until Clean's bus supports binary fields (C10,
[#16](https://github.com/Verified-zkEVM/leanerVM/issues/16)). `LeanerVM/Parameters/Field.lean`
and `LeanerVM/Parameters/Generator.lean` define `K`, `E`, `y`, `ofK`, `E.limb`, `E.ofLimbs`,
`IsInK`, `IsCanonical128`, `g`, and `gpow`, and prove `orderOf_g` and `gpow_injOn` from the seven
`decide +kernel` checks; Clean's `FiniteField K` instance is `instFiniteFieldK` in the plain file
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
and `BytecodeMsg` (`deriving ProvableStruct`) and makes Layer 3's `Regs`, now parametric in the
field, the state message (`deriving instance ProvableStruct for Regs`); the prover-data tables
`memDataName`, `bytecodeDataName` with their rows `memRows`, `bytecodeRows`, the readings
`imageOf` and `programOf`, and the shape `WellShapedData` under which they drop no row; the six
channels `StatePull` … `BytecodePush` (guarantees on the memory and bytecode pulls only); the
gadgets `memRead` and `bytecodeRead` (`Channel.pull` then `Channel.push`, the count advanced by
`g`); and the bus data `Direction`, `channelDir`, `channelSep`, `busTuple`. It proves the three
`toElements` lemmas, `busTuple_getElem`, `wellShapedData_iff`, `imageOf_apply`, and
`programOf_code`. `./scripts/validate.sh` is green, the
axiom closure of every declaration is `propext, Classical.choice, Quot.sound`, and the kernel axiom
audit is enabled in CI (`axiom-audit-root: LeanerVM`). Clean is consumed from plain files and the
aggregates are plain (finding C8, now the roadmap's module-system convention); kernel-`decide` over
`E` arithmetic works from plain files but not from `module`s (P1); a derived `DecidableEq` on a
`K`-valued structure does not decide in the kernel (E5, new with Layer 3); `lake test` builds the
test library because no executable may link the field module (P3). `Bytecode.lean` imports no
Clean and is a `module`; `Channels.lean` is the plain boundary the roadmap's module-system
convention places at the first Clean import.

### Roadmap coverage

| Layer | Status | Notes |
| --- | --- | --- |
| 0 — fields, limbs, generator | landed (PR #6) | `instFiniteFieldK` lives in the plain `CleanField.lean` (C8); `E` arithmetic not kernel-reducible from `module` files (P1) |
| 1 — BLAKE2s | landed (PR #7) | flags are 32-bit words, not `Bool` (decision 6); vectors kernel-checked from a `module` file (L1) |
| 2 — instructions, image, public input | landed (PR #8) | `gLog?` is noncomputable behind `gLog?_spec`, hypothesis `κ < 64`; `MemImage` is an `abbrev`; `Instr.opcode` added (see the frontier) |
| 3 — `step`, `ValidExecution` | landed (PR #11) | Category A, written from §2 first and diffed against `execute.rs` afterwards (no new divergence); `Regs` equality by hand (E5); fixtures in a plain test file (decision 4, settled); unchanged by F6, whose hypothesis sits on Layer 10; `Regs` made parametric in the field by PR #17 (`Regs K` the machine's pair, `Regs (Expression K)` a row's state message), the semantics otherwise untouched |
| 4 — bytecode encoding | landed (PR #9) | `decode` is exact (`decode_eq_some_iff`): a nonzero spare slot is no instruction; `derefFlags` added for Layer 6; a `module`, no Clean |
| 5 — channels | built and proved; draft PR #17, held until Clean's bus supports binary fields (C10) | plain file (C8); the state pull carries no guarantee (decision 7); each channel names its separator and direction, `busTuple` and the `toElements` lemmas (decision 8); gadgets emit through `Channel.pull`/`Channel.push`, never `emit` (C10); the image and program are read off `ProverData` by table name |
| 6 — six tables | untouched; consumes Clean | plain files (C8); row tests are kernel checks against `E.ofLimbs` words (E5) |
| 7 — boundary blocks | untouched; consumes Clean | plain files (C8) |
| 8 — statement | untouched; consumes Clean | plain files (C8); `Caps` requires power-of-two heights and the bytecode length (decision 8) |
| 9 — bus soundness | untouched; consumes a Clean change | statements land as block comments with Layer 8; `exists_run_of_balanced` and `no_row_at_sentinel` under `WellFormedBytecode` (decisions 7 and 9) |
| 10 — T1 | untouched; consumes Layer 9 | both theorems take `WellFormedBytecode prog` (decision 9, F6) |

### The frontier

- **Layer 5 is built as PR #17** (`feat(arithmetization): leanISA Layer 5: bus channels`), a
  draft. Its reading list is `LeanerVM/Arithmetization/Channels.lean`,
  `tests/LeanerVMTests/Arithmetization/Channels.lean`, and the roadmap's Layer 5 section, which
  shows the built shapes. Every Layer 5 target of the roadmap is present and proved; nothing in
  the layer is vacuous, and the tests state, as theorems, the three facts about Clean's bus over
  `K` that the roadmap's channel pairs work around (C10). The review of 2026-09-11 settled
  three further points, each written into the roadmap: the state message is Layer 3's `Regs`,
  made parametric in the field (`Regs K` the machine's pair, `Regs (Expression K)` a row's),
  rather than a second structure; the two prover-data tables have named accessors `memRows`
  and `bytecodeRows`; and the floor-logarithm normalisation of `imageOf`/`programOf`, which
  drops the rows of a table whose count is not a power of two, is made explicit as
  `WellShapedData`, the shape under which the two specifications `imageOf_apply` and
  `programOf_code` hold, to be a conjunct of Layer 8's `Caps`. `channelSep`/`channelDir` stay
  as they are, with the note that `Direction` and `channelDir` are deleted for Clean's
  direction tag once #16 is upstreamed. The roadmap's sketch was adjusted in five further
  places, each written into the roadmap:
  - `memRead` and `bytecodeRead` emit through `Channel.pull` and `Channel.push`, not
    `Channel.emit 1`: `emit` builds its interaction with `assumeGuarantees := false`
    (`Clean/Circuit/Basic.lean:124-127`), so a Layer 6 soundness proof could never assume the
    memory or bytecode guarantee of its own pull; `pull` sets the flag and multiplicity `-1`,
    which is `1` in `K` (`Basic.lean:130-133`), and `push` sets multiplicity `1`. Every
    interaction thus has multiplicity `1` and the direction is the channel (acceptance test 13).
  - The three `toElements` lemmas are stated on `(toElements m).toList`, the list form, since
    `toElements` returns a `Vector K (size M)` whose length is a `combinedSize'` term.
  - `BytecodePull.Guarantees` writes the entry as `#v[b.opcode] ++ b.op`; core's `Vector` has no
    `::ᵥ`.
  - `imageOf` and `programOf` are given bodies: the `"mem"` and `"bytecode"` tables of Clean's
    `ProverData` (`String → (n : ℕ) → Array (Vector F n)`), log-size the floor logarithm of the
    row count (`Nat.log 2`), `programOf` capped at `maxLogBytecode`; a missing word is `0` and a
    missing or undecodable instruction is `XOR 0 0 0`, whose first read is at address `0` and
    fails. `imageOf_apply` and `programOf_code` are their specifications under
    `WellShapedData`, and the two table names are interface declarations (`memDataName`,
    `bytecodeDataName`).
  - `channelSep` returns `0`, which is no separator (`gpow_ne_zero`), on a channel that is none
    of the six, and `channelDir` returns `.push` there; both read the channel's `name`.
  Held as a draft: the rule set for this layer is that a collision with Clean's characteristic-2
  bus keeps the work out of `main` until Clean supports binary fields
  ([#16](https://github.com/Verified-zkEVM/leanerVM/issues/16)); the collision is
  real in Clean's raw channels and balance (C10), though Layer 5's own statements do not
  depend on it.
- **Clean's bus over `K`, exhibited** (C10, 2026-09-10, with Layer 5). Three facts are now
  kernel-checked theorems in `tests/LeanerVMTests/Arithmetization/Channels.lean`: `(-1 : K) = 1`;
  `MemPull.toRaw.Guarantees 1 v data ↔ MemPull.Guarantees (fromElements v) data`, so
  `Channel.toRaw` grants the typed guarantee at the multiplicity of a push, and
  `MemPull.toRaw.Requirements m v data` holds for `m ∈ {0, 1}`, so every requirement of every
  interaction a component emits is vacuous; and `¬ BalancedInteractions (i :: j :: rest)` for
  any two interactions, since `ringChar K = 2`. Layer 5 is stated so as not to depend on any of
  the three; Layers 6 and 7 route push obligations through `Spec`, Layer 8 balances through
  `BalancedPair`, and Layer 9 is blocked on the Clean change of the roadmap's dependency table,
  now requested upstream through
  [#16](https://github.com/Verified-zkEVM/leanerVM/issues/16).
- **Layers 0 to 4 were reviewed on 2026-09-10** (the `leanerVM-review` skill's three passes on
  `main` at `2a84f9b`, every changed module read in full, the pinned sources read first for the
  Category B content). Specification pass: every theorem inhabited, every load-bearing condition
  with a negative test, one finding against the target (F6, below). Fidelity pass: the moduli and
  limb order, the generator, the six codes, the caps, the six rows of the §8.1 slot table, the
  three flag pairs, the BLAKE2s constants, mixing function, initial state and finalization, the
  cell and metadata encodings, and the two executor vectors all match the pin; the one declared
  deviation (flags as words) is licensed by `flock/src/hash.rs:206-214`. Hygiene pass: the Lean
  is clean; this file, issue #4, `README.md`, the scaffold `Basic.lean` docstrings and the
  roadmap's Layer 1 signatures were behind the merges and are updated with the review.
- **Layer 3** landed as PR #11 (`feat(semantics): leanISA Layer 3: step and valid executions`)
  on 2026-09-10. Its reading list is `LeanerVM/Semantics/Step.lean`,
  `LeanerVM/Semantics/Execution.lean`, `tests/LeanerVMTests/Semantics/Execution.lean`,
  `scripts/dump-mul-rust.sh`, and the roadmap's Layer 3 section, which shows the built shapes.
  The roadmap's sketch was adjusted in six places, each written into the roadmap:
  - `step` is `prog.fetch r.pc >>= execute L r`, with `execute L r : Instr → Option Regs` the
    six arms of §2's table, so that a fetched instruction's arm is the one-line rewrite
    `step_of_fetch_eq_some` (the sketch inlined the match). One semantics still: `execute` is
    the body of `step`, never called on its own by a specification.
  - The halting test is in `run`, not in `step`: `run (n + 1) r` is `none` when `r.pc` is the
    sentinel `Program.finalPc prog = g^(N_prog - 1)`, so `run n initial = some final` is the
    exact halting time with the sentinel never executed (`run_intermediate`), while a table row
    at the sentinel counter still has a `step` for its `Spec`.
  - `HasPublicBoundary` states the public words through `MemImage.read` at `g^0` and `g^1`
    rather than `t.image ⟨1, _⟩`, whose index proof needs the `κ ≥ 16` conjunct.
  - `BLAKE2S` reads its four message cells as four `let`s, not a `mapM`, so that `CompressCells`
    takes the literal `![m0, m1, m2, m3]`.
  - `Regs` has a hand-written `DecidableEq` (E5).
  - `Trace.regs` is the `filterMap` of `run` over `0 … steps`, with `Trace.regs_length` under
    the run hypothesis; the roadmap's `List Regs` type is kept.
- **Category A discipline for Layer 3.** `Step.lean` and `Execution.lean` were written from §2
  (and §6.1 for the final `fp`) starting from the roadmap's pinned sketch, before the executor
  was opened in this build; the sketch itself was Rust-informed when the roadmap was written
  (survey record). The executor (`execute.rs:540-584` loop head, `:584-831` arms) was then
  diffed arm by arm: no divergence beyond R1–R24. Confirmed in passing: the local cell of a
  `DEREF` in `pc` and `fp` modes is access-counted (`bump_access_count(a3)`) though its value
  is unused (S3, acceptance test 6); the `BLAKE2S` chaining-value and output pairs are read at
  `fp + o` and `fp + o + 1`, that is `fp · o` and `fp · (g · o)`; `JUMP` asserts `c, d, f ∈ K`
  on every row; `Program::from_bytecode` starts at exponents `(0, 0)` and its `main_frame`
  argument is prover bookkeeping only (R25).
- **Closed walks and the state pull** (F5, decision 7, issue
  [#10](https://github.com/Verified-zkEVM/leanerVM/issues/10), settled 2026-09-10). Specification
  Proposition 6.1 splits a balanced state channel into one walk from `(1, 1)` to the final
  state and closed walks, and §8.3 fills tables with closed walks "disjoint from the program's
  own run". The roadmap's former Layer 5 `StatePull.Guarantees` ("a pulled state is reachable")
  and Layer 9 `state_channel_sound` claimed more, and every padded honest witness refuted them.
  The roadmap now gives the state pull no guarantee and states Proposition 6.1 once, as
  `exists_run_of_balanced` (acceptance test 21).
- **A `JUMP` sentinel executes** (F6, decision 9, found by the review on 2026-09-10). The
  instruction tables place no condition on a row's `pc`, so a row may sit at the sentinel
  counter; every instruction but `JUMP` then pushes `(g^N_prog, fp)`, which no row can pull, but
  a `JUMP` sentinel pushes whatever its cells say. The two-slot program `[JUMP; JUMP]` whose
  first row jumps to `(g, g)` and whose sentinel row, read in frame `g`, jumps to `(g, 1)` has
  two rows that are `step`s and balance the state channel, while `run` halts at `(g, g)` for
  every step count (kernel-checked during the review). `constraintSoundness` as the roadmap
  stated it was therefore false, and so was the walk theorem proposed in #10. Both T1 theorems
  now take `WellFormedBytecode prog`, a structure whose `sentinelHalts` field excludes a `JUMP`
  sentinel and whose `hasFillBlocks` field is the former `HasFillBlocks` hypothesis; Layer 9
  gains `no_row_at_sentinel`. Layer 3 is unchanged: the semantics halts at the first arrival
  at the sentinel counter, as §2 and the executor do (`execute.rs:369`), and the compiled guest
  is well formed (`lean_compiler/src/lib.rs:162` pads the sentinel with `SET_CONSTANT`).
  Recorded in `docs/leanvm-target.md` as a durable discrepancy between the constraints and §2.
- **Bus data on the channels and power-of-two heights** (decision 8, issue
  [#13](https://github.com/Verified-zkEVM/leanerVM/issues/13), settled 2026-09-10). Layer 5's
  channels name their separator and direction (`channelSep`, `channelDir`) and their sixteen-slot
  tuple (`busTuple`), with the element order of the typed messages pinned by three `toElements`
  lemmas; Layer 8's `Caps` requires every table height to be a power of two and the bytecode
  length to be `2^logSize`. Both requests came from the proof-system roadmap (#12) so that it
  proves exactly `SatisfiedBy` and reads the bus off leanISA's channels.
- **Kernel-decided fixtures** are written in one shape: `step_of_fetch_eq_some` at the literal
  state, `show` the fetched arm, `simp only [execute, one_mul, read_lit L j, …]` to rewrite
  every read at a literal index, then `decide +kernel` on the residual closed term; runs peel
  `run_succ_of_ne` under `simp (disch := decide +kernel)`. The literal-index helpers
  `fetch_lit`, `fetch_one`, `read_lit`, `read_one`, `read_g`, and `ofK_eq_ofLimbs` live in the
  test file; Layer 6's row tests will want the same, at which point they can move to Layers 0
  and 2 as load-bearing lemmas.
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
- **Layer 4** landed as PR #9 (`feat(arithmetization): leanISA Layer 4 — bytecode encoding`).
  Every Layer 4 target of the roadmap is present; the roadmap's Layer 4 text records two things
  the build settled:
  - `decode` is exact (`decode_eq_some_iff : decode v = some i ↔ v = entry i`), so a nonzero
    spare slot is no instruction, not only the flag pair `(1, 1)` and an unknown opcode. The
    reason is completeness: every table's bytecode tuple carries literal zeros in its spare
    coordinates (R24), so no row can pull such an entry, and a semantics that fetched an
    instruction there would execute programs the constraints cannot.
  - `derefFlags : DerefMode → K × K` names the flag pair `(f_pc, f_fp)` of `isa.rs:69-78`, which
    Layer 6's `DEREF` table reads; `derefMode?` inverts it.
  The decoder reads coordinates and never compares whole vectors, so it needs no
  `DecidableEq (Vector K 8)` (L1): the tests decide `decode` on literal vectors and slot reads
  in the kernel from a `module` test file, and state vector equalities on word lists.
- **`gLog?` is noncomputable** (2026-09-09). Its index is `Classical.choose` of
  `∃ i : Fin (2^κ), a = gpow i`, so `MemImage.read`, `Program.fetch`, `execute`, `step`, and
  `run` are specifications that cannot be run, by construction rather than by cost; its body is
  still not exposed, so a `module` importer reasons through `gLog?_spec` (`MemImage.read`,
  `Program.fetch`, and their lemmas are exposed). It replaced a fuel-bounded scan of
  `g^0, g^1, …` that ran at about 50 µs per `K` multiplication (E4) and would have made every
  read of a running execution a discrete logarithm; the `mulG` fast-path idea went with it. The
  scan's two induction helpers became a `split_ifs` on the choice, and the failure side gained
  `gLog?_eq_none_iff` (no size bound) and `gLog?_gpow_eq_none` (a power past the end), which
  Layer 3's out-of-range tests use. For the back of the mind only, not planned: if a runnable
  machine is ever wanted, it is a computable carrier bridged to this specification in the
  CompPoly shape, with exponent-indexed state and a memoized reverse index `g^j ↦ j` as the
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
  equality is decided on its word list. The Layer 3 fixtures are therefore a plain test file
  (decision 4, settled), where the kernel sees every body; the Layer 6 per-table row tests can
  also use compiled evaluation (`#guard` under `meta import`).
- **Layer 6** can start on the draft: it needs Layer 5's channels and gadgets, consumes
  `step_of_fetch_eq_some` and the arms of `execute` for its `Spec`s, assumes the memory and
  bytecode guarantees through `Channel.pull`'s interactions, and must state every push
  obligation in `Spec`, since Clean's `Requirements` are vacuous over `K` (C10).
- **The Rust vectors.** Layer 1's (`blake2s_computes_the_compression`) is reproduced by
  `scripts/dump-blake2s-rust.sh`; Layer 3's (`mul_192bit_word`, `cpu/mod.rs:981-998`) by
  `scripts/dump-mul-rust.sh`, whose product CompPoly reproduces in the kernel
  (`mulX * mulY = mulXY`, acceptance test 9). The `BLAKE2S` step fixture reuses the Layer 1
  cells; they are copied into the Layer 3 test file because the Layer 1 test module does not
  export them.
- **Clean's bus** is the remaining external item for Layers 9–10. The contract is stated in the
  roadmap's dependency table; Clean [#452](https://github.com/Verified-zkEVM/clean/issues/452)
  covers only the side-condition half of the balance change, and the combined request (direction
  tag plus `ℕ`-counted multiset balance, with the kernel-checked exhibits of C10) is tracked here
  as [#16](https://github.com/Verified-zkEVM/leanerVM/issues/16), whose action is a
  pull request to Clean.
- **Clean PR [#446](https://github.com/Verified-zkEVM/clean/pull/446)** removes the three named
  hypotheses of Layer 8 when it lands; until then they stay in `SatisfiedBy`.

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
4. **Executable tests versus kernel `decide`** (P1, L1, E4, E5). Settled for Layer 3 on
   2026-09-10: its fixtures are proofs in the plain file
   `tests/LeanerVMTests/Semantics/Execution.lean` that peel `run` through `run_succ_of_ne`,
   rewrite each fetch and read through `Program.fetch_gpow` and `MemImage.read_gpow` at a
   literal index, and decide the residual closed term in the kernel; the whole module
   elaborates in about seven seconds. Open for Layer 6's row tests: the same shape, compiled
   `#guard`s under `meta import`, or a CompPoly pin bump making `Ext.ofFn` and
   `Ext.instDecidableEq` kernel-reducible under the module system (a literal-vector or
   `List.ofFn`-free construction, since the blocker is core's unexposed `Array.ofFn`; a
   list-comparing `DecidableEq E`, since core's `Vector` equality is unexposed too, and derived
   (E5)). Since `gLog?` is noncomputable, `ValidExecution` is neither kernel-decidable nor
   compilable at any `κ`.
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

## Open findings against the sources

Numbered for citation from pull requests and `docs/leanvm-target.md`. **S** = internal to the
specification document; **R** = Rust versus specification; **C** = Clean versus leanISA; **P** =
CompPoly versus leanISA; **L** = Lean core versus the roadmap's expectations; **E** = the Lean
environment; **F** = the roadmap's or the architecture's targets. The roadmap's acceptance
tests already encode the ones that bind a definition.

**Specification.** S1 halting is tested after execution in §2 but before the fetch in the Rust
and the bus (acceptance test 5; Layer 3's `run` tests before the fetch). S2 final `fp = g^0` is
required by §6.1 and the Rust, not by §2 (test 4; Layer 3's `Regs.final`). S3 `DEREF` reads
`fp·o3` unconditionally in §7.4, unstated in §2 (test 6; Layer 3's `deref` arm). S4 the
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
in the Layer 1 tests and by the Layer 3 step mutation). R12 metadata split confirmed (test 11).
R13 flag booleanity is not an AIR constraint (test 18). R14 halt asserts `fp = 0` (test 4). R15
step cap `10^8`. R16 the filler phase executes fill blocks after halt and can raise `κ_mem`
(test 15). R17 `g = 0x2` (test 1; Layer 0 `g`, certified). R18 `SET`'s immediate is one `F192`
(Layer 2 `setConstant (o : K) (k : E)`). R19 slot packing matches §8.1 (test 16; Layer 4's
`entry` and `encodeSlots` transcribe `layout.rs:229-290`). R20 `cpu/mod.rs` cites a stale
`.tex` filename. R21 the repository holds two BLAKE2s compressions:
`flock::hash::blake2s_compress` (two flag words; the opcode) and `primitives::hash::compress`
(last-block flag only; the byte hasher). Layer 1 transcribes the former. R22 the opcode's IV,
sigma, rotations and round count agree with RFC 7693 (`crates/primitives/src/hash.rs:19-62`),
so no leanVM-specific compression exists. R23 the verifier rejects a public input with a
nonzero top limb (`cpu/mod.rs:139-143`); Layer 2's `PublicInput` cannot express one, so the
check is a type, not a hypothesis. R24 a table's bytecode tuple passes five operand coordinates
(`tables.rs:486-491`, `:553-558`, `:636`, `:742-747`), seven for `BLAKE2S` (`:876-889`), and
relies on the bus's zero padding to `m = 16` slots (`05-arithmetization.tex:12`) to match the
seed's eight public columns (`layout.rs:385-395`); Layer 6 emits all seven explicitly, as the
roadmap's `XOR` template does, because Clean messages are typed, and Layer 4's `decode` rejects
a nonzero spare slot for the same reason. R25 `Program::from_bytecode(prog, main_frame)`
(`cpu/mod.rs:289-296`) starts at exponents `(0, 0)` and `main_frame` is a frame-allocation
hint for the prover, not part of the machine; the Layer 3 fixtures transcribe only `prog`.

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
list-comparing instance (as decision 4 already asks for L1) would remove it.

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
form (`ofK_eq_ofLimbs`) before the kernel compares it.

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
was false (decision 9, settled; roadmap acceptance test 20; `docs/leanvm-target.md`).

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
  seeding 173–177; `as_addr` 36–40. Tables `tables.rs:436-908`; `BLAKE2S` flushes 890–907 and
  addresses 373–386; `FlushBuilder` 126–183; `TOWER_LANES` 44–49; `jump_identity` 63–78;
  opcode constants 95–100. Caps `cpu/mod.rs:51-64`, checked in `read_public` at 158–166, with
  the third-limb rejection at 139–143. ISA `cpu/isa.rs:6-66`. `Program::from_bytecode`
  `cpu/mod.rs:289-296` (R25); executor tests `mul_192bit_word` `:981-998`, `blake2s_program`
  `:855-887`. Boundary blocks `layout.rs:355-395`; bytecode columns 229–290 (slot packing
  252–290) and the bytecode seed and finalize blocks 385–395; count blocks 410–412. Cell
  packing `hash_flock.rs:117-139, 162-185`; the compression `flock/src/hash.rs:191-231` with
  constants in `primitives/src/hash.rs:19-62`; `F192` limb order `c0, c1, c2` in
  `primitives/src/field/gf2_64x3.rs:34-47` (`E.ofLimbs` order). BLAKE2S floor: `filler.rs:43`
  (`MIN_ROWS`) and `crates/flock/src/hash.rs:283-286` (`min_n_blocks_log`, `max(8)`). No
  checked-in fixtures; no textual bytecode format. Smallest executor tests: `mul_192bit_word`
  (`cpu/mod.rs:985`), `blake2s_computes_the_compression` (`:893`),
  `blake2s_self_hash_aliased_operands` (`:938`), `blake2s_requires_zero_third_limb` (`:922`).
  The executor bodies were read while writing the roadmap and, for Layer 2, its seeding and
  address decoding were read before `Memory.lean` was written (recorded in its docstring);
  Layer 3 was authored from §2 first and the arms diffed afterwards (the frontier). Layer 0
  cites `gf2_64.rs:19-22` (bit encoding), `:28` (`F64::G`), and `python-verifier/verifier.py:177`
  (`E.__repr__`), `:182` (`GEN`).
- **CompPoly**: the working checkout `../CompPoly` (`40bac6e4`) is byte-identical to the pin on
  every field module. No generator, no order lemma, no `IsScalarTower`, no `{1, y, y²}` basis
  (Layer 0 adds `E.eq_sum_limbs`); no multiply-by-`x` lemma on `BF64` (a runnable carrier, if
  ever built, could use one); the MLE representation (`CMlPolynomialEval`, `eqPolynomial`)
  exists, sumcheck does not. Every CompPoly file is a `module` with `@[expose] public section`;
  P1 is inherited from core, not from CompPoly's own exposure. `Ext P` is a `def` over
  `Vector F P.d`; `Ext.ofVector`, `Ext.coeff`, `Ext.ext` and `Ext.coeff_ofFn` are the API
  Layer 0 wraps. `BF64`'s `Mul` is `reduce (carryLessMul …)` (`BF64/Impl.lean:70`) and its
  `Pow` is `npowBinRec` (`:169`), both kernel-evaluable on literals.
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
  a `Vector`-field message's
  `toElements` is rewritten to its append form with `change` and then `Vector.toList_append` by
  `rw` (a `simp` set does not fire on the `combinedSize'`-indexed appends); the channels are
  computable even though `MemPull.Guarantees` mentions the noncomputable `MemImage.read`, since a
  `Prop`-valued field is erased; a prover-data fixture that matches on table *names* exhausts
  the elaborator's `decide` on the string comparison, and so does unifying an indexed row with an
  `entry`, so the kernel-decided fixture matches on arity, the name-sensitive one is checked by
  `#guard`, and the decoded row is a `decide +kernel` fact.
  A git worktree has no `.lake/`; symlinking or copying `.lake/packages` from the main checkout
  reuses the built dependencies. On a fresh checkout `lake build --wfail` fails at
  `CompPoly:extraDep`: CompPoly's `preferReleaseBuild` finds no release tag at `3468b38c` and
  warns. CI and `validate.sh` therefore build without `--wfail` and with Lake's caches enabled,
  and CI fetches Mathlib's oleans with `lake exe cache get` before building; without them the
  job compiled Mathlib from source and hit its time limit (`docs/dependencies.md`).
