# Review: faithfulness of the leanerVM Lean to the pinned leanVM

Reviewed on 2026-09-15 against leanerVM `main` at commit
`a999d0390a2ad7d59ba3eb106cda193868e65592` (`feat(arithmetization): leanISA Layer 6: the six
opcode tables (#19)`), read against leanVM at the pinned commit
`a386121f84292f6fa663aaa3e570c15bc0240ea2` (`docs/leanvm-target.md`). Both working trees were
clean at those commits. Clean was read at `93c9d1ef45be9f687214625d7857889cf2485504`, the
manifest pin. This is a fidelity review (pass B of the `adversarial-review` skill): the
question is whether the Lean models the same objects as leanVM and gives the same party control
over each value, not whether the Lean is internally consistent.

## Scope and evidence

Every first-party Lean file under `LeanerVM/` was read in full: `Parameters/{Basic, Field,
Generator, Isa, Blake2s, CleanField}.lean`, `Semantics/{Basic, Memory, Instruction, Blake2s, Step,
Execution}.lean`, `Arithmetization/{Basic, Bytecode, Channels}.lean`,
`Arithmetization/Tables/{Basic, Xor, MulNative, SetConstant, Deref, Jump, Blake2s}.lean`,
`Protocol/{Basic, Field}.lean` (24 files, 3953 lines). Tests under `tests/` were not re-verified;
they are evidence, not scope.

On the leanVM side the following were read in full: `doc/leanvm/body/02-vm-specification.tex`,
`05-arithmetization.tex`, `06-bus-interactions.tex`, `07-instruction-tables.tex`,
`08-end-to-end-protocol.tex`, `10-isa-programming.tex`; `crates/lean_vm/src/tables.rs`,
`cpu/layout.rs`, `cpu/execute.rs`, `cpu/mod.rs`, `cpu/isa.rs`, `cpu/filler.rs`, `cpu/trace.rs`;
`crates/lean_compiler/src/filler.rs` and `lib.rs:140-181`. Read in the cited ranges:
`crates/lean_vm/src/hash_flock.rs:1-200`, `leaf.rs:21-48` (the `Coord` type) and its evaluation
sites, `crates/flock/src/hash.rs:1-60, 119-136, 180-300`, `crates/primitives/src/hash.rs:1-140`,
`crates/primitives/src/field/gf2_64.rs:1-60`, `gf2_64x3.rs:1-120`, and
`python-verifier/verifier.py:520-600, 640-900, 1355-1439` as the cross-check. Clean:
`Circuit/Expression.lean` (`ProverData`, `Environment`), `Circuit/Channel.lean` (`toRaw`),
`Circuit/Basic.lean:100-150` (`pull`, `push`, `emit`), `Circuit/Formal.lean:310-360`
(`GeneralFormalCircuit`), `Circuit/Operations.lean:693-699` (`ConstraintsHold.Soundness`),
`Air/FlatComponent.lean:151-165` (`Table`), `Air/FlatEnsemble.lean:19-25` (`EnsembleWitness`).

The repository documents were read first: `docs/leanvm-target.md`, `docs/architecture.md`,
`docs/roadmap/leanisa-blueprint.md`, `docs/roadmap/leanisa-status.md`,
`.claude/skills/adversarial-review/references/faithfulness.md`,
`.claude/skills/lean-spec-authoring/references/sources.md`, `AGENTS.md`, `CONTRIBUTING.md`,
`docs/reviews/leanisa-layer6-tables.md`. The status file at `main` records findings S1 to S9,
R1 to R26, C1 to C11, P1 to P5, L1 to L3, E1 to E7 and F1 to F8; F9 and decision 12 are not
on `main` and are not cited here.

Layers 7 to 10 (boundary blocks, `SatisfiedBy`, bus soundness, T1) are not in the Lean at `main`.
Where the task asks about them (the index column, the three Layer 8 hypotheses,
`WellFormedBytecode`), the rows below cite the roadmap text and say so.

### Not checked, and why

- Flock's R1CS matrices, the ring switching, GKR, WHIR and the PCS: no Lean counterpart at
  `main`; they are the Protocol roadmap's (#12) and Flock's (#3), and the leanISA roadmap
  consumes only the compression relation (`leanisa-blueprint.md:83-94`).
- The compiler beyond the sentinel pad and `filler.rs`, the recursion guest, and the bodies of
  the ten hints (`cpu/hints.rs`): witness generation, recorded as R8 and out of scope.
- The Python verifier's WHIR, GKR and Flock code: only its layout, tables, flushes, caps and
  bytecode entry were cross-checked.
- The Layer 7 branch (`feat/leanisa-boundary`): concurrent work; only the roadmap text for
  Layers 7 to 10 was read. The verifier's `finalPc` coordinate on that branch is being changed
  and is mentioned only as context.
- No Lean was built or run. The review is static; the tests were not re-executed.

## The divergence table

Ranked most severe first. "Lean" and "leanVM" cite `file:line` at the two commits above;
`§` cites `doc/leanvm/body/`. "Justified?" names the license: a Clean limitation with its
tracker, a Category A choice with its recorded finding, or none.

| # | Lean | leanVM | Divergence | Meaning | Justified? | Resolution |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `Arithmetization/Channels.lean:161,167` (`bytecodeDataName`, `bytecodeRows`), `:181-184` (`programOf`), `:226-229` (`BytecodePull.Guarantees` over `programOf data`); `Tables/Xor.lean:183-184`, `MulNative.lean:155-156`, `SetConstant.lean:125-126`, `Deref.lean:185-186`, `Jump.lean:186-187`, `Tables/Blake2s.lean:217-218` (each `*Spec` over `programOf data`); Clean `Circuit/Expression.lean:21-22`, `Air/FlatEnsemble.lean:19-25` (`data` is a field of the witness) | `cpu/layout.rs:9-11, 225-229, 288-290` (the program is public, rides the seed and finalize blocks as `Coord::Public`), `:385-395`; `leaf.rs:36-39`; `06-bus-interactions.tex:93` ("The program is public, i.e. not committed") | The program is the `"bytecode"` table of Clean's `ProverData`, part of `EnsembleWitness`, so the prover supplies it; every table `Spec` and the bytecode pull guarantee are stated relative to it. leanVM never commits the program; the verifier evaluates it itself. | At `main` a table's `soundness` concludes "the row is a step of the program the prover named". Naming a different program changes the meaning of every `Spec`, and everything derived from the program (`Program.finalPc`, `logSize`) inherits that status. No theorem at `main` is false, but the exported contract is about a prover-controlled object where leanVM's is about a public one. The roadmap closes the gap only at Layer 8, by the conjunct `programOf w.data = prog` and the hypothesis `BytecodeRowsAreTheProgram` (`leanisa-blueprint.md:796, 809-810`). | Partly. A Clean limitation (finding C4, `ProverData` untied from anything public; Clean PR #446), recorded in the roadmap's dependency table and Layer 5 and 8 text. Not yet a wrong theorem; a weaker object than leanVM's until Layer 8 lands. | Make the program a parameter of the definitions Clean treats as public: `xorTable (prog : Program)` with `Spec := XorRefines prog (imageOf data).2` and `BytecodePull (prog : Program)` with `Guarantees` over `prog.fetch`; likewise for the other five tables. This needs no Clean change and removes `BytecodeRowsAreTheProgram`'s program half. Otherwise Clean #446. |
| 2 | `Channels.lean:158,164` (`memDataName`, `memRows`), `:173-175` (`imageOf`), `:212-214` (`MemPull.Guarantees` over `imageOf data`) | `cpu/layout.rs:12-15` (`MEM_LO/HI/TOP` committed columns), `:361-382` (the seed and finalize blocks read those same columns); `06-bus-interactions.tex:86` | The image the guarantee is stated against is a `ProverData` table, a second prover-supplied object beside the seed rows the bus will carry (roadmap `memTable`, `leanisa-blueprint.md:764-766`). leanVM has one object: the committed columns, read by both blocks. | The party is right (prover in both), the object count is not. An image and a seed table that disagree are both prover-chosen; a `Spec` over `imageOf data` says nothing about the bus rows until the hypothesis `SeedRowsAreTheImage` (`leanisa-blueprint.md:795, 809`) ties them. | Partly. C4, Clean #446, roadmap hypothesis recorded. | Clean #446 (proof-committed `ProverData`), or define the image from the `memTable` rows of the witness at Layer 7 and drop the `"mem"` table. |
| 3 | Roadmap only: `leanisa-blueprint.md:764-766` (`MemRow.idx` a row field), `:794` (`IndexColumnsAreRowIndices`). No Lean at `main`. | `cpu/layout.rs:365, 376, 388` (`Coord::Index`), `leaf.rs:34-35`, `06-bus-interactions.tex:95-100` (the verifier computes the index column's MLE) | A verifier-computed column becomes a prover-supplied row field under a named hypothesis. | Without the hypothesis a prover seeds address `g^j` at row `i`; with it the object is leanVM's. | Partly. C3 (a component cannot see its row index), Clean #446, recorded in the roadmap. Not code at `main`. | Clean #446 (indexed fixed columns), or a component parameterised by its row index. |
| 4 | `Channels.lean:184` (`programOf` maps an undecodable row to `.xor 0 0 0`); `Bytecode.lean:69-73` (`derefMode?` is `none` on `(1, 1)`), `:108-125` (`decode` rejects unknown codes and nonzero spare slots); `Semantics/Instruction.lean:47-51, 55-70` (three modes, six constructors) | `python-verifier/verifier.py:1365, 1429` (the public bytecode is any `Sequence[K]`), `cpu/layout.rs:315-316` ("the multilinear an outermost verifier is handed in place of a structured program"); `tables.rs:616-623` (`deref_store` is defined at every flag pair: at `(1, 1)` lane 0 is `v3₀ + g²·pc + fp`); `isa.rs:61-66` (the Rust `Op` has three modes) | Lean's machine is defined on `Program`, whose slots are decodable instructions. leanVM's verifier surface accepts any `K`-array as the public bytecode, and the constraint system gives an undecodable entry a definite meaning (a fourth `DEREF` mode, a `SET` with a nonzero spare slot, a non-opcode code). The Rust `Program`/compiler never produce one. | A leanVM proof about such bytecode is accepted and has no Lean counterpart: `BytecodeRowsAreTheProgram` would exclude the witness from `SatisfiedBy`, so T1 makes no false claim, but it is silent there. A coverage gap, not a soundness gap. | Partly. A Category A choice (§2:54-68, 71-79 define six instructions with three modes; acceptance test 18; R13). The wider verifier surface and the fourth-mode meaning are not recorded anywhere. | Record it in `leanisa-status.md` as a new R finding, and state in `docs/leanvm-target.md` that T1 covers decodable bytecode only (or add decodability to `WellFormedBytecode`'s prose). |
| 5 | `Channels.lean:241-251` (`memRead`, `bytecodeRead`: `Channel.pull` on the `*.pull` channel, `Channel.push` on the `*.push` channel), `:255-278` (`Direction`, `channelDir`, `channelSep`); roadmap `BalancedPair` `leanisa-blueprint.md:789-792`; Clean `Circuit/Channel.lean:35-43` (`toRaw` reads direction off `mult = -1`), `Circuit/Basic.lean:130-133, 142-145` | `tables.rs:104-165` (one bus, `push` and `pull` lists per table), `05-arithmetization.tex:12-16` (one bus, tuples of 16, balance as multiset equality), `:20-37` (grand product with soundness error `4·2^μ/\|E\|`) | Six channels for three interactions, direction as data, multiplicity `1` on every interaction (since `-1 = 1` in `K`), balance per pair as `List.Perm`. leanVM has one bus with signed sides and proves balance by a fingerprinted grand product. | The wrong reading, Clean's sign convention over `K`, would grant every push its own guarantee and make every requirement vacuous (acceptance tests 13, 14). The pair construction models the same three multisets of sixteen-slot tuples (`busTuple`, `channelSep`); the product argument's error is the Protocol layer's. | Yes. C1, C2, C10, C11 recorded and kernel-checked in the Layer 5 tests; issue #16 and Clean #452 track the upstream fix. | Clean direction tag and `ℕ`-counted balance (#16), then delete `Direction` and `channelDir`. |
| 6 | Roadmap `leanisa-blueprint.md:869-878` (`WellFormedBytecode`: `sentinelHalts`, `hasFillBlocks`), `:880-883`; `docs/architecture.md:216-223`; `Semantics/Execution.lean:64-66, 76-78` (`run` never executes the sentinel) | `07-instruction-tables.tex` places no condition on a row's `pc` (whole section); `02-vm-specification.tex:34` and `execute.rs:361-369` never execute the sentinel; `lean_compiler/src/lib.rs:162` pads the sentinel with `SET`; `cpu/filler.rs:38-43`, `lean_compiler/src/filler.rs:26-47` (fill blocks) | Lean states both T1 theorems for well-formed programs; leanVM's verifier checks neither property. The constraints accept a walk through a `JUMP` sentinel that §2 and the executor never take (F6); a program without fill blocks has no satisfying witness (F1, acceptance test 15). | For a `JUMP`-sentinel program leanVM accepts proofs that correspond to no §2 execution. This is a leanVM finding surfaced by the Lean, not a Lean error; the hypothesis restricts T1 to the programs the compiler emits. | Yes. F1, F6, decision 9, acceptance tests 15 and 20; `docs/leanvm-target.md` records it. | None needed in Lean. Upstream: constrain the sentinel slot or have the verifier check it. |
| 7 | `Tables/Blake2s.lean:85-137` (eighteen limb columns), `:141-143` (`Blake2sRelation`), `:249` (`Assumptions r _ := Blake2sRelation r`) | `tables.rs:388-422` (`BLAKE2S_VALUE_COLS` are virtual, never committed), `cpu/layout.rs:160-168`, `cpu/mod.rs:443-453, 790-814` (their bus claims route to `q_flock` slots), `07-instruction-tables.tex:118-120` | Lean has eighteen ordinary row columns and assumes the compression relation on them. leanVM has no such columns: the bus coordinates are the Flock witness words, and Flock proves the relation. | `blake2sTable.soundness` is conditional on the assumption; the composed leanVM claim (row limbs are Flock words, Flock relation holds) is exactly that assumption. Binding is proved here, compression is not (`blake2sRow_complete`, `Tables/Blake2s.lean:288-296`). | Yes. F3 recorded; the boundary with #3 is stated in the docstring and as a theorem. | None needed at this layer; #3 discharges `Blake2sRelation`. |
| 8 | `Semantics/Step.lean:130-135` (`JUMP` successor `⟨d.limb 0, f.limb 0⟩` for any `K` words) | `execute.rs:773-774` (`g.log(d).expect("JUMP target not a g-power")`, same for `fp`); `02-vm-specification.tex:86` (no g-power condition) | The executor panics on a taken jump whose target or frame is not a small g-power; Lean sets the registers and the next fetch or read fails. | Same accepted set of executions up to one step; the executor is stricter than §2. | Yes. R9; Category A, §2 is the standard. | None needed. |
| 9 | `Step.lean:123-129` (`DEREF`: `IsInK p`, read at `p.limb 0 * o2`) | `execute.rs:647-675` (the pointer must be a g-power already indexed or below `2^16`) | The executor panics on a pointer that is not a small g-power; Lean's read at a non-address fails. | Same as row 8. | Yes. R10. | None needed. |
| 10 | `Semantics/Blake2s.lean:148-153` (`CompressCells`: all nine cells canonical) | `execute.rs:787-799` (the seven read cells are checked, outputs constructed canonical); `tables.rs:896-907` (`memory_128` puts a literal `0` top limb on all nine reads) | The executor checks seven cells; the constraints force nine; Lean follows the constraints. | An image whose output cell has a nonzero top limb cannot balance the bus and is not a `step`; the executor never produces one. | Yes. R11, acceptance test 12. | None needed. |
| 11 | `Step.lean:126` (`DEREF` reads the local cell `fp·o₃` in every mode) | `execute.rs:679-717` (the local value is read only in `Cell` mode), `:734` (its count is bumped in every mode); `07-instruction-tables.tex:87` (unconditional local read); `02-vm-specification.tex:71-81` (silent) | §2 is silent, §7.4 reads it unconditionally, the executor reads its value only in `Cell` mode but reads it on the bus in every mode. Lean follows §7.4. | A `pc`- or `fp`-mode `DEREF` with an out-of-range local address is rejected by Lean and by the bus, accepted by a reading of §2 alone. | Yes. S3, decision 1, acceptance test 6. | None needed; an S finding for the specification. |
| 12 | `Execution.lean:76-78` (`run` tests for the sentinel before the fetch), `:70` (`Regs.final` has `fp = 1`) | `02-vm-specification.tex:34` (the test follows the execute step; no `fp` condition); `execute.rs:361-369` (tested before the fetch, `fp` asserted `0`); `06-bus-interactions.tex:8` (the boundary pull is `(g^(N-1), g^0)`) | Halting order and the final frame pointer: Lean and the executor agree; §2 differs on both. | The program with `N = 1` has the empty execution (acceptance test 5); a run reaching the sentinel with `fp ≠ 1` is invalid (test 4). | Yes. S1, S2, R14. | None needed; S findings for the specification. |
| 13 | `Semantics/Memory.lean:77-81` (a total image, one `read`); `Semantics/Instruction.lean:55-70` (operands are `K` elements) | `execute.rs:12-34, 261-297` (write-once cells, unset cells read as zero), `:602-609` (`MUL` back-solving), `:679-717, 884-901` (`DEREF` fill and deferral), `:418-567` (hints), `:411` (step cap `10^8`), `:183` (registers as `u32` exponents), `:253-260, 916-919` (growth, padding), `:361-407` (filler phase) | The executor's witness-generation behaviour has no counterpart in `step`; all nondeterminism is the image. | One semantics (acceptance test 19); these behaviours produce an image, they do not define the machine. | Yes. R1 to R8, R15, R16, R25. | None needed. |
| 14 | `Execution.lean:100-101` (`ValidExecution` accepts any image) | `cpu/mod.rs:536-542` (`prove` panics if the run read a cell nothing wrote, below the fill base), `execute.rs:909-912` (`unconstrained_reads`) | The Rust prover refuses to prove an execution that reads a never-written program cell. Lean has no such condition. | Prover-side only; the verifier accepts such proofs, so the Lean's accepted set is the verifier's. It extends R3 ("reads as zero with a diagnostic") to a hard refusal on the proving path. | Partly. The semantics is right (Category A, the verifier is the standard); the prover-side refusal is not recorded in the status file. | Add it to R3 in `leanisa-status.md`. |
| 15 | `Semantics/Blake2s.lean:44-51` (declared deviation: flags as `UInt32` words), `:93-98, 105-110` | `crates/flock/src/hash.rs:206-214` (`f0`, `f1` XORed in as words), `:50-51` (both flags free 32-bit inputs of the R1CS); RFC 7693 §3.2 (one Boolean flag) | Two 32-bit flag words where the RFC has one Boolean. | A metadata cell with a flag word other than `0` or `0xFFFFFFFF` satisfies the constraints; a Boolean type would reject it. | Yes. Decision 6, acceptance test 10; the stated license holds at the pin (lines 212-213 XOR the words unchanged). | None needed. |
| 16 | `Tables/Jump.lean:198-199` (`w`, `b` as Clean `witness` operations) | `tables.rs:706-711` (`W`, `B` committed columns, "never flushed"), `:783-806` (batched inversion) | Local witnesses instead of committed columns. | Both are prover-supplied; Clean soundness quantifies over every environment (`Circuit/Formal.lean:332`). The column count differs by two (14 vs 12 + 2 witnesses). | Yes. R26. | None needed. |
| 17 | `Tables/Xor.lean:196`, `MulNative.lean:168-169`, `SetConstant.lean:138-139`, `Deref.lean:201-202`, `Jump.lean:207` (seven operand coordinates, spare ones literal `0`) | `tables.rs:486-491, 553-558, 636, 742-747` (five operand coordinates), `:876-889` (seven for `BLAKE2S`); `05-arithmetization.tex:12` (zero-padding to 16) | Explicit zeros where leanVM relies on the bus padding. | The same sixteen-slot tuple. | Yes. R24. | None needed. |
| 18 | `Tables/Deref.lean:203-207` (reads: pointer, local, target) | `tables.rs:640-642` and `verifier.py:779-781` (pointer, target, local); `07-instruction-tables.tex:86-88` (pointer, local, target) | Flush order differs between the specification and both implementations; Lean follows the specification. | Immaterial to multiset balance. | Yes. S9. Note the Python verifier follows the Rust, so the specification is the odd one out. | None needed; an S finding. |
| 19 | `Channels.lean:173-184` (`imageOf`, `programOf` take the floor logarithm, capped), `:191-195` (`WellShapedData`) | `cpu/mod.rs:157-160` (`bytecode_size.is_power_of_two()`, `MIN_LOG_MEM ≤ log_mem ≤ MAX_LOG_MEM`); `verifier.py:856-864` | A store whose row count is not a power of two within its cap is silently truncated in Lean; leanVM rejects the announcement. | Only under `WellShapedData`, a conjunct of Layer 8's `Caps`, does `imageOf`/`programOf` drop nothing; the docstring records the truncation ("Wrong readings excluded", `Channels.lean:101-103`). | Yes. Decision 8; the shape is named and required where the caps are. | None needed. |
| 20 | Line citations: `Tables/SetConstant.lean:18-19` (`tables.rs:532-543`, `:553-566`), `Tables/Deref.lean:19-20` (`:590-613`, `:637-650`), `Tables/Blake2s.lean:19-20` (`:846-882`, `:889-921`), `Tables/Xor.lean:18-20` (`:487-500`, `:470-476`), `Tables/MulNative.lean:20` (`:478-480`), `Tables/Jump.lean:20` (`:63-78`), `Bytecode.lean:28` (`isa.rs:58-79`), `Step.lean:19` (`02:90-96`); `leanisa-status.md:591-594` repeats them | At the pin: `mod set` is `tables.rs:527-538`, `SetTable::flushes` `:548-561`; `mod deref` `:586-609`, `DerefTable::flushes` `:633-643`; `mod blake2st` `:833-863`, `Blake2sTable::flushes` `:873-908`; `Arith::flushes` `:483-495`, `arith_result` `:461-473`; `jump_identity` `:70-74`; `isa.rs` has 75 lines; `02-vm-specification.tex` has 95 | Cited line ranges drift by up to 16 lines from the pin; the named functions are the right ones. | A reader following a citation lands in the wrong function; the content compared was still the right function. | No. Pass B1 counts a drifting citation as a finding on its own. Low severity. | Refresh the ranges in the six table docstrings, `Bytecode.lean`, `Step.lean`, and the status survey record. |
| 21 | Nothing at `main`: `Caps`, `CountsNonzero`, balance, `SatisfiedBy` are roadmap Layer 8 (`leanisa-blueprint.md:797-811`) | `cpu/mod.rs:130-178` (`read_public`: caps, `BLAKE2S` floor, PCS `mu` window `:174`, `log_inv_rate` `:167`), `:82-93` (`fs_seed` binds the program hash and the R1CS digest), `:745-755` (public-input line), `:765` (Flock), `verifier.py:546` (`count_root ≠ 0`); `08-end-to-end-protocol.tex:55, 69-70, 100` | leanVM's verifier checks these; the Lean at `main` states none of them. | The leanISA roadmap states the relation the proof system proves (`SatisfiedBy`), and leaves Fiat-Shamir, the PCS window, the rate and Flock to the Protocol roadmap (#12) and #3. | Yes. Scope boundary, `leanisa-blueprint.md:83-94`; `Caps`, `CountsNonzero` and balance are Layer 8 targets. | Land Layer 8; the rest is #12 and #3. |

## Per-artifact fidelity counts

Columns: Rust `n_committed_columns` against the fields of the Lean row structure, in order.
Constraints: Rust `n_constraints` against `assertZero` calls in `main`. Flushes: Rust
push/pull pairs against Lean pull/push pairs; a `memRead`/`bytecodeRead` is one pair, the state
pull and push one pair. Coordinates were compared one by one.

| Artifact | Columns Rust / Lean | Constraints Rust / Lean | Flush pairs Rust / Lean | Coordinates | Source |
| --- | --- | --- | --- | --- | --- |
| `XOR` | 15 / 15 (`XorRow`, `Tables/Xor.lean:106-129`) | 0 / 0 | 5 / 5 | all matched; bytecode 5 + padding vs 7 explicit (row 17) | `tables.rs:436-495`; §7.1 |
| `MUL_NATIVE` | 15 / 15 (`MulRow`, `MulNative.lean:78-101`) | 0 / 0 | 5 / 5 | all matched; the three lanes are `TOWER_LANES` (`tables.rs:45-49`) term by term (`MulNative.lean:173-177`) | `tables.rs:436-495, 461-473`; §7.2:36-49 |
| `SET_CONSTANT` | 8 / 8 (`SetRow`, `SetConstant.lean:63-76`) | 0 / 0 | 3 / 3 | all matched | `tables.rs:527-561`; §7.3 |
| `DEREF` | 15 / 15 (`DerefRow`, `Deref.lean:82-109`) | 0 / 0 (no flag booleanity on either side) | 5 / 5 | all matched; store lanes `(1 + f_pc + f_fp)·v₃ + f_pc·g²·pc + f_fp·fp, …` equal `deref_store` (`tables.rs:616-623`) term by term; `Prod(FPC, PC, 2)` is `g²·f_pc·pc` (`leaf.rs:29-33`); read order differs (row 18) | `tables.rs:586-643`; §7.4 |
| `JUMP` | 14 / 12 + 2 local witnesses (`JumpRow`, `Jump.lean:89-114`, `:198-199`) | 2 / 2 (`b + c·w`, `c·(b + 1)`: `tables.rs:70-74`, `Jump.lean:200-201`) | 5 / 5 | all matched; successor `b·v_pc + g·b·pc + g·pc`, `b·v_fp + b·fp + fp` (`tables.rs:736-741`, `Jump.lean:202-204`) | `tables.rs:688-751`; §7.5 |
| `BLAKE2S` | 37 / 37 (`Blake2sRow`, `Tables/Blake2s.lean:85-137`; 18 limb columns in the Rust order m0..m3, out0, out1, cv0, cv1, md) | 0 / 0 | 11 / 11 | all matched; `Prod(FP, O_CV, 1)` is `g·fp·o_cv` = `fp * (g * ocv)`; top limb literal `0` on all nine | `tables.rs:833-908`; §7.6 |
| Count columns (Layer 8 `CountsNonzero`) | 4+4+2+4+4+10 = 28 / 28 count fields | | | | `tables.rs:479-481, 544-546, 629-631, 718-720, 869-871`; `layout.rs:412-414` |
| Boundary blocks (Layer 7, not at `main`) | state push/pull 1 each; memory seed/finalize `2^κ`; bytecode seed/finalize `2^κ_bc` | | | roadmap shapes `leanisa-blueprint.md:764-771` match `layout.rs:354-395` coordinate by coordinate | |
| Bytecode entry | 8 public columns / `entry : Vector K 8` (`Bytecode.lean:79-86`) | | | six slot rows of §8.1:16-21 matched; `SET`'s `k₂` at slot 7 (`layout.rs:270`), `BLAKE2S` at slots 4-10 (`:262, 269, 275, 281, 285`) | |
| Semantics | six arms of `execute` (`Step.lean:106-147`) against §2:54-68, 71-81, 86, 90-93 and `execute.rs:585-831` | | | divergences from the executor all recorded (rows 8 to 14) | |
| BLAKE2s constants and encoding | `iv` 8 words, `sigma` 10×16, 8 `G` lanes, rotations 16/12/8/7, 10 rounds, `initialState` (`v[12..15]` XOR `t_lo, t_hi, f0, f1`), finalization `h ^ v ^ v[+8]`; `cellWords`, `wordsCell`, `unpackMetadata`, `messageWords` | | | all matched against `primitives/hash.rs:20-62`, `flock/hash.rs:192-228`, `hash_flock.rs:119-139, 163-185`, `execute.rs:800-812` | |
| Field, generator, caps, codes, separators | `K`, `E`, limb order, `y`; `g = 2` with a seven-prime order certificate; caps 16/32/32/32/3; codes `g^0..g^5`; separators `g^0, g^1, g^2` | | | all matched (`gf2_64.rs:2-3, 19-28`, `gf2_64x3.rs:1-6, 34-44`, `cpu/mod.rs:51-64, 166`, `filler.rs:43`, `flock/hash.rs:283-286`, `tables.rs:90-100`, `verifier.py:182, 679-681, 821`) | |

## Unjustified or under-justified

Rows whose "Justified?" is No or Partly, in the recommended order of fixes.

1. Row 1 (program in `ProverData`). The highest-value fix and the cheapest: parameterise the six
   tables and `BytecodePull` by `prog : Program`. This puts the program where Clean already
   treats data as public (a definition's parameters) and matches `layout.rs:288-290` and §6.4
   without waiting on Clean #446. Do it before Layer 8 so that `SatisfiedBy` needs neither
   `programOf w.data = prog` nor the program half of `BytecodeRowsAreTheProgram`.
   *Resolution taken (2026-09-16, decision 14 in `leanisa-status.md`):* the parameter was
   built and discarded as unfaithful to leanVM's layering (an AIR is fixed for all programs)
   and as buying no soundness; the channels and tables are program-free, the bytecode
   guarantee is static decodability, and `SatisfiedBy prog`'s conjunct
   `BytecodeRowsAreTheProgram prog` pins the block's rows to the program, Clean #446's fixed
   columns by hand.
2. Row 4 (undecodable public bytecode). Record the wider verifier surface and the fourth
   `DEREF` mode as an R finding in `leanisa-status.md`, and say in `docs/leanvm-target.md` that
   T1 is stated for decodable bytecode. No Lean change is needed unless the project wants T1 to
   speak about every proof leanVM accepts.
3. Row 2 (image in `ProverData`) and row 3 (index column). Both wait on Clean #446 or on the
   Layer 7 design; at Layer 7, defining the image from `memTable`'s rows removes one of the two
   objects without Clean.
4. Row 14 (prover-side refusal of unconstrained reads). One sentence added to R3.
5. Row 20 (line citations). Refresh the cited ranges against the pin in eight files and the
   status survey record.

## Checked and faithful

The following were compared on both sides and match. Each is a place a wrong object could have
hidden.

- Who supplies what: opcodes and separators are constants (`Expression.const`, `Const`);
  `pc`, `fp`, operands, read words, counts are prover-supplied row columns on both sides; the
  finalize counts are committed in leanVM and are row fields of the roadmap's boundary blocks;
  the public input is `Fin 4 → K` in Lean and two `F192` halves with a rejected third limb in
  leanVM (`cpu/mod.rs:141-143`, R23). The `JUMP` witnesses are prover-supplied on both sides.
- `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`, bit `i` the coefficient of `x^i`;
  `E = K[y]/(y^3 + y + 1)` with limbs `c0 + c1·y + c2·y²`; `y = (0, 1, 0)`; `g = 0x2` with
  `orderOf g = 2^64 - 1` certified by seven `decide +kernel` checks (`Generator.lean:65-95`).
- Opcode codes `g^0 … g^5` in the order XOR, MUL, SET, DEREF, JUMP, BLAKE2S; separators
  `g^0, g^1, g^2`; caps `16 ≤ κ_mem ≤ 32`, `τ ≤ 32`, `κ_bc ≤ 32`, `τ_BLAKE2S ≥ 3`
  (`n_blocks_log(1) = 3` from `min_n_blocks_log`, `flock/hash.rs:285`).
- The sixteen-slot bytecode encoding of §8.1, all six rows, and its exact decoder
  (`decode_eq_some_iff`); `DEREF` flags `(0,0), (1,0), (0,1)` (`isa.rs:68-75`).
- All six tables: column count and order, constraint count, flush pairs, and every coordinate,
  including the twelve `MUL` products folded by `y^3 = y + 1`, the `DEREF` gating polynomial
  (identical, not merely equal on admissible flags), the literal-zero upper limbs of `memory_k`
  and `memory_128`, and the `JUMP` successor polynomials in characteristic two.
- The state, memory and bytecode tuples and their coordinate orders (`regs_toElements`,
  `memMsg_toElements`, `bytecodeMsg_toElements`, `busTuple`), the read rule (pull `count`, push
  `g·count`), the seed count `1`, and the boundary states `(1, 1)` and `(g^(N-1), 1)`.
- `execute`: `XOR` and `MUL` as `E` arithmetic on three read words; `SET` on the three-limb
  immediate; `DEREF` with `IsInK p`, target at `p·o₂`, sources `v₃`, `g²·pc`, `fp`; `JUMP` with
  three unconditional `K` assertions and the branch on `c ≠ 0`; `BLAKE2S` on nine cells with the
  second cell of each pair at `g·o`. Initial registers `(1, 1)`, fall-through `g·pc`, halting at
  the first arrival at `g^(N-1)` with `fp = 1`, memory addressed by `g`-powers with `0` and
  out-of-range powers invalid.
- BLAKE2s: IV, message schedule, `G` lanes, rotations, round count, working-state
  initialisation with both flag words, finalization; the cell packing (low word of `a₀` first),
  the message order (four cells in operand order), the chaining-value and output pairs, the
  metadata split (`counter = limb 0`, `final = low 32 bits`, `last_node = high 32 bits` of limb
  1). The opcode transcribes `flock::hash::blake2s_compress` (two flags), not
  `primitives::hash::compress` (one flag, `primitives/hash.rs:89-114`; R21, R22).
- The state pull carries no guarantee, matching Proposition 6.1 and the closed walks of §8.3
  (F5, decision 7); the memory and bytecode pull guarantees state Theorem 6.4's per-tuple fact.
- The stated licenses of every "Wrong readings excluded" bullet and of the one declared
  deviation hold at the pin (rows 10, 11, 15, 17, 18 and the checks above).
- `Protocol/Field.lean` transcribes nothing: `E` is the challenge field (§5.2 samples
  `α ∈ E^4`, `β ∈ E`), `card_E = 2^192` is CompPoly's, and the column oracle has no leanVM
  counterpart to diverge from.
