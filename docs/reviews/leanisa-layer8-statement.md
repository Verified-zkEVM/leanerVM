# Review: leanISA Layer 8, the constraint statement

Reviewed on 2026-09-17 against the uncommitted Layer 8 work of the worktree `leanisa-task-8`
on top of `main` at `42bbd51`, by an adversarial reviewer run with the repository's
`adversarial-review` skill and the `lean4:review` command. The report below is the reviewer's,
unedited. The disposition of each finding is recorded here and in
[`docs/roadmap/leanisa-status.md`](../roadmap/leanisa-status.md) (the Layer 8 frontier entry);
the fixes landed the same day on the same branch.

## Disposition

| Finding | Disposition |
| --- | --- |
| A1 (high): `SatisfiedBy` omits the BLAKE2s validity check | Met: the conjunct `Blake2sRowsValid w` (`blake2s_valid`), the reader `blake2sRowAt`, and `assumptions_of_blake2sRowsValid : Blake2sRowsValid w → w.Assumptions`; the blueprint's Layer 8, Layer 10 and trusted-surface text updated; tests `blake_cells_compress`, `fill_blake2sValid`, and the wrong-digest rejection `¬ Blake2sRowsValid digestW`. The Flock design note's D5 later replaces the conjunct by the constraints themselves. |
| A2 (medium): the `CountsNonzero` rejection is not load-bearing | Met: `fillW c rA cnt` gained the product row's read count; `zero_count_witness` shows the zero-count witness satisfies every other conjunct and fails `CountsNonzero` alone. |
| B1 (low): `Caps` is documented as all of `read_public` | Met in the module and structure docstrings and the blueprint: three checks transcribed, two by type, the rate and stacked-size checks the protocol layer's. |
| B2 (low): citation drift | Met: §8.5 for §8.4 (module, blueprint, `Boundary.lean`), `layout.rs:365`/`:376` for `:388`, `cpu/mod.rs:982-999`, `cpu/filler.rs:36-87`. |
| A3 | Met in docstrings: `RowSteps` and `AssignmentRepresents` state occurrence, not an embedding. |
| A4 | Met in the `public_input_eq` docstring. |
| A5 | Met in the `IndexColumnsAreRowIndices` docstring. |
| A6 | Met: `CountsNonzero` reads `i.msg[1]` under `1 < i.msg.size`. |
| A7 | Met by correcting the Layer 9 block comment (channels by name, messages typed), keeping the roadmap's block-comment convention. |
| A8 | Met: `Caps.well_shaped` labelled a representation hypothesis. |
| B3 | Met in the module docstring and the test header. |
| Pass C hygiene | Met: module docstring trimmed, `snake_case` fields, `rawRow`, `filter_eq_nil_of_rowOps`, `touched`/`untouched`, long lines, the two filler examples deleted, `fill_t1_instance` named. Not merged: the eight `*_constraints` lemmas, each of which unfolds its own table. |
| Missing tests | Added: the wrong-digest, shifted-index, wrong-word, three-row and four-row-`BLAKE2S` rejections and the load-bearing count witness. Not added: a channel-name-confusion test (no component of the ensemble pushes on a pull channel), the `SeedRowsAreTheImage` and `BytecodeRowsAreTheProgram` rejections, and the state-walk rejections (each needs a further kernel permutation). |

# Review: leanISA Layer 8, the constraint statement

Reviewed on 2026-09-17, read-only, in the worktree `leanisa-task-8` (uncommitted changes on top
of `main` at `42bbd51`). Files read in full: `LeanerVM/Arithmetization/Statement.lean` (new, 372
lines), `tests/LeanerVMTests/Arithmetization/Statement.lean` (new, 863 lines), the diffs of
`LeanerVM.lean`, `tests/LeanerVMTests.lean`, `README.md`, `docs/roadmap/leanisa-blueprint.md`,
`docs/roadmap/leanisa-status.md`; upstream `Channels.lean`, `Boundary.lean`, the six tables'
flush sites, `Semantics/{Memory,Execution,Step,Instruction}.lean`; Clean `93c9d1ef`
(`Air/FlatEnsemble.lean`, `Air/FlatComponent.lean`, `Circuit/Operations.lean:680-720`,
`Circuit/Channel.lean`). leanVM at the pin `a386121f` (clean checkout at
`/home/scaraven/Documents/leanEthereum/leanVM`): `doc/leanvm/body/05-arithmetization.tex`,
`06-bus-interactions.tex`, `08-end-to-end-protocol.tex`; `crates/lean_vm/src/cpu/mod.rs`
(`read_public` :130-178, `verify` :711-780, the caps :46-64), `cpu/layout.rs` (whole file),
`cpu/filler.rs` (whole file), `tables.rs` (separators :89-99, flush builders :127-166, the six
`count_columns`/`flushes` at :475-500, :540-565, :625-650, :714-760, :865-900), `pcs.rs:49-51`,
`crates/flock/src/hash.rs:280-286`, `crates/lean_compiler/src/filler.rs:1-12`.

Category A discipline: my expectation of the accept relation was written from §5.1, §6.2, §8.2
and §8.5 (Opening step 4) before `cpu/verify` (`mod.rs:711-780`) was opened; Category B items
(`read_public`, the count channel, the index column, the public columns) were read in the Rust
first and then checked against the Lean.

## Verdict

The statement is well built: `w.Constraints` is Clean's assertions-and-lookups only (no pull
guarantee is folded in, so nothing balance should prove is assumed), balance is a `List.Perm`
per separator pair over every component including the verifier, `CountsNonzero` covers exactly
leanVM's 28 read-count columns and nothing else, the boundary and public-input facts are faithful,
the three admitted hypotheses are true of leanVM's verifier by construction, the fixture is a
genuine `ValidExecution` whose witness satisfies every conjunct in the kernel, and the axiom
closure is standard. One conjunct is missing: the BLAKE2s compression relation (`Blake2sRelation`,
the BLAKE2S table's `Assumptions`), which the leanVM verifier enforces through flock
(`verify`, `mod.rs:759-768`; §8.5 "BLAKE2s validity") and which no field of `SatisfiedBy` and no
hypothesis of the blueprint's `constraintSoundness` carries. With it absent, `SatisfiedBy` accepts
a witness with a wrong-but-canonical digest and `constraintSoundness` as stated in the blueprint
is false for any program whose run executes `BLAKE2S`. The fixture cannot see this because its
eight BLAKE2S rows are fill rows off the run's path. Second: the `CountsNonzero` rejection does
not show that conjunct is load-bearing (the same witness is also unbalanced, verified in a
scratch file), so nothing would fail if the field were deleted. The rest is documentation
precision (`Caps` is not all of `read_public`; §8.4 for §8.5; two line citations) and hygiene.

## Pass A: specification

### Findings

**A1. High. `SatisfiedBy` omits the BLAKE2s validity check, so it is strictly more permissive
than the verifier and the blueprint's `constraintSoundness` is unprovable.**
`LeanerVM/Arithmetization/Statement.lean:259-284` (the structure), `:93-99` and `:254-258`
(its docstrings: "the relation the proof system proves and extracts", "what the M3 model means by
an accepted instance"); `docs/roadmap/leanisa-blueprint.md:14-16`, `:1098-1099` (T1-S over
`SatisfiedBy` alone), `:1277-1281` (the trusted-surface paragraph lists `Blake2sRelation` as
"assumed rather than proved" but no statement assumes it).
What is wrong. `blake2sTable.Assumptions r _ := Blake2sRelation r` (`Tables/Blake2s.lean:248`) is
Clean's soundness *assumption*, and `SatisfiedBy` consumes `w.Constraints` (assertions and
lookups, `Clean/Circuit/Operations.lean:687-689`) but never `w.Assumptions`
(`Clean/Air/FlatEnsemble.lean:219-220`). The BLAKE2S component has no polynomial constraint at
all: `blake2s_constraints (env : Environment K)` (tests `:584-587`) holds for every environment.
So nothing in `SatisfiedBy` ties a BLAKE2S row's `out0, out1` to `compress` of its inputs. The
leanVM verifier does: §8.5 "BLAKE2s validity" and Opening step 4 ("flock's reduction"), and
`verify` replays flock's reduction and ring-switches its claim into the one PCS opening
(`cpu/mod.rs:759-768`, `verify_reduction`, `ring_switch_verify`, `pcs::verify`). Clean cannot
route it through `soundness_of_tableSoundness_and_specConsistency` either: the ensemble-level
`Assumptions : PublicIO F → Prop` (`FlatEnsemble.lean:414-417`) cannot carry a per-row fact, so
the field has to live in the statement.
Concrete failure. Take the executor's BLAKE2S program (the test at `cpu/mod.rs:976-979` asserts
its digest cells), whose *run* executes one `BLAKE2S`. Build its honest witness, then replace
the row's `out0, out1` by any other canonical pair and the image's two output cells by the same
pair, keeping every count. Every conjunct still holds: the constraints (none on that table), the
memory pair (the block's seed and finalize rows are built from the same modified image and the
row's nine reads match it), the state and bytecode pairs (unchanged), `CountsNonzero`, `Caps`,
the three hypotheses, the two words. So `SatisfiedBy prog input w'`. But `execute` guards
`CompressCells` on the nine cells (`Semantics/Step.lean:136-147`), so `run` is `none` from that
step on, and `AssignmentRepresents.image_eq` forces `t.image` to be the modified image: no `t`
with `ValidExecution prog input t` exists. `constraintSoundness` (blueprint `:1098`) is false
for this `prog`. leanVM rejects `w'` (`CpuError::Blake2s` or the opening).
Fix. Add a field, e.g. `blake2s_rows : (tableAt w 5).Assumptions` (Clean's `Table.Assumptions`,
`FlatComponent.lean:188-190`, which unfolds to `∀ row ∈ blake2sRows w, Blake2sRelation
(rowInput …)`), or spell it with a `blake2sRowAt` reader parallel to `memRowAt`; cite §8.5 and
`mod.rs:759-768`; say in the docstring that this is the one conjunct the proof system discharges
through Flock (#3) rather than through the bus. Update the blueprint's Layer 8 block, the
trusted-surface paragraph (`:1277-1281`) and the Layer 10 proof plan (`:1102-1104`). Add to the
tests the honest instance (`Blake2sRelation (blakeRow j)`, one kernel compression, as the Layer 6
tests already do) and the wrong-digest rejection. If instead T1 is meant to take
`w.Assumptions` as an explicit hypothesis, the blueprint's two T1 statements and the module
docstring's "what the M3 verifier accepts" must say so; either way Layer 8 as built and Layer 10
as sketched are jointly inconsistent today.

**A2. Medium. The `CountsNonzero` rejection is not load-bearing: the mutated witness is rejected
by balance too, so no test guards the conjunct.**
`tests/LeanerVMTests/Arithmetization/Statement.lean:850-854`, docstring `:34-35`.
What is wrong. `fillW 0 memCnt` gives `setRow0` a count of `0`, so its read of cell `2` pulls
`(g², 0, x)` and pushes `(g², g·0, x) = (g², 0, x)`, a self-cancelling pair, and the chain of
counts at cell `2` loses its `1 → g` step: the push side carries `{1, 0, g²}` and the pull side
`{0, g, g²}`. Verified: `¬ BalancedPair (fillW 0 memCnt) MemPull.toRaw MemPush.toRaw` elaborates
with `decide +kernel` (scratch `probe_count0.lean`, `mem_balanced_iff` generalised over the
count). Since `fill_constraints` holds for every `c`, the witness fails exactly two conjuncts,
and deleting `countsNonzero` from `SatisfiedBy` would leave every test passing (the
`¬ CountsNonzero` example is about the definition, not the structure).
Concrete failure. The scenario §6.2 introduces the count product for (Theorem 6.4's proof: a
zero count survives `g·𝔠 = 𝔠`) is a self-cancelling read of a value *not in the image*; it
balances and only `CountsNonzero` rejects it. That witness is never built.
Fix. Parameterise `mulRow.rA` (or add a second count parameter to `fillW`): with `setRow0`'s
count `0`, `mulRow.rA := 1` and `memCnt 2 := g`, every conjunct but `countsNonzero` holds. Better
still, let the count-`0` read carry `x' ≠ x`: the unsound read the conjunct exists to exclude.
One more 124-message `decide +kernel` (about 30 s at the file's current rate).

### Observations (no failure scenario)

- **A3.** `AssignmentRepresents.regs_embed` (`Statement.lean:305-306`) is per-pair existence,
  not an embedding: a witness with one traversal of a loop `(pc,fp) → … → (pc,fp)` "represents"
  a trace with two. Harmless for T1 (the image determines the run), but the docstrings
  (`:104-106`, `:296-297`) say "embedded". Either say "each consecutive pair occurs as some
  row's pull and push", or strengthen to an injection of steps into rows, which Proposition 6.1's
  walk decomposition supplies for free in T1-S and T2 would want.
- **A4.** `publicInput_eq` (`:262`) is inert: `leanIsaVerifier` ignores its input
  (`Boundary.lean:312`) and no component reads `PublicIO`; the binding is `word0_eq/word1_eq`.
  Not wrong (leanVM binds the input through the transcript and the §8.2 line), but the statement
  should say the lanes are consumed by nothing so a reader does not look for the check there.
- **A5.** `IndexColumnsAreRowIndices` (`:229-230`) is redundant with `SeedRowsAreTheImage`
  (`:236-240`) once `idx i := gpow i` is written into the latter, and the bytecode block's index
  column is pinned inside `bytecodeRowOf` (`Boundary.lean:274-276`) with no separate conjunct.
  The asymmetry is deliberate (two Rust facts) but undocumented at `:227-230`.
- **A6.** `CountsNonzero` tests `i.msg[1]? ≠ some 0` (`:208`): on a channel of arity `< 2` the
  conjunct would hold vacuously. Both channels have arity 5 and 10 (`same_size`), so it cannot
  bite here; `∀ h : 1 < i.msg.size, i.msg[1] ≠ 0` says what is meant.
- **A7.** The four Layer 9 statements (`:344-366`) do not typecheck as written:
  `MemPull.Guarantees i.msg w.data` needs a `MemMsg K` (`fromElements i.msgVector`), and
  `i.msg.pc`, `i.msg.opcode`, `i.msg.op` project an `Array K`. A block comment cannot drift-check
  itself. The repository forbids `sorry`, but a `def MemChannelSound (prog input w) : Prop := …`
  is allowed, kernel-checked, axiom-free, and Layer 9 then proves `theorem mem_channel_sound :
  MemChannelSound …`. That is the better home for blocked statements.
- **A8.** `Caps.wellShaped` (`:222-223`) is a representation hypothesis on the prover data, not a
  verifier check; the docstring at `:74-76` says so, but it sits inside a structure documented as
  "`read_public`". Consider a separate field group or a one-line label on the field itself.
- Non-vacuity: every hypothesis of every theorem and every conjunct of `SatisfiedBy` is
  instantiated by `fillW 1 memCnt` (`fill_satisfiedBy`, `fill_represents`, `:761-773`,
  `:823-824`), which is a `ValidExecution` (`:412`). Nothing collapses to `True`; the only
  conjunct trivially true given the others is none (each is independent; `constraints` is nearly
  so, since only the JUMP table has assertions, but that is leanVM's shape, see B3).
- Over-strengthening: no conjunct excludes an honest prover. `minLogMem_le` and `wellShaped`
  match the prover's padding (`mod.rs:46-47`), `blake2s_height` the filler's floor
  (`cpu/filler.rs:43`), the two `List.ofFn` hypotheses the blocks' exact column layout
  (`layout.rs:361-395`).

## Pass B: fidelity to leanVM `a386121f`

### Findings

**B1. Low. `Caps` is documented as `read_public` but transcribes three of its eight checks and
names only one of the rest.**
`Statement.lean:30`, `:70-78`, `:210-223`; `docs/roadmap/leanisa-blueprint.md:1000-1010`.
`read_public` (`cpu/mod.rs:130-178`) checks: (1) announced-size scalars have `c1 = c2 = 0`
(`:133`, transcript format); (2) both public-input halves have `c2 = 0` (`:141-143`); (3) the
bytecode length is a power of two `≤ 2^32` (`:158-159`); (4) `log_mem ∈ [16, 32]` (`:160`); (5)
every `tau ≤ 32` (`:161`); (6) `tau_5 ≥ n_blocks_log(1) = 3` (`:166`; `flock/src/hash.rs:283-286`,
`max(1, 8) = 8 = 2^3`); (7) `validate_log_inv_rate` (`:167`); (8) the stacked size
`mu ∈ [MIN_MU, MAX_MU] = [15, 28]` (`:174-176`; `pcs.rs:49-51`). The Lean has (4), (5), (6)
explicitly, (3) by `Program.logSize_le` (named at `:76-77`) and (2) by
`PublicInput.word0/word1` (`Semantics/Memory.lean:107-111`, unnamed). (7) and (8) are omitted
and unnamed; (8) is the binding cap in practice at the pin (`2^28` K-elements in total, against
`2^32` rows per table with eight or more columns each). Omitting them only weakens the soundness
hypothesis, and they are PCS parameters rather than M3 facts, so leaving them to the protocol
layer is defensible. But "`Caps w` is `read_public`" and the blueprint's "exactly the relation
the proof-system roadmap proves and extracts" are then inexact.
Fix. Cite `:130-178`; list (2) as by type, (7) and (8) as the protocol verifier's, and say why.

**B2. Low. Citation drift.**
- "§8.4" for the unrolled protocol at `Statement.lean:35`, `:88`, `:279` (the field docstring);
  `08-end-to-end-protocol.tex:44` is §8.4 "Fiat Shamir instanciation", `:48` is §8.5 "The
  unrolled protocol", whose Bus item 4 (`:70`) is the cited text. The same file says §8.5 at
  `:244`. Also `blueprint.md:213`, `:779`, `:1004` and `Boundary.lean:23` (landed with Layer 7).
- `layout.rs:388` (`Statement.lean:83`, `:228`) is the *bytecode* block's `Index`; the memory
  block's index coordinate is `:365` (seed) and `:376` (finalize).
- `cpu/mod.rs:981-998` (tests `:10`) is `:982-999` (doc comment `:982-984`, fn `:985-999`).
- `crates/lean_compiler/src/filler.rs` (tests `:13`, blueprint `:1086`) emits the blocks; their
  shape, sizes `[128, …, 1]`, the `MIN_ROWS = [1,1,1,1,1,8]` floor and the frame layout are
  `crates/lean_vm/src/cpu/filler.rs:36-87`. Cite both.

### Enumeration (B7 of the reference)

- **Count channel** (Category B, `layout.rs:73`, `:412-414`; `tables.rs` `count_columns`):
  Arith `[RA, RB, RC, RBC]` ×2, Set `[R, RBC]`, Deref `[R1, R2, R3, RBC]`, Jump `[RC, RD, RF,
  RBC]`, Blake2s `[R_M0 … R_MD, RBC]`: 4+4+2+4+4+10 = **28** committed count columns, each the
  `Col(count)` coordinate of exactly one pull (`tables.rs:150-151` bytecode, `:161-162` memory),
  and `MFCNT`/`BFCNT` are not count blocks. Lean: the six tables' pulls on `mem.pull`/`bc.pull`
  are 4+4+2+4+4+10 = **28** (`Tables/*.lean`, the `memRead`/`bytecodeRead` sites), the count at
  message index 1 of both `MemMsg (addr, count, v)` and `BytecodeMsg (pc, count, opcode, op)`
  (`Channels.lean:153-173`, `memMsg_toElements`, `bytecodeMsg_toElements`), i.e. bus
  coordinate 2, and `w.tables.take 6` excludes the two blocks. **Match.**
- **Boundary blocks** (`layout.rs:352-395`): state push `(ST, 1, 1)` / pull `(ST, g^{B-1}, 1)`
  (`:354-358`) ↔ `leanIsaVerifier prog` (`Boundary.lean:311-314`); memory seed `(MEM, Index, 1,
  MEM_LO, MEM_HI, MEM_TOP)` / finalize with `MFCNT` (`:361-382`) ↔ `memTable` with
  `IndexColumnsAreRowIndices` and `SeedRowsAreTheImage`; bytecode seed/finalize with eight
  `Public` columns and `BFCNT` (`:383-395`) ↔ `bytecodeTable` with `BytecodeRowsAreTheProgram
  prog` (`bytecodeRowOf` writes `gpow i` and Layer 4's `entry`). **Match.**
- **Public input** (§8.2 `:27-33`; `verify` `mod.rs:746-755`): the Rust checks one combined
  equation `c₀ + Y·c₁ = interp(pi₀, pi₁, r)` and pools `0` for the top limb; sound because
  `{1, Y}` is `K`-independent, so the meaning is cells `g^0, g^1` equal the two words with top
  limb `0`. Lean: `word0_eq`, `word1_eq` on `imageOf w.data` (tied to the committed block by
  `SeedRowsAreTheImage`), top limb `0` by `PublicInput.word0`. **Match** (Category A reading).
- **Heights**: powers of two (`announce_public`, `:113-117`; `layout.rs:458-465`), at least one
  row (`cpu/filler.rs:43`, `:124-126`), BLAKE2S at least eight (`:43`; `mod.rs:166`) ↔
  `Caps.heights`, `blake2s_height`. **Match.**
- **Separators and per-pair balance**: `SEP_STATE, SEP_MEM, SEP_BYTECODE = g^0, g^1, g^2`
  (`tables.rs:90-92`) are distinct constants, so whole-bus multiset equality (§5.1 `:14`) is
  equivalent to the three per-pair `List.Perm`s over messages without the separator. **Match.**
- **B0**: nothing historical (no Poseidon, KoalaBear, three-table model, LogUp, sign-encoded
  direction). Clean.
- **Deviation declared by the docstring**: balance as `List.Perm` rather than Clean's field sum;
  the licence (`ringChar K = 2`) holds and is tested at `:856-861` only for `List.Perm` itself
  (see E).
- **Deviation not declared**: A1 (flock) and B1 ((7), (8)).

### Observation

- **B3.** The fixture's fill blocks are closed walks (`cpu/filler.rs:5-14`), but not the
  compiler's shape: leanVM's closing `JUMP` uses one frame cell `DEST` as both condition and
  destination and its dummy `JUMP` falls through on `ZERO` (`:59-87`); the fixture uses distinct
  `c`, `d` cells and no fall-through dummy. Irrelevant to Layer 8; "as the compiler extends a
  program" (tests `:11`) is loose. Also the tables' polynomial-constraint count matches
  leanVM's: only `JUMP` has assertions (`tables.rs:724-731`, `n_constraints = 2`), the other
  seven components and the verifier have none, which is why `w.Constraints` reduces to the
  JUMP residuals (`tests:564-612`). Worth one sentence in the module docstring.

## Pass C: hygiene

- `Statement.lean:21-134`: 114 of 372 lines. The citations, the `read_public` reading, the
  "Wrong readings excluded" list (`:117-133`) and the Layer 9 note earn their place. "Reading a
  witness" (`:46-54`) and "The statement" (`:93-99`) restate the declaration docstrings word for
  word; cut them to the non-obvious facts (name-based channels, `rowInput`, the words not on the
  bus). Accuracy: §8.4 (B2), "`Caps` is `read_public`" (B1), "what the M3 verifier accepts" (A1).
- `Statement.lean:203-208`: "coordinate `1`" is the message index; the specification's tuple
  coordinate is 2 (§6.2 "Tuple and columns"). Say "message index 1, bus coordinate 2".
- `Statement.lean:259-284`: field names mix `snake_case` equations (`publicInput_eq`,
  `state_balanced`, `word0_eq`) with `lowerCamelCase` propositions (`countsNonzero`,
  `indexColumns`, `seedRows`, `bytecodeRows`). Mathlib style is `snake_case` for every
  Prop-valued field.
- Lines over 100 characters: `Statement.lean:355` (106, inside the block comment);
  `tests/…/Statement.lean:536` (102), `:787` (104).
- `tests:684-685`: docstring "Every read count is a power of `g`" states more than the theorem
  (`≠ 0`).
- `tests:856-861`: two examples test `List.Perm` and `ringChar K = 2`, not Layer 8 (see E).
- `tests:149`: `def row` shadows the variable name used throughout `Statement.lean`
  (`memRowAt w row`); `rawRow` or `rowOf` reads better.
- `tests:342`: `data_eq` is `rfl` and used twice where `show … from rfl` is used inline elsewhere
  (`:692-693`); pick one.
- Duplication: `memT_filter`/`bcT_filter` (`:453-482`), `memRow_push`/`memRow_pull`
  (`:493-521`), `memT_pushes`/`memT_pulls` (`:524-539`), eight `*_constraints` (`:564-602`)
  differing only in the unfolded name. One lemma "a component whose `rowOperations` has no
  assertion and no lookup satisfies `ConstraintsHold` in every environment" plus one lemma "a
  table whose row interactions are on channels `c₁, c₂` sends nothing on a channel of another
  name" replace ten declarations.
- Development-history language: none. The nine "finding E8" references in the test file are
  durable constraints on the next author (hygiene C2's exception); a single section comment
  "Why these proofs take this shape (E8)" at `:422` would let the per-lemma mentions go.
- Structure, imports, `public`/plain-file boundary, namespace, section headers: per
  `CONTRIBUTING.md`; `LeanerVM.lean` and `tests/LeanerVMTests.lean` updated exactly once each.

## The five axes

**a. Faithfulness.** `SatisfiedBy` says what the M3 verifier accepts *except* for flock's BLAKE2s
validity (A1). `Caps` is three of `read_public`'s eight checks plus two by type; the stacked-size
window and the rate check are omitted and unnamed (B1). `CountsNonzero` covers exactly the six
tables' 28 read counts and not the blocks' finalize counts (B enumeration); the count is at
message index 1 for both tuples. The three admitted hypotheses are faithful to `Index`,
`MEM_LO/HI/TOP` + `MFCNT`, and `Coord::Public` + `BFCNT`; they are the weakest faithful
statements in the sense that each leaves exactly the committed column free (`SeedRowsAreTheImage`
also leaves `idx` free, which `IndexColumnsAreRowIndices` then pins, A5). The public words are
checked the way §8.2 means, and the Rust's combined line check is sound for the same reason
(B enumeration). Balance is per pair and multiset-counted, and per-pair is equivalent to the
whole-bus multiset because the separators are distinct constants. `log_inv_rate` is rightly the
protocol's; the `half.c2 != 0` check is by `PublicInput`'s construction; say both. Nothing
excludes an honest prover.

**b. Vacuity.** Every conjunct and hypothesis is instantiated (`fill_satisfiedBy`,
`fill_represents`, over a `ValidExecution`); `SatisfiedBy` is falsifiable (the finalize-count
rejection is genuinely balance-only). No conjunct is trivially true given the others.
`Caps.heights` over `w.tables` versus the verifier table does not matter: the verifier table has
one row and is not in `w.tables`. `RowSteps` cannot be met by a row with extra state messages
(singleton-list equality) nor by the verifier (not in `w.tables`); `AssignmentRepresents` says
only image equality plus per-pair row existence (A3). `fill_constraints` holds for all `c`,
`cnt`, so the two rejections do fail on the intended conjunct, but the count-`0` witness fails
balance as well (A2, verified), so the `CountsNonzero` rejection is not load-bearing; `¬
[m, m].Perm []` and `(1 : K) + 1 = 0` are filler. Underconstrained reading found: the
wrong-digest witness (A1). Over-constrained reading: none.

**c. Maintainability.** Positional coupling is the main risk: `tableAt w 5/6/7`, `Fin 8`,
`w.tables.take 6`, `[1]?`, and the list literal at `:147-148` all encode the ensemble's order,
guarded only by three `rfl` examples in the test file (`:271-281`). Name the indices in the
production file (`blake2sIndex : Fin 8 := 5` with `(leanIsaEnsemble prog).tables[5] = ⟨blake2sTable⟩
:= rfl` next to it), and write `CountsNonzero` over `j : Fin 6` and `tableAt w (j.castAdd 2)`.
Name-based channel identity is the right call given `RawChannel` carries propositions; a typed
`ChannelPair` structure would stop `BalancedPair w StatePush MemPull`. `abbrev` for the three row
readers is right (they must unfold under `rw`); `tableAt` as a `def` is right. `SatisfiedBy` and
`Caps` as structures are right (Layers 9 and 10 project by name). `65507` and `29`
(`tests:543-560`, `:657-668`) should be `2 ^ minLogMem - touched` with `touched := 29` named
once, and `mem_balanced_iff` should take the count `c` (the probe shows the same proof works).
The eight `*_constraints`, the two `*_filter` and the push/pull pairs are one lemma each.
`decide +kernel` on 18/49/124-message permutations of `Array K` is acceptable for a fixture and
the E8 workarounds are sound and documented; the 2 min 15 s elaboration is the price and should
be watched. The Layer 9 block comment should become `Prop`-valued definitions (A7).

**d. Readability.** The module docstring is proportionate in what it carries but repeats the
declaration docstrings (Pass C); its inaccuracies are §8.4 (B2), "`Caps` is `read_public`" (B1)
and the accept-relation claim (A1). Names say what they mean; `RowSteps` and
`AssignmentRepresents` overstate ("embedded", A3). The test file is navigable (fixture, rows,
tables, image, run, helpers, conjuncts, trace, rejections) and its section headers are good; the
"proof helpers" section is the longest and would benefit from the merges above. No comment
restates code except the two paragraphs named.

**e. Test relevance.** See the table. Load-bearing for the audit: `fill_satisfiedBy` and its
twelve conjunct theorems, `fill_represents`, the three balance theorems, `jumpT_constraints`, the
finalize-count rejection, and the three `tableAt_*` guards. Redundant: the two filler examples,
the second ensemble-as-data example. Exercising the wrong thing: the `CountsNonzero` rejection
(A2). Missing: below.

## Test relevance

| Declaration (tests/…/Statement.lean) | What it tests | Verdict |
|---|---|---|
| `mulX … rustOut1`, `mulInput`, `cellK`, `fillProg`, `fillCells`, `fillImage`, `fillTrace`, `fillRows`, `fillData`, `fillCounts`, `memCnt`, `bcCnt`, `bcCntFin` (`:47-144`) | fixture data | scaffolding, keep |
| `memRows_fill`, `memCnt_of_ge` (`:121-138`) | E8 readers | scaffolding, keep |
| `row`, `row_size`, `rows_size`, `jumpRaw`, `jumpRaw_size` (`:149-209`) | row plumbing | scaffolding, keep; rename `row` |
| the fourteen row defs, `mkT`, the eight tables, `fillW` (`:164-266`) | the witness | scaffolding, keep |
| `example` ensemble tables (`:271-274`) | the ensemble's order, `rfl` | obvious but the only guard of `tableAt`'s indices: move to production as a named guard |
| `example` verifier (`:276`) | `rfl` | delete |
| `tableAt_five/six/seven` (`:279-281`) | positional coupling | keep, merge into one |
| `blakeT_table`, `memT_table`, `bcT_table`, `memBlockRows_eq` (`:285-293`) | E8 readers | scaffolding, keep |
| `fill_logSize`, `fill_wellShaped`, `fill_pow_eq`, `fillRows_get?`, `fill_image_apply'`, `fill_image_apply`, `fill_imageOf`, `data_eq` (`:297-342`) | E8, the image equality | scaffolding, keep; inline `data_eq` |
| `fetch_at`, `fetch_one`, `read_at` (`:347-360`) | Layer 3 helpers | scaffolding |
| `fill_step0..3`, `fill_run1..4`, `fill_run`, `fill_boundary`, `example ValidExecution`, `fill_regs` (`:362-420`) | Layer 3 behaviour of the new program | keep (needed by `fill_represents`); fold `fill_run1..3` |
| `table_interactions_eq`, `rowMessagesOn_eq` (`:427-430`, `:778-782`) | Clean's `interactions_eq` restated for the kernel | scaffolding, keep; candidate for `Tables/Basic.lean` |
| `memTable_rowOps`, `bytecodeTable_rowOps` (`:433-450`) | Layer 7 flush shapes, `rfl` | established upstream; keep as E8 plumbing |
| `memT_filter`, `bcT_filter` (`:453-482`) | foreign channels are `[]` | scaffolding, merge |
| `seedMsg`, `finMsg`, `memRow_push`, `memRow_pull`, `memT_pushes`, `memT_pulls`, `seeds_split`, `fins_split` (`:485-560`) | the memory block's 2^16 messages without enumeration | scaffolding, keep; merge push/pull |
| `xor_… bytecode_… verifier_constraints` (`:564-602`) | seven components have no assertion | real fact about Layers 6–7, one lemma suffices |
| `jumpT_constraints` (`:605-612`) | JUMP residuals on four rows | real, keep |
| `fill_constraints` (`:616-628`) | `w.Constraints` for all `c`, `cnt` | real, keep (its generality is what makes the rejections meaningful) |
| `fill_state_balanced`, `fill_bytecode_balanced`, `fill_mem_balanced` (`:632-682`) | `BalancedPair`/`messagesOn` over a full witness | real, load-bearing, keep |
| `mem_balanced_iff` (`:657-676`) | reduction to the touched cells | scaffolding; generalise over `c`, name `29`/`65507` |
| `fill_countsNonzero`, `fill_caps`, `fill_indexColumns`, `seedRows_gen`, `seedRows_of`, `fill_seedRows`, `fill_bytecodeRows`, `fill_word0/1` (`:685-758`) | each conjunct instantiated | real, keep; fix the `countsNonzero` docstring |
| `fill_satisfiedBy` (`:761-773`) | non-vacuity of the statement | load-bearing, keep |
| `fill_regs_embed`, `represents_of`, `fill_represents` (`:785-824`) | `RowSteps`, `AssignmentRepresents` | real, keep |
| `example` T1-C instance (`:826-828`) | the three facts together | keep, make it a named theorem |
| `example` via `assignmentRepresents_image` (`:831-832`) | the production theorem on the instance | obvious given `fill_imageOf`; keep only as its one exercise |
| `wrongCnt`, `wrongCnt_of_ge`, `¬ BalancedPair` (`:837-848`) | §6.2 finalize count | real, load-bearing, keep |
| `¬ CountsNonzero (fillW 0 memCnt)` (`:851-854`) | the definition on a witness also rejected by balance | exercises the wrong thing (A2); replace |
| `¬ [m, m].Perm []` (`:858-859`) | `List.Perm` | filler; replace by `¬ BalancedPair` of a doubled push |
| `(1 : K) + 1 = 0` (`:861`) | Layer 0 | delete |

**Missing tests** (cheap ones first; the ones marked * need one more kernel permutation):
1. A rejection for each admitted hypothesis: the block with `idx` shifted by one row
   (`¬ IndexColumnsAreRowIndices`), with one word not the image's (`¬ SeedRowsAreTheImage`),
   with one slot's opcode changed (`¬ BytecodeRowsAreTheProgram fillProg`).
2. A wrong public word: `mulInput` with `lanes 0 := 3` fails `word0_eq`; a wrong `publicInput`
   fails `publicInput_eq` (and shows A4: nothing else notices).
3. A non-power-of-two height (`setT` with three rows) and a BLAKE2S table of four rows fail `Caps`.
4. Channel-name confusion, claimed at `Statement.lean:121-123` and untested: a push emitted on
   `MemPull` counts as a pull in `messagesOn`.
5. The load-bearing `CountsNonzero` witness (A2).*
6. The wrong-digest witness: accepted today (documents A1), rejected once the field lands.*
7. A bytecode read of a nonexistent slot (`pc = g^32`) unbalances the bytecode pair; a state
   message missing a step (drop `mulRow`) unbalances the state pair.*
8. `¬ RowSteps (fillW 1 memCnt) ⟨gpow 31, 1⟩ r'` for every `r'` (no row leaves the sentinel), and
   `¬ AssignmentRepresents (fillW 1 memCnt) t'` for a trace with another image.

## Scripts and axioms

- `./scripts/audit-lean.sh`: "First-party Lean source policy passed."
- `./scripts/check-imports.sh`: "Production and test aggregate imports are complete."
- `./scripts/check-layers.sh`: "Lean layer dependencies respect the architecture DAG."
- Axiom closure (scratch `axioms.lean` via `lake env lean`): `memRowAt_toElements`,
  `assignmentRepresents_image`, `fill_satisfiedBy`, `fill_represents`, `fill_constraints`,
  `mem_balanced_iff`, `fill_run` each depend on `[propext, Classical.choice, Quot.sound]` only.
- Probe (scratch `probe_count0.lean`): `¬ BalancedPair (fillW 0 memCnt) MemPull.toRaw
  MemPush.toRaw` proved by the generalised `mem_balanced_iff'` and `decide +kernel` (A2).

## Documentation moved with the code?

- Blueprint Layer 8 block (`:895-1000`): matches the built declarations field for field and type
  for type (`tableAt`, the three `abbrev`s, `messagesOn`, `rowMessagesOn`, `memRowAt`,
  `BalancedPair`, `CountsNonzero`, `Caps`'s five fields, the three hypotheses, `SatisfiedBy`'s
  twelve fields in order, `RowSteps`, `AssignmentRepresents`'s three fields, the two theorems).
  Drift: "(§8.4, Bus 4)" at `:1004` versus §8.5 at `:934`; "`Caps` is `read_public`" (B1); the
  trusted-surface paragraph `:1277-1281` versus A1. The "Large witnesses" convention row and the
  index list (`:1265-1270`) are current.
- Status: "fully proved" is true (no `sorry`, standard axioms); the seven listed departures are
  the seven bullets and each is in the code; the E8 text matches the test file's comments; table
  rows 7/8/9 are current. Nit: "the memory pair reduced to the touched cells (125)" is 124
  messages a side (95 table reads plus 29 block cells). The claim is correctly "T1's completeness
  instance for that program, by hand", not CC-C.
- README: "Layers 0 to 7 landed" matches `git log` (`42bbd51` = PR #21, Layer 7, at the head of
  `main`); "Layer 8 … is built on this branch" and "no proof-system claim has landed" are honest.
- Target classification: the work advances the *statement surface* of T1 (both directions) and
  nothing else; no theorem of T1–T8, CC-S or CC-C is claimed, and the docs say so. The module
  docstring lacks the one-sentence AGENTS.md classification (artifact, direction, boundary,
  contribution); add it, and with A1 fixed say that flock's relation is the one conjunct
  discharged outside the bus.

## lean4:review (batch mode)

**Resolved inputs.** targets: `LeanerVM/Arithmetization/Statement.lean`,
`tests/LeanerVMTests/Arithmetization/Statement.lean`; `--scope=file` on each; `--mode=batch`;
no hook, no `--json`, no Codex. Layer-2 activation: **advisory**, source `intent.source =
remote-heuristic` (helper record valid: `repository_kind = other-lean`, `contributing_upstream =
no`). Post-review action-plan prompt: skipped as instructed.

### Layer 1

- **Build.** Both modules import cleanly under `lake env lean` (scratch files elaborate against
  their `.olean`s); the caller reports `lake build` of both targets green.
- **Sorry audit.** `lean4-skills-sorry-analyzer --report-only`: 0 sorries in each file.
- **Axiom status.** Standard axioms only (scratch `#print axioms`, list above).
  `lean4-skills-check-axioms-inline` was not run: it appends `#print axioms` to the file under
  review, which this read-only review must not do (and it has no `--help`).
- **Style notes.** `Statement.lean:355` 106 chars; `tests:536` 102; `tests:787` 104. Prop-valued
  structure fields mix `snake_case` and `lowerCamelCase` (`Statement.lean:259-284`). `fun x ↦`,
  `by` placement, focusing dots, `where` syntax, `/-! ## -/` headers: conforming.
- **Golfing.** `lean4-skills-find-golfable --filter-false-positives`: "No optimization
  opportunities found" for both files. By hand: `memRowAt_toElements` (`:311-319`) could avoid
  `convert` by `Vector.ext` directly on `valueFromOffset`; `fill_caps.heights` (`:694-705`) is
  eight identical `⟨τ, by decide, _⟩` branches over an `rcases`, a `Fin 8` `interval_cases`
  would halve it; `fill_run1..3` (`:387-397`) are subsumed by `fill_run4`'s `simp` set.
- **Complexity.** Longest proofs: `mem_balanced_iff` (20 lines), `memT_filter`/`bcT_filter` (14
  each), `assignmentRepresents_image` (13), `fill_imageOf` (11). Kernel-heavy: four
  `decide +kernel` permutations and `fill_countsNonzero`; whole-file elaboration 2 min 15 s (the
  status file's figure).

### Advisory (mathlib-style, Layer 2)

- `docstring` / `module-doc`: every public declaration and both modules are documented; the
  module docstring restates declaration docstrings (Pass C).
- `file-placement` / `import-hygiene`: `Arithmetization` is the owner layer; imports are the
  six tables, `Boundary`, and `Clean.Air.FlatEnsemble`, nothing wider.
- `api` / `generalization`: `BalancedPair (pull push : RawChannel K)` is an unbundled pair
  (a `ChannelPair` structure would type the three pairs); `Caps` bundles a representation
  hypothesis with verifier checks (A8); `SeedRowsAreTheImage`'s existential `idx` is redundant
  (A5); `AssignmentRepresents.regs_embed` is weaker than its name (A3). No `vacuous-api`
  instance: no public declaration collapses to `True`.
- `attribute` / `simp` / `instance`: none added; nothing to review.
- `module-system`: plain files by the repository's Clean boundary; aggregates updated.
