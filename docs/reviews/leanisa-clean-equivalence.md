# Review: leanISA Layers 5–10 and the adaptor on Clean main

Reviewed on 2026-10-29, read-only, on branch `feat/leanisa-clean-equivalence` at `a0abe35e`
(`git diff 0ff06f8e..HEAD`, nine commits: the port to Clean `9dd71e82` via the fork pin
`61c6e013`, the equivalence, two golfing commits), with the merged base (#82/#83 completeness,
#166 soundness) as it now reads. Pinned leanVM `a386121f` read first for the Category B items
(`cpu/mod.rs:130-178`, `cpu/layout.rs:352-395`, `tables.rs:88-166`, `count_columns`); Clean
read at the pin (`Air/{Balance,FlatEnsemble,FlatComponent,Lookup,Vm}.lean`,
`WitnessGeneration/Generation.lean`). No Lean probe was run: every finding below is settled by
an exact reading, and none claims a defect in a theorem. `audit-lean.sh`, `check-layers.sh`,
`check-imports.sh` and `check-docs.py` pass. Classification: T1 in both directions (CC-S by
`constraintSoundness`, CC-C by `constraintCompleteness`), stated correctly in the docstrings.

## Findings, by severity

**1. Statements — no defect found** (CONFIRMED by reading). `SatisfiedBy`
(`Statement.lean:312-331`) has exactly the verifier's checks: Clean's constraints, three-channel
`Balance.multiset`, `CountsNonzero`, `Caps`, `Blake2sRowsValid`, the two public words, and the
public input. The three deleted hypotheses are enforced by the witness type: row `i` of the
memory block has address `g^i` and its word is row `i` of the derived `"mem"` data
(`memBlock_rows`, from `Table.fixed_rows_match` + `data_consistent` + `same_data`), and the
bytecode block's rows are the program's entries (`bytecodeBlock_rows`, from
`bytecodeMode_fixedAt_iff`). Nothing is lost: `WellShapedData` is `getRows_size_of_preallocated`
(`memRows_size`). The program enters only through `bytecodeComponent prog` and
`leanIsaVerifier prog`, as decision 14 asks. `CountsNonzero` covers the six tables' memory and
bytecode pulls (4, 4, 2, 4, 4, 10 counts), which is leanVM's `count_columns` table for table.
`Caps` transcribes checks (4)–(6) of `read_public`. The adaptor's `satisfiedBy_witnessOf`
(`Protocol/LeanIsa/Sound.lean:238`) proves every conjunct from `M3Holds` plus `Sizes.Admissible`;
the fixed cells of `witnessOf` are honest by construction (`memBlockRowsOf` uses `gpow x`,
`bytecodeBlockRowsOf` uses `bytecodeRowOf prog`), so the fixed-column facts cost the stack
nothing. `TraceExtraction` and `leanIsaTraceExtraction` are unchanged in meaning.

**2. `satisfiable_iff_valid` is the honest form** (PLAUSIBLE that nothing stronger holds).
`Equivalence.lean:89`: the hypothesis `hfit : (∃ t, Valid) → ∃ t, Valid ∧ t.Fits` is exactly the
gap between the two one-directional theorems, which are the strongest unconditional statements
(`satisfiable_of_valid`, `valid_of_satisfiable`, both present). The two candidate unconditional
iffs fail: `Satisfiable ↔ ∃ t, Valid ∧ Fits` is refuted in principle by a witness at
`κ = maxLogMem` whose run already has power-of-two table heights and eight `BLAKE2S` rows (no
room, `Fits.room` false, but satisfying); `Satisfiable ↔ ∃ t, Valid` by a program whose every
valid run exceeds `6·2^32` steps (`completeness_needs_fit` has the run; it refutes a witness
representing `t`, not `Satisfiable` for the input, so this iff is unrefuted by a test). No change
needed; optionally restate `hfit` as `∀ t, Valid t → ∃ t', Valid t' ∧ t'.Fits` (equivalent,
reads as "some fitting execution exists whenever one does").

**3. The `generation` metadata of the opcode tables is not honest as documented** (CONFIRMED).
`Tables/Basic.lean:51-61` says `opcodeGeneration Row` gives "one row per pushed state". Clean's
`DemandMode.guard` defaults to `fun _ => .true` (`Generation.lean:131-134`), and Clean's own
docstring says opcode tables sharing a state channel "are told apart by guards". None is set, so
if Clean's generator ran on `leanIsaEnsemble`, every pushed state would create a row in all six
tables, five of them with placeholder cells; the result is never a witness of `SatisfiedBy`.
The metadata is dead (no theorem uses it; `FixedInputAt` is `True` for `.demand`) but a reader
of the blueprint's Clean table ("the six tables demand components") can mistake it for T2's
generator. Fix: in the `opcodeGeneration` docstring and the blueprint's Clean row, say that the
mode is a stub without a guard, that running Clean's generator does not produce a satisfying
witness, and that T2 is separate. A guard reading the opcode at the message's `pc` would need
the program in a hint table, which decision 14 keeps out of the prover data; do not add one.

**4. Stale status text after the fork pin** (CONFIRMED). `docs/roadmap/leanisa-status.md:21`
("Everything builds except three protocol pieces held by a name clash"), `:593` and `:832`
(`Conditions.lean`, `Refinement.lean`, `LeanIsaComplete.lean` "written but unbuilt") predate
commit `60c2018d`; the three modules now build (`.lake/build/.../Conditions.olean`,
`Refinement.olean`, `LeanIsaComplete.olean` at 15:16–15:17, after the 14:47 pin), and the pin
commit says `validate.sh` is green. Fix: rewrite the three sentences to say the pieces build at
the fork pin and that C13 is now issue #183 (return to upstream after Clean #496). The
blueprint's Clean table (`leanisa-blueprint.md:168`) names `Direction`; at the pin the type is
`ChannelDirection` (`BusDir` here). Say so in the row, since the table "records the API used"
(issue #23's acceptance).

**5. `Caps.heights` is documented against the wrong Rust line** (CONFIRMED, harmless at the
constants). `Statement.lean:291-292` cites `cpu/mod.rs:161` for "every table's height";
`:161` caps the six announced `taus` only, the memory block being `:160` and the bytecode
`:158-159`. The Lean quantifies over all eight tables, which is equivalent because
`maxLogRows = maxLogMem = maxLogBytecode = 32` (`Parameters/Isa.lean:70-79`), and the adaptor's
`Sizes.Admissible` caps the six only, as Rust does. Fix the docstring: "(5) the six opcode
tables' heights (`:161`); the two blocks' heights are `2^κ` and `2^prog.logSize`, within the
same bound by (4) and the bytecode cap, so `heights` quantifies over all eight."

**6. Clean reuse** (CONFIRMED). Nothing re-proved here is available in Clean main. Clean's
`Lookup` is a multiplicity-column (LogUp-style) static table and does not model the counted
read (`g·count` bump, seed/finalize) of §6.2, so `lookup_sound` is the right generic theorem
and belongs here; `Balance.multiset`, `activeMessages`, `deriveProverData`, `withDerivedData`,
`Component.weakSoundness` and `Table.circuitAssumptions_of_assumptions` are consumed, not
copied (`Steps.lean:172` uses Clean's per-row soundness for every row). The status page's
assessment of `Air/Vm.lean` (`addVm` vacuous with a `True` state guarantee, no computable trace)
is correct. `Balance.multiset`'s `length < 2^64` conjunct is one check Rust's verifier does not
make directly; it is implied by `Caps` (`interactionsWith_length_lt`,
`Protocol/LeanIsa/Relation.lean:185`) and consumed unchanged, so it is redundant, not wrong.

**7. Hygiene** (PLAUSIBLE). (a) `Arithmetization/Rows.lean` (Layer 9, soundness) now imports
`Completeness/Messages.lean`, the single closed form of every row circuit; a shared base under a
`Completeness/` folder misleads on ownership. Move it to `Arithmetization/Messages.lean` (no
content change; both aggregates updated). (b) The remaining duplication is vocabulary, not
proof: `Rows.lean`'s `OpcodeSends` (arbitrary rows) and `Completeness/Rows.lean`'s
`sendsOf`/`rowOf_sends` (honest rows) both derive from `*_sends_gen`; unifying them is optional.
(c) `Statement.lean:163-193`: eight private `*_channels` lemmas each `change` to a hand-written
list that drifts when a table's reads change; one lemma by `decide` on names would do.
(d) Docstrings in `Statement.lean`, `Channels.lean` and `Boundary.lean` still carry layer and
finding codes ("Layer 9's", "finding E8", "acceptance test 21"), against the rule that Lean
comments are self-contained. (e) `public_input_eq` is read by no component and follows from
`word0_eq`/`word1_eq`; it stays because Clean's `Ensemble.Statement` carries the public input.
Observation only.

## Passes

*Specification.* Every public theorem inhabited (`fill_satisfiedBy`, `sent_satisfiedBy`,
`bad_satisfiable`, the adaptor round trip); every load-bearing conjunct has a rejection
(`Statement.lean` tests `:1049-1207`; shifted index column and changed entry rejected by
`FixedRowsMatch`, `Boundary.lean:309`, `Bus.lean:120`); `SentinelSafe` load-bearing.

*Fidelity.* Separators `g^0, g^1, g^2` (`tables.rs:90-92`); pull `(…, count, …)`, push
`(…, g·count, …)` (`FlushBuilder::bytecode`, `memory_coords`); verifier push `(1,1)`, pull
`(g^(B-1), 1)` (`layout.rs:356-358`); memory seed `(Index, 1, LO, HI, TOP)` and finalize with
`MFCNT`; bytecode seed/finalize with `Index`, `BFCNT` and the eight `Public` columns; the index
column verifier-known (`gpowCell` here, `idxColumn` in the adaptor); the image the committed
value columns. All match. BLAKE2S floor `n_blocks_log(1) = 3`.


## Disposition

Applied on 2026-10-29 in `34d769c5`; no theorem statement changed.

| Finding | Disposition |
| --- | --- |
| 1. Statements | Kept: no defect. |
| 2. `satisfiable_iff_valid` | Kept: the honest form; `hfit` not restated. |
| 3. `opcodeGeneration` | Fixed (`34d769c5`): the docstring and the blueprint's Clean row call it guardless metadata, not a witness generator, used by no theorem; no guard added (decision 14). |
| 4. Stale status text | Fixed (`34d769c5`): the three protocol pieces build at the fork pin `61c6e013`, C13 tracked by issue #183; the blueprint names `ChannelDirection` at the pin and describes the current row closed forms. |
| 5. `Caps.heights` citation | Fixed (`34d769c5`): `:161` for the six opcode tables, `:160` and `:158-159` for the two blocks. |
| 6. Clean reuse | Kept: nothing to change. |
| 7a. `Completeness/Messages.lean` | Fixed (`34d769c5`): moved to `Arithmetization/Messages.lean`, names unchanged. |
| 7b. `OpcodeSends` and `sendsOf` | Kept: vocabulary, unification optional. |
| 7c. The eight `*_channels` lemmas | Kept: Clean's `RawChannel` has no decidable equality, so one `decide` on names does not prove `⊆`. |
| 7d. Layer and finding codes in docstrings | Kept: out of this pass. |
| 7e. `public_input_eq` | Kept: observation only. |
| Dead `filter_eq_nil_of_rowOps` | Fixed (`34d769c5`): deleted, no user. |
