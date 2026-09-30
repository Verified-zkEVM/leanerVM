
## H. Findings

Twenty findings: 3 major, 13 minor, 4 notes; none critical. None is a divergence from leanVM
in the sense of the brief (the documents disagree with each other and with the repository,
not with the pinned sources), except where a finding says otherwise; the classification line
says so each time. Proposed changes that are long are in §G and referenced.

### H.1 The base theorem of extraction lacks the program hypothesis its own composition needs

- **Severity**: major (a statement cannot be proved as written).
- **Evidence**: blueprint Layer 13, `protocol-blueprint.md:1247-1250`:
  "`theorem baseVerifier_extractsExecution (fs bcs mca flock) (h : verify prog input proof =
  true) : except with probability niError, ∃ t, ValidExecution prog input t`" and
  "`theorem baseProver_complete (hfill : HasFillBlocks prog) (h : ValidExecution prog input t)
  : …`", said to compose `constraintSoundness` and `constraintCompleteness` (`:1253-1255`);
  the contract row `:222` consumes "`constraintSoundness`, `HasFillBlocks`,
  `constraintCompleteness` (Layer 10)". The leanISA blueprint states both with a program
  hypothesis (`leanisa-blueprint.md:1156-1166`): "`theorem constraintSoundness (hwf :
  WellFormedBytecode prog) (h : SatisfiedBy prog input w) : …`", "`theorem
  constraintCompleteness (hwf : WellFormedBytecode prog) …`", where `WellFormedBytecode` has
  two fields, `sentinelSafe` and `hasFillBlocks`. `architecture.md:224-228`: "Both directions
  are stated for well-formed programs … a hypothesis of each, since the constraint system
  enforces neither". `leanvm-target.md:57-62` gives the reason: a bytecode whose sentinel slot
  holds a `JUMP` "admits accepted walks that execute the sentinel". The hole comment repeats
  both statements (`issue-12-comment-5833669972.md:190`). So the soundness theorem cannot be
  obtained by the composition it names, and the completeness theorem's `HasFillBlocks` does
  not give `constraintCompleteness`'s hypothesis.
- **Classification**: an error of the blueprint, against the leanISA roadmap (the program
  condition itself is faithful to leanVM, where the compiler guarantees it:
  `leanvm-target.md:60-62`).
- **Proposed change**: `:1247-1250` become
  "`theorem baseVerifier_extractsExecution (fs bcs mca flock) (hwf : WellFormedBytecode prog)
  (h : verify prog input proof = true) : except with probability niError, ∃ t, ValidExecution
  prog input t`" and "`theorem baseProver_complete (hwf : WellFormedBytecode prog) (h :
  ValidExecution prog input t) : verify prog input (prove prog input (witness of t)) = true`";
  `:222` consumes "`constraintSoundness`, `WellFormedBytecode`, `constraintCompleteness`
  (leanISA Layer 10)". Reason: the named composition then typechecks, and the hypothesis is
  visible in the statement a reader audits.
  [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: the alternative, `verify` deciding
  the program condition on the public program and rejecting otherwise, removes the hypothesis
  from the soundness theorem; which one the blueprint takes is a technical decision.]

### H.2 The blueprint hands the specification of the holes to a tracker comment that contradicts it

- **Severity**: major (through the delegation, the blueprint specifies a public-input
  transcript leanVM does not use, and signatures that cannot be stated).
- **Evidence**: the blueprint sends the reader to the comment three times
  (`protocol-blueprint.md:339-340` "its specification is a section of the hole comment";
  `:590-591` "Its specification is a section of the hole comment on the dashboard #12";
  `:1485-1487`). The tracker body says it "holds nothing that is not in them"
  (`issue-12-body.md:6`). The comment's own head says only four of its thirteen sections were
  rewritten after the spine was built (`issue-12-comment-5833669972.md:3`); the other sections
  still give the pre-spine signatures (§B.3, items 1 to 3, 5, 7, 8), which do not typecheck
  against `Phase.Def` as built (`LeanerVM/Protocol/Spine/Phase.lean:37`, three arguments). Its
  section on the public-input phase says "the prover sends nothing" (`:93-94`), while leanVM's
  §8.2 has the prover send `c_0, c_1` (`08-end-to-end-protocol.tex:27-33` at the pin, as quoted
  by `protocol-status.md:466`; the Rust reads the two scalars, `cpu/mod.rs:745-755`) and the
  phase on `main` follows it (`PublicInput.pSpec`, `LeanerVM/Protocol/PublicInput.lean:99`:
  "`def pSpec : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[E, List E]⟩`"). The comment also
  holds tests and one technical remark found nowhere else (§G.4, column "only in the
  comment").
- **Classification**: an error of the blueprint (its delegated specification of the
  public-input phase differs from leanVM's §8.2; the built phase is faithful).
- **Proposed change**: move each section as §G.4 says; replace the three pointers as §G.2 and
  §G.1 say; edit the comment in place to the pointer of §G.4.

### H.3 The per-layer sketches use types the spine does not have

- **Severity**: major (the statements cannot be stated as written).
- **Evidence**: §B.4, items 1 to 9: Layer 6's local `structure BusOut where ζ … rem … pool :
  List Claim … α … β` (`:960-964`) against the spine's `BusOut I` of two claim lists
  (`:481`; `Seams.lean:130-135`); Layer 7's `tableSumcheck … (StmtIn := BusOut) … (StmtOut :=
  BusOut × ColumnClaims)` (`:988`) against `Phases.table` (`:533`); Layer 9's `FlockInterface`
  with an `OracleReduction` field from `ColumnClaims` to `WeightedClaim` and an unbound `s`
  (`:1077-1085`) against `Phases.flock` (`:535`); Layer 10's own `Weight`, `WeightedClaim`,
  `Claim.toWeighted`, `leanVmPiop (prog) (s) (input) (flock)` over `M3Witness` and
  `m3Relation`, and master theorems with `Set.univ` and `rbrKnowledgeSoundness`
  (`:1109-1130`) against the spine's (`:541-547`; `Compose.lean:162-177`); `Sumcheck.Def`,
  `Gkr.Def`, `Batch.Def` (`:952, 984, 1104`), which exist nowhere; seven names used and never
  defined (`Claim`, `ColumnClaims`, `LeafLayout`, `StackLayout`, `M3Witness`, `m3Relation`,
  `commitPhase`). Layer 8 (`:1011-1027`) is the only phase sketch on the spine's types.
- **Classification**: an error of the blueprint.
- **Proposed change**: restate Layers 6, 7, 9 and 10 on Layer 8's pattern:
  "`def busPhase (I : M3Instance) : Phase.Def I I.Stmt (I.Stmt × BusOut I)`",
  "`def busComplete I : Phase.Complete I (busPhase I) (Seam.commit I) (Seam.bus I)`",
  "`def busSecurity I : Phase.Security I (busPhase I) (Seam.commit I) (Seam.bus I)`", and
  likewise `tableSumcheck` (from `Seam.bus` to `Seam.table`), the Flock phase (`Seam.pub` to
  `Seam.flock`) and `openingPhase` (`Seam.flock` to `Seam.done`); delete Layer 6's `BusOut`,
  Layer 10's `Weight`, `WeightedClaim` and its `leanVmPiop` block (the spine's are in "What the
  spine fixes"); restate the generic components of Layers 4 and 5 as `Component.Def`s with
  their `Complete` and `Security`, and their theorems in the `rbrKnowledgeSoundnessWorstCaseWith`
  form of convention *Holes* (`:332`). Reason: the spine is built and is the contract.
  [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: the message schedules, errors and
  internal relations of each phase, and the opening phase's schedule against specification
  §8.5.]

### H.4 The status and the tracker describe a repository two merges old

- **Severity**: minor (stale text), the most visible one.
- **Evidence**: §B.1 (the status heads itself as a snapshot of `f4d858c` and calls the
  public-input phase a draft on a branch; fifteen items), §B.2 (the tracker shows Layer 1 in
  review behind the closed #18, the public-input phase open with the opposite transcript, four
  closed pull requests as open, "revision 2" defined nowhere, and renders "ArkLib #1", "ArkLib
  #4" and "#3 there" as links to leanerVM items), §B.11 (both say the pins are unchanged;
  pull request 61 moved four). The Layer 1 review's two edits of the tracker were never made
  (`docs/reviews/protocol-layer1.md:211`). `README.md:32-33` says "no proof-system claim has
  landed" and `docs/README.md:38-47` says the three reviewed branches are still branches.
- **Classification**: not a divergence from leanVM.
- **Proposed change**: §G.3 (status), §G.4 (tracker body). `README.md:32-33`: "The proof
  system's spine, with its two master theorems conditional on the phases, Layer 1 and the
  public-input phase are on `main`; see `docs/roadmap/protocol-status.md`." `docs/README.md`:
  "whose findings the branch now meets" becomes "whose findings were met before it merged", in
  the three entries. For the future: a status whose coverage is checked against the repository
  (§E.4) cannot drift this way unnoticed.

### H.5 The blueprint states superseded pins as current

- **Severity**: minor (stale text), with a technical consequence left to the orchestrator.
- **Evidence**: §B.11, items 1 to 6: after pull request 61 the blueprint says in one new
  paragraph that its API tables "record the original implementation baseline"
  (`:52-54` at `144c5aa`) and elsewhere still says ArkLib is "a Lake dependency at `dca90385`"
  (`:113`), that the pins are ArkLib `dca90385`, CompPoly `3468b38c`, Clean `93c9d1ef`, VCVio
  `f9dc47d9` "(through ArkLib)", Lean `v4.33.1` (`:167-172`), that Layer 0 adds "ArkLib at
  `dca90385`" with CompPoly resolved at `3468b38c` (`:633-635`), and heads the upstream
  ledger "ArkLib state at `dca90385`" (`:261`).
- **Classification**: not a divergence from leanVM.
- **Proposed change**: `:167-172` becomes "The pins are in `upstreams.json`, with the history
  of each in [dependencies.md](../dependencies.md); leanVM is pinned at `a386121f`." `:113`
  becomes "ArkLib as a Lake dependency, with …". Layer 0 (`:633-635`) says what Layer 0 did at
  the time and that the pins have since moved ("Layer 0 added ArkLib, then at `dca90385`, …").
  The ledger's column becomes "ArkLib state at the pin" and is re-read at `7653a901`.
  [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: which ledger rows (admitted
  sumcheck round, admitted composition, round-by-round to plain, Fiat–Shamir and BCS,
  correlated agreement, ring-switching packing) still hold at ArkLib `7653a901`, from the
  library review.]

### H.6 Letter codes collide, and some point at the wrong thing

- **Severity**: minor (avoidable reading cost; two misdirected references).
- **Evidence**: §D: at least 128 codes and 1036 occurrences in the eight texts; 34 codes with
  two or more meanings inside the proof system's own documents (the code `C1` has five: a hole,
  a ledger entry, and a finding of each of the three reviews), 11 more that mean something else
  in the leanISA status; within the status alone `A1` and `C1` each have four meanings. Two
  references resolve to the wrong finding: "finding F3 of the status file"
  (`protocol-blueprint.md:1440`) means the leanISA status's finding, the protocol status's
  being "one root for push and pull" (§B.5, item 9); and the status's legend says its letter
  `F` continues the leanISA numbering (`protocol-status.md:281-283`), where leanISA's letter
  for the same subject is `R` (§B.1, item 13). The blueprint's "the generic holes carry the
  ledger letters of the ArkLib work they will become" (`:592-593`) is false (§B.4, item 12).
  The codes have reached the trackers: issue 28 "Layer 2/C1", issue 23 "P3", issue 31 "P05"
  (§D.3).
- **Classification**: not a divergence from leanVM.
- **Proposed change**: §F (names for holes, ledger entries and findings; numbers kept, with
  names, for layers, acceptance tests, decisions and target theorems; one index, drafted in
  §F.3). The two misdirected references: `:1440` "(finding F3 of the status file)" becomes
  "(the leanISA status's finding on the BLAKE2S value limbs)"; `protocol-status.md:282-283`
  "**F** = Rust versus specification, continuing the leanISA numbering where the subject
  overlaps" becomes "**F** = Rust or Python versus the specification (numbered independently
  of the leanISA status, whose letter for this is **R**)", until §F retires the letters.

### H.7 The same fact is written in three to six places

- **Severity**: minor (drift, and a larger text to audit).
- **Evidence**: §A: the upstream ledger three times with different rows and columns
  (`protocol-blueprint.md:257-267`, `protocol-status.md:171-184`, `issue-12-body.md:61-74`;
  the blueprint's has nine ArkLib rows, the other two drop one and add four); the specification
  of the bus phase four times with three different types (§A, "Signatures"); the record of a
  review four times.
- **Classification**: not a divergence from leanVM.
- **Proposed change**: §E (one home per kind of fact), applied by §G.

### H.8 The import rule of the proof system is false of `main` as written

- **Severity**: minor.
- **Evidence**: §B.5, item 12: convention *The wall* (`:331`) lists the modules allowed to
  import `LeanerVM/Arithmetization/`, and acceptance test 25 (`:1341-1345`) takes as its
  witness a `grep` that "lists the exceptions of convention *The wall* only". The `grep`
  returns `LeanerVM/Protocol/FixedColumns.lean:11` and `LeanerVM/Protocol/Basic.lean:3`
  (`public import LeanerVM.Arithmetization.Basic`); `Basic.lean` is the layer's empty root
  module (a docstring and an empty section), imported by `LeanerVM.lean:19` and by no
  module. It exposes nothing, so no phase sees the arithmetization through it; the rule's
  statement and its test are what is wrong. The rule has no script
  (`scripts/check-layers.sh:30-41` checks the layer DAG only), as the Layer 1 review found.
- **Classification**: not a divergence from leanVM.
- **Proposed change**: either drop the import from `LeanerVM/Protocol/Basic.lean` (it
  declares nothing, so it needs none; the policy tests build their own fixture tree,
  `scripts/test-policy-checks.py:35-45`, and do not read this file), or add "the layer's empty
  root `Basic.lean`" to the exceptions of `:331` and of acceptance test 25. Then write the rule
  into `scripts/check-layers.sh` with an allow-list, and a planted violation in
  `scripts/test-policy-checks.py`.

### H.9 The review tooling the blueprint prescribes is not in the repository

- **Severity**: minor.
- **Evidence**: `protocol-blueprint.md:1512`: "the reviewer runs the `leanerVM-review` skill's
  three passes"; no skill has that name; the skill is `adversarial-review`, as the status and
  the handoffs call it (`protocol-status.md:438, 479, 506`). Both it and `lean-spec-authoring`,
  which "sets the rules" (`:178`), live under `.claude/`, which is git-ignored (`.gitignore:9`;
  `git ls-files .claude` is empty), so a contributor who clones the repository has neither.
- **Classification**: not a divergence from leanVM.
- **Proposed change**: the blueprint describes the review by what it does (§G.1, last
  bullet) and `:178` says "(the rules are in `CONTRIBUTING.md`)"; or the owner tracks the two
  skills in the repository and the blueprint names them correctly.

### H.10 "How work is tracked" is contradicted by practice

- **Severity**: minor.
- **Evidence**: §B.7: claims by comment on issue 12 are impossible for a contributor without
  write access, and the four live claims are in intention issues; intention issues are titled
  by layer, not by hole; the open pull requests name no hole, category, ledger entry or target;
  the labels are unused; the status uses a state ("built, draft") the tracker does not define;
  `CONTRIBUTING.md:16-19` asks for a design issue first where the blueprint says no issue is
  opened for a hole; a review fact "is recorded on the dashboard's history"
  (`protocol-status.md:553-554`), where no reader of the repository finds it.
- **Classification**: not a divergence from leanVM.
- **Proposed change**: §G.1, which also states the owner's rule that a tracker changes by an
  edit of its body.

### H.11 The blueprint records state and history, against its own rule

- **Severity**: minor.
- **Evidence**: `:1474-1475` "does not record history, status, or who is doing what", and
  §B.4, item 11 (seven places: "done on the spine's branch", "The port is done and closes hole
  C1", "(#13, taken)", "folded there on 2026-09-25", "already in flight", the column "Existing
  work" with pull requests in flight, "a rule … is still to be written").
- **Classification**: not a divergence from leanVM.
- **Proposed change**: delete those phrases and the columns "Existing work" and "Issue"
  (§G.2); the facts are the status's.

### H.12 Decisions are numbered, but most of their content is gone and the numbers collide

- **Severity**: minor.
- **Evidence**: §B.8: decisions 1 to 5 were questions in the first status (`51021d9`); today
  decisions 1 and 3 survive as "was taken" (`protocol-status.md:214`) and decisions 6 to 10
  only as outcomes (`:217-224`); two choices have no number (`:224-227`); the blueprint cites
  "decision 8" and "decision 6" (`:557, 560`) without defining them; the leanISA roadmap
  numbers its decisions from 1, so "decision 15" means two things (issue 4 against
  `protocol-status.md:258`).
- **Classification**: not a divergence from leanVM.
- **Proposed change**: a section "Decisions" in the blueprint (§E.3, item 11) with one row per
  decision: number, name, the choice in one line, the convention or test that records it
  (drafted in §F.3); the status keeps none.

### H.13 The list of public names is not the public boundary

- **Severity**: minor (auditability: the reviewer's reading list is incomplete).
- **Evidence**: `:1419` "Everything not listed is a proof, a helper, or a test". Of 333
  non-private declarations under `LeanerVM/Protocol/` at `b435631`, 197 are not in the list
  (`unlisted_public.py`, re-run), among them definitions the blueprint says later work reads:
  `PublicInput.check`, `pooled`, `prover`, `verifier`, `pSpec` ("Layer 12 reads those",
  `:1049-1051`), `publicInputComplete`, `publicInputSecurity`, and the generic modules
  `ToArkLib/GuardedVerdict.lean` and `ToArkLib/KeepOracles.lean`, which the spine's
  pass-through and send components now import (`protocol-status.md:74-75`) and of which the
  blueprint names neither the module `KeepOracles` nor its declarations. `Ensemble.toM3` is
  listed under "Spine:" (`:1369`) although it is Layer 2's.
- **Classification**: not a divergence from leanVM.
- **Proposed change**: add to the list, under "Protocol (leanVM)", `publicInputComplete
  publicInputSecurity PublicInput.pSpec PublicInput.check PublicInput.pooled PublicInput.prover
  PublicInput.verifier PublicInput.verifier_verify`, and under "Protocol (generic)",
  `Verifier.GuardedForm.of_probEvent_pos Reduction.mem_support_run_of_guarded keepOracles
  OracleVerifier.materializeOutput_of_keepOracles probEvent_uniformSample_le_of_card_le`
  (names at `b435631`); name `GuardedVerdict` and `KeepOracles` in the spine's list of generic
  modules (`:343-344`); move `Ensemble.toM3` out of "Spine:". Reason: the list is the
  reviewer's reading list (`:1362`).

### H.14 Names and references that point at nothing, or at the wrong thing

- **Severity**: minor.
- **Evidence**: `StateMsg` (`:220`) and `leanIsaTables` (acceptance test 5, `:1280`) exist
  nowhere (§B.5, items 4, 5); "Lemma 5.1" (`:601`, and the status and tracker) does not exist
  in the specification, whose Lemma 5.2 and Theorem 5.1 share one counter
  (`05-arithmetization.tex:36, 40`; `preamble/theorems.tex:4-5`); acceptance test 14 names
  `bytecodeColumn_slot` as its witness (`:1306-1307`), which the Layer 1 review showed restates
  the definition, the pinning statement being `bytecodeColumn_answer_boolVec`
  (`FixedColumns.lean:85, 97`); the hole table lists the spine's `Weight`, `WeightedClaim` and
  `FlockOut` as products of the opening and Flock phases (§B.5, item 6); the status's ledger
  names a module `ToCompPoly/Claims.lean` that does not exist (`:177`); three citations into
  ArkLib at the old pin drifted (§B.10).
- **Classification**: not a divergence from leanVM.
- **Proposed change**: `:220` drops `StateMsg` (or names the state channel's message type as
  leanISA declares it); `:1280` "distinguished by the flush polynomials of the leanISA
  instance"; `:601` per §G.2; `:1306-1307` "Witness: `bytecodeColumn_answer_boolVec` on a
  two-instruction program, against reversed slot bits
  (`tests/LeanerVMTests/Protocol/FixedColumns.lean`)"; the hole table per §G.2; the status
  per §G.3; the three ArkLib citations per §B.10 (to be re-read at the new pin).

### H.15 The upstream ledger misses the Merkle trees of the pinned VCVio, and cites a closed issue

- **Severity**: minor (possibly avoidable audit surface).
- **Evidence**: §B.9: the ledger says of Merkle trees "absent (only coding-theory lemmas) …
  Written here" (`:265`), Layer 11 plans `merkleRoot` and `merkleVerify` locally
  (`:1179-1182`), and the upstream named for them is ArkLib issue 4, closed on 2026-09-27 in
  favour of VCVio issue 571. At the VCVio pin `f9dc47d9`, read before the upgrade,
  `CryptoFoundations/MerkleTree/` held nineteen modules with no `sorry`.
- **Classification**: not a divergence from leanVM. Unverified: whether that library fits
  leanVM's Merkle trees (BLAKE2s, the leaf encoding, pruned paths,
  `crates/fiat_shamir/src/merkle.rs:14-67`); and its state at the new pin `a4232d08`.
- **Proposed change**: the ledger row and Layer 11 name VCVio's Merkle-tree library and VCVio
  issue 571 as the upstream, with the decision whether Layer 11 builds on it.
  [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: that decision, from the review of
  Layer 11 or the library review.]

### H.16 Discrepancies in the sources are not where both status files say they are

- **Severity**: minor.
- **Evidence**: `protocol-status.md:281`: findings "numbered for citation from pull requests
  and `docs/leanvm-target.md`"; the blueprint: "Durable source discrepancies are also recorded
  in leanvm-target.md" (`:1500-1501`). `leanvm-target.md` records one discrepancy, the
  sentinel (`:57-62`), and none of the proof system's twenty-seven findings against the
  specification, the Rust and the Python verifier (§B.7, item 6).
- **Classification**: the findings themselves are divergences inside leanVM (between its
  specification, Rust and Python); this finding is only about where they are recorded.
- **Proposed change**: §E.2: one register in `leanvm-target.md`, by name, for both roadmaps.

### H.17 The Layer 0 module's comments cite the roadmap, layer numbers and a letter code

- **Severity**: note.
- **Evidence**: §B.5, item 13: `LeanerVM/Protocol/Field.lean:18, 29, 31, 37, 66` at `b435631`
  ("Protocol roadmap Layer 0 (`docs/roadmap/protocol-blueprint.md`)", "(leanISA status finding
  P3)", "(roadmap convention *The oracle*)", "Layer 11"), against the convention "Comments …
  cite the specification, never this roadmap" (`:329`). Still so at `144c5aa`, where the
  upgrade updated the same docstring's pins and wrote "and of VCVio through it", although
  VCVio is now a direct requirement. Every later module of `LeanerVM/Protocol/` follows the
  convention.
- **Classification**: not a divergence from leanVM.
- **Proposed change**: rewrite the module docstring's first paragraph without the roadmap,
  the layer numbers and the code ("the eager `Fintype BF64` instance" in words), and "of
  VCVio, a direct requirement".

### H.18 A review's tracker edits are not applied, while its handoff says "met"

- **Severity**: note.
- **Evidence**: the Layer 1 review left two edits for GitHub, "the L1 line and the open pull
  request table of the dashboard #12" (`docs/reviews/protocol-layer1.md:211`); neither was made
  (§B.2, items 1 and 3).
- **Classification**: not a divergence from leanVM.
- **Proposed change**: §G.1, bullet "Reviews": tracker edits a review asks for are made in the
  pull request that meets it.

### H.19 The completeness base theorem composes leanISA's existence theorem, where `architecture.md` says witness generation

- **Severity**: note.
- **Evidence**: `protocol-blueprint.md:147-148` ("the honest prover here starts from an
  `EnsembleWitness`") and `:1255` (`baseProver_complete` composes `constraintCompleteness`);
  `architecture.md:273-275`: T4's "completeness dual composes T2 with the honest prover".
- **Classification**: a deliberate scope choice of the blueprint (witness generation, T2, is
  out of scope, `:147-148`), not written down as a deviation from `architecture.md`.
- **Proposed change**: one sentence in Layer 13: "`baseProver_complete` is existential in the
  witness (it composes leanISA's `constraintCompleteness`); the computable form through the
  witness generator (T2) is `architecture.md`'s, out of scope here."

### H.20 What was checked and found right

- **Severity**: note (negative results).
- **Evidence**: §B.10: every local Markdown link and anchor of the 115 tracked Markdown files
  resolves (150 links); every one of 81 citations into the pinned leanVM sources resolves to an
  existing range once its crate is known (22 are ambiguous as written: `transcript.rs`,
  `witness.rs`, `lib.rs`, `filler.rs`, and specification files that also exist under
  `doc/leanvm/drafts/`); 40 of 43 citations into the pinned libraries are at the cited place
  (the old pins); all 30 references to numbered acceptance tests point at the intended test;
  the spine's sketch in the blueprint (`:442-554`) agrees with the code; the Layer 8 sketch
  agrees with `PublicInput.lean`.
- **Proposed change**: none; the ambiguous citations would name their crate
  (`crates/fiat_shamir/src/transcript.rs`).
