# Dossier: the documentation debt of the proof system

Task `docs-debt`. Reviewed: leanerVM `main` at `b435631`; the tracker (issue 12 of
`Verified-zkEVM/leanerVM`) and the related issues and pull requests as they stood on
2026-09-29/30, read with `gh` only. Nothing was edited, posted or committed. No Lean was run:
every probe is a Python script or a `grep` over text, listed in the appendix.

Conventions of this dossier. Things are named in words; a letter-number code appears only in
parentheses after the name, or as data in the tables of section D, whose subject is the codes.
The dossier's own sections are written §B.5 and so on, never as a bare letter and number.

Revisions. The object of the review is `main` at `b435631`. `main` has since moved to
`144c5aa` (pull request 61, the upgrade to Lean 4.34.1, which moved every library pin; brief,
section 8), and the checkout now contains it. Citations `file:line` are of `b435631`
(`git show b435631:<path>`) unless a passage says `144c5aa`; the status file is identical at
the two revisions, and the blueprint differs by 6 lines (its lines after 50 are shifted by 4 at
`144c5aa`). The proposed texts of §G describe `144c5aa`, as the orchestrator asked. For the
tracker, citations are lines of the raw texts saved under `.claude/reports/blueprint-review/probes/docs-debt/`
(`issue-12-body.md` for the body, `issue-12-comment-5833669972.md` for the "hole comment").
"BP", "ST", "TB", "HC", "OC", "RS", "RL", "RP" in tables abbreviate the blueprint, the status,
the tracker body, the hole comment, the other comments, and the handoffs of the reviews of the
spine, of Layer 1 and of the public-input phase.

## Summary

**What was examined.** In full: the blueprint (1549 lines at `b435631`), the status (622), the
three review handoffs of the proof system, `leanth-reuse.md`, `architecture.md`,
`leanvm-target.md`, `docs/README.md`, `development.md`, `dependencies.md`, `ci.md`, `README.md`,
`CONTRIBUTING.md`, `AGENTS.md`; the body of issue 12 and its five comments, among them the "hole
comment"; the bodies of issues 3, 4, 13, 16, 20, 22, 23, 27 to 33, 35 to 37 and of the thirteen
closed `[Hole]` issues 45 to 57; the descriptions and comments of pull requests 39, 42, 43, 58,
59, 60; the state of 31 upstream issues and pull requests the status names; and the changes of
pull request 61 (`144c5aa`, the upgrade to Lean 4.34.1, merged after `b435631`) to the
documents. Checked mechanically (§B.10, appendix): 194 names of the blueprint's interface list,
333 declarations of `LeanerVM/Protocol/`, 150 local links, 81 citations into the pinned leanVM
sources, 43 into the libraries, and every letter-number code of eight texts. A second pass
re-checked the first draft of this dossier and corrected it (next section).

**Conclusions.**

1. **There is no single source of truth.** One kind of fact lives in three to six places, and
   the copies have drifted: the upstream ledger three times with different rows, the
   specification of a hole four times with three different types, the record of a review four
   times (§A). The blueprint hands the specification of every hole to a comment on the tracker
   (`protocol-blueprint.md:339-340, 590-591, 1485-1487`); eight of that comment's thirteen
   sections still carry the signatures of the design before the spine was built, and its
   section on the public-input phase says "the prover sends nothing", where leanVM's §8.2 and
   the code on `main` have the prover send two scalars (§B.3; finding H.2).
2. **The blueprint contradicts itself and the leanISA roadmap.** The sketches of Layers 4 to 7,
   9 and 10 use types the spine does not have (`BusOut` with challenges, `Claim`, `M3Witness`,
   `Sumcheck.Def`, master theorems over `Set.univ`; §B.4; finding H.3). The two base theorems
   of the target "base proof extraction and completeness" (T4) omit the program hypothesis
   `WellFormedBytecode` that the leanISA theorems they are composed from require, so the
   extraction theorem cannot be obtained by the composition it names (§B.6; finding H.1).
3. **The status and the tracker are two landings stale.** The status heads itself as a snapshot
   of `f4d858c`, calls the public-input phase a draft on a branch, and says the pins are
   unchanged; the tracker shows Layer 1 and the public-input phase as not landed, lists four
   closed pull requests as open, and links "ArkLib #1" and "ArkLib #4" to leanerVM items. Since
   pull request 61, five passages of the blueprint also state the former pins as current
   (§B.1, §B.2, §B.11; findings H.4, H.5).
4. **The letter codes are worse than hard to read.** At least 128 codes occur at least 1036
   times in the eight texts; 34 have two or more meanings inside the proof system's own
   documents (`C1` has five) and 11 more mean something else in the leanISA status; two
   references resolve to the wrong finding; the codes have reached issue bodies (issue 28's
   "Layer 2/C1", issue 23's "P3"). All but layers, acceptance tests, decisions and target
   theorems can be names; one index can define the rest (§D, §F; finding H.6).
5. **Smaller defects, each with a fix:** the import rule's own `grep` witness returns an
   unlisted module (`LeanerVM/Protocol/Basic.lean`); the review skill the blueprint prescribes
   has a wrong name and is not in the repository; 198 of 333 public declarations are missing
   from the "list of public names"; the ledger ignores the sorry-free Merkle trees of the
   pinned VCVio and cites a closed ArkLib issue; decisions 1 to 10 survive only as numbers or
   outcomes (findings H.8 to H.16).
6. **What is sound:** every local link and anchor resolves; every citation into the pinned
   leanVM sources lands in range once its crate is known; 40 of 43 library citations are exact;
   every reference to a numbered acceptance test is right; the spine's sketch matches the code
   (finding H.20).

**Findings by severity** (§H): critical 0; major 3 (H.1 to H.3); minor 13 (H.4 to H.16);
note 4 (H.17 to H.20).

**Proposal** (§E to §G). One home per kind of fact. The blueprint owns everything wanted or
decided: the specification of every hole (moved from the hole comment, section by section, as
§G.4 maps), the one upstream ledger, the decisions and one index of names. The status owns only
where things stand, and its coverage can be read off the repository (a hole is built when the
names its row marks are declared) and checked by a script. The body of issue 12 becomes
pointers and one checklist line per hole, changed by editing the body, never by comments
(§G.4, ready to paste). Findings against the leanVM sources move to `leanvm-target.md`. Holes,
ledger entries and findings get names; layers, acceptance tests, decisions and target theorems
keep their numbers with a name beside them. Every proposed text marks with
`[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: …]` where the review's technical
findings will change it again.

**Against the brief.** The ground moved during the task: `main` is now `144c5aa`, which
changes every library pin; the proposed status and tracker texts describe `144c5aa`, as the
orchestrator asked, while all citations are of `b435631` unless marked. Nothing else in the
brief was contradicted.

## How this dossier was made, and what the second pass re-checked

An earlier agent wrote sections A to F and the start of G (`probes/docs-debt/dossier-part1.txt`)
and was interrupted. This pass re-checked that draft against the sources before relying on it,
corrected it, completed §G, and wrote §H and the summary.

**Re-checked, and right.** Every numbered item of §B.1 to §B.7 (the earlier draft's 69) and the
prose of §B.8 and §B.9 were read against both sides at the cited lines (the blueprint, the status, the saved tracker texts, the leanISA
blueprint and status, `architecture.md`, `leanvm-target.md`, `README.md`, `docs/README.md`,
`CONTRIBUTING.md`, the pinned specification's `05-arithmetization.tex:36, 40` and
`preamble/theorems.tex:4-5`, the VCVio pin's `CryptoFoundations/MerkleTree/`). The live state of
GitHub was read again on 2026-09-29/30: the body of issue 12 and the hole comment are unchanged
since 2026-09-28 14:28 UTC (a `diff` against the saved copies differs by a trailing newline only);
the open pull requests are 39, 42, 43, unlabelled; issues 27, 32, 35, 36 are closed and 28 to 31,
33, 37 open; issue 34 is not an intention issue but a merged pull request on the semantics. The
ArkLib figure (347 commits past the pin at `origin/main` `7653a901e`, 246 at `66f39b4`) was
recounted with `git rev-list --count` in the sibling checkout. The saved probe outputs were
produced at `b435631`; `unlisted_public.py` was re-run on an export of `b435631` and gives 198,
as the draft said (197 on the working tree at `144c5aa`). The Lean snippets of "Objects named
in this dossier" were compared line by line with the files at the cited lines. The probes
`check_anchors.py` and `check_interface_names.py` were re-run and give the same numbers (the
first now also walks the review's own reports, which the orchestrator has committed under
`.claude/`, and still finds 150 links, none broken). The leanVM citation probe's output was
regrouped by citation: each of its 89 citation groups has a candidate file in range (appendix).

**Re-checked in section D.** Thirteen codes across the families (units of work, ledger entries,
ArkLib, specification, Rust, Lean-environment findings, target theorems) were recounted with an
independent whole-word pattern over the eight texts, and their "defined at" lines read.

**Corrected.**
- §B.3, item 8: the hole comment's "the spine's six `ProtocolSpec`s" is at `:178`, not `:176`.
- §B.9: VCVio's Merkle-tree directory at the pin holds nineteen modules, not sixteen.
- §B.1, item 14: 58 of the 66 lines of "Decisions pending" are decisions taken, not 60.
- Section D: the code counts are lower bounds (the pattern skips codes in backticks); two cells
  corrected.
- The earlier draft's proposed status text said that no proof-system module other than
  `FixedColumns.lean` imports the arithmetization. That is false: `LeanerVM/Protocol/Basic.lean:3`
  does. Added as §B.5, item 12 and a finding; the proposed text in §G.3 is corrected.
- The earlier summary announced findings (major 4, minor 17, note 5) for a section H that did not
  exist. §H is written from scratch; its counts are in the summary.

**Added.** §B.11, the pins after pull request 61 (at the orchestrator's request); §B.1, item 15
(ArkLib issue 907 closed); §B.2, the Layer 1 review's two GitHub edits
never applied; §B.5, items 12 and 13 (the import rule's witness; the Layer 0 module's comments);
§D.3, codes that already collide in the trackers.

## Objects named in this dossier

A reader who knows zkVMs and not these libraries needs nine objects.

- **`OracleReduction` (ArkLib, at the former pin `dca90385`).** ArkLib's type of an interactive protocol with
  a fixed message schedule in which some prover messages are oracles the verifier queries. Its
  declaration is at `.lake/packages/Arklib/ArkLib/OracleReduction/Basic.lean:633`.
- **`M3Instance`, `M3Holds` (leanerVM, the spine).** The abstract description of an
  arithmetization (tables, constraint polynomials, bus tuples, stack layout) and the relation
  on one committed column `q` that the proof system proves knowledge of
  (`LeanerVM/Protocol/Spine/Instance.lean:119`).
- **`Phase.Def` (leanerVM, the spine).** One phase of the protocol over the one committed
  oracle. It takes three arguments, the instance and the two statement types; this matters in
  section B. Copied from `LeanerVM/Protocol/Spine/Phase.lean:36-38`:

  ```lean
  /-- A phase: a component from a statement to a statement over the stack. -/
  abbrev Def (StmtIn StmtOut : Type) : Type 1 :=
    Component.Def StmtIn (TheOracle I) Unit StmtOut (TheOracle I) Unit
  ```

- **`Phases` (leanerVM, the spine).** The bundle of the five phases after the commit, with their
  statement types. Copied from `LeanerVM/Protocol/Spine/Compose.lean:73-84` (docstrings elided):

  ```lean
  structure Phases where
    bus : Phase.Def I I.Stmt (I.Stmt × BusOut I)
    table : Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)
    pub : Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I)
    flock : Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I)
    opening : Phase.Def I (I.Stmt × FlockOut I) Unit
  ```

- **`BusOut` (leanerVM, the spine).** What the bus phase hands to the table sumcheck: two lists
  of claims and nothing else. Copied from `LeanerVM/Protocol/Spine/Seams.lean:130-135`:

  ```lean
  structure BusOut (I : M3Instance) where
    /-- The linear claims. -/
    linear : List (LinearClaim I)
    /-- The column claims. -/
    columns : List (ColumnClaim I)
  ```

- **`EnsembleWitness`, `Component` (Clean, at the former pin `93c9d1ef`; at `42fe4b26` the structure is at line 23).** Clean's witness of a set of tables
  (`Clean/Air/FlatEnsemble.lean:19`) and Clean's word for one table's circuit. leanerVM's spine
  has its own, unrelated `Component.Def` (a protocol piece), and ArkLib has a directory
  `ProofSystem/Component/` of small reductions: three meanings of one word (section C).
- **`SatisfiedBy`, `WellFormedBytecode`, `ValidExecution` (leanerVM, leanISA).** The constraint
  relation on a Clean witness (`LeanerVM/Arithmetization/Statement.lean:311`), the hypothesis
  on the program that both leanISA theorems take (specified at
  `docs/roadmap/leanisa-blueprint.md:1156`, not built), and the execution relation
  (`LeanerVM/Semantics/Execution.lean:114`).
- **`ProbComp`, `QueryImpl`, `perfectCompleteness`, `rbrKnowledgeSoundnessWorstCaseWith`
  (VCVio and ArkLib).** `ProbComp σ` is VCVio's type of a probabilistic computation returning
  a `σ`, and `QueryImpl []ₒ (StateT σ ProbComp)` an implementation of the (here empty) oracle
  the protocol shares, with a state; the security games of ArkLib are run with them.
  `perfectCompleteness init impl R S` says the honest prover, on an input in relation `R`,
  makes the verifier accept with an output in `S`, with probability 1.
  `rbrKnowledgeSoundnessWorstCaseWith … R S witMid E K err` is ArkLib's round-by-round knowledge
  soundness for a *named* extractor `E` and knowledge state function `K`: at each verifier
  challenge `i` a cheating prover moves `K` from false to true with probability at most
  `err i`, whatever the transcript so far.
- **The master theorems as built.** Copied from `LeanerVM/Protocol/Spine/Compose.lean:162-177`:

  ```lean
  theorem piop_perfectCompleteness (P : Phases I) (C : P.Complete) {σ : Type}
      (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
      (leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I) :=
    C.toDef.complete init impl
  theorem piop_rbrKnowledgeSoundness (P : Phases I) (S : P.Security) {σ : Type}
      (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
      (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel I)
        (Seam.done I) S.toDef.witMid (piopExtractor P S) (S.toDef.kSF init impl)
        (piopError P) :=
    S.toDef.rbr init impl
  ```

## A. Inventory: which document says what

Columns. BP: the blueprint. ST: the status. TB: the tracker body. HC: the hole comment. OC:
other comments (four on issue 12, one on issue 3, one each on pull requests 39, 42, 43). RS,
RL, RP: the review handoffs of the spine, of Layer 1, of the public-input phase. AR:
`architecture.md`. LT: `leanvm-target.md`. PR: pull-request descriptions. II: intention issues.
A cell gives line numbers; a dash means absent.

| Kind of fact | BP | ST | TB | HC | OC | RS | RL | RP | AR | LT | PR | II | Elsewhere |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Targets: the theorems wanted | 11-31, 543-548, 1124-1130, 1218-1227, 1247-1250 | 23-25, 81-83 | 12, 14 | 16, 176, 190 | issue 12 comment of 09-28 | 49-62 | - | 85-98 | 261-275 | 123 | 58 | - | `README.md:19-33` |
| Signatures | 442-554 and every layer, 633-1250 | 41-51, 98, 101 | 14, 29-34 | every section | the comments on 39, 42, 43 and on issue 3 | 66-249, 493-649, 667-766 | 28-43 | 552-626 | - | - | 58, 59, 60 | 28, 31, 33, 37 | - |
| Conventions | 308-335 | 214-268 | 96 | - | - | - | - | - | 48-57 | - | - | - | `CONTRIBUTING.md:44-121`, `AGENTS.md:57-82` |
| Acceptance tests, tests per unit | 1261-1358 and the "Tests:" paragraph of each layer | by reference | - | 22, 38, 71, 85, 97, 125, 152, 166, 180, 194 | - | 466-475 | 91-98 | 648-659 | - | - | - | 28 to 37, last paragraph | - |
| Coverage: what is built | leaks at 260, 339-345, 591, 611, 1105, 1143, 1459 | 15-83, 85-109 | 14, 20-40 | 9, 131-142 | issue 12 comment of 09-28 | 30-47 | 24-43 | 64-83 | - | 112-128, not updated | 58, 59, 60 | - | `README.md:19-33`, `docs/README.md:31-47`, `leanth-reuse.md:411-445` |
| Frontier: what can start | 1455-1470 | 134-164 | 42, 80-85 | - | issue 12 comment of 09-28 | - | - | - | - | - | - | - | - |
| Claims: who is doing what | - | 92-97 | 23-28 | "Claim" line of each section | three comments of 09-20 and 09-24 | - | - | - | - | - | - | 28, 31, 33, 37 | the label `hole` |
| Open pull requests | 598-610, column "Existing work" | 111-132 | 44-57 | - | same comments | 406-422 | - | - | - | - | GitHub | - | - |
| Findings against the leanVM sources | cited at 193, 323-326, 973, 1275, 1289-1291, 1330; stated in full at 322, 1053-1062 | 279-330 | 85 | 66, 80, 120, 176 | - | 283-322 | 112-169 | 239-375 | - | 57-62, one finding | 60 | - | `leanisa-status.md:634-915` |
| Findings about the libraries and Lean | 281-284, 297-298, 569-570 | 332-432 | 84-85 | - | - | 355-381 | - | - | - | - | - | - | `dependencies.md:52-55, 81-88`, `development.md:56-57`, `tests/README.md` |
| Decisions, taken and pending | 556-563 and, silently, the conventions | 212-277 | 87-89 | 13, 24, 67 | issue 12 comment of 09-28; the comment on issue 3 | 34-38 | - | 71, 568-573 | - | - | 60 | - | `leanth-reuse.md:484-489` |
| Upstream ledger | 253-267 | 166-184 | 59-74 | per section | - | - | - | - | - | - | 58 | 31 | `leanth-reuse.md:447-458`, `dependencies.md:47-51` |
| Upstream watch | 598-614, column "Existing work" | 186-210 | 8, 76-78 | 40, 111, 154, 168, 182 | - | - | - | - | - | - | - | 28 to 37 | `leanth-reuse.md:461-482` |
| Record of reviews | 1337 | 124-132, 438-536 | 14 | 3 | issue 12 comment of 09-28 | whole | whole | whole | - | - | 59, 60 | - | `docs/README.md:31-47` |
| How to work | 1455-1515 | 7-11, 188 | 18, 91-96 | 3 and every "Claim" line | - | - | - | - | - | - | - | - | `CONTRIBUTING.md`, `AGENTS.md`, `development.md`, the labels |
| Pins and dependency contracts | 160-306, 1517-1549 | 10-11, 161-163, 565-622 | 3-4, 14 | - | - | 3-12 | 3-14 | 8-19 | - | 1-24 | 58, 59, 60 | - | `dependencies.md`, `upstreams.json` |
| The list of public names | 1360-1429 | 41-51, 72-76 | 14 | - | issue 12 comment of 09-28 | 667-714 | - | 481-525 | - | - | 58, 59, 60 | - | - |
| Prior work and reuse | 170-174, 348-353, 1545-1549 | 206-210 | - | - | - | - | - | - | - | - | - | 28 to 37 | `leanth-reuse.md` |

Reading the table. Every row but one has at least three filled cells. The three worst cases:

- **Signatures** are written in nine kinds of place. A unit such as the bus phase has four
  specifications: the hole table (`protocol-blueprint.md:606`), the Layer 6 sketch
  (`:949-979`), the hole comment (`issue-12-comment-5833669972.md:61-73`) and the checklist line
  (`issue-12-body.md:30`). Section B shows that they give three different types for it.
- **The upstream ledger** is written three times, with different columns and different rows.
  The blueprint's has nine rows about ArkLib and a column "Action"
  (`protocol-blueprint.md:257-267`). The status's and the tracker's have twelve rows: they drop
  the context-lifting row and add four about Clean and leanISA
  (`protocol-status.md:171-184`, `issue-12-body.md:61-74`). The column "Needed by" names layers
  in the blueprint and holes in the other two.
- **The record of a review** is written four times: the handoff's disposition table, the
  status's survey record (`protocol-status.md:438-536`), the tracker body
  (`issue-12-body.md:14`), and one line of `docs/README.md:38-47`.

Facts that exist only on the tracker, against the tracker's own claim to hold nothing of its
own: the tests of nine units (`issue-12-comment-5833669972.md:38, 71, 85, 97, 125, 152, 166,
180, 194`), for example "`blake2sBytes` on the RFC 7693 test vector" (`:166`) and "every pinned
coding parameter with an achievability witness" (`:152`); the remark that leanVM's chain is
Merkle-Damgård and not a duplex sponge, "so the transfer theorem, not the sponge, is what
applies" (`:182`); the review order of the open pull requests (`issue-12-body.md:48-57`); and
what the spine asks of the Flock roadmap, which is a comment on issue 3 (id 5872015596).

## B. Contradictions and stale statements

Each item quotes both sides. "Today" means `main` at `b435631` and GitHub on 2026-09-29.

### B.1 The status, after the merge of pull request 60

| # | The status says | Today |
| --- | --- | --- |
| 1 | `protocol-status.md:3-6`: "as of `main` at `f4d858c` (Layer 1, PR #59, merged on 2026-09-29) ... together with ... the public-input phase (hole P5) as built on the branch `feat/protocol-public-input` (pull request #60); this snapshot accompanies that branch" | `main` is `b435631`, "feat(protocol): the public-input phase (#12) (#60)"; pull request 60 merged on 2026-09-29 at 15:57 UTC (`probes/docs-debt/pr-60.json`) |
| 2 | `:58-60`: "The public-input phase (hole P5) is built, on the branch `feat/protocol-public-input`, pull request #60, a draft" | merged; `LeanerVM/Protocol/PublicInput.lean` is on `main` (400 lines) |
| 3 | `:101`: "built, draft #60 ... lands when #60 merges" | landed |
| 4 | `:119`: "#60 (draft) ... mark ready, review and merge" | merged |
| 5 | `:146-148`: "is the draft #60 ... #60 ticks P5 on the dashboard when it merges" | merged, and the box is not ticked (`issue-12-body.md:32`) |
| 6 | `:161`: "ArkLib `main` is 246 commits past `dca90385`" | 347 commits on 2026-09-29 (`git rev-list --count dca90385..origin/main` in the sibling checkout after `git fetch origin`; `origin/main` was `7653a901e`). The figure 246 is exact for `66f39b4`, the revision the status names at `:345` |
| 7 | `:177`: "staged in `ToCompPoly/{Stacking,AmbientStacking,Claims}.lean` (#59)" | there is no `ToCompPoly/Claims.lean`; the claim record is `LeanerVM/Protocol/BlockClaims.lean`, as the same file says at `:50` and `:415-420` |
| 8 | `:190`, table head: "State (checked 2026-09-24)", in a file whose head says "checked on 2026-09-29" (`:4`) and whose first row is dated 2026-09-28 | mixed dates in one table |
| 9 | `:192`: ArkLib pull request 615 "open since 2026-09-08"; `:193`: ArkLib 818 "open since 2026-09-04"; `:204`: Clean 446 "draft since 2026-08-16" | created 2026-07-07, 2026-08-31 and 2026-08-07; the dates given are the dates of last update (`probes/docs-debt/upstream/*.json`) |
| 10 | `:183`, `:203`: Clean pull request 464 is "draft, the maintainer's" | not a draft (`isDraft: false`), review required; its author is the owner of leanerVM, so "the maintainer's" is ambiguous |
| 11 | `:205`: VCVio 784 "merged 2026-09-24" | merged 2026-09-23 at 00:41 UTC |
| 12 | `:178`: "ArkLib #4 (Merkle)" as the upstream issue of the WHIR and Merkle entry | ArkLib issue 4 was closed as "not planned" on 2026-09-27, its tracking transferred to VCVio issue 571: "The Merkle implementation and its security work are maintained upstream" (`probes/docs-debt/upstream/ArkLib-4-comments.txt`). See §B.9 |
| 13 | `:281-283`: "**F** = Rust versus specification, continuing the leanISA numbering where the subject overlaps" | in the leanISA status the letter for Rust against the specification is `R`, and `F` is "the roadmap's or the architecture's targets" (`leanisa-status.md:636-640`). Nothing is continued: both files have their own `F1` to `F10` |
| 14 | `:212`, heading "Decisions pending", over a section of which 58 lines out of 66 (`:212-269`) are decisions taken | the blueprint's rule is that a decision taken is "removed from the status file and the dashboard" (`protocol-blueprint.md:1506-1507`) |
| 15 | `:179`: ArkLib's coding-theory track, "the #907 slices landing on `main`"; the hole comment says the same, "landing daily on `main`" (`issue-12-comment-5833669972.md:154`) | ArkLib issue 907 was closed as completed on 2026-09-26 (`probes/docs-debt/upstream/ArkLib-907.json`) |

### B.2 The tracker body, against `main` and GitHub

| # | The tracker body says | Today |
| --- | --- | --- |
| 1 | `issue-12-body.md:21`: "- [ ] **L1 — Layer 1 ...** Generic half in draft #18 (rebase onto `main` pending ...) ... *in review*; nothing lands before #18 does" | Layer 1 merged as pull request 59 (`f4d858c`); pull requests 18, 38, 40, 41 are closed |
| 2 | `:32`: "- [ ] **P5 — the public-input phase ...: one challenge, one pooled column claim per line, the prover sends nothing.** — *open; the smallest phase, a good first hole*" | built and merged, and the prover sends a message: `PublicInput.pSpec` is "the challenge in `E`, then the prover's values, a `List E`" (`protocol-status.md:101`; blueprint `:1013`) |
| 3 | `:44-57`, "Open pull requests (2026-09-28)": eight rows, among them 18 (draft), 40, 38, 41 | open today: 39, 42, 43 only |
| 4 | `:82`: "#18 must be rebased and landed before the five pull requests stacked on it can get CI" | 18 is closed; its content landed through 59 |
| 5 | `:83`: "The status file at `main` still describes the spine as on its branch and in review; the next pull request that lands a hole rewrites it whole" | the status was rewritten twice since; the sentence is about a state two merges old |
| 6 | `:40`: "- [x] **VCVio controls for K3 and P7.** #29, #30 — *landed upstream*" | issues 29 and 30 are still open, although the blueprint says an intention issue "is closed by the pull request that lands the slice" (`protocol-blueprint.md:1491`) |
| 7 | `:85`: "Findings that bind a definition: F1, F3, F5, F6, F8, F11" and "new are S14 ..., E7 ..., E8 ... and E9" | the status has since added the order of equal-size blocks (F17), which binds the adaptor's layout, the two public-input checks (F18), which binds the compiled verifier, and nine findings about Lean |
| 8 | `:89`: decisions up to 14 | decision 15 (the transcript of the public-input phase) was taken on 2026-09-29 (`protocol-status.md:256-268`) |
| 9 | `:6`: "This issue holds nothing that is not in them" | see the end of section A |
| 10 | `:1`: "Revision 2 (2026-09-24, *The spine*) is on `main`" | the blueprint carries no revision number or date; "revision 2" is defined nowhere |
| 11 | rendered body: "ArkLib #1", "ArkLib #4", "leanth #16", and "(sumcheck; #3 there is closed)" | GitHub links them to pull request 1 and issues 4, 16 and 3 of leanerVM: the wrong repository (`probes/docs-debt/issue-12-body.html`; the same for "ArkLib #1" once and "ArkLib #4" twice in the hole comment) |

The Layer 1 review left exactly these two edits for GitHub: "On GitHub: the L1 line and the open
pull request table of the dashboard #12" (`docs/reviews/protocol-layer1.md:211`). Neither was made
(items 1 and 3 above): a review handoff whose tracker edits are not applied leaves the tracker
wrong while the handoff's disposition table reads "met".

### B.3 The hole comment, against the blueprint and the code

The comment says of itself that the spine's section "is kept for the record" and that four
sections "were rewritten on 2026-09-28" (`issue-12-comment-5833669972.md:3`). The other eight
were not, and they are the specifications of the units still to be built.

| # | The hole comment says | The blueprint or the code says |
| --- | --- | --- |
| 1 | `:66`, bus phase: "`busPhase I (G : Gkr.Def) : Phase.Def I Unit (BusOut I) (busSpec I) (M3Holds I) (Seam.bus I)`" | `Phase.Def` takes the instance and two statement types (`Phase.lean:37`); the bus phase is `Phase.Def I I.Stmt (I.Stmt × BusOut I)` (`Compose.lean:76`). There is no `Gkr.Def` and no `busSpec`; the comment's own note says so at `:9` |
| 2 | `:80`, table sumcheck: "`tableSumcheck I (S : Sumcheck.Def) : Phase.Def I (BusOut I) (TableOut I) (tableSpec I) (Seam.bus I) (Seam.table I)`" | the same: six arguments where there are three, `Sumcheck.Def` and `tableSpec` do not exist |
| 3 | `:120`, opening phase: "`openingPhase I (B : Batch.Def) (S : Sumcheck.Def) : Phase.Def I (FlockOut I) Unit (openSpec I) (Seam.flock I) (fun _ _ ↦ True)`", and "`Claim.toWeighted` (a `BlockClaim` of #38 ...)", and "Consumes: ... `Pool`" (`:123`) | no `Pool` (`:9` of the same comment); the Layer 1 review established that a phase over an abstract instance cannot form a `BlockClaim` and that the step is `ColumnClaim.holds_iff_weighted` (`protocol-layer1.md:28`, `protocol-status.md:127-129`) |
| 4 | `:66`: "`leaf_decomposition` (specification (5.4) ...)" | "equation (5.4)" does not exist; it is equation (2) of section 5.4 (`protocol-layer1.md:36`, `protocol-status.md:303`) |
| 5 | `:32`, `:148`, `:162`: modules under `LeanerVM/Protocol/Generic/` | the convention names `ToArkLib/`, `ToCompPoly/`, `ToVCVio/` (`protocol-blueprint.md:329`); the blueprint's Layers 5 and 11 name `ToArkLib/GrandProduct.lean` and `ToArkLib/Whir.lean` (`:916`, `:1152`) |
| 6 | `:92-94`, public-input phase: "the prover sends nothing" | blueprint `:1030-1033`: "The prover sends, as one message, the values at `r` of the lines whose value is sent"; decision 15 |
| 7 | `:190`, base theorems: "composed as `verify_knowledgeSound` ∘ `knowledgeSound_of_refinement`" | the same comment at `:9`: "`Refinement.map_option_valid` replaces `knowledgeSound_of_refinement`"; blueprint `:1253` |
| 8 | `:178`: "Consumes: the spine's six `ProtocolSpec`s" | the spine fixes one schedule, the commit phase's; the others "travel with each `Def`" (`protocol-blueprint.md:419-422`; the comment's own note at `:9`) |
| 9 | three ways to claim: "by assigning yourself" (`:42, 73, 87, 127, 156, 170, 184, 196`), "by assigning yourself and commenting; slices go through `[Intention]` issues as usual" (`:26`), "by commenting on this issue" (`:59, 100, 113`) | the blueprint: "comment on #12 ... No `[Hole]` or `[Intention]` issue is opened for it" (`:1487-1489`); the label `hole` on GitHub: "claim it by assigning yourself" |

The closed `[Hole]` issue of the public-input phase (issue 50) gave yet another specification:
"its `Phase.Security` with error `2/|E|`" (`probes/docs-debt/issue-50-body.md`), where the
blueprint and the code have `1/|E|`.

### B.4 The blueprint against itself: the per-layer sketches and the spine

The blueprint announces the difference in one sentence, "where a signature below says
`(prog) (s)`, read `leanIsaInstance prog s`" (`protocol-blueprint.md:622`), and for Layer 10
says that the master theorems "below are the spine's" (`:1104-1105`). The sketches differ by
more than that reading.

| # | Sketch | Spine section of the same document, and the code |
| --- | --- | --- |
| 1 | Layer 6, `:956-964`: "`def busPhase (prog) (s) : OracleReduction []ₒ (StmtIn := Unit) ... (StmtOut := BusOut)`" and "`structure BusOut where ζ : Fin μ_bus → E ; rem : Fin 3 → E ; pool : List Claim ; α : Fin 4 → E ; β : E`" | `:481`: "`structure BusOut I where (linear : List (LinearClaim I)) (columns : List (ColumnClaim I))`", and `:560`: "The seams carry *claims*, not challenges". Code: `Seams.lean:130-135`, quoted above |
| 2 | Layer 7, `:988`: "`def tableSumcheck (prog) (s) : OracleReduction []ₒ (StmtIn := BusOut) … (StmtOut := BusOut × ColumnClaims)`" | `:533`: "`table : Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)`" |
| 3 | Layer 9, `:1075-1085`: the docstring says the structure supplies "the `Phase.Def` and `Phase.Security` at the flock seam"; its fields are "`reduction : OracleReduction []ₒ (StmtIn := ColumnClaims) ... (StmtOut := WeightedClaim)`", "`relIn`", "`relOut`", "`rbrKnowledgeSoundness : reduction.verifier.rbrKnowledgeSoundnessWorstCase … flockError`"; "`limbColumns : Column μ → Fin 18 → Column (s.τ 5)`" with `s` unbound | `:535`: "`flock : Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I)`"; a phase's security is the named-extractor form (`:332`, `:512`) |
| 4 | Layer 10, `:1109-1110`: "`structure Weight (μ) where (onCube : ETable μ) (mle : (Fin μ → E) → E) ...`", "`structure WeightedClaim (μ) where (W : Weight μ) (c : E)`" | `:479-480`: "`structure Weight μ where (onCube : CMlPolynomialEval E μ) (mle : Vector E μ → E) ...`", "`structure WeightedClaim I where (weight : Weight I.μ) (value : E)`". Code: `Seams.lean:103-120` |
| 5 | Layer 10, `:1116-1130`: "`def leanVmPiop (prog) (s) (input) (flock : FlockInterface prog s) : OracleReduction []ₒ (StmtIn := PublicInput) (OStmtIn := fun _ : Empty ↦ Unit) (M3Witness prog s) ...`", "`theorem piop_rbrKnowledgeSoundness (hs : s.Admissible prog) : (leanVmVerifier prog s input flock).rbrKnowledgeSoundness init impl (m3Relation prog s) Set.univ (piopError s)`" | `:541-547` and the code quoted above: over `(P : Phases I) (S : P.Security)`, no admissibility hypothesis, `rbrKnowledgeSoundnessWorstCaseWith`, `M3Rel I`, `Seam.done I`, a named extractor |
| 6 | Layer 4, `:894-895`: "`theorem sumcheck_rbrKnowledgeSoundness : (sumcheck V).verifier.rbrKnowledgeSoundnessWorstCase ...`"; Layer 5, `:936-937`, the same form for the grand product | convention *Holes*, `:332`: the form "`rbrKnowledgeSoundnessWorstCaseWith` ..., so the extractor is named, not merely shown to exist" |
| 7 | Layers 6, 7, 10 need "Layer 5's `Gkr.Def`" (`:952`), "Layer 4's `Sumcheck.Def`" (`:984`), "`Sumcheck.Def` and `Batch.Def`" (`:1104`); the hole table and the picture name them too (`:397`, `:598-602`) | no such shape exists in the spine section or in the code (`grep` over `LeanerVM/` and `tests/`: no match); a generic component is a `Component.Def` |
| 8 | Layer 2, `:768-773`: "`flushes : List (Direction × Vector (MvPolynomial (Fin width) F) 16)`", "`count : List (Fin width)`" | `:458`, `:462`: "`flushes : (j) → List (Side × Vector (CMvPolynomial (width j) K) 16)`", "`counts`". `Direction` is also ArkLib's name for the direction of a message, listed as such at `:234` |
| 9 | used and never defined in the document: `Claim` (`:963`, `:1111`), `ColumnClaims` (`:988`, `:1078`), `LeafLayout` (`:955`), `StackLayout` (`:1111`), `M3Witness` (`:1117`), `m3Relation` (`:1126`), `commitPhase` (`:1119`, `:1133`) | the spine has `ColumnClaim`, `Layout`, `M3Rel`, `commitDef` |
| 10 | heading `:617`: "The build: the spine, then fourteen layers" | `:620`: "The spine (hole S) is built after Layer 0". The count is right (Layers 0 to 13); the order in the heading is not |
| 11 | `:1474-1475`: "This document ... does not record history, status, or who is doing what" | it does: "done on the spine's branch" (`:611`, `:1459-1460`), "The port is done and closes hole C1" (`:1143`), "(#13, taken)" (`:221`), "the `[Hole]` issues were folded there on 2026-09-25" (`:591`), "`L1` groups the leaves of Layer 1 already in flight" (`:591-592`), the column "Existing work" with open pull requests (`:598-614`), "a rule in `scripts/check-layers.sh` is still to be written" (`:1344-1345`) |
| 12 | `:592-593`: "the generic holes carry the ledger letters of the ArkLib work they will become" | the generic units are coded `G1` to `G6`; the ledger's letters are `A` and `C`. The sentence has no reading under which it is true |

### B.5 The blueprint against the repository

The probe `check_interface_names.py` looked up the 194 names of the list "Interfaces supplied
to later work" (`protocol-blueprint.md:1366-1416`): 127 are declared, 3 are structure fields,
64 are absent. All 64 belong to units not yet built, which is expected. The four names the
task asked about:

| Name | Result |
| --- | --- |
| `Blocks.stack_eval₂` | exists: `LeanerVM/Protocol/ToCompPoly/Stacking.lean:345` |
| `Toy.layout` | exists: `LeanerVM/Protocol/Spine/Toy.lean:60` |
| `BlockClaim` | exists: `LeanerVM/Protocol/BlockClaims.lean:54` |
| `Ensemble.toM3`, listed under the heading "Spine:" (`:1369`) and again under "Arithmetization:" (`:1398`) | absent; it is Layer 2's, not built, and not the spine's |

What the probes did find:

| # | The blueprint says | The repository |
| --- | --- | --- |
| 1 | `:1419`: "Everything not listed is a proof, a helper, or a test" | of 333 non-private declarations under `LeanerVM/Protocol/`, 198 are not in the list, among them definitions the blueprint itself says later work reads: `PublicInput.check`, `pooled`, `prover`, `verifier`, `pSpec` (blueprint `:1049-1051`: "Layer 12 reads those"), `publicInputComplete`, `publicInputSecurity`, and `Component.sendSpec`, `sendExtractor`, which `commitSpec` and `commitExtractor` abbreviate (`probes/docs-debt/unlisted_public.out`) |
| 2 | `:343-344`: the spine's generic modules are "`Oracles`, `Component`, `KnowledgeAppend`, `PassThrough`, `SendOracle`, `Refinement`" | `LeanerVM/Protocol/ToArkLib/` also holds `GuardedVerdict.lean` and `KeepOracles.lean`, which the pass-through and send components now import (`protocol-status.md:74-75`); `KeepOracles` appears nowhere in the blueprint |
| 3 | `:1306-1307`, acceptance test 14: "Witness: `bytecodeColumn_slot` on a two-instruction program" | the Layer 1 review showed that `bytecodeColumn_slot` "restates the definition and does not pin the bit order" and that the statement which does is `bytecodeColumn_answer_boolVec` (`protocol-layer1.md:30, 82-89`). Both exist (`FixedColumns.lean:85, 97`); the test with reversed slot bits is at `tests/LeanerVMTests/Protocol/FixedColumns.lean:99` |
| 4 | `:220`: leanISA supplies "`MemMsg`, `StateMsg`, `BytecodeMsg`" | `MemMsg` and `BytecodeMsg` exist (`Arithmetization/Channels.lean:153, 164`); `StateMsg` does not |
| 5 | `:1280`, acceptance test 5: "distinguished by `leanIsaTables` flush polynomials" | no `leanIsaTables` in the code or in any other document |
| 6 | `:603`, `:608`, `:609`, `:610`, column "Produces": the opening phase produces "`Weight`, `WeightedClaim`, `openingPhase`"; the Flock phase produces "`FlockOut`, ..." | `Weight`, `WeightedClaim` and `FlockOut` are the spine's and are on `main` (`Seams.lean:103, 116, 147`). A reader, or a script, counting produced names takes the opening phase for three-quarters built (`probes/docs-debt/coverage_from_blueprint.out`) |
| 7 | `:1512`: "the reviewer runs the `leanerVM-review` skill's three passes" | the skill is `adversarial-review` (`.claude/skills/adversarial-review/SKILL.md`), and it is what the status and the three handoffs call it (`protocol-status.md:438, 479, 506`). Moreover `.claude/` is git-ignored (`.gitignore:9`), so neither this skill nor `lean-spec-authoring`, which "sets the rules" at `:178`, is in the repository a contributor clones |
| 8 | `:601`, and `protocol-status.md:95`, `issue-12-body.md:26`: the fingerprint unit is "fingerprint, Lemma 5.1, the collision bound" | the specification has Theorem 5.1 (the collision bound, `05-arithmetization.tex:36`) and Lemma 5.2 (a product identity is a multiset identity, `:40`); its environments share one counter per section (`doc/leanvm/preamble/theorems.tex:4-6`). There is no Lemma 5.1. Layer 5 of the blueprint has it right (`:921, 924`) |
| 9 | `:1440`: "virtual columns here (finding F3 of the status file)" | in the protocol status that code is "one root for push and pull" (`protocol-status.md:309-310`). The finding meant is the leanISA status's: "the BLAKE2S value limbs are virtual columns in Flock's stack in the Rust; ordinary columns here" (`leanisa-status.md`, section "Targets") |
| 10 | `README.md:32-33`: "no proof-system claim has landed" | the spine with its two conditional master theorems, Layer 1 and the public-input phase with `publicInputSecurity` are on `main` |
| 11 | `docs/README.md:38-47`: three handoffs "whose findings the branch now meets" | the three branches are merged |
| 12 | convention *The wall*, `:331`: "imports nothing from `LeanerVM/Arithmetization/`; the only exceptions are the fixed columns (`FixedColumns.lean`, Layer 1), the Clean bridge (Layer 2), the adaptor (Layer 3), the compiled verifier (Layer 12) and T4 (Layer 13)"; acceptance test 25, `:1343-1344`: the `grep` "lists the exceptions of convention *The wall* only" | `LeanerVM/Protocol/Basic.lean:3` is `public import LeanerVM.Arithmetization.Basic`. The module is an empty placeholder (a docstring and an empty `public section`) that nothing under `LeanerVM/` or `tests/` imports, so no phase sees the arithmetization through it; but the `grep` the blueprint names as the witness of the import rule returns it, and the rule as written is false of `main` |
| 13 | convention *Generic code*, `:329`: "Comments everywhere are brief and self-contained: they cite the specification, never this roadmap" | `LeanerVM/Protocol/Field.lean:18` "Protocol roadmap Layer 0 (`docs/roadmap/protocol-blueprint.md`)", `:29` "(leanISA status finding P3)", `:31` "every error bound of the roadmap", `:37` "(roadmap convention *The oracle*)", `:37, 66` "Layer 11"; `tests/LeanerVMTests/Protocol/Field.lean:9` "Protocol Layer 0 tests". Layer 0 predates the rule (merged 2026-09-11 in `51021d9`); every later module of `LeanerVM/Protocol/` follows it (the same `grep` over the other 24 files finds nothing) |

### B.6 The blueprint against the leanISA blueprint and `architecture.md`

| # | The proof-system blueprint | The other document |
| --- | --- | --- |
| 1 | `:1247-1248`: "`theorem baseVerifier_extractsExecution (fs bcs mca flock) (h : verify prog input proof = true) : except with probability niError, ∃ t, ValidExecution prog input t`", which "composes ... `constraintSoundness`" (`:1253-1254`) | `leanisa-blueprint.md:1163`: "`theorem constraintSoundness (hwf : WellFormedBytecode prog) (h : SatisfiedBy prog input w) : ...`". `architecture.md:224-228`: "Both directions are stated for well-formed programs ... a hypothesis of each, since the constraint system enforces neither". `leanvm-target.md:57-62` records why: a bytecode whose sentinel slot holds a `JUMP` "admits accepted walks that execute the sentinel". The base theorem as written has no such hypothesis and cannot be obtained by the composition it names |
| 2 | `:1249-1250`: "`theorem baseProver_complete (hfill : HasFillBlocks prog) ...`", which "composes `constraintCompleteness`" (`:1255`); `:222` lists "`constraintSoundness`, `HasFillBlocks`, `constraintCompleteness`" as what is consumed | `leanisa-blueprint.md:1156-1166`: `constraintCompleteness` takes `WellFormedBytecode prog`, a structure with two fields, `sentinelSafe` and `hasFillBlocks`. `HasFillBlocks` alone does not give it |
| 3 | `:147-148`: "witness generation from an execution (T2): the honest prover here starts from an `EnsembleWitness`"; completeness composes leanISA's existence theorem, the completeness half of arithmetization and ISA equivalence (T1) (`:1255`) | `architecture.md:273-275`: the completeness dual of base proof extraction and completeness (T4) "composes T2 with the honest prover" |
| 4 | the hole comment repeats items 1 and 2 word for word (`issue-12-comment-5833669972.md:190`) | - |

Item 1 is more than a wording issue and is a finding in section H. Whether the intended
theorem takes `WellFormedBytecode prog` as a hypothesis, or the compiled verifier checks it on
the public program, is a technical decision for the orchestrator; this dossier only records
that the documents disagree and that the statement as written is not provable by the named
composition.

### B.7 How work is tracked: the text against practice and against the owner's wish

| # | Text | Practice |
| --- | --- | --- |
| 1 | `protocol-blueprint.md:1487-1488`: "To claim a hole, or a slice of one, comment on #12"; `issue-12-body.md:18, 93` the same | the owner now wants issue bodies updated rather than comments added (the task's statement). A contributor without write access cannot edit the body: "I lack label/dashboard permissions" (`issue-12-comment-5749712916.md`, and again in the two later comments). The four live claims are in the bodies of intention issues 28, 31, 33, 37, not in comments on issue 12 |
| 2 | `:1489-1491`: an intention issue is titled "`[Intention]: protocol - <hole>: …`" | all ten intention issues are titled by layer: "[Intention]: protocol - Layer 4: ..." |
| 3 | `:1466-1470`: a pull request's description names "the hole, the sources and pin, the category of each new definition, the ledger entries it touches, and the T4 obligation it feeds" | the open pull requests 39, 42, 43 name a layer and an intention issue; none names a hole, a category, a ledger entry or the target (`probes/docs-debt/pr-39-body.md`, `pr-42-body.md`, `pr-43-body.md`) |
| 4 | `:1511`: "Pull requests carry `awaiting-review` when the author is done" | 39, 42 and 43 carry no label; their author asked three times for it to be set |
| 5 | `:1480-1484`: issue 12 is "the layer checklist with one of *open / claimed / in review / landed* per layer" | the checklist is per hole (`issue-12-body.md:16-40`); the status uses a fifth state, "built, draft" (`protocol-status.md:101`) |
| 6 | `:1498-1501`: "Durable source discrepancies are also recorded in `leanvm-target.md`"; `protocol-status.md:281`: findings are "numbered for citation from pull requests and `docs/leanvm-target.md`" | `leanvm-target.md` records one discrepancy, the sentinel (`:57-62`), and cites no number. None of the proof system's twenty-seven findings against the sources is there |
| 7 | `CONTRIBUTING.md:16-19`: "For a large contribution ... open a design issue first" | the blueprint: no issue is opened for a hole (`:1488-1489`) |
| 8 | `protocol-status.md:553-554`: the reading audit of the stacked pull requests "is recorded on the dashboard's history" | a fact kept in the edit history of an issue body is not retrievable by a reader of the repository |

### B.8 Decisions

Decisions 1 to 5 were stated as questions in the first version of the status (commit
`51021d9`). Today the status says only "Decision 1 was taken with #13, and decision 3 with
revision 2" (`protocol-status.md:214`): what decision 1 decided is no longer written anywhere
in the current documents, and decisions 6 to 10 exist only as outcomes (`:217-224`). Two
further choices "were made" without a number (`:224-227`: the seams carry claims only; the
schedules travel with the definitions). The blueprint cites "decision 8" and "decision 6"
(`:557, 560`) and defines neither. The leanISA roadmap numbers its own decisions from 1, so
"decision 13" is "public lines, not cells" here and "the program is a parameter" in the title
of issue 22, and `leanth-reuse.md:485`, a proof-system document, cites "Decision 14" of
leanISA without saying so.

### B.9 The upstream ledger's row on Merkle trees

The blueprint's ledger says of ArkLib at the pin: "A7 WHIR, Merkle, BLAKE2s | absent (only
coding-theory lemmas) | Layer 11 | Written here" (`protocol-blueprint.md:265`), and Layer 11
plans `merkleRoot` and `merkleVerify` locally (`:1179-1182`). The blueprint's list of what is
consumed from VCVio has one row, `SampleableType` (`:251`), and the survey record lists the same
(`protocol-status.md:607-609`).

Fact, at the pin `f9dc47d9` of VCVio (the revision leanerVM builds against, through ArkLib):
the directory `.lake/packages/VCVio/VCVio/CryptoFoundations/MerkleTree/` holds nineteen modules
(`Inductive/{Defs,Completeness,Binding,Extractability,Extractor,QueryBound,Uniqueness}.lean`,
four under `Inductive/Batch/`, six under `Addressed/`, two under `Vector/`), with no `sorry` in any of them
(`grep -rn sorry`: 0 lines), for example `theorem functional_completeness` at
`Inductive/Completeness.lean:41`. And ArkLib's Merkle tracker, which four documents cite as the
upstream of this work, was closed on 2026-09-27 in favour of VCVio issue 571.

Inference, not verified: that this library fits leanVM's Merkle trees (BLAKE2s, leanVM's leaf
encoding and pruned paths). Verifying it means reading `Inductive/Defs.lean` against
`crates/fiat_shamir/src/merkle.rs:14-67`; it belongs to the review of Layer 11. What is
established here is that the ledger and the survey record do not mention a library that is in
the build, and that the upstream destination they name no longer exists.

### B.10 Cross-references checked, with the negative results

| Check | How | Result |
| --- | --- | --- |
| Local Markdown links and anchors, the 24 Markdown files tracked at `b435631` | `check_anchors.py`, anchors computed as GitHub does | 150 links, 0 broken |
| The repository's own link check | `python3 scripts/check-docs.py` | passes. It checks files only, not anchors, not external links, and matches per line |
| Citations into leanVM at the pin, blueprint and status | `check_leanvm_citations.py` | 81 distinct citations; every one resolves to a file at `a386121f` with the cited range inside it and plausible first lines (the full list is `probes/docs-debt/leanvm_citations.out`). 22 are ambiguous as written, because the file name exists in two or more crates: `transcript.rs`, `witness.rs`, `lib.rs`, `filler.rs`, and the specification's file names, which also exist under `doc/leanvm/drafts/` |
| Citations into the pinned libraries | `check_lib_citations.py` | 43 declarations; 40 at the cited file and line (within two lines). Three drifted: `Direction` is in `OracleReduction/Prelude.lean:66`, not `ProtocolSpec/Basic.lean`; `fsChallengeOracle` is an alias at `ProtocolSpec/Basic.lean:854`, not in `FiatShamir/Basic.lean:114-138`; `Sumcheck.Domain` is `ProofSystem/Sumcheck/Domain.lean`, which the blueprint's list reads as under `Spec/` |
| References to numbered acceptance tests | every "acceptance test N" and "test N" of the eight documents read against the blueprint's list | 30 references, all to the intended test |
| Witnesses named by acceptance tests 13, 15, 24, 26, 27, 28 | `grep` in `tests/LeanerVMTests/Protocol/` | present: `FixedColumns.lean:37-51`, `Stack.lean:83-90`, `Spine.lean:158-159`, `Spine.lean:113`, `Spine.lean:32-52`. Test 14 names the wrong witness (§B.5, item 3) |
| The spine sketch against the code | `PublicLine`, `M3Instance`, `BusOut`, `Weight`, `WeightedClaim`, `Phases`, the three theorems of `Compose.lean` read side by side with `protocol-blueprint.md:442-554` | they agree |
| The leanISA names the blueprint consumes (`:215-222`) | looked up in `LeanerVM/` | 30 of 35 exist; `constraintSoundness`, `constraintCompleteness`, `HasFillBlocks` are leanISA Layer 10, not built; `StateMsg` and `leanIsaTables` exist nowhere (§B.5) |
| The import rule of the proof system (acceptance test 25's own witness) | `grep -rn 'import LeanerVM.Arithmetization' LeanerVM/Protocol` | two lines: `FixedColumns.lean:11`, an exception the convention lists, and `Basic.lean:3`, which it does not (§B.5, item 12) |

Not checked: external links other than the hole comment's; the figure "3298 declarations" of
the axiom audit (`protocol-status.md:59`), which needs a run of `validate.sh`; the line numbers
the handoffs cite into the branches they reviewed, which no longer exist as such.

### B.11 The pins, after the dependency upgrade (pull request 61, `main` at `144c5aa`)

Pull request 61 ("chore(deps): upgrade to Lean 4.34.1", merged 2026-09-29 22:31 UTC, commit
`144c5aa`) moved every pin but leanVM's: ArkLib `dca90385` → `7653a901`, CompPoly `3468b38c` →
`572f9973`, Clean `93c9d1ef` → `42fe4b26`, VCVio `f9dc47d9` → `a4232d08` (now a direct Lake
requirement, `lakefile.toml:40-43` at `144c5aa`, beside a new direct PolyFun `41d3b21d`), Lean
and Mathlib `v4.33.1` → `v4.34.1` (`git show 144c5aa:upstreams.json`;
`git show 144c5aa:docs/dependencies.md`, lines 5-15 and the section "Lean 4.34 port review").
It added one paragraph to the blueprint and rewrote the blueprint's convention *Module system*;
it did not touch the status. In this table only, blueprint and status lines are those of
`144c5aa` (the blueprint's lines after 50 are those of `b435631` plus 4).

| # | The document says, at `144c5aa` | Today |
| --- | --- | --- |
| 1 | blueprint `:52-54` (new): "The dependency API tables and signatures below record the original implementation baseline. [dependencies.md] records current pins and the 4.34 native-probability port, which retains the relations, extraction conditions, and error bounds." | the only sentence of the blueprint that knows of the upgrade; the passages below still state the old pins as the current ones, and nothing says which of them are history |
| 2 | blueprint `:113` (Scope): "ArkLib as a Lake dependency at `dca90385`" | `7653a901` |
| 3 | blueprint `:167-172`: "The pins are in `upstreams.json` and [dependencies.md]: leanVM `a386121f`, ArkLib `dca90385`, CompPoly `3468b38c`, Clean `93c9d1ef`, VCVio `f9dc47d9` (through ArkLib), Lean `v4.33.1`." | four of the six pins changed, and VCVio is no longer "through ArkLib" |
| 4 | blueprint `:257-261`: "**Admitted at the pin, and what this roadmap does about it.**" and the column "ArkLib state at `dca90385`" of the upstream ledger | the ledger describes the old pin. Whether each admitted result is still admitted at `7653a901` is not established by any document of the repository |
| 5 | blueprint `:633-635` (Layer 0): "Add ArkLib at `dca90385` as the `Arklib` requirement (its package name). ArkLib requires CompPoly at the `v4.33.1` tag; the root pin `3468b38c` wins the resolution" | `dependencies.md` at `144c5aa`: "CompPoly's current main revision overrides ArkLib's `v4.34.0` CompPoly requirement", and Mathlib is now a root requirement |
| 6 | blueprint `:1529-1530` (References): ArkLib "at `dca90385`" | `7653a901` |
| 7 | status `:10-11`: "The dependency pins are unchanged."; `:161-163`: "**The pins have not moved.** ArkLib `main` is 246 commits past `dca90385` (finding A18); the next bump is one planned change (Lean 4.34, …)"; the headings of its findings, "**ArkLib** (`dca90385`)" `:332`, "**Clean** (`93c9d1ef`)" `:355`, "**CompPoly** (`3468b38c`)" `:360` | the planned bump has happened; the findings about the libraries are findings about revisions that are no longer the pins |
| 8 | tracker body `:4`: "**Framework:** … ArkLib at `dca90385`"; `:14`: "Pins unchanged: leanVM `a386121f`, ArkLib `dca90385`, CompPoly `3468b38c`, Clean `93c9d1ef`, Lean `v4.33.1`"; `:84`: "The pins have not moved." | the same |
| 9 | `LeanerVM/Protocol/Field.lean:18-20` at `144c5aa` (updated by the upgrade): "the first consumer of ArkLib (pin `7653a901…`) and of VCVio through it (`a4232d08…`)" | the pins are right; "through it" is not, VCVio being a direct requirement |

Every other pin statement in the proof system's documents that is a statement about history
(the survey record, the review handoffs, "the port of ArkLib #615 at `ca7a2577`") is right as
history and should say so where it can be read as current. The proposed texts of §G state the
new pins once, in the status, and elsewhere point to `upstreams.json`.

## C. Vocabulary

Counts are whole-word, case-insensitive occurrences (`vocab_counts.py`; BP, ST, TB, HC as in
section A). "Keep" follows the brief's vocabulary where it decides.

| One thing | Variants, with counts | Keep | Remark |
| --- | --- | --- | --- |
| The document that says what is wanted | "roadmap": BP 25, ST 16, TB 13; "blueprint": BP 5, ST 3, TB 3, HC 11, the handoffs 37. The file is `protocol-blueprint.md`; its title is "Roadmap: ..." | blueprint | a reader of the tracker meets both words for one file in one sentence (`issue-12-body.md:1`) |
| The tracking issue | "dashboard": BP 7, ST 2; "tracker": BP 2; "tracking issue": BP 1, ST 2; "this issue" | tracker | at `protocol-blueprint.md:1489` "the tracker" means all of GitHub's issues, not issue 12 |
| A unit of work | "hole": BP 48, TB 29, HC 21; "layer": BP 172, HC 40; "unit": BP 29; "slice": BP 9; "half": BP 10; "leaf": see below | "hole", defined once ("a unit of work the spine leaves open: a phase, a generic component, the adaptor, or a piece of the compilation"), always with its name; "layer" for the blueprint's section number | "hole" is not a word a zkVM engineer knows, so its definition goes in the index; a hole has up to four identifiers today (hole code, layer number, the closed issue's number, the pull request). The earlier draft proposed "unit of work" instead; the second pass keeps "hole", the brief's word, the word of the spine's Lean docstrings ("the hole interfaces") and of 48 places in the blueprint. In §E and §F below, "unit of work" and "unit" mean a hole |
| The table of upstream gaps | "ledger": BP 24, ST 10; "upstream ledger": BP 2; "upstream watch": BP 3, HC 5; "upstream candidates" (`leanth-reuse.md:447`) | "upstream ledger" for what is admitted or absent at the pin and what replaces it; "upstream watch" for external work in flight | two different tables; the blueprint's hole table has a third, the column "Existing work" |
| The relation between two phases | "seam": BP 62; "interface": BP 28; "boundary": BP 17 | seam | "interface" also means an assumed structure (`FlockInterface`) and the list of public names; "boundary" also means the boundary blocks of the bus and the section "Boundaries" with other roadmaps |
| One step of the protocol | "phase": BP 131; "reduction": BP 17; "component": BP 60; "stage": BP 3 | phase for the six steps; component for a generic piece | `Component` is three things: Clean's table circuit (`:291`), the spine's `Component.Def` (`:501`), ArkLib's `ProofSystem/Component/` (`:244`) |
| The committed object | "stack": BP 41; "stacked columns"; "the oracle": BP 51; "committed column/polynomial"; "`q`" | the stack | "column" is both a table's column and the stack itself (`Column μ`) |
| A coordinate of `E` over `K` | "limb": BP 24; "lane": BP 5 | limb | "lane" has three meanings: a word of the BLAKE2s block (`:325`), the four `K`-words of the public input in leanISA (`leanisa-blueprint.md:356`), and a track of work in the Flock roadmap (`:1446`). "limb" is also used for a column: "the three memory limbs" |
| The claims handed to the opening | "claim pool": BP 5; "pool", "pooled": BP 19, RP 33 | claim pool | "claim" is also the act of taking a unit of work ("claimed": BP 7, TB 7) |
| Done | "landed": TB 13, ST 9; "built": BP 8, ST 5; "on `main`": ST 10; "merged": ST 16; "met" (of a finding): the handoffs 39; "done"; "taken" (of a decision) | "on main" for code; "met" for a finding; "taken" for a decision | the tracker defines four states (`issue-12-body.md:18`); the status uses a fifth, "built, draft" |
| The import rule | "the wall": BP 7, ST 4, RL 6 | "the import rule of the proof system", stated once | a metaphor; the rule is one sentence (`:331`) |
| The map between the two relations | "adaptor": BP 29; "adapter": ST 1 (another thing, a compatibility file); "bridge": BP 11; "refinement": BP 13 | adaptor for the leanISA one; refinement for the generic notion | "the Clean bridge" is Layer 2, a different unit |
| The protocol | "oracle protocol": BP 11; "PIOP" in names (`leanVmPiop`); "IOR": BP 1; "IOPP" (`leanVmIopp`): BP 5 | oracle protocol | `leanVmIopp` names as a proximity proof the compiled protocol "WHIR in place of the evaluation oracle" (`:1214-1215`) |
| A bus entry | "flush": BP 12; "interaction": ST 10; "tuple" | flush, as the specification | "side" (`Side`, spine) against "direction" (`Direction`, Layer 2 sketch, and ArkLib's message direction) |
| The public data | "public input": ST 23; "public statement": BP 3; "public words": BP 6; "public line": BP 4 | public input for the two words; public line for the spine's object | `PublicInput` is a leanISA type and also a namespace of the proof system (`PublicInput.check`) |
| The work item inside a layer | "leaf", "leaves": BP 26 | - | four meanings: a leaf of the product tree (`:319`), "the leaves of Layer 1 already in flight" (`:591`), "the missing leaf" of ArkLib's sumcheck (`:259`), "packing leaves" (`:267`) |

Terms a zkVM engineer would not recognize without the blueprint's definitions: hole, seam,
spine, the wall, ledger, frontier, toy (instance), Category A and Category B, M3 (expanded only
in the references, `:1539`), IOR. Of these only "M3" and "IOR" are terms of art elsewhere.

Words with two meanings that matter: **claim** (an evaluation claim; the act of taking work),
**instance** (`M3Instance`; a Lean type-class instance; "an instance of a theorem"),
**statement** (the public statement `I.Stmt`; a theorem's statement; Clean's
`Ensemble.Statement`), **Layer N** (the proof system's and leanISA's, both from 0; the table at
`protocol-blueprint.md:215-222` uses the bare form for leanISA's and "Layer 11 here" for its
own in the same row), **component**, **lane**, **leaf**, **Direction**.

## D. The letter codes: complete inventory

Source of the counts: `extract_codes.py` over the eight documents (blueprint, status, tracker
body, hole comment, the four other comments, the three handoffs), and `code_contexts.py`, whose
output was read occurrence by occurrence for every code with more than one meaning.

Re-check (this dossier's second pass). The script's pattern skips a code written inside
backticks or followed by `/` (for example `` `L1` `` at `protocol-blueprint.md:591`), so every
count below is a lower bound. An independent count with a plain whole-word pattern over the same
eight texts, for thirteen codes across the families (`L1`, `G4`, `P5`, `K2`, `A4`, `C1`, `A18`,
`F17`, `E16`, `S16`, `T4`, `I2`, `E7`), agrees on 102 of 104 cells; the two differences are
corrected below (`L1`: 6 in the blueprint, not 5; `P5`: 3 in the public-input handoff, not 2).
The "defined at" line of each of those thirteen codes was read at the cited line and is right.

### D.1 The families

| Family | Codes | Distinct | Occurrences | Defined in | Letter explained? |
| --- | --- | --- | --- | --- | --- |
| Units of work ("holes") | `0`, `L1`, `S`, `I1`, `I2`, `G1`-`G6`, `P1`-`P8`, `C1`, `K1`-`K4` | 24 | about 470 | blueprint `:595-615`; hole comment | no. `S`, `G`, `I`, `P`, `C`, `K`, `L` are never expanded |
| Layers | Layer 0 to Layer 13 | 14 | "layer" 172 times in the blueprint | blueprint `:625-1259` | - |
| Upstream ledger | `A1`-`A9`, `C1`-`C4` | 13 | about 95 | blueprint `:257-267` (the `A` rows); status `:171-184` (the `C` rows) | no |
| Findings, ArkLib | `A10`-`A19` | 10 | 16 | status `:332-353` | status `:281-283` |
| Findings, specification | `S6`, `S9`-`S16` | 9 | 24 | status `:285-303` | yes |
| Findings, Rust and Python | `F1`-`F18` | 18 | 62 | status `:305-330` | yes, wrongly (§B.1, item 13) |
| Findings, Clean | `C5`, `C6`, `C10`, `C11` | 4 | 8 | status `:355-358` | yes |
| Findings, CompPoly | `P1`, `P3`-`P6` | 5 | 8 | status `:360-363` | yes |
| Findings, Lean environment | `E6`-`E18` | 13 | 41 | status `:365-432` | yes |
| Spine review | `A1`-`A6`, `B1`-`B2`, `I1`-`I3`, `C1`-`C2`, `H1`-`H6` | 19 | about 150 | `protocol-spine.md:32-47` | passes A, B, C are named; `I` and `H` are not |
| Layer 1 review | `A1`-`A6`, `B1`-`B4` (and `B0`, `B6`), `D1`-`D17`, `C1`-`C9` | 38 | about 80 | `protocol-layer1.md:26-43` | `D` is not |
| Public-input review | `B1`-`B3`, `C1`-`C4`, `A1`-`A4`, `H1`-`H6` | 17 | about 120 | `public-input-phase.md:66-79` | `H` is not |
| Flock roadmap's milestones | `F1`, `F3`-`F6`, `F8` cited | 6 | 13 | the body of issue 3, `:92-101` | there, not here |
| Decisions | 1 to 15 | 15 | 27 references | status `:212-277` | - |
| Acceptance tests | 1 to 28 | 28 | 30 references | blueprint `:1266-1358` | - |
| Target theorems | `T1`, `T2`, `T4`, `T5`, `T6` cited | 5 | 41 | `architecture.md:203-376` | yes |
| Categories | Category A, Category B | 2 | 22 | blueprint `:178-184` | yes |
| leanth's audit codes | `FW-1`, and in `leanth-reuse.md` `FW-4`, `DR-101`, `DR-110`, `DR-112`, `DR-113`, `PS-2`, `PS-3`, `F-1`, `F-3`, `F-6`, `F-8` | 12 | 1 in the blueprint (`:1337`) | the private repository | no |
| A contributor's private codes | `P17`, `P05` | 2 | 1 each (`issue-12-comment-5749874958.md:5`; the body of issue 31) | nowhere | no |

The machine count over the eight documents: at least 128 distinct letter-number codes and at
least 1036 occurrences, of which the status has 266, the blueprint 169, the spine handoff 151, the
tracker body 141 (`extract_codes.py`).

### D.2 Every code, one sentence each

The column "Uses" counts occurrences of the code string, whatever it means there; §D.3 splits
the codes that mean several things. For the spine's code the count is by hand (the letter `S`
alone is also a Lean variable and a class letter): 22 uses, BP 10, ST 4, TB 3, HC 3, OC 2.

**Units of work (the documents' "holes")**

| Code | What it denotes | Defined at | Uses in the eight documents |
| --- | --- | --- | --- |
| `0` | the ArkLib dependency and the field instances (Layer 0); a layer number used as a hole code | tracker body:20; status:89; not in the blueprint's table | 2 |
| `S` | the spine: instance, relation, seams, phase interfaces, composition, toy instance | blueprint:597; hole comment:5 | 22 (see above) |
| `L1` | tables and stacking (Layer 1): hypercube tables, stacking, the fixed columns | blueprint:603; no section in the hole comment | 21: BP 6, ST 6, TB 7, RL 2 |
| `I1` | Clean expressions as polynomials (Layer 2) | blueprint:604; no section in the hole comment | 26: BP 3, ST 5, TB 6, HC 1, OC 2, RS 9 |
| `I2` | the adaptor (Layer 3): the leanISA instance, `stackOf`, `witnessOf` and their theorems | blueprint:605; hole comment:44 | 49: BP 5, ST 8, TB 11, HC 6, OC 3, RS 15, RL 1 |
| `G1` | generic sumcheck, definition and completeness (Layer 4) | blueprint:598; no section in the hole comment | 26: BP 7, ST 8, TB 7, HC 3, OC 1 |
| `G2` | generic sumcheck, round-by-round knowledge soundness (Layer 4) | blueprint:599 | 12: BP 3, ST 4, TB 4, HC 1 |
| `G3` | batching of claims by powers of one challenge (Layer 4) | blueprint:600 | 15: BP 2, ST 7, TB 5, HC 1 |
| `G4` | fingerprint, product-determines-multiset lemma, collision bound (Layer 5) | blueprint:601 | 12: BP 2, ST 5, TB 4, HC 1 |
| `G5` | grand-product GKR, definition and completeness (Layer 5) | blueprint:602; hole comment:28 | 14: BP 2, ST 4, TB 4, HC 4 |
| `G6` | grand-product GKR, knowledge soundness (Layer 5) | blueprint:602; hole comment:28 | 14: BP 5, ST 2, TB 2, HC 4, OC 1 |
| `P1` | bus phase, definition and completeness (Layer 6) | blueprint:606; hole comment:61 | 21: BP 4, ST 5, TB 4, HC 3, OC 1, RS 2, RP 2 |
| `P2` | bus phase, knowledge soundness (Layer 6) | blueprint:606; hole comment:61 | 13: BP 4, ST 2, TB 3, HC 4 |
| `P3` | table sumcheck phase, definition and completeness (Layer 7) | blueprint:607; hole comment:75 | 19: BP 4, ST 6, TB 3, HC 3, OC 1, RP 2 |
| `P4` | table sumcheck phase, knowledge soundness (Layer 7) | blueprint:607; hole comment:75 | 12: BP 4, ST 2, TB 2, HC 4 |
| `P5` | public-input phase, both halves (Layer 8) | blueprint:608; hole comment:89 | 36: BP 2, ST 15, TB 3, HC 3, OC 3, RS 7, RP 3 |
| `P6` | Flock phase as an interface supplied by issue 3 (Layer 9) | blueprint:609; hole comment:102 | 19: BP 2, ST 4, TB 4, HC 3, OC 2, RS 4 |
| `P7` | opening phase and claim pool, definition and completeness (Layer 10) | blueprint:610; hole comment:115 | 20: BP 2, ST 6, TB 5, HC 4, RS 1, RP 2 |
| `P8` | opening phase, knowledge soundness (Layer 10) | blueprint:610; hole comment:115 | 16: BP 5, ST 2, TB 3, HC 4, RS 2 |
| `C1` | knowledge-soundness composition, ported from ArkLib pull request 615 | blueprint:611; hole comment:129 | 41: BP 5, ST 9, TB 5, HC 4, OC 3, RS 6, RL 4, RP 5 |
| `K1` | WHIR opening over binary Reed-Solomon codes (Layer 11) | blueprint:612; hole comment:144 | 25: BP 4, ST 8, TB 9, HC 3, OC 1 |
| `K2` | Merkle trees, BLAKE2s byte hasher, WHIR parameters (Layer 11) | blueprint:613; hole comment:158 | 17: BP 4, ST 4, TB 5, HC 3, OC 1 |
| `K3` | transcript, proof object, compiled verifier `verify` and its refinement theorem (Layer 12) | blueprint:614; hole comment:172 | 29: BP 4, ST 7, TB 7, HC 6, RS 5 |
| `K4` | the two base theorems of target T4 (Layer 13) | blueprint:615; hole comment:186 | 10: BP 2, ST 1, TB 2, HC 3, RS 2 |

**Upstream ledger entries**

| Code | What it denotes | Defined at | Uses in the eight documents |
| --- | --- | --- | --- |
| `A1` | ArkLib admits the sumcheck's single-round knowledge soundness | blueprint:259; status:173; tracker body:63 | 32: BP 3, ST 9, TB 2, OC 1, RS 9, RL 3, RP 5 |
| `A2` | ArkLib admits the knowledge-soundness composition of appended reductions | blueprint:260; status:174; tracker body:64 | 39: BP 7, ST 9, TB 2, HC 3, OC 2, RS 8, RL 3, RP 5 |
| `A3` | ArkLib admits "round-by-round implies plain" knowledge soundness | blueprint:261; status:175; tracker body:65 | 24: BP 1, ST 6, TB 1, RS 11, RL 2, RP 3 |
| `A4` | ArkLib admits every context-lifting security theorem (not consumed) | blueprint:262 only; absent from the status's and the tracker's tables | 16: BP 1, ST 4, RS 6, RL 3, RP 2 |
| `A5` | ArkLib admits or lacks Fiat-Shamir and BCS security | blueprint:263; status:176; tracker body:66 | 17: BP 4, ST 2, TB 1, HC 1, RS 7, RL 2 |
| `A6` | ArkLib has no grand product, GKR, batching or stacking | blueprint:264; status:177; tracker body:67 | 16: BP 2, ST 3, TB 1, HC 2, RS 5, RL 3 |
| `A7` | ArkLib has no WHIR, Merkle tree or BLAKE2s | blueprint:265; status:178; tracker body:68 | 6: BP 2, ST 2, TB 1, HC 1 |
| `A8` | ArkLib admits mutual correlated agreement up to the Johnson bound | blueprint:266; status:179; tracker body:69 | 7: BP 4, ST 1, TB 1, HC 1 |
| `A9` | ArkLib admits the ring-switching packing lemmas | blueprint:267; status:180; tracker body:70 | 5: BP 1, ST 2, TB 1, HC 1 |
| `C1` | Clean has no polynomial reading of expressions and no degree bound | status:181; tracker body:71; not in the blueprint's table | 2 of the 41 above |
| `C2` | request to leanISA: power-of-two heights in `Caps`, bus data per channel (done) | status:182; tracker body:72; not in the blueprint's table | 9: ST 2, TB 1, RS 2, RL 2, RP 2 |
| `C3` | Clean lacks a balance counted in the naturals with direction tags | status:183; tracker body:73; not in the blueprint's table | 5: ST 1, TB 1, RL 1, RP 2 |
| `C4` | Clean lacks fixed columns and sound prover data | status:184; tracker body:74; not in the blueprint's table | 5: ST 1, TB 1, RL 1, RP 2 |

**Findings about ArkLib beyond the ledger**

| Code | What it denotes | Defined at | Uses in the eight documents |
| --- | --- | --- | --- |
| `A10` | ArkLib relations are sets of pairs; the documented refactor has not happened | status:332 | 1: ST 1 |
| `A11` | ArkLib's averaged round-by-round notion is weaker than the worst-case one the layers prove | status:334 | 1: ST 1 |
| `A12` | ArkLib's `extractability` for commitments is `False`-valued; not cited | status:336 | 1: ST 1 |
| `A13` | two ArkLib statements contain `sorry` in their types; never cited | status:337 | 1: ST 1 |
| `A14` | ArkLib's typed-interaction replacement has no security definitions yet | status:338 | 2: ST 2 |
| `A15` | ArkLib's toy problem is sorry-free; its code-generation probes are the pattern for `verify` | status:340 | 1: ST 1 |
| `A16` | ArkLib pins CompPoly at a tag; leanerVM's pin wins the resolution | status:341 | 1: ST 1 |
| `A17` | ArkLib's position-query oracle instance on `Vector` is global, so `Column` must be a structure | status:342 | 1: ST 1 |
| `A18` | ArkLib `main` had moved 246 commits past the pin on 2026-09-24 | status:345 | 4: ST 3, TB 1 |
| `A19` | ArkLib pull request 615's composition file compiles unchanged against the pin | status:346 | 3: ST 3 |

**Findings internal to the specification**

| Code | What it denotes | Defined at | Uses in the eight documents |
| --- | --- | --- | --- |
| `S6` | specification section 8.4 (Fiat-Shamir) is `TODO` (inherited from leanISA) | status:285 | 1: ST 1 |
| `S9` | the proof of specification Lemma 5.2 is `TODO` | status:286 | 2: BP 1, ST 1 |
| `S10` | specification section 5.3 does not state the degree of a radix-4 round polynomial | status:287 | 1: ST 1 |
| `S11` | specification section 8.5 does not say the push and pull roots are one scalar | status:289 | 1: ST 1 |
| `S12` | Annex B omits the 17 grinding bits per level that the Rust applies | status:291 | 1: ST 1 |
| `S13` | retired: a bound of 5 instead of 4, read off a PDF that is not the pinned text | status:293 | 8: ST 2, TB 1, RS 5 |
| `S14` | the PDF `leanVM-b-2.pdf` is not the pinned text and must not be cited | status:297 | 4: ST 2, TB 1, RS 1 |
| `S15` | the specification gives no rule for stacking blocks of equal size | status:303 | 3: ST 2, RL 1 |
| `S16` | the specification's equations are numbered (1) to (4); "equation (5.4)" does not exist | status:303 | 3: ST 2, RL 1 |

**Findings, Rust and Python against the specification**

| Code | What it denotes | Defined at | Uses in the eight documents |
| --- | --- | --- | --- |
| `F1` | no domain-separation labels: four numeric tags in lane 3 | status:305 | 9: BP 4, ST 3, TB 1, HC 1 |
| `F2` | Flock's fixed coordinate is a hard-coded constant without provenance | status:307 | 2: BP 1, ST 1 |
| `F3` | one root for the push and pull products | status:309 | 8: BP 4, ST 2, TB 1, HC 1 |
| `F4` | the table sumcheck's target is derived by the verifier, never sent | status:310 | 4: BP 1, ST 2, HC 1 |
| `F5` | the three bus forms share the last three powers of the batching challenge | status:311 | 6: BP 3, ST 1, TB 1, HC 1 |
| `F6` | the table round polynomial is a cubic; three scalars travel | status:312 | 9: BP 4, ST 3, TB 2 |
| `F7` | one coefficient of every round polynomial is never transmitted | status:313 | 1: ST 1 |
| `F8` | ring-switched claims take the low powers in the opening batch | status:315 | 5: BP 2, ST 1, TB 1, HC 1 |
| `F9` | the Python verifier omits four caps that the Rust verifier checks | status:316 | 3: ST 2, TB 1 |
| `F10` | the Rust verifier's rejection set; structure checks are `assert!`s | status:319 | 2: BP 1, ST 1 |
| `F11` | the count tree holds the tables' count columns only | status:321 | 2: ST 1, TB 1 |
| `F12` | fill blocks make announced heights exact | status:322 | 1: ST 1 |
| `F13` | grinding binds the nonce even when the check fails | status:324 | 1: ST 1 |
| `F14` | the seed hashes one constant naming the circuit, not the matrices | status:325 | 2: ST 1, HC 1 |
| `F15` | the bound on the stack height is checked separately from the caps | status:327 | 1: ST 1 |
| `F16` | 128 security bits round by round; the bus needs no grinding | status:328 | 1: ST 1 |
| `F17` | blocks of equal size are stacked in the order of the column index | status:330 | 7: ST 4, RL 1, RP 2 |
| `F18` | the pinned verifiers check one equation on the public words, the specification one per limb | status:330 | 7: ST 5, RP 2 |

**Findings about Clean, CompPoly and the Lean environment, and the one leanISA finding cited**

| Code | What it denotes | Defined at | Uses in the eight documents |
| --- | --- | --- | --- |
| `C5` | Clean has no degree bound on expressions (inherited from leanISA) | status:355 (by reference) | 3: BP 1, ST 1, RL 1 |
| `C6` | Clean has no prover-chosen heights (inherited from leanISA) | status:355 (by reference) | 3: BP 1, ST 1, RL 1 |
| `C10` | Clean's `EnsembleWitness` has no generator | status:355 | 1: ST 1 |
| `C11` | Clean's `Ensemble.Statement` assumes the non-overflow side condition | status:356 | 1: ST 1 |
| `P1` | CompPoly's extension arithmetic is not kernel-reducible from a `module` (inherited from leanISA) | status:360 (by reference) | 1 of the 21 of `P1` |
| `P3` | CompPoly's `Fintype BF64` instance is evaluated at the start of an executable (inherited) | status:360 (by reference) | 4 of the 19 of `P3` |
| `P4` | CompPoly has no sum over the cube and no pointwise product of tables | status:360 | 1 of the 12 of `P4` |
| `P5` | CompPoly's additive NTT is instantiated only at `GF(2^8)` | status:361 | 1 of the 35 of `P5` |
| `P6` | CompPoly has no Frobenius on extensions | status:362 | 1 of the 19 of `P6` |
| `E6` | a Lake race on ArkLib's lint plugin at first build | status:365 | 2: ST 2 |
| `E7` | no `LawfulBEq E` at the CompPoly pin, so no polynomial with coefficients in `E` | status:368 | 3: ST 1, TB 1, RS 1 |
| `E8` | no `OracleInterface E` at the ArkLib pin | status:375 | 3: ST 1, TB 1, RS 1 |
| `E9` | `decide` cannot unfold CompPoly's `X` and `*` inside a `module` | status:380 | 4: ST 1, TB 1, RS 2 |
| `E10` | a phase with a nonzero error is a `noncomputable` bundle | status:383 | 2: ST 1, RP 1 |
| `E11` | a binder over `Finset.univ : Finset E` makes a linter enumerate the field | status:388 | 1: ST 1 |
| `E12` | `simp` does not rewrite inside instance arguments of `Component.Def.red` | status:391 | 3: ST 1, RP 2 |
| `E13` | a `Decidable` instance written by `unfold` never evaluates under `#guard` | status:396 | 3: ST 1, RP 2 |
| `E14` | Mathlib's overlapping-instances linter rejects `[Zero R]` under `[CommRing R]` | status:400 | 4: ST 3, RP 1 |
| `E15` | `#guard` finds no `Decidable` instance for vectors of computed length | status:405 | 2: ST 1, RP 1 |
| `E16` | a generic module's destination is read off its objects and imports (a rule, not a fact about Lean) | status:407 | 6: ST 5, RP 1 |
| `E17` | being stated over any ring does not make a declaration generic (a rule, not a fact about Lean) | status:415 | 6: ST 3, RL 1, RP 2 |
| `E18` | a `#guard` with a numeral of `E` next to an operation finds no `Decidable` instance | status:429 | 2: ST 1, RP 1 |
| `R21` | leanISA finding: the repository holds two BLAKE2s compressions | `leanisa-status.md`; cited at blueprint:216, hole comment:162 | 2: BP 1, HC 1 |

**Target theorems cited by the proof-system documents**

| Code | What it denotes | Defined at | Uses in the eight documents |
| --- | --- | --- | --- |
| `T1` | arithmetization and ISA equivalence, both directions | `architecture.md`:203 | 7: BP 4, ST 1, TB 2 |
| `T2` | witness-generator correctness | `architecture.md`:230 | 3: BP 2, ST 1 |
| `T4` | base proof extraction and completeness, the proof system's target | `architecture.md`:261 | 21: BP 11, ST 1, TB 2, HC 3, RS 4 |
| `T5` | recursive-verifier correctness | `architecture.md`:277 | 6: BP 5, HC 1 |
| `T6` | recursion and correct-trace extractability (open) | `architecture.md`:284 | 4: BP 4 |

**The codes of the three reviews** (each defined in its handoff's disposition table; "uses"
are in the handoff and, in parentheses, in the status)

| Review | Code | What it denotes | Uses |
| --- | --- | --- | --- |
| Spine | `A1` | the bus seam admits linear claims of any degree | 9 (2) |
| Spine | `A2` | the Flock predicate's strength is undetermined | 7 (2) |
| Spine | `A3` | the master knowledge theorem does not name its extractor | 11 (1) |
| Spine | `A4` | a list of public cells cannot be served by the public-input phase | 6 (2) |
| Spine | `A5` | the adaptor's soundness theorem needs the caps as a hypothesis | 7 (1) |
| Spine | `A6` | no inhabitant of a phase's security; the pass-through has no knowledge half | 5 (0) |
| Spine | `B1` | citation drift, and the PDF handed to the review is not the pinned text | 2 (0) |
| Spine | `B2` | a status finding was stated against a text that is not the pin | 2 (0) |
| Spine | `I1` | polynomials with coefficients in `E` have no ring operations at the pin | 5 (0) |
| Spine | `I2` | scalar prover messages have no oracle interface | 3 (0) |
| Spine | `I3` | the layout plan covers aligned blocks only | 3 (0) |
| Spine | `C1` | the pull request's description is stale | 3 (0) |
| Spine | `C2` | module docstrings do not state the target contribution | 2 (0) |
| Spine | `H1`-`H6` | six reductions of the audit surface: a `Shape` record, derived `Decidable` instances, `Seam.of`, a one-line `read_eval`, a shorter `guardedAppend`, the pass-through's knowledge half | 27 (2) |
| Layer 1 | `A1` | the block-claim pairing cannot be used by the opening phase | 3 (2) |
| Layer 1 | `A2` | `Blocks.layout` has not the type of an instance's layout | 3 (1) |
| Layer 1 | `A3` | `bytecodeColumn_slot` restates the definition | 2 (1) |
| Layer 1 | `A4`-`A6` | three weak tests | 8 (1) |
| Layer 1 | `B1` | the order of equal-size blocks is stated backwards in the blueprint | 4 (1) |
| Layer 1 | `B2` | the claims docstrings describe one weight construction where the source has two | 5 (1) |
| Layer 1 | `B3` | "equation (5.4)" does not exist | 2 (1) |
| Layer 1 | `B4` | a citation that is a comment cut mid-sentence | 3 (1) |
| Layer 1 | `B0`, `B6` | items of the review skill's checklist, "clean" | 1 each; defined nowhere in the handoff |
| Layer 1 | `D1` | the import rule is not enforced by the script the blueprint names | 3 (2) |
| Layer 1 | `D2`-`D17` | sixteen mismatches between the documents and the branch, described together (`protocol-layer1.md:182-192`); `D3` and `D6` are never named singly | 20 (0) |
| Layer 1 | `C1` | per-file copyright and author headers in two modules | 4 (1) |
| Layer 1 | `C2`-`C9` | eight hygiene items | 11 (0) |
| Public input | `B1` | the specification's check and the deployed check are not equivalent at a fixed challenge | 5 (1) |
| Public input | `B2` | Schwartz-Zippel cited as Lemma 5.2; it is Lemma 3.8 | 2 (0) |
| Public input | `B3` | six slips in the changed documents | 2 (0) |
| Public input | `C1` | fragile proofs declared the template for three more phases | 5 (1) |
| Public input | `C2` | ten unprefixed public names | 2 (1) |
| Public input | `C3` | the module docstring has no pin and no provenance | 2 (0) |
| Public input | `C4` | generic lemmas kept in the phase module | 2 (0) |
| Public input | `A1` | the output drops a claim on a short message | 5 (1) |
| Public input | `A2` | the flag `sent` is fixed by no statement and no test | 5 (1) |
| Public input | `A3` | several tests restate definitions | 3 (0) |
| Public input | `A4` | the message type is wider than two scalars | 2 (0) |
| Public input | `H1`-`H6` | six reductions of the audit surface: one output, one list of sent values, five lemmas private, `pubWitMid` inlined, a shared lemma for guarded verdicts, a shared embedding | 52 (2) |

### D.3 Every collision

**Inside the proof system's own documents: 34 codes with two or more meanings.** The split of
the occurrences by meaning was made by reading each one (`ctx_A.txt`, `ctx_C.txt`, `ctx_I.txt`,
`ctx_P.txt`, `ctx_F.txt`).

| Code | Meanings, with the number of occurrences of each |
| --- | --- |
| `A1` | ledger entry 10; spine review 11; Layer 1 review 5; public-input review 6 |
| `A2` | ledger entry 20; spine review 9; Layer 1 review 4; public-input review 6 |
| `A3` | ledger entry 6; spine review 12; Layer 1 review 3; public-input review 3 |
| `A4` | ledger entry 2; spine review 8; Layer 1 review 4; public-input review 2 |
| `A5` | ledger entry 7; spine review 8; Layer 1 review 2 |
| `A6` | ledger entry 7; spine review 5; Layer 1 review 4 |
| `B1`, `B2` | three reviews, three meanings each |
| `B3` | Layer 1 review; public-input review |
| `C1` | unit of work (the composition) 25; ledger entry (Clean's expressions) 2; spine review 3; Layer 1 review 5; public-input review 6 |
| `C2` | ledger entry 2; spine review 2; Layer 1 review 2; public-input review 3 |
| `C3`, `C4` | ledger entry 2; Layer 1 review 1; public-input review 2 |
| `C5`, `C6` | Clean finding 2; Layer 1 review 1 |
| `H1` to `H6` | spine review; public-input review |
| `I1` | unit of work (Clean expressions as polynomials) 21; spine review finding 5 |
| `I2` | unit of work (the adaptor) 46; spine review finding 3 |
| `P1` | unit of work 20; CompPoly finding 1 |
| `P3` | unit of work 15; CompPoly finding 4 |
| `P4`, `P5`, `P6` | unit of work 11, 34, 18; CompPoly finding 1 each |
| `F1` | finding (no labels) 7; the Flock roadmap's milestone "executable algebra" 2 |
| `F3` | finding (one root) 6; Flock milestone "baseline reduction" 1; a reference that means the leanISA finding of that code 1 |
| `F4` | finding (derived target) 3; the leanISA finding of that code, so named, 1 |
| `F5` | finding (shared powers) 4; Flock milestone "packed openings" 2 |
| `F6` | finding (cubic round polynomial) 3; Flock milestone "concrete PCS" 6 |
| `F8` | finding (low powers) 4; Flock milestone "concrete hash instances" 1 |

Within the status file alone the code `A1` has four meanings (`protocol-status.md:49`, `:173`,
`:254`, `:443`) and the code `C1` has four (`:104`, `:145`, `:181`, `:445`); "review finding
A1" at `:49` and at `:254` are two different findings of two different reviews. Within the
spine handoff alone `I1` and `I2` are both a unit of work and a finding, once on adjacent rows
(`protocol-spine.md:42-44`, `:334-335`).

**Against the leanISA status: 11 more codes.** The same code, another thing:

| Code | In the proof-system status | In the leanISA status |
| --- | --- | --- |
| `S9` | the proof of Lemma 5.2 is `TODO` | section 7.4 lists the `DEREF` memory flushes in another order than the Rust |
| `F2`, `F7`, `F9`, `F10` (and `F1`, `F3`-`F6`, `F8` above) | Rust or Python against the specification | the roadmap's or the architecture's targets: for example `F9` is "the roadmap's Layer 7 sketch was unbuildable in two places" |
| `E6` | a Lake race on ArkLib's lint plugin | core's `BitVec` simprocs fire on numerals of `K` |
| `E7` | no `LawfulBEq E` | `circuit_norm` strands the `Decidable` instance of a witness program |
| `E8` | no `OracleInterface E` | lazy unfolding evaluates a table of `2^16` rows |
| `C10` | `EnsembleWitness` has no generator | Clean's raw channels and balance are degenerate over `K` |
| `C11` | `Ensemble.Statement` assumes the non-overflow side condition | `RequirementsChannelsLawful` |
| `L1` | the unit of work "tables and stacking" | core's `DecidableEq` for `Vector` is not exposed (cited as "finding L1" in `tests/README.md`) |
| `P4`, `P5` (third meaning) | see above | the derived `DecidableEq` of extensions; `simp` lemmas keyed on `Ext.coeff` |

Other documents cite these codes without saying which file: `docs/dependencies.md:55` cites
"status finding E6" (the proof system's), `docs/development.md:56` "finding P3" with the file,
`tests/README.md` "finding L1" and "finding E5" without one.

**Collisions already in the trackers.** The body of intention issue 28 says "Tracks #12, Layer
2/C1", where `C1` is the ledger entry on Clean's expressions, not the unit of work that `C1`
names on the checklist of issue 12. Issue 23 says "the bump also has to survive P3, the eager
`Fintype BF64`", the leanISA finding, while `P3` on issue 12 is the table sumcheck's definition.
Issue 4 cites "decision 15" (leanISA's: fixed columns after Clean pull request 446), while the
proof system's decision 15 is the public-input transcript. `docs/dependencies.md:87` cites
"finding C8" without saying which status file. The body of intention issue 31 uses a private
code, "P05 depends only on #18's multilinear API".

**Numbered things that collide across the two roadmaps.** Decisions 1 to 15 (§B.8), layers 0 to
13 and 0 to 10, acceptance tests 1 to 28 and 1 to about 20. Inside the proof system's documents
every cross-reference to a leanISA layer or test says "leanISA", with the exception of the
table at `protocol-blueprint.md:215-222` and of `leanth-reuse.md:485`.

**Other letters that look like codes.** `S1` to `S4` in `architecture.md:80-83` are the four
reference specifications. The single letters `L`, `S`, `P` are classes of declarations in the
public-input handoff (`public-input-phase.md:483-484`), and `S`, `M`, `L` are sizes of effort
in `leanth-reuse.md:58`. "Category A" and "Category B" are kinds of source; "Pass A", "Pass B",
"Pass C" are the review's passes, whose findings take the pass's letter, which is why a finding
of pass A collides with the ledger's `A`.

### D.4 Used and never defined; defined and never used

Used and never defined in any current document of the repository:

| Code | Where used |
| --- | --- |
| `P17` | `issue-12-comment-5749874958.md:5`: "no P17 replacement was implemented" |
| `P05` | the body of issue 31: "P05 depends only on #18's multilinear API" |
| `FW-1` | `protocol-blueprint.md:1337`: "catalog audit FW-1"; the audit is in the private repository |
| `B0`, `B6` | `protocol-layer1.md:114-115` |
| `D3`, `D6` and the other single members of `D2`-`D17` | named only inside ranges |
| decisions 1 and 3, as questions | `protocol-status.md:214` (§B.8) |
| "revision 2" | `issue-12-body.md:1, 10`; `protocol-status.md:214` |
| the letters `S`, `G`, `I`, `P`, `C`, `K`, `L` of the units | everywhere |
| the Flock roadmap's `F1`, `F3`-`F6`, `F8` | defined in the body of issue 3 only |

Defined and cited nowhere else (26 codes occur exactly once): `A10`, `A11`, `A12`, `A13`,
`A15`, `A16`, `A17`; `S10`, `S11`, `S12`; `F7`, `F12`, `F13`, `F15`, `F16`; `E11`; `C10`,
`C11`; the CompPoly findings `P4`, `P5`, `P6`; and five single `D` codes. A code that is never
cited buys nothing over a sentence.

## E. Proposal: who owns what

### E.1 The rule

A fact has one home. Every other place links to the home and restates nothing: no summary, no
"for convenience" copy, no table repeated with fewer columns. A reader who wants the fact
follows the link; a writer who changes the fact changes one place.

### E.2 The owners

| Kind of fact | Owner | What the other places do |
| --- | --- | --- |
| Targets, scope, conventions, the spine, acceptance tests | the blueprint | the status and the tracker link to the section |
| The specification of each unit of work: what it produces, with signatures; what it needs; its sources; its tests; the upstream work to read first | the blueprint, one section per unit | the hole comment is reduced to a pointer; the checklist line carries a name and a link, no signature |
| Decisions, taken and open | the blueprint, a section "Decisions" | the status and the tracker hold none |
| The upstream ledger: what is admitted or absent at the pin, what replaces it here, the upstream number, when the local copy goes | the blueprint, inside "Dependencies and exact contracts" | the status's and the tracker's copies are deleted |
| Coverage: what is on `main` | the repository; the status prints it, and a script checks the print | the tracker's checklist is ticked from it; the blueprint says nothing |
| What can start now | the status, derived from the units' "needs" and the coverage | the tracker links |
| Upstream watch: external work in flight, with its adoption condition | the status | the blueprint's column "Existing work" is deleted; its content becomes the "upstream work to read first" of the unit, without state |
| Who is doing what | the tracker's checklist line, linking the claimant's intention issue or pull request | the status holds no claim |
| Open pull requests | GitHub | no table anywhere |
| Discrepancies in the leanVM sources at the pin (specification, Rust, Python) | `docs/leanvm-target.md`, a new section "Known discrepancies at the pin", for both roadmaps | the blueprint cites a discrepancy by name where it binds a definition; both status files lose the section |
| Limits of the pinned libraries | `docs/dependencies.md`, under each library | the same |
| Lean pitfalls | `tests/README.md`, which already holds five of them, linked from `docs/development.md` | the same |
| The record of a review | the handoff under `docs/reviews/` | see §E.6 |
| What was read, and when | an archive (§E.5) | - |
| How to work on the proof system | the blueprint's section "How work is tracked"; the general rules stay in `CONTRIBUTING.md` and `AGENTS.md` | the tracker links |

No new kind of document is created. Three existing documents each gain one section
(`leanvm-target.md`, `dependencies.md`, `tests/README.md`), which is where their subject
already lives: `dependencies.md` already explains two limits of Clean and cites a finding by
its code (`:52-55`, `:81-88`), and `tests/README.md` already explains five pitfalls.

Why `leanvm-target.md` for the discrepancies. They are facts about the target at the pin, not
about either roadmap: they hold until the pin moves, they are shared (the missing section 8.4
is one finding in both status files), and both status files already say they are "numbered for
citation from ... `docs/leanvm-target.md`". One register also ends the collision between the
two files' letters. The alternative, an appendix of the blueprint, keeps two registers, one
per roadmap, and is not recommended.

### E.3 What the blueprint contains, and what leaves it

Table of contents proposed:

1. What is proved: the two master theorems, the compiled verifier's theorem, the two base
   theorems (T4) (today's introduction).
2. For zkVM engineers.
3. Scope.
4. Dependencies and exact contracts, ending with the upstream ledger (one table).
5. Pinned conventions.
6. The spine.
7. The units of work: one table with names (§G.2), then one section per unit in build
   order. Each section merges today's per-layer sketch and the hole comment's section, and has
   the same five parts: produces, needs, sources, tests, upstream work to read first.
8. Acceptance tests and nearby false statements.
9. Interfaces supplied to later work.
10. Boundaries with the other roadmaps.
11. Decisions: a table of those taken (number, name, the choice in one line, the convention or
    test that records it) and a list of those open.
12. How work is tracked (§G.1).
13. Index of names and numbers (§F.3).
14. References.

What leaves the blueprint: every sentence of status or history listed in §B.4, item 11; the
columns "Existing work" and "Issue" of the hole table; the section "Ordering and parallelism",
whose content is the column "needs"; the per-layer sketches that contradict the spine, which
are rewritten on the spine's types when merged into section 7.

What enters it: the tests and upstream notes that exist only in the hole comment (end of
section A); the statement of decisions 1 to 10, of which only the outcomes are written today;
what the spine asks of the Flock roadmap, which is a comment on issue 3.

### E.4 What the status contains, and what can be generated

Table of contents proposed:

1. Head: two sentences. What the file is; that the coverage table is checked by a script.
2. Coverage: one row per unit, generated.
3. What can start now: generated, or five lines by hand.
4. Upstream watch: the item, the unit, what it would replace, the adoption condition. No state
   and no date: the state is one click away and is what goes stale.
5. Pointers: to the blueprint's decisions and ledger, to the three registers, to the reviews.

**Coverage from the repository.** The repository forbids `sorry`, and the kernel axiom audit
rejects `sorryAx`, so a declaration that exists is proved. A unit is therefore built exactly
when the declarations that mark it exist. The probe `coverage_from_blueprint.py` does this
today from the blueprint's hole table, with no Lean: it reports the tables-and-stacking unit
at 15 of 15 names, the composition at 2 of 2, the public-input phase at 1 of 1, and every
unbuilt unit at 0, except where the table lists names that are not the unit's own (§B.5, item
6). What it needs from the blueprint is a column "built when declared" holding, for each unit,
names that this unit and no other declares. The public-input phase sets the pattern: a phase
`x` is marked by `xPhase` and `xComplete` for its first half and `xSecurity` for its second.

Proposed, for the owner to decide: `scripts/check-protocol-status.py`, run by
`scripts/validate.sh` and by the workflow "Documentation integrity". It reads the units table
of the blueprint, looks each marking name up under `LeanerVM/`, and compares the result with
the table between two markers in the status; on a difference it fails and prints the table to
paste, and with `--write` it rewrites it. A planted difference goes into
`scripts/test-policy-checks.py`, as for the other policy scripts. The same script can check
two more things this review found by hand: that every name of the interface list that belongs
to a built unit is declared, and the import rule of the proof system (no
`import LeanerVM.Arithmetization` under `LeanerVM/Protocol/` outside an allow-list), which the
Layer 1 review left open.

The head then needs no commit hash. A file cannot name the commit that contains it; today's
head names the parent and is wrong by construction after every merge (§B.1, items 1 to 5).

**Upstream state.** `scripts/check-upstreams.sh` already needs `gh` and the network and runs
weekly in the workflow "Upstream drift". It can print the state of each watched item next to
the pins' drift. The state then lives in the workflow's report and is never committed.

### E.5 The survey record

The 190 lines of "Survey record" (`protocol-status.md:434-622`) are a log of what was read.
They are history, useful "so the searches are not repeated", and they are what makes the
status long. Two options. Recommended: move them once, unchanged, to
`docs/reviews/protocol-survey-record.md`, headed as an archive; the directory is already the
repository's archive of reviews. Alternative: keep them as the last section of the status,
headed "Record (history, not a source of truth)", which keeps a hand-maintained status long.

### E.6 The review handoffs

A handoff is a record of what was found at one commit. It is never a specification.

- A finding that is accepted becomes blueprint text (a convention, a signature, an acceptance
  test, a decision) in the pull request that meets it. The handoff's disposition table cites
  the blueprint's section, by name.
- The handoff gets one line at its head: the commit it describes, and "an archive; names and
  paths are the reviewed commit's; for the current state read the blueprint".
- The status does not summarise reviews. `docs/README.md` keeps its index of handoffs, one
  line each, without dispositions.
- Texts a handoff drafts for GitHub (`protocol-spine.md:662-769`) are applied by editing the
  blueprint, since the specifications they patch move there.

### E.7 The tracker and the hole comment

The body of issue 12: the pointers, the checklist, and two lines on how to claim (§G.4).
No ledger, no watch list, no table of pull requests, no decisions, no list of names, no
"frontier".

The hole comment: its thirteen sections move to the blueprint, corrected on the way (§B.3). The
comment is then edited by its author to one line, "The specifications of the units of work
are in the blueprint, section 'The units of work'", so that links to it still land somewhere.

The three comments by the other contributor are a record of claims made in September and need
nothing. Their content that is still live (four claims) is already in the bodies of intention
issues 28, 31, 33, 37.

**Claiming without comments.** A maintainer, or an agent acting for one, edits the checklist
line in the body. A contributor without write access cannot edit the body; they open an
intention issue whose body names the unit and the exact declarations taken, which they can
edit themselves, and the maintainer links it from the checklist line. Nobody claims by
comment. This is what the four live claims already do.

## F. Proposal: the codes

### F.1 What is replaced by names, and what stays

| Family | Proposal |
| --- | --- |
| Units of work | names. The letters `S`, `G`, `I`, `P`, `C`, `K`, `L` go |
| Ledger entries | names |
| Findings of reviews | names, in the handoff's own disposition table; never cited by letter outside the handoff |
| Findings against the leanVM sources, the libraries, Lean | names, each a heading in its register, so that it has an anchor; the former code is kept once, in the register, to read old pull requests |
| Layers 0 to 13 | stay, as the numbers of the blueprint's sections, with the name: "the bus phase (Layer 6)" |
| Acceptance tests 1 to 28 | stay, with the name the blueprint already gives each in bold |
| Decisions 1 to 15 | stay, each given a name |
| Target theorems T1 to T8 | stay; owned by `architecture.md` |
| Category A, Category B | replaced by the two words they stand for: "written from the specification", "transcribed from its source" |

The rule for what stays: **the name stands beside the number at every use.** "Acceptance test
24" alone is not allowed; "the extractor computes (acceptance test 24)" is. A reference to the
other roadmap's layer, test or decision always says "leanISA".

If the owner prefers to keep numbers for the findings against the sources, the scheme without
collisions is a single counter in `docs/leanvm-target.md`, without letters, across both
roadmaps ("source finding 31"), with the former codes in one column. Letters are what collide.

### F.2 The mapping from every code to its name

**Units of work.** The short form is for branch names, pull-request titles and the checklist.

| Former code | Name | Short form |
| --- | --- | --- |
| `0` | field instances (Layer 0) | `field-instances` |
| `L1` | tables and stacking (Layer 1) | `tables-stacking` |
| `S` | the spine | `spine` |
| `C1` | knowledge-soundness composition (the port of ArkLib pull request 615) | `knowledge-append` |
| `I1` | Clean expressions as polynomials (Layer 2) | `clean-polynomials` |
| `I2` | the adaptor (Layer 3) | `adaptor` |
| `G1` | sumcheck: definition and completeness (Layer 4) | `sumcheck-def` |
| `G2` | sumcheck: knowledge soundness (Layer 4) | `sumcheck-security` |
| `G3` | batching by powers (Layer 4) | `batching` |
| `G4` | fingerprint and collision bound (Layer 5) | `fingerprint` |
| `G5` | grand-product GKR: definition and completeness (Layer 5) | `gkr-def` |
| `G6` | grand-product GKR: knowledge soundness (Layer 5) | `gkr-security` |
| `P1` | bus phase: definition and completeness (Layer 6) | `bus-def` |
| `P2` | bus phase: knowledge soundness (Layer 6) | `bus-security` |
| `P3` | table sumcheck phase: definition and completeness (Layer 7) | `table-def` |
| `P4` | table sumcheck phase: knowledge soundness (Layer 7) | `table-security` |
| `P5` | public-input phase (Layer 8) | `public-input` |
| `P6` | Flock phase, the interface to the Flock roadmap (Layer 9) | `flock-interface` |
| `P7` | opening phase: definition and completeness (Layer 10) | `opening-def` |
| `P8` | opening phase: knowledge soundness (Layer 10) | `opening-security` |
| `K1` | WHIR opening (Layer 11) | `whir` |
| `K2` | Merkle trees, byte hasher, WHIR parameters (Layer 11) | `merkle-parameters` |
| `K3` | transcript, proof object, compiled verifier (Layer 12) | `compiled-verifier` |
| `K4` | the base theorems of T4 (Layer 13) | `base-theorems` |

**Ledger entries.**

| Former code | Name |
| --- | --- |
| `A1` | admitted upstream: sumcheck round knowledge soundness |
| `A2` | admitted upstream: composition of knowledge soundness |
| `A3` | admitted upstream: round-by-round implies plain |
| `A4` | admitted upstream: context lifting (not consumed) |
| `A5` | admitted or absent upstream: Fiat-Shamir and BCS security |
| `A6` | absent upstream: grand product, GKR, batching, stacking |
| `A7` | absent upstream: WHIR, Merkle trees, BLAKE2s |
| `A8` | admitted upstream: correlated agreement up to Johnson |
| `A9` | admitted upstream: ring-switching packing |
| `C1` | absent in Clean: expressions as polynomials |
| `C2` | asked of leanISA: power-of-two heights, bus data per channel (done) |
| `C3` | absent in Clean: balance counted in the naturals |
| `C4` | absent in Clean: fixed columns and sound prover data |

**Findings against the leanVM sources** (to `docs/leanvm-target.md`).

| Former code | Name |
| --- | --- |
| `S6` | Fiat-Shamir section is `TODO` |
| `S9` | proof of the product lemma is `TODO` |
| `S10` | degree of the radix-4 round polynomial not stated |
| `S11` | one bus root not stated |
| `S12` | grinding per level not in Annex B |
| `S13` | retired |
| `S14` | the PDF is not the pinned text |
| `S15` | no rule for equal-size blocks |
| `S16` | equations are (1) to (4) |
| `F1` | numeric tags, no labels |
| `F2` | Flock's fixed coordinate has no provenance |
| `F3` | one root for push and pull |
| `F4` | sumcheck target derived, not sent |
| `F5` | bus forms share the last three powers |
| `F6` | cubic round polynomial, three scalars |
| `F7` | one coefficient never sent |
| `F8` | ring-switched claims take the low powers |
| `F9` | Python verifier omits four caps |
| `F10` | rejection set of the Rust verifier |
| `F11` | count tree holds the tables' counts only |
| `F12` | fill blocks make heights exact |
| `F13` | grinding binds the nonce on failure |
| `F14` | seed hashes a constant naming the circuit |
| `F15` | stack height bound checked separately |
| `F16` | security level and no grinding for the bus |
| `F17` | equal-size blocks in column-index order |
| `F18` | one equation on the words, not one per limb |

**Findings about the libraries** (to `docs/dependencies.md`) and **about Lean** (to
`tests/README.md`): the one-sentence descriptions of §D.2 serve as names; the former
codes `A10`-`A19`, `C5`, `C6`, `C10`, `C11`, `P1`, `P3`-`P6`, `E6`-`E15`, `E18` are kept in
one column of each register. The two "environment" findings that are rules (`E16`, `E17`) are
already the blueprint's convention *Generic code* (`protocol-blueprint.md:329`) and are
deleted.

**Findings of the three reviews**: the names are the third column of the last table of §D.2.
They are used inside the handoffs only.

### F.3 The index, drafted

One table, in the blueprint, section 13. It lists what keeps a number and what had a code.

| Name | Number or former code | Kind | In one sentence | Specified or decided at |
| --- | --- | --- | --- | --- |
| base proof extraction and completeness | T4 | target theorem | an accepted proof has an execution, and an execution has an accepted proof | `architecture.md`, "Target theorem ladder" |
| arithmetization and ISA equivalence | T1 | target theorem | constraint assignments and executions correspond, for well-formed programs | `architecture.md`; leanISA blueprint, Layer 10 |
| witness-generator correctness | T2 | target theorem | the generated assignment satisfies the constraints; out of scope here | `architecture.md` |
| recursive-verifier correctness | T5 | target theorem | out of scope here; `verify` is shaped for it | `architecture.md`; blueprint, "Boundaries" |
| recursion extraction | T6 | target theorem | open research; out of scope here | `architecture.md` |
| field instances | Layer 0; formerly hole `0` | unit of work | ArkLib as a dependency; sampling and oracle instances for the fields | blueprint, "The units of work" |
| tables and stacking | Layer 1; formerly `L1` | unit of work | hypercube tables, stacking with selectors, the index and bytecode columns | same |
| the spine | formerly `S` | unit of work | the instance, the relation, the seams, the phase interfaces, the composition | blueprint, "The spine" |
| knowledge-soundness composition | formerly hole `C1` | unit of work | the port of ArkLib pull request 615, deleted when the pin passes it | blueprint, "The spine" |
| Clean expressions as polynomials | Layer 2; formerly `I1` | unit of work | constraint and flush polynomials read off a Clean component | blueprint, "The units of work" |
| the adaptor | Layer 3; formerly `I2` | unit of work | the leanISA instance and the two maps between the stack and Clean's witness | same |
| sumcheck: definition and completeness | Layer 4; formerly `G1` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: one sentence, after the review of Layer 4] | same |
| sumcheck: knowledge soundness | Layer 4; formerly `G2` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR] | same |
| batching by powers | Layer 4; formerly `G3` | unit of work | several claims become one by the powers of one challenge | same |
| fingerprint and collision bound | Layer 5; formerly `G4` | unit of work | specification Lemma 5.2 and Theorem 5.1 | same |
| grand-product GKR: definition and completeness | Layer 5; formerly `G5` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR] | same |
| grand-product GKR: knowledge soundness | Layer 5; formerly `G6` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR] | same |
| bus phase: definition and completeness | Layer 6; formerly `P1` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR] | same |
| bus phase: knowledge soundness | Layer 6; formerly `P2` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR] | same |
| table sumcheck phase: definition and completeness | Layer 7; formerly `P3` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR] | same |
| table sumcheck phase: knowledge soundness | Layer 7; formerly `P4` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR] | same |
| public-input phase | Layer 8; formerly `P5` | unit of work | specification section 8.2: one challenge, the sent values checked per limb, one claim per public line | same |
| Flock phase | Layer 9; formerly `P6` | unit of work | the interface the Flock roadmap (issue 3) inhabits | same |
| opening phase: definition and completeness | Layer 10; formerly `P7` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: pending the question of specification section 8.5] | same |
| opening phase: knowledge soundness | Layer 10; formerly `P8` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR] | same |
| WHIR opening | Layer 11; formerly `K1` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR] | same |
| Merkle trees, byte hasher, WHIR parameters | Layer 11; formerly `K2` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: see §B.9 on VCVio's Merkle trees] | same |
| transcript, proof object, compiled verifier | Layer 12; formerly `K3` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR] | same |
| the base theorems | Layer 13; formerly `K4` | unit of work | [TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: see §B.6 on the program hypothesis] | same |
| heights are powers of two | decision 1 | decision, taken | leanISA's `Caps` requires it, so the two roadmaps state one relation | leanISA blueprint, Layer 8; issue 13 |
| statement and parameters | decision 2 | decision, taken | the public input is the statement; the instance indexes the protocol family | convention *Statements and parameters* |
| where the zerocheck is charged | decision 3 | decision, taken | in the bus phase, where the point is drawn; no separate phase | convention *Seams* |
| where generic code lives | decision 4 | decision, open | the `To<Library>` folders, or an ArkLib branch | blueprint, "Decisions" |
| an end-to-end run of the honest prover | decision 5 | decision, open | depends on the cost of the encoder | blueprint, "Decisions" |
| the witness is the stack | decision 6 | decision, taken | the protocol's witness is the committed column, in `Type 0` | "The relation ladder" |
| phases over an abstract instance | decision 7 | decision, taken | every phase is tested on the toy instance | convention *The wall* |
| five clauses, caps outside | decision 8 | decision, taken | the caps are a hypothesis of the adaptor's soundness theorem | "What the spine fixes" |
| balance is a permutation | decision 9 | decision, taken | the pushed and pulled tuple lists are permutations of each other | "What the spine fixes" |
| worst-case round-by-round knowledge soundness | decision 10 | decision, taken | per component, composed by the ported theorem | convention *Holes* |
| extractors are computable definitions | decision 11 | decision, taken | the protocol's extractor is `piopExtractor` | convention *Extractors*; acceptance test 24 |
| the strong Flock predicate | decision 12 | decision, taken | the predicate is Flock's R1CS on the committed region | Layers 3 and 9 |
| public lines, not cells | decision 13 | decision, taken | the statement fixes cells 0 and 1 of listed columns | convention *Public input* |
| the degree bound belongs to the instance | decision 14 | decision, taken | the bus seam bounds every term by it | convention *Seams*; acceptance test 28 |
| the public-input transcript | decision 15 | decision, taken | the prover sends the values; a line says whether its value is sent | convention *Public input*; Layer 8 |
| seams carry claims, never challenges | none today | decision, taken | what a phase emits is fixed by its knowledge soundness | "What the spine fixes" |
| schedules travel with the definitions | none today | decision, taken | the spine fixes the commit phase's schedule only | "What the spine fixes", item 4 |
| fingerprint degree | acceptance test 1 | acceptance test | the error carries a factor 4 | blueprint, "Acceptance tests" |
| padding leaves are 1 | acceptance test 2 | acceptance test | a zero pad zeroes every product | same |
| the nonzero count root is load-bearing | acceptance test 3 | acceptance test | a read with count zero balances | same |
| one root, not two | acceptance test 4 | acceptance test | the push and pull roots are one scalar | same |
| domain separators | acceptance test 5 | acceptance test | coordinate 0 separates the three buses | same |
| zerocheck point recycling | acceptance test 6 | acceptance test | the point is drawn after the commitment | same |
| back-loaded padding | acceptance test 7 | acceptance test | the lift keeps the table's sum | same |
| degree three, three scalars | acceptance test 8 | acceptance test | the wire carries three coefficients | same |
| shared bus powers | acceptance test 9 | acceptance test | the three bus forms share the last three powers | same |
| top limb of the public input | acceptance test 10 | acceptance test | the third claim is pooled though nothing is sent for it | same |
| joint list binding | acceptance test 11 | acceptance test | one member of the list satisfies all claims | same |
| absorb before squeeze | acceptance test 12 | acceptance test | sizes and root are observed before the first challenge | same |
| index column bit order | acceptance test 13 | acceptance test | bit `k` is coordinate `k` | same |
| bytecode slot bits | acceptance test 14 | acceptance test | the opcode is slot 3, low bit first; witness `bytecodeColumn_answer_boolVec` | same |
| selector alignment | acceptance test 15 | acceptance test | blocks sit at multiples of their size, largest first | same |
| variable order | acceptance test 16 | acceptance test | the highest variable is bound first | same |
| radix and parity | acceptance test 17 | acceptance test | one radix-2 layer when the height is odd | same |
| counts in the count tree | acceptance test 18 | acceptance test | the tables' count columns only | same |
| the extractor reads the stack | acceptance test 19 | acceptance test | the witness is read off the committed column | same |
| no exceptional challenge | acceptance test 20 | acceptance test | perfect completeness has no side condition | same |
| sizes are parameters | acceptance test 21 | acceptance test | the protocol is a family indexed by the sizes | same |
| tags, not labels | acceptance test 22 | acceptance test | four numeric tags | same |
| numeric error | acceptance test 23 | acceptance test | the bound at the caps | same |
| the extractor computes | acceptance test 24 | acceptance test | an extractor chosen classically proves soundness, not knowledge | same |
| the import rule holds | acceptance test 25 | acceptance test | no phase imports the arithmetization | same |
| seams are the contract | acceptance test 26 | acceptance test | a phase's output relation is the next one's input relation by definition | same |
| the toy instance is honest | acceptance test 27 | acceptance test | each clause fails alone | same |
| the bus seam bounds the degree | acceptance test 28 | acceptance test | a cubic term is rejected | same |
| admitted upstream: sumcheck round knowledge soundness | formerly ledger `A1` | ledger entry | the single-round bound is admitted in ArkLib at the pin | blueprint, "Dependencies", the ledger |
| admitted upstream: composition of knowledge soundness | formerly ledger `A2` | ledger entry | proved here by the port; the port is deleted at the pin bump | same |
| (the other eleven ledger entries, as in §F.2) | | ledger entry | | same |

[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: rows for the findings against the sources that the blueprint cites, once the
other agents' findings are merged into the register.]


## G. Proposed text

Drafts, ready to apply once the owner agrees; nothing was edited and nothing was posted. Each
passage is quoted as it stands at `b435631` (the status and the "How work is tracked" section
are unchanged at `144c5aa`; the blueprint's lines after 50 are 4 higher there) and then given
in full as proposed. Where a passage will have to change again because of technical findings
of the review that this dossier does not know, it carries a line
`[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: …]`. In the proposed texts, links are
written as the blueprint writes them (relative paths from `docs/roadmap/`, GitHub anchors
computed from the headings at `144c5aa`).

### G.1 The blueprint's section "How work is tracked"

**As it stands** (`protocol-blueprint.md:1472-1515`):

````markdown
## How work is tracked

- **This document** says what is wanted. It is edited by pull request and does not record
  history, status, or who is doing what.
- **[protocol-status.md](protocol-status.md)** says where things stand: coverage per layer,
  the frontier, the upstream ledger with issue numbers, open findings against the sources, and
  the decisions still pending. It is hand-maintained, headed by the commit it describes, and
  rewritten whole when a layer lands.
- **Issue [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12)** is the dashboard: the
  layer checklist with one of *open / claimed / in review / landed* per layer, links to the
  intention issue and pull request of each, the upstream ledger, and the frontier. It links to
  this document and to the status file at `main`, holds nothing that is not in them, and is
  updated when the status file is. Where the issue and the files disagree, the files win.
- **Holes.** Each unit of [The holes](#the-holes) is a section of the hole comment on the
  dashboard #12, stating what it consumes from the spine, what it produces, its tests and its
  upstream-watch rows. To claim a hole, or a slice of one, comment on #12 naming the hole and
  the exact declarations taken; the checklist line moves to *claimed*. No `[Hole]` or
  `[Intention]` issue is opened for it (the tracker stays small and readable whole); an issue is
  opened only when a slice needs its own discussion thread, titled
  `[Intention]: protocol - <hole>: …`, and it is closed by the pull request that lands the slice.
  A hole's `Def` with its `Complete`, and its `Security`, are separate slices and separate pull
  requests. Whoever takes a hole reads its upstream-watch rows first.
- **Upstream watch.** The status file keeps a table of external pull requests and issues that
  would replace or feed a hole: repository and number, the hole, the state, the condition under
  which it is adopted (usually a pin bump), and the date last checked. Whoever bumps a pin
  rewrites the table; whoever opens a hole's pull request cites the rows it consumed.
- **To report a problem with this roadmap** — a wrong or unclear target, a source discrepancy, a
  missing prerequisite — open an issue titled `[Roadmap]: protocol — …` naming the layer and
  the acceptance test or convention it touches. Durable source discrepancies are also recorded
  in [leanvm-target.md](../leanvm-target.md).
- **To change this document**, open a pull request that edits it, titled `docs(protocol): …`,
  and reference the dashboard in the description; say which layer, acceptance test, ledger entry
  or convention it touches. A pull request that lands a layer rewrites
  [protocol-status.md](protocol-status.md) whole in the same change and ticks the layer on the
  dashboard. A decision taken on a pending item is written here, as the convention or
  acceptance test it settles, and removed from the status file and the dashboard.
- **Upstream work** is tracked in the ledger of the status file: each entry carries the ArkLib
  (or Clean, CompPoly) issue or pull request number once opened, and the leanerVM layer that
  deletes its local copy when the pin moves.
- Pull requests carry `awaiting-review` when the author is done and `awaiting-author` after a
  review that asks for changes; the reviewer runs the `leanerVM-review` skill's three passes
  (specification, fidelity, hygiene) and reads the changed modules in full. A phase or component
  pull request imports spine names only, never `LeanerVM.Arithmetization`, and its tests run on
  the toy instance.
````

**As proposed.** The earlier draft's version, tightened: the table of homes stays; the tracker
is changed by editing its body; a maintainer sets the labels (contributors cannot, §B.7, item
4); the review skill is described by what it does, since the skill's files are under the
git-ignored `.claude/` and its name is wrong (§B.5, item 7); "hole" is kept and defined.

```markdown
## How work is tracked

A fact has one home, and every other place links to it and restates nothing.

| Kind of fact | Home |
| --- | --- |
| What is wanted and what was decided: the targets, the conventions, the specification of every hole, the acceptance tests, the decisions, the upstream ledger | this document |
| What is built on `main`, what can start now, the external work to watch | [protocol-status.md](protocol-status.md) |
| Who is taking which hole | the checklist in the body of issue [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12) |
| Discrepancies between the leanVM specification, its Rust and its Python verifier at the pin | [leanvm-target.md](../leanvm-target.md) |
| Limits of the pinned libraries | [dependencies.md](../dependencies.md) |
| Lean pitfalls met while building | [tests/README.md](../../tests/README.md) |
| What a review found at one commit | its handoff under [docs/reviews/](../reviews/), an archive |

- **This document** is the specification. It changes only by a pull request titled
  `docs(protocol): …` that names the hole, acceptance test, decision or convention it
  touches. It records no state, no date of landing, no number of a pull request in flight and
  no person.
- **The status** says what is built and nothing about what is wanted. Its coverage table has
  one row per hole of [The holes](#the-holes); a hole is built when the declarations its row
  there marks in bold exist under `LeanerVM/`. The pull request that lands a hole updates that
  row and the status's head in the same change and writes nothing else there by hand.
- **Issue #12** is the tracker: a link to this document and to the status, and one checklist
  line per hole with its name, its state (*open*, *claimed*, *in review*, *on `main`*), the
  claimant's intention issue or pull request, and a link to its layer section here. It holds
  no specification, no ledger, no decision and no list of pull requests. It is changed by
  editing its body; no comment is added and no issue opened to change it. Where it and the
  files disagree, the files win.
- **Holes.** A hole is a unit of work the spine leaves open: a phase, a generic component, the
  adaptor, or a piece of the compilation. Its specification is its layer section here: what it
  produces, what it needs, its sources at the pin, its tests, and the upstream work to read
  first. A hole in two halves (the definition with its completeness; the knowledge soundness)
  is two checklist lines and two pull requests.
- **To take a hole**, or part of one: with write access, edit its checklist line; without,
  open an issue titled `[Intention]: protocol - <name of the hole>: …` whose body names the
  declarations taken, and a maintainer links it from the line. An intention issue is closed by
  the pull request that lands it. Claims are not made in comments.
- **Names.** Holes, ledger entries, decisions and findings are called by the names the index
  at the end of this document gives them. Layers, acceptance tests, decisions and the target
  theorems of [architecture.md](../architecture.md) keep their numbers, always with the name
  beside the number: "the extractor computes (acceptance test 24)". A layer, test or decision
  of the leanISA roadmap is always called "leanISA …". No letter-number code is introduced.
- **Decisions.** A decision taken is written here as the convention, signature or acceptance
  test it settles, and as one row, with its name, of [Decisions](#decisions); an open
  decision is a row of the same table. Neither is copied anywhere else.
- **Upstream.** The ledger in [Dependencies and exact contracts](#dependencies-and-exact-contracts)
  says, for each result this work needs that is admitted or absent upstream at the pin, what
  replaces it here, the upstream issue or pull request, and when the local copy is deleted.
  External work in flight that may feed or replace a hole is the status's upstream watch.
  Whoever bumps a pin updates the ledger, the pins this document states, and the watch.
- **Discrepancies in the sources.** A difference between the specification, the Rust and the
  Python verifier at the pin is recorded under a name in
  [leanvm-target.md](../leanvm-target.md); where it binds a definition, the convention or
  layer section here cites it by that name.
- **Reviews.** A review's handoff records one commit. What is accepted from it becomes text of
  this document, and any edit it asks of the tracker is made, in the pull request that meets
  it; the handoff's disposition cites that text. Nothing cites a handoff as a specification.
- **To report a problem with this document**, open an issue titled `[Roadmap]: protocol - …`
  naming the hole and the acceptance test or convention it touches.
- **Pull requests** are titled `feat(protocol): …` and land with `./scripts/validate.sh`
  green. The description names the hole, the sources and the pin, whether each new definition
  is written from the specification or transcribed from its source, the ledger entries it
  touches and the target theorem it feeds. A maintainer labels it `awaiting-review` when the
  author is done and `awaiting-author` after a review that asks for changes. The reviewer reads
  the changed modules in full, in three passes: the statements against the specification,
  fidelity to the pinned sources, and hygiene. A phase or a generic component imports spine
  names only, never `LeanerVM.Arithmetization`, and is tested on the toy instance.
```

Two choices are left to the owner. (1) If the check proposed in §E.4 is adopted, the second
bullet gains one sentence: "`scripts/check-protocol-status.py`, run by `./scripts/validate.sh`,
fails when the coverage table and the repository disagree." (2) The link
[Decisions](#decisions) presumes the section "Decisions" of §E.3; until it exists, the bullet
reads "… as one row, with its name, of the status's decision list" and the status keeps that
list.

### G.2 The blueprint's table "The holes", its heading "The build", and the two sentences that send the reader to the hole comment

**As it stands** (`protocol-blueprint.md:588-615`):

````markdown
### The holes

Every hole consumes spine names only. Its specification is a section of the hole comment on the
dashboard #12 (the `[Hole]` issues were folded there on 2026-09-25); `L1` groups the leaves of
Layer 1 already in flight; the generic holes carry the ledger letters of the ArkLib work they will
become.

| Hole | Unit | Produces | Consumes | Existing work | Issue |
| --- | --- | --- | --- | --- | --- |
| S | the spine | everything under [What the spine fixes](#what-the-spine-fixes); built under `LeanerVM/Protocol/Spine/` | Layer 0 only (Layer 1's `Blocks.layout` inhabits `Layout` for aligned blocks) | leanth's explore branch | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| G1 | virtual sumcheck, `Sumcheck.Def` and completeness (Layer 4) | `Virtual`, `sumcheck`, `sumcheck_perfectCompleteness` | nothing | #42, ArkLib #1128, ArkLib `main`'s `Sumcheck/Interaction/` | [#37](https://github.com/Verified-zkEVM/leanerVM/issues/37) |
| G2 | sumcheck rbr knowledge, `Sumcheck.Security` (Layer 4, A1) | `sumcheck_rbrKnowledgeSoundness`, `d/\|F\|` per round | G1 | ArkLib #1129, `Interaction/Soundness.lean` | [#37](https://github.com/Verified-zkEVM/leanerVM/issues/37) |
| G3 | batching by powers, `Batch.Def` and `Security` (Layer 4) | `batchClaims`, `(k − 1)/\|F\|` | nothing | #43, ArkLib #615's `gammaPowers` | [#31](https://github.com/Verified-zkEVM/leanerVM/issues/31) |
| G4 | fingerprint, Lemma 5.1, the collision bound (Layer 5) | `fingerprint`, `sideProduct`, `sideProduct_poly_eq_iff`, `sideProduct_collision` | nothing | #39, ArkLib #901 | [#33](https://github.com/Verified-zkEVM/leanerVM/issues/33) |
| G5, G6 | GKR: `Gkr.Def` and completeness; `Gkr.Security` (Layer 5) | `gkr`, `gkrError`, its two theorems | G1 (G6 also G2) | ArkLib #818 as a pattern | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| L1 | Layer 1: tables, stacking, the fixed columns | `Blocks`, `stack_eval`, `unstack_eval₂`, `stack_eval_ambient`, `bitProductTable`, `powersTable`, `placeSlice`; `Blocks.layout`, `Layout.comap`, `ColumnClaim.holds_iff_weighted`, `padHigh`, `BlockClaim`, `idxColumn_eval`, `bytecodeColumn_answer_boolVec`, `bytecodeColumn_eval` | Layer 0; the spine's `Layout` and claims | leanth, per the catalog [leanth-reuse.md](leanth-reuse.md) | #27, #32, #35, #36 |
| I1 | Clean components as polynomials (Layer 2) | `Expression.toMvPolynomial`, `degreeBound`, `Component.toM3`, `Ensemble.toM3`, the two bridge theorems | Clean | Clean #466 | [#28](https://github.com/Verified-zkEVM/leanerVM/issues/28) |
| I2 | the adaptor (Layer 3) | `leanIsaInstance`, `stackOf`, `witnessOf`, `satisfiedBy_witnessOf`, `m3Holds_stackOf`, `witnessOf_stackOf` | S, I1, leanISA Layers 5–8, L1; #3 (the Flock witness generator, "the R1CS holds ⇒ the limb slots compress") | | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| P1, P2 | the bus phase (Layer 6) | `busPhase`, `leaf_decomposition`, `busError`; its `Security` | S, G5 (P2 also G6, G4), L1 | | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| P3, P4 | the table sumcheck phase (Layer 7) | `tableSummand`, `tableSummand_target`, `tableSumcheck`; its `Security` | S, G1 (P4 also G2) | #42 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| P5 | the public-input phase (Layer 8) | `publicInputPhase`, both halves | S, L1 | | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| P6 | the Flock phase at the flock seam (Layer 9) | `FlockOut`, `limbColumns`, `flockError_le`; the inhabitant is #3's | S | #3, ArkLib #383, #893 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| P7, P8 | the claim pool and the opening phase (Layer 10) | `Weight`, `WeightedClaim`, `openingPhase`; its `Security` | S, G3, G1, L1, #43 | | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| C1 | the knowledge-soundness append (ledger A2) | `Verifier.KnowledgeStateFunction.appendGuarded`, `Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first` in `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean`, the port of ArkLib #615's `Append/Knowledge.lean`: done on the spine's branch, as the port; deleted at the pin bump | ArkLib only | ArkLib #615, #676 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| K1 | WHIR over binary Reed–Solomon codes (Layer 11) | `encode`, `whirOpen`, `whirOpen_rbrSoundness`, `McaJohnson` | `WeightedClaim`, Layers 0, 1 | #3 F6, ArkLib #383, #992 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| K2 | Merkle, BLAKE2s bytes, the WHIR parameters (Layer 11) | `merkleRoot`, `merkleVerify`, `blake2sBytes`, `ladder` | leanISA Layer 1 | ArkLib #4 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| K3 | transcript, `Proof`, `verify`, `verify_iff_compiled`, the FS and BCS interfaces (Layer 12) | as Layer 12 | S (schedules, phase `Def`s), K1, K2 | ArkLib #848, #469, #627 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| K4 | T4 (Layer 13) | `baseVerifier_extractsExecution`, `baseProver_complete` | K3, I2, leanISA Layer 10 | | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
````

**As proposed.** Every row is named in words; the rows are in build order; a hole in two
halves has one row per half, matching the checklist; the field instances (Layer 0), a line of
today's checklist, get a row; the columns "Existing work" and "Issue" leave (their content
goes, without state, to each layer section's "upstream work to read first", and to the
tracker); "Consumes" becomes "Needs" and names holes, not codes or pull requests. In
"Produces", names the spine owns are removed (`Weight`, `WeightedClaim` from the opening phase,
`FlockOut` from the Flock phase: §B.5, item 6), "Lemma 5.1" becomes the specification's Lemma
5.2 and Theorem 5.1 (§B.5, item 8), and the generic shapes `Sumcheck.Def`, `Gkr.Def`,
`Batch.Def`, which the spine replaced by `Component.Def` (§B.4, item 7), are gone. A name in
bold is one this hole and no other declares, so that the status's coverage can be read off the
repository (§E.4); names not yet built follow the pattern of the public-input phase
(`xPhase`, `xComplete`, `xSecurity`) and are proposals.

```markdown
### The holes

A hole is a unit of work the spine leaves open: a phase, a generic component, the adaptor, or
a piece of the compilation. Every hole consumes spine names only, and its layer section below
is its specification: what it produces, what it needs, its sources, its tests and the upstream
work to read first. The table lists every hole in build order. A name in bold is declared by
this hole and no other; the hole is built when the names in bold of its row are declared.

| Hole | Specified in | Produces | Needs |
| --- | --- | --- | --- |
| field instances | [Layer 0](#layer-0-the-arklib-dependency-and-the-field-instances) | `Column`, `instSampleableTypeK`, **`instSampleableTypeE`**, **`card_E`**, **`evalOracle`**, `evalOracle_answer`, `instOracleInterfaceE`, `instOracleInterfaceListE` | nothing |
| the spine | [The spine](#the-spine) | everything under [What the spine fixes](#what-the-spine-fixes), under `LeanerVM/Protocol/Spine/` and the generic modules of `LeanerVM/Protocol/ToArkLib/` it imports; marked by **`M3Holds`**, **`Phases`**, **`piop_perfectCompleteness`**, **`piop_rbrKnowledgeSoundness`** | field instances |
| the knowledge-soundness composition | [What the spine fixes](#what-the-spine-fixes), item 5 | **`Verifier.KnowledgeStateFunction.appendGuarded`**, **`Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`** (`ToArkLib/KnowledgeAppend.lean`, the port of ArkLib pull request 615, deleted when the pin passes it) | ArkLib only |
| tables and stacking | [Layer 1](#layer-1-hypercube-tables-stacking-the-index-and-bytecode-columns) | `Blocks`, **`Blocks.stack_eval`**, **`Blocks.unstack_eval₂`**, **`Blocks.stack_eval_ambient`**, `bitProductTable`, `powersTable`, `placeSlice`, **`Blocks.layout`**, `Layout.comap`, **`ColumnClaim.holds_iff_weighted`**, `padHigh`, `BlockClaim`, **`idxColumn_eval`**, **`bytecodeColumn_answer_boolVec`**, `bytecodeColumn_eval` | field instances; the spine's `Layout` and claims |
| Clean expressions as polynomials | [Layer 2](#layer-2-clean-components-as-polynomials) | **`Expression.toMvPolynomial`**, `Expression.degreeBound`, `Component.toM3`, **`Ensemble.toM3`**, **`toM3_constraints_iff`**, **`toM3_flushes_eq`** | Clean |
| the adaptor | [Layer 3](#layer-3-the-m3-instance-of-leanisa) | **`leanIsaInstance`**, `stackOf`, `witnessOf`, **`satisfiedBy_witnessOf`**, **`m3Holds_stackOf`**, `witnessOf_stackOf` | the spine; Clean expressions as polynomials; tables and stacking; leanISA Layers 5 to 8; from the Flock roadmap (#3), its witness generator and the lemma "the R1CS holds ⇒ the limb slots compress" |
| sumcheck: definition and completeness | [Layer 4](#layer-4-sumcheck-for-eq-weighted-virtual-polynomials) | `Virtual`, **`sumcheck`**, **`sumcheck_perfectCompleteness`** | nothing |
| sumcheck: knowledge soundness | [Layer 4](#layer-4-sumcheck-for-eq-weighted-virtual-polynomials) | **`sumcheck_rbrKnowledgeSoundness`**, error `d/\|F\|` per round | sumcheck: definition and completeness |
| batching by powers | [Layer 4](#layer-4-sumcheck-for-eq-weighted-virtual-polynomials) | **`batchClaims`** with both halves, error `(k − 1)/\|F\|` | nothing |
| fingerprint and collision bound | [Layer 5](#layer-5-fingerprints-the-grand-product-and-gkr) | `fingerprint`, `sideProduct`, **`sideProduct_poly_eq_iff`** (specification Lemma 5.2), **`sideProduct_collision`** (specification Theorem 5.1) | nothing |
| grand-product GKR: definition and completeness | [Layer 5](#layer-5-fingerprints-the-grand-product-and-gkr) | `ProductTree`, **`gkr`**, `gkrError`, **`gkr_perfectCompleteness`** | sumcheck: definition and completeness |
| grand-product GKR: knowledge soundness | [Layer 5](#layer-5-fingerprints-the-grand-product-and-gkr) | **`gkr_rbrKnowledgeSoundness`** | grand-product GKR: definition and completeness; sumcheck: knowledge soundness |
| bus phase: definition and completeness | [Layer 6](#layer-6-the-bus-phase) | `pushLeaves`, `pullLeaves`, `countLeaves`, `leaf_decomposition`, `busError`, **`busPhase`**, **`busComplete`** | the spine; grand-product GKR: definition and completeness; tables and stacking (`Blocks.stack_eval_ambient_one`, `idxColumn_eval`, `bytecodeColumn_eval`) |
| bus phase: knowledge soundness | [Layer 6](#layer-6-the-bus-phase) | **`busSecurity`** | bus phase: definition and completeness; grand-product GKR: knowledge soundness; fingerprint and collision bound |
| table sumcheck phase: definition and completeness | [Layer 7](#layer-7-the-table-sumcheck-phase) | `tableSummand`, `tableSummand_target`, **`tableSumcheck`**, **`tableSumcheckComplete`** | the spine; sumcheck: definition and completeness |
| table sumcheck phase: knowledge soundness | [Layer 7](#layer-7-the-table-sumcheck-phase) | **`tableSumcheckSecurity`** | table sumcheck phase: definition and completeness; sumcheck: knowledge soundness |
| public-input phase | [Layer 8](#layer-8-the-public-input-phase) | **`publicInputPhase`**, **`publicInputComplete`**, **`publicInputSecurity`**; the computable `PublicInput.pSpec`, `check`, `pooled`, `prover`, `verifier` that the compiled verifier reads | the spine; tables and stacking (`evalMle_append_boolVec`) |
| Flock phase | [Layer 9](#layer-9-the-flock-and-ring-switching-boundary) | **`FlockInterface`**, with `limbColumns` and `flockError_le`; its inhabitant is the Flock roadmap's (#3) | the spine |
| opening phase: definition and completeness | [Layer 10](#layer-10-the-claim-pool-the-opening-sumcheck-and-the-oracle-protocol) | **`openingPhase`**, **`openingComplete`** | the spine; batching by powers; sumcheck: definition and completeness; tables and stacking (`ColumnClaim.holds_iff_weighted`) |
| opening phase: knowledge soundness | [Layer 10](#layer-10-the-claim-pool-the-opening-sumcheck-and-the-oracle-protocol) | **`openingSecurity`** | opening phase: definition and completeness; batching by powers; sumcheck: knowledge soundness |
| WHIR opening | [Layer 11](#layer-11-whir-over-binary-reedsolomon-codes-and-merkle-trees) | `encode`, `encode_column_weight`, **`whirOpen`**, **`whirOpen_rbrSoundness`**, `McaJohnson` | the spine's `WeightedClaim`; field instances; tables and stacking |
| Merkle trees, the byte hasher and the WHIR parameters | [Layer 11](#layer-11-whir-over-binary-reedsolomon-codes-and-merkle-trees) | **`merkleRoot`**, **`merkleVerify`**, **`blake2sBytes`**, **`ladder`** | leanISA Layer 1 (`compress`) |
| transcript, proof object and compiled verifier | [Layer 12](#layer-12-compilation-the-transcript-the-proof-and-the-executable-verifier) | `FsState`, `Proof`, `RoundPoly.decode`, `leanVmIopp`, **`verify`**, **`verify_iff_compiled`**, `FiatShamirSecurity`, `BcsSecurity`, **`verify_knowledgeSound`** | the definitions of the five phases (not their knowledge soundness); WHIR opening; Merkle trees, the byte hasher and the WHIR parameters |
| the base theorems (target T4) | [Layer 13](#layer-13-t4-and-the-fixtures) | **`baseVerifier_extractsExecution`**, **`baseProver_complete`** | transcript, proof object and compiled verifier; the adaptor; leanISA Layer 10 |
```

[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: the names and shapes of the generic
components of Layers 4 and 5 once they are restated as `Component.Def`s with their `Complete`
and `Security` (today's sketch states `sumcheck`, `gkr` and `batchClaims` as bare
`OracleReduction`s); the statement types of the bus, table sumcheck, Flock and opening phases;
the opening phase's schedule, pending the question of specification §8.5 ("there is no
separate reduction sumcheck"); whether Layer 11 reuses the Merkle trees of the VCVio pin
(§B.9); the hypothesis on the program of the base theorems (§B.6, item 1). Each may change a
row's "Produces" or "Needs".]

**The heading and first paragraph of the build**, as they stand (`protocol-blueprint.md:617-623`):

````markdown
## The build: the spine, then fourteen layers

Every layer names what to define and what to prove, intrinsically. Each layer's tests are part
of the layer. The spine (hole S) is built after Layer 0; the layers
keep their numbers and are read as the holes of the table above. Layers 3 and 6 to 10 are written
over `I : M3Instance`; where a signature below says `(prog) (s)`, read `leanIsaInstance prog s`.
A layer lands only fully proved; a hole's `Def` and `Security` are separate landings.
````

As proposed. The heading says the spine comes first, which is false (Layer 0 precedes it,
`:620`); "hole S" and "read as the holes" go. No link in the repository points at the old
anchor `#the-build-the-spine-then-fourteen-layers` (`grep` over the tracked Markdown).

```markdown
## The layers

Fourteen layers, numbered 0 to 13, are built in order, with the spine after Layer 0. Each layer
section specifies the holes of [The holes](#the-holes) that name it: what to define and what to
prove, its sources, its tests, which are part of it, and the upstream work to read first. The
phases (Layers 6 to 10) are written over an abstract `I : M3Instance` with the statement types
of `Phases`; Layer 3 builds the leanISA instance and the adaptor. A hole lands only fully
proved, and its definition with its completeness lands apart from its knowledge soundness.
```

[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: today's sentence "where a signature
below says `(prog) (s)`, read `leanIsaInstance prog s`" is dropped above because the sketches
of Layers 4 to 7, 9 and 10 are to be restated on the spine's types (§B.4); if they are not
restated in the same pull request, the sentence stays.]

**The two sentences that send the reader to the hole comment.** As they stand
(`protocol-blueprint.md:339-341`): "The spine is the one pull request (hole S; its
specification is a section of the [hole comment](…#issuecomment-5833669972) on the dashboard
#12) that fixes everything two neighbouring pieces of work would otherwise have to agree on,
and proves the composition once." And `:590-593`, quoted in the table above. As proposed: the
first becomes "The spine fixes everything two neighbouring pieces of work would otherwise have
to agree on, and proves the composition once."; the second is replaced by the new first
paragraph of "The holes" above.

### G.3 The status file's head and "At a glance", for `main` at `144c5aa`

**As it stands** (`protocol-status.md:1-27`, identical at `b435631` and `144c5aa`):

````markdown
# Status: the leanVM proof system on ArkLib

This file records where the [protocol roadmap](protocol-blueprint.md) stands as of `main` at
`f4d858c` (Layer 1, PR #59, merged on 2026-09-29), checked on 2026-09-29, together with the open
pull requests and the public-input phase (hole P5) as built on the branch
`feat/protocol-public-input` (pull request #60); this snapshot accompanies that branch. It is a
hand-maintained snapshot, rewritten whole when a layer or hole lands or a decision is taken; the
roadmap is the authority on what is wanted, and the tracking issue
[#12](https://github.com/Verified-zkEVM/leanerVM/issues/12) mirrors the hole checklist below.
Open pull requests and prerequisite-branch adoption are not changes landed on `main`. The
dependency pins are unchanged.

## Where this roadmap stands

**At a glance.** Layer 0 is on `main` (#15, 2026-09-11), and so is the spine (hole S, #58,
`5cb7da6`, 2026-09-28) with the knowledge-soundness append ArkLib admits (hole C1, ledger A2),
ported from ArkLib #615 to `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean`: `#print axioms` on
`piop_rbrKnowledgeSoundness` gives the kernel's three axioms. The spine is generic over
`I : M3Instance` and imports nothing from `LeanerVM/Arithmetization/` (the wall holds). Concrete
in it: the instance and the relation `M3Holds` (decidable; the toy instance decides it by
evaluation), the claims and the six seams, the hole interfaces
`Component.Def`/`Complete`/`Security` with their binary composition, the pass-through phase and
the commit phase with both halves proved, the bundle `Phases`, the protocol's extractor
`piopExtractor` and the two master theorems `piop_perfectCompleteness` and
`piop_rbrKnowledgeSoundness`, each conditional on the phases only, and the refinement of
relations. It was revised before merging after the adversarial review
[protocol-spine.md](../reviews/protocol-spine.md).
````

What is wrong with it today: it describes `f4d858c` and calls the public-input phase a draft
on a branch (§B.1, items 1 to 5); it says the pins are unchanged, and pull request 61 has moved
four of them (§B.11, item 7); it names holes by code. The "At a glance" paragraph itself is
still true of the spine; what it omits is everything after it.

**As proposed.** The head names the revision it describes (the status cannot name the commit
that contains it; it names the last merge it accounts for, as today), states the pins once,
and says what the file is. "At a glance" becomes a table of what is on `main` and three short
paragraphs. Names replace codes throughout; a hole's name is the one of §G.2.

```markdown
# Status: the leanVM proof system on ArkLib

Where the [protocol blueprint](protocol-blueprint.md) stands on `main` at `144c5aa`
(2026-09-29), checked on 2026-09-30. This file says what is built and nothing about what is
wanted: the blueprint is the specification, and issue
[#12](https://github.com/Verified-zkEVM/leanerVM/issues/12) says who is taking which hole.
Open pull requests are not part of `main`.

The pins are those of `upstreams.json` at `144c5aa`: leanVM `a386121f` (unchanged), ArkLib
`7653a901`, CompPoly `572f9973`, Clean `42fe4b26`, VCVio `a4232d08`, PolyFun `41d3b21d`, Lean
and Mathlib `v4.34.1`. The upgrade to them, pull request #61, is described in
[dependencies.md](../dependencies.md#lean-434-port-review).

## Where this stands

**At a glance.** Five holes are on `main`, and the pins moved once since the last of them:

| On `main` | Pull request | Commit | Merged |
| --- | --- | --- | --- |
| field instances (Layer 0) | #15 | `51021d9` | 2026-09-11 |
| the spine | #58 | `5cb7da6` | 2026-09-28 |
| the knowledge-soundness composition, ported from ArkLib pull request 615 | #58 | `5cb7da6` | 2026-09-28 |
| tables and stacking (Layer 1) | #59 | `f4d858c` | 2026-09-29 |
| the public-input phase (Layer 8), both halves, error `1/\|E\|` on its one challenge | #60 | `b435631` | 2026-09-29 |
| no hole: the upgrade to Lean 4.34.1 and the new pins | #61 | `144c5aa` | 2026-09-29 |

The two master theorems, `piop_perfectCompleteness` and `piop_rbrKnowledgeSoundness`, are
proved over an abstract instance `I : M3Instance` and are conditional on the five phases after
the commit (`Phases.Complete`, `Phases.Security`); of those five, the public-input phase is
built. The upgrade changed proofs and imports under `LeanerVM/Protocol/` and no statement; the
two probability bridges (`ToArkLib/GuardedVerdict.lean`, `ToVCVio/UniformSample.lean`) were
restated in VCVio's new probability notation with the same relations and bounds.

The import rule of the proof system (no module above the adaptor imports
`LeanerVM/Arithmetization/`) is checked by review, not by `scripts/check-layers.sh`. Two
modules import the arithmetization: `FixedColumns.lean`, whose bytecode column names the
program, an exception the blueprint lists; and `Basic.lean`, an empty placeholder that nothing
imports and the blueprint does not list.

Not built: the bus, table sumcheck, Flock and opening phases; the generic components
(sumcheck, batching by powers, the fingerprint and collision bound, grand-product GKR); Clean
expressions as polynomials; the adaptor; the WHIR opening; Merkle trees, the byte hasher and
the WHIR parameters; the transcript, the proof object and the compiled verifier; the two base
theorems (target T4). Three pull requests are open, each part of a hole: #39 (the fingerprint
polynomial) and #43 (power batching), both based on the branch of the closed #18, and #42 (the
honest round polynomials of a sumcheck), based on `main`; all three still put their modules
under `LeanerVM/Protocol/Generic/`, which the convention *Generic code* replaced.
```

[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: at `b435631` the status recorded that
`#print axioms` on `piop_rbrKnowledgeSoundness` and on every Layer 1 theorem gives the
kernel's three axioms (`protocol-status.md:17-18, 130-131`), and an axiom audit of 3298
declarations (`:59`); this dossier ran no Lean and cannot confirm either at `144c5aa`, where
the local build is not yet redone (brief, section 8). Whether the knowledge-soundness
composition that ArkLib admitted at `dca90385` is still admitted at `7653a901`, which decides
whether the local port stays, is a finding of the library review; the third row of the table follows it. The effect of the new CompPoly
pin on numerals in `K` (brief, section 8) belongs here if any fixture of the proof system
changed meaning.]

**The rest of the status, at the same revision.** The head and "At a glance" above replace
`:1-27`. The following lines must also change, or the file contradicts its own head:

- `:55-56` "(review finding D1)": name the finding ("the Layer 1 review's finding that the
  import rule has no script") and add `Basic.lean`, as above.
- `:58-60`: "The public-input phase (hole P5) is built, on the branch
  `feat/protocol-public-input`, pull request #60, a draft, …" becomes "The public-input phase
  is on `main` (#60, `b435631`, 2026-09-29)."; the rest of the paragraph stands.
- `:78-80` "Three pull requests are open beside #60": "Three pull requests are open".
- `:90-109`, the coverage table: row "P5" (`:101`) "built, draft #60 … lands when #60 merges"
  becomes "on `main` (#60, `b435631`)"; row "G4" (`:95`) "Lemma 5.1" becomes "Lemma 5.2 and
  Theorem 5.1"; every hole code becomes the name of §G.2.
- `:113-119`: the sentence "#60 carries the public-input phase" and the table row "#60
  (draft)" go.
- `:146-148`: "The public-input phase (P5) is the draft #60 … #60 ticks P5 on the dashboard
  when it merges" becomes "The public-input phase is on `main` (#60)".
- `:159-160`: the holes that can start now, by name.
- `:161-163`: "The pins have not moved. ArkLib `main` is 246 commits past `dca90385` (finding
  A18); the next bump is one planned change …" becomes "The pins moved with pull request 61
  (see the head)."
- `:177` "`ToCompPoly/{Stacking,AmbientStacking,Claims}.lean`": `Claims.lean` does not exist;
  the claim record is `BlockClaims.lean`.
- `:178` "ArkLib #4 (Merkle)": closed on 2026-09-27 in favour of VCVio issue 571 (§B.9).
- `:179` "the #907 slices landing on `main`": ArkLib issue 907 closed on 2026-09-26.
- `:190-206`, the upstream watch: its states are dated 2026-09-24 and several are wrong
  (§B.1, items 8 to 11).
- `:212` heading "Decisions pending" over decisions mostly taken: "Decisions".
- `:332`, `:355`, `:360`: the findings about ArkLib, Clean and CompPoly are headed by the former
  pins; they say so ("at the former pin `dca90385`").

[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: which rows of the upstream watch
(`:190-206`) and of the upstream ledger (`:171-184`) the upgrade settled or changed: ArkLib
`main`'s typed executor and one-round bound, "adopt when: the pin bump" (`:201`), are now in the
pin; Clean pull requests 466, 464 and 446 against the new Clean pin `42fe4b26`; "a CompPoly
containing #331" (`:162`).]

### G.4 The body of issue 12, and where the hole comment goes

**As it stands.** The body (`issue-12-body.md:1-97`, unchanged since 2026-09-28 14:28 UTC) has
nine parts: pointers and pins (`:1-4`), a claim to hold nothing of its own (`:6`), related
issues (`:8`), "What this roadmap builds (revision 2)" (`:10-14`, a 1,700-word restatement of the
spine), the hole checklist (`:16-40`), "Ordering" (`:42`), "Open pull requests (2026-09-28)"
(`:44-57`), "Upstream ledger" (`:59-74`), "Upstream watch" (`:76-78`), "Frontier" (`:80-85`),
"Decisions pending" (`:87-89`) and "How to work on this" (`:91-96`). Its checklist, quoted
whole because it is what the new body replaces:

````markdown
## Hole checklist

Status per hole: **open** / **claimed** (by a comment on this issue naming the declarations taken) / **in review** (the PR carrying `awaiting-review`) / **landed** (the merged PR). Each hole's specification (produces, consumes, tests, upstream watch) is a section of the [hole comment](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972). Tick a hole only when its pull request has merged with `./scripts/validate.sh` green and its tests in `tests/`. A hole with two halves ticks twice.

- [x] **0 — ArkLib dependency and field instances (Layer 0).** — *landed* (#15, 2026-09-11)
- [ ] **L1 — Layer 1: generic tables and stacking, and the leaves.** Generic half in draft #18 (rebase onto `main` pending; #25, #26 merged into it); leaves in review: #40 (`stack_eval_ambient`, #36), #38 (`unstack`, `BlockClaim`, #35), #41 (`idxColumn_eval`, `bytecodeColumn_slot`, #32), #26 (coefficient transport, #27). — *in review*; nothing lands before #18 does
- [x] **S — the spine.** — *landed* (#58, `5cb7da6`, 2026-09-28; reviewed the same day, [`docs/reviews/protocol-spine.md`](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/reviews/protocol-spine.md))
- [ ] **G1 — virtual sumcheck, `Sumcheck.Def` and completeness (Layer 4).** #37; the honest round algebra and the ArkLib bridge in #42 — *claimed*
- [ ] **G2 — sumcheck round-by-round knowledge, `Sumcheck.Security` (Layer 4, ledger A1).** #37; a one-round leaf prepared, unpublished — *claimed*
- [ ] **G3 — batching by powers, `Batch.Def` and `Security` (Layer 4).** #31; the algebra and the `(J − 1)/|F|` count in #43 — *claimed*
- [ ] **G4 — fingerprint, Lemma 5.1, the collision bound (Layer 5).** #33; the fingerprint in #39 — *claimed*
- [ ] **G5, G6 — GKR: a `Component.Def` for the grand product and its two halves (Layer 5).** — *open*
- [ ] **I1 — Clean components as polynomials (Layer 2).** #28; Clean #466 approved, unmerged — *claimed*
- [ ] **I2 — the adaptor (Layer 3): `leanIsaInstance` (an `M3Instance` with `d := 2`, three public lines on `mem_0, mem_1, mem_2`, and a layout with two readers: #18's `Blocks` for the aligned blocks, a strided reader for the eighteen BLAKE2S limb slots of `q_flock`), `stackOf`, `witnessOf`, `satisfiedBy_witnessOf (hs : s.Admissible prog)`, `m3Holds_stackOf`, `witnessOf_stackOf`.** — *open; needs I1, #18, and #3's witness generator and compression lemma*
- [ ] **P1, P2 — the bus phase (Layer 6): `Phase.Def I I.Stmt (I.Stmt × BusOut I)` against `Seam.commit`, `Seam.bus`.** — *open; P1 needs G5*
- [ ] **P3, P4 — the table sumcheck phase (Layer 7): `Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)` against `Seam.bus`, `Seam.table`.** — *open; needs G1*
- [ ] **P5 — the public-input phase (Layer 8): `Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I)` against `Seam.table`, `Seam.pub`, over `I.publicLines`: one challenge, one pooled column claim per line, the prover sends nothing.** — *open; the smallest phase, a good first hole*
- [ ] **P6 — the Flock phase (Layer 9): `Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I)` against `Seam.pub`, `Seam.flock`; its input predicate is the strong `aux`, Flock's R1CS on `q_flock` (decision 12), the eighteen column claims over the strided reader `limbColumns`; the inhabitant is #3's.** — *open; needs #3*
- [ ] **P7, P8 — the opening phase (Layer 10): `Phase.Def I (I.Stmt × FlockOut I) Unit` against `Seam.flock`, `Seam.done`.** — *open; needs G1, G3*
- [x] **C1 — the knowledge-soundness append (ledger A2).** — *landed* with the spine (#58): `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean`, the port of ArkLib #615's `Append/Knowledge.lean` at `ca7a2577`, with its attribution; `Component.Security.append` and the master knowledge theorem take no assumption. The file is deleted, and its two names replaced by ArkLib's, when the pin moves past #615
- [ ] **K1 — WHIR over binary Reed–Solomon codes (Layer 11).** Shared with #3 F6 — *open*
- [ ] **K2 — Merkle trees, BLAKE2s bytes, the WHIR parameters (Layer 11).** — *open*
- [ ] **K3 — transcript, `Proof`, `verify`, `verify_iff_compiled`, the FS and BCS interfaces (Layer 12).** — *open; needs the phase `Def`s, K1, K2*
- [ ] **K4 — T4: `baseVerifier_extractsExecution`, `baseProver_complete` (Layer 13).** — *open; needs K3, I2, leanISA Layer 10*
- [x] **VCVio controls for K3 and P7.** #29, #30 — *landed upstream* (VCVio #784)

Ordering: P1, P3, P5 (`Def`s), G1 to G6, I1, K1 and K2 can start now on `main`; I2 after #18 and I1 land; P2, P4, P8 also need the `Security` of the generic component they use. K3 needs the phase `Def`s, K1 and K2. K4 last.
````

Against the repository at `b435631`/`144c5aa` and GitHub on 2026-09-30, its state is wrong in
five lines: Layer 1 is on `main` (#59), not "in review" behind #18 (`:21`); the public-input
phase is on `main` (#60) and its line specifies the opposite transcript, "the prover sends
nothing" (`:32`); pull requests 18, 38, 40, 41 are closed (`:21`, `:50-53`); the VCVio controls
(`:40`) are not a hole; and the pins of `:4` and `:14` are no longer the pins (§B.11).

**As proposed**, ready to paste as the whole body. It restates nothing of the blueprint: the
specification, the ledger, the decisions, the ordering and the list of pull requests are gone
(they are in the blueprint, on GitHub, or generated in the status). The state of each line is
derived from `main` at `144c5aa` (declarations present), from the merged pull requests (15, 58,
59, 60), and from the open intention issues and pull requests (28, 31, 33, 37; 39, 42, 43),
not from the old body. Links to sections use the anchors of the headings at `144c5aa`; those of
§G.2 ("The holes", "The layers") are the proposed ones.

````markdown
**Blueprint:** [`docs/roadmap/protocol-blueprint.md`](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md): what is wanted; the specification of every hole, in its layer section; the decisions; the upstream ledger.
**Status:** [`docs/roadmap/protocol-status.md`](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-status.md): what is built on `main`, what can start now, the external work to watch.
**Pins:** [`upstreams.json`](https://github.com/Verified-zkEVM/leanerVM/blob/main/upstreams.json).

This issue is the checklist below and nothing else. It changes by an edit of this body, never by a comment; where it and the files disagree, the files win. The rules are in the blueprint's [How work is tracked](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#how-work-is-tracked).

Related: #4 (leanISA: the relation `SatisfiedBy` the adaptor targets), #3 (Flock: the Flock phase, and the witness generator and compression lemma the adaptor takes), #16 and #20 (Clean's bus balance over binary fields), #23 (fixed columns after Clean pull request 446).

## Holes

State: **open**; **claimed** (the claimant's intention issue, and any pull request carrying part of the hole); **in review** (the hole's pull request, labelled `awaiting-review`); **on `main`** (the merged pull request). A line is ticked when its pull request has merged.

- [x] **Field instances** (Layer 0): on `main`, #15. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-0-the-arklib-dependency-and-the-field-instances)
- [x] **The spine**: on `main`, #58. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#the-spine)
- [x] **The knowledge-soundness composition** (the port of ArkLib pull request 615): on `main`, #58. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#what-the-spine-fixes)
- [x] **Tables and stacking** (Layer 1): on `main`, #59. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-1-hypercube-tables-stacking-the-index-and-bytecode-columns)
- [ ] **Clean expressions as polynomials** (Layer 2): claimed, #28; upstream as Clean pull request 466. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-2-clean-components-as-polynomials)
- [ ] **The adaptor** (Layer 3): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-3-the-m3-instance-of-leanisa)
- [ ] **Sumcheck: definition and completeness** (Layer 4): claimed, #37; the honest round polynomials in #42. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-4-sumcheck-for-eq-weighted-virtual-polynomials)
- [ ] **Sumcheck: knowledge soundness** (Layer 4): claimed, #37. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-4-sumcheck-for-eq-weighted-virtual-polynomials)
- [ ] **Batching by powers** (Layer 4): claimed, #31; the batching algebra in #43. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-4-sumcheck-for-eq-weighted-virtual-polynomials)
- [ ] **Fingerprint and collision bound** (Layer 5): claimed, #33; the fingerprint polynomial in #39. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-5-fingerprints-the-grand-product-and-gkr)
- [ ] **Grand-product GKR: definition and completeness** (Layer 5): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-5-fingerprints-the-grand-product-and-gkr)
- [ ] **Grand-product GKR: knowledge soundness** (Layer 5): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-5-fingerprints-the-grand-product-and-gkr)
- [ ] **Bus phase: definition and completeness** (Layer 6): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-6-the-bus-phase)
- [ ] **Bus phase: knowledge soundness** (Layer 6): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-6-the-bus-phase)
- [ ] **Table sumcheck phase: definition and completeness** (Layer 7): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-7-the-table-sumcheck-phase)
- [ ] **Table sumcheck phase: knowledge soundness** (Layer 7): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-7-the-table-sumcheck-phase)
- [x] **Public-input phase** (Layer 8), both halves: on `main`, #60. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-8-the-public-input-phase)
- [ ] **Flock phase** (Layer 9): open; its inhabitant is #3's. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-9-the-flock-and-ring-switching-boundary)
- [ ] **Opening phase: definition and completeness** (Layer 10): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-10-the-claim-pool-the-opening-sumcheck-and-the-oracle-protocol)
- [ ] **Opening phase: knowledge soundness** (Layer 10): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-10-the-claim-pool-the-opening-sumcheck-and-the-oracle-protocol)
- [ ] **WHIR opening** (Layer 11): open; shared with #3. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-11-whir-over-binary-reedsolomon-codes-and-merkle-trees)
- [ ] **Merkle trees, the byte hasher and the WHIR parameters** (Layer 11): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-11-whir-over-binary-reedsolomon-codes-and-merkle-trees)
- [ ] **Transcript, proof object and compiled verifier** (Layer 12): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-12-compilation-the-transcript-the-proof-and-the-executable-verifier)
- [ ] **The base theorems** (Layer 13, target T4 of `docs/architecture.md`): open. [Specification](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#layer-13-t4-and-the-fixtures)

## To take a hole

With write access, edit its line above. Without, open an issue titled `[Intention]: protocol - <name of the hole>: …` whose body names the declarations taken; a maintainer links it here. To report a problem with the blueprint, open `[Roadmap]: protocol - …`.
````

[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: holes the review adds, splits, renames
or removes (for example if the opening phase has no sumcheck of its own, or if Layer 11 takes
VCVio's Merkle trees), mirrored from the table of §G.2; the list must stay one line per row of
that table.]

Two notes on the proposed body. The VCVio controls line of today's checklist (`:40`) is not a
hole; the controls landed upstream (VCVio pull request 784) and their two intention issues
should close (§G.5). The line on Clean expressions as polynomials says "claimed" and not "in
review": its implementation is a Clean pull request, not a leanerVM one, and no leanerVM pull
request carries the `awaiting-review` label today.

**Where each section of the hole comment goes.** The comment
(`issue-12-comment-5833669972.md`, thirteen sections, last edited 2026-09-28) is the
specification the blueprint points to (§B.3). Each section goes to one layer section of the
blueprint; most of its content is already there, some is only in the comment and must move,
and some is obsolete and must not move.

| Section of the comment | Goes to | Already in the blueprint | Only in the comment: move | Obsolete: do not move |
| --- | --- | --- | --- | --- |
| the spine (`:5-26`) | The spine | everything, as built (`:410-554`); acceptance tests 24 to 27 | nothing | the pre-build signatures (`Pool`, `Seam.pool`, `busSpec`… `openSpec`, `Sumcheck.Def`, `Gkr.Def`, `Batch.Def`, `KnowledgeAppend` as an assumption, `knowledgeSound_of_refinement`), which its own note at `:9` disowns; "settle them on this issue" (`:24`) |
| grand-product GKR, both halves (`:28-42`) | Layer 5 | `ProductTree`, `gkr`, `gkrError` with its three terms, the schedule (convention *GKR*, `:321`; `:940-942`), the tests `gkr 1 2`, `gkr 3 3` and the changed leaf | the test "the message count for odd μ (acceptance test 17)" (`:38`); "upstream as `ProofSystem/GKR/GrandProduct`" (`:40`) | `LeanerVM/Protocol/Generic/Gkr.lean` (`:32`; Layer 5 names `ToArkLib/GrandProduct.lean`); `gkr … : Gkr.Def` and `Gkr.Security.complete`, `.rbr` |
| the adaptor (`:44-59`) | Layer 3 | all of it: `d := 2`, the three public lines, the two readers, `satisfiedBy_witnessOf (hs …)`, the strong auxiliary predicate, the witness generator (`:833-861`) | nothing | "consumes … #38, #40" (closed pull requests, now Layer 1 on `main`) |
| bus phase, both halves (`:61-73`) | Layer 6 | the leaf tables, `busError`, `leaf_decomposition`, one root and `R_c ≠ 0` (`:955-977`); the zerocheck charge (convention *Seams*, `:333`); the test on two blocks | the Layer 1 lemmas the leaf decomposition needs, `stack_eval_ambient_one`, `idxColumn_eval`, `bytecodeColumn_eval` (`:66`); the tests "the whole phase run on the toy instance's honest `q`" (the blueprint says "on the Layer 3 one-row witness", which a phase over an abstract instance cannot use before the adaptor exists), the zero-count mutation (acceptance test 3) and the pad-0 mutation (test 2) (`:71`) | `busPhase I (G : Gkr.Def) : Phase.Def I Unit (BusOut I) (busSpec I) (M3Holds I) (Seam.bus I)` (`:66`); "specification (5.4)" (it is §5.4, equation (2)); "#40", "#41" |
| table sumcheck phase, both halves (`:75-87`) | Layer 7 | `tableSummand`, `tableSummand_target`, the errors, the output relation (`:987-1003`); the summand's powers, padding and variable order (convention *Table sumcheck*, `:323`) | the test "a row violating a constraint" (`:85`) in place of the blueprint's "violating a JUMP identity" (`:1004`), which the toy instance cannot express; the test "the reversed variable order mismatches `eq` (test 16)" | `tableSumcheck I (S : Sumcheck.Def) : Phase.Def I (BusOut I) (TableOut I) (tableSpec I) …` (`:80`); "#42's honest round algebra" (a pull request as a dependency) |
| public-input phase (`:89-100`) | Layer 8 | all of it, as built and as decided (decision 15) | nothing | the whole section: "the prover sends nothing" (`:93-94`) is the design the public-input phase replaced |
| Flock phase (`:102-113`) | Layer 9 | the strong predicate, `limbColumns`, the strided reader (`:1088-1099`); ArkLib pull request 383 and issue 893 (ledger row on ring-switching packing) | nothing | nothing beyond the claim line |
| opening phase, both halves (`:115-127`) | Layer 10 | `Weight`, `WeightedClaim` (the spine's), the pool order (convention *Claim pool order*, `:324`), the errors `(J − 1)/\|E\|` and `2/\|E\|` per round | the tests "the phase run on the toy instance; a claim value changed after λ is drawn rejected; the empty pool" (`:125`: Layer 10's tests are about the whole protocol only); that the `(J − 1)/\|E\|` term is to be stated in ArkLib's probability form (`:121`) | `Claim.toWeighted` over "a `BlockClaim` of #38" (`:120`; the Layer 1 review showed a phase cannot form one, and the step is `ColumnClaim.holds_iff_weighted`); `openingPhase I (B : Batch.Def) (S : Sumcheck.Def) : Phase.Def I (FlockOut I) Unit (openSpec I) …`; `Pool` (`:123`) |
| knowledge-soundness composition (`:129-142`) | The spine, item 5 | all of it (`:423-430`, `:1136-1144`) | "its two witness lemmas reuse the pinned ArkLib's proofs, and the wrappers into the existential and averaged forms are left out" (`:138-139`): a fact about the module, for its docstring, not the blueprint | "The hole closed with the merge of #58" (history) |
| WHIR opening (`:144-156`) | Layer 11 | `novelBasis`, `encode`, `encode_column_weight`, `whirOpen`, its two theorems, `McaJohnson`, the joint list binding (acceptance test 11), the tests at `κ = 3` and at toy parameters | the test "every pinned coding parameter with an achievability witness (… a list-decoding pin can be false at the production rate)" (`:152`) | `LeanerVM/Protocol/Generic/Whir.lean` (Layer 11 names `ToArkLib/Whir.lean`); the upstream watch "ArkLib #4 (Merkle umbrella)", closed, and "ArkLib #907 slices … landing daily", closed (`:154`) |
| Merkle trees, byte hasher, WHIR parameters (`:158-170`) | Layer 11 | the six parameters, `ladder`, `ladder_queries_eq`, `blake2sBytes`, `merkleRoot`, `merkleVerify`, the tests on the four-leaf tree and against `verifier.py:910` | the test "`blake2sBytes` on the RFC 7693 test vector" (`:166`); that the Merkle module is generic (the blueprint names no module for `merkleRoot`, `merkleVerify`) | `LeanerVM/Protocol/Generic/Merkle.lean`; "ArkLib #4 (Merkle trees, definition and security)" (`:168`), closed in favour of VCVio issue 571 |
| transcript, proof, compiled verifier (`:172-184`) | Layer 12 | `FsState` and its four operations, the seed (convention *Fiat–Shamir*, `:325`), `Proof`, `RoundPoly.decode`, `leanVmIopp`, `verify`, `settleFixedClaims`, `verify_iff_compiled`, the two interfaces, `verify_knowledgeSound`, the tests on the dumped proof and six mutations, the code-generation probe (`:1230-1231`) | "leanVM's chain is Merkle–Damgård, not a duplex sponge, so the transfer theorem, not the sponge, is what applies" (`:182`), which fixes what `FiatShamirSecurity` is an instance of | "the spine's six `ProtocolSpec`s" (`:178`; the spine fixes one) |
| the base theorems (`:186-196`) | Layer 13 | both statements, with the same program hypotheses (§B.6); the test on the fixture | nothing (`piopError_le` at the caps, `:194`, is already Layer 10's test, `:1148`) | "`verify_knowledgeSound` ∘ `knowledgeSound_of_refinement`" (`:190`; the spine has `Refinement.map_option_valid`) |

Twelve of the thirteen sections end with a "Claim" line, in one of three forms (§B.3, item 9); none moves:
the way to take a hole is the blueprint's "How work is tracked" (§G.1). "Upstream watch" rows
that are still open move without their state into each layer section's "upstream work to read
first" (§E.2).

[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: the statement types of the bus, table
sumcheck, Flock and opening phases and the schedule of the opening phase, which the layer
sections receive in place of the obsolete signatures of the comment; whether the adaptor's and
the base theorems' hypotheses change.]

**The comment itself.** Once its content is in the blueprint, its author edits it, in place, to
one paragraph, so that the links to it still land somewhere (an edit, not a new comment):

```markdown
The specifications of the holes are in the blueprint, each in its layer section: see
[The holes](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md#the-holes).
This comment held them from 2026-09-25 until that move; its earlier text is in the edit history.
```

The four other comments on issue 12 (a contributor's three of 2026-09-20 to 2026-09-24 and the
owner's of 2026-09-28) are a record and need nothing: their live content (four claims) is in
the bodies of intention issues 28, 31, 33 and 37.

### G.5 The other issues and pull requests, as far as the proof system's documentation goes

The owner's rule applies to each: a change is an edit of the existing body (or description),
not a comment and not a new issue. The states are those of 2026-09-30.

**Issue 3 (the Flock roadmap).** Its body does not mention the proof system. What the proof
system asks of Flock (the strong auxiliary predicate, the strided reader of the limb slots,
the witness generator, the compression lemma) is in the owner's comment of 2026-09-28
(`issuecomment-5872015596`) and already in the blueprint, Layers 3 and 9
(`protocol-blueprint.md:850-861, 1088-1099`). Proposed: one line added to the body's
"Related trackers": "leanerVM #12 (the leanVM proof system): it consumes this roadmap as its
Flock phase and takes the witness generator and the compression lemma in its adaptor; the
interface is specified in `docs/roadmap/protocol-blueprint.md`, Layers 3 and 9." Title:
nothing. On the proof system's side, the blueprint cites this issue's milestones by their codes
("#3's F3–F5 and F8", `:1097`; "#3 F6", `:612`; "F1 there", status `:363`), which collide with
the status's findings of the same letter; the blueprint should use the names issue 3 already
gives them ("the concrete PCS (#3, F6)").

**Issue 4 (the leanISA tracker).** Its "Related" line says "#12 (the proof-system roadmap,
which proves `SatisfiedBy`; its requests #13 are settled in the roadmap)". The proof system
proves knowledge of its own relation on the committed stack, and reaches `SatisfiedBy` only
through the adaptor, which is not built. Proposed, in the body: "#12 (the proof-system roadmap:
its adaptor, not yet built, turns a stack satisfying the proof system's relation into a witness
satisfying `SatisfiedBy`; its two requests, #13, are settled)". The same line's "decision 15"
should read "leanISA decision 15", the proof system having a decision 15 of its own. Title:
nothing.

**Issue 16 (Clean's bus argument is vacuous over K).** Nothing: its body is about leanISA and
Clean, and the blueprint cites it correctly (`:359`).

**Issue 20 (Clean bus balance over binary fields).** Nothing: its line on #12, "the
proof-system roadmap reads the M3 bus off the same channels", is right.

**Issue 23 (fold three hypotheses into fixed columns after Clean pull request 446).** Two
edits of the body. Its "Blocked on" says the Clean bump "also has to survive P3, the eager
`Fintype BF64`, see the status file": a bare code that is the table sumcheck's definition on
issue 12; it should read "leanISA status finding P3 (the eager `Fintype BF64`)", or name it only.
Its "Where it is recorded" should add the proof system: the upstream ledger's entry on fixed
columns and sound prover data (today the status's row `:184`), consumed by the adaptor, which
states the three facts as known coordinates of the leanISA instance (`Coord.known`). Title:
nothing.
[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: whether the new Clean pin `42fe4b26`
(pull request 61) contains Clean pull request 446, and whether the eager-`Fintype` concern is
retired by the new CompPoly pin, which would change "Blocked on".]

**Issue 28 (intention: Layer 2).** Its first line, "Tracks #12, Layer 2/C1", uses the code of
the ledger entry on Clean, which is also the code of the knowledge-soundness composition on
issue 12's checklist. Proposed: "Tracks #12: the hole 'Clean expressions as polynomials'
(Layer 2), whose upstream is Clean pull request 466." Title: nothing (it could carry the
hole's name: "[Intention]: protocol - Clean expressions as polynomials: …").

**Issues 29 and 30 (intention: the VCVio controls).** Their bodies already record that the
controls landed through VCVio pull request 784; the blueprint's rule is that an intention
issue is closed by the pull request that lands it (`:1490-1491`). Proposed: close both, with
no comment; remove their line from issue 12 (§G.4). Titles: nothing.

**Issue 31 (intention: batching by powers).** Three phrases of the body are stale or coded:
"P05 depends only on #18's multilinear API. The game depends on P05" (a private code for the
algebra slice, and a closed pull request): "The algebra depends only on
`LeanerVM/Protocol/ToCompPoly/Multilinear.lean` on `main`. The game depends on the algebra";
"tracked by [ArkLib #3]", which is closed: "ArkLib #1"; "ledger A6": "the ledger entry 'grand
product, GKR, batching and stacking are absent upstream'". Title: nothing.

**Issues 27, 32, 35, 36 (intentions: Layer 1).** Closed with pull request 59. Nothing.

**Issue 33 (intention: fingerprint and collision bound).** "Base: PR #18 at `41b79b3c…`"
and "Depends on the corrected fingerprint slice over PR #18": pull request 18 is closed and its
content is on `main` (pull request 59). Proposed: "Base: `main`, using
`LeanerVM/Protocol/ToCompPoly/Multilinear.lean`" and "over `main`". Title: nothing.

**Issue 34.** A merged pull request on the semantics, not an intention issue. Nothing.

**Issue 37 (intention: sumcheck).** Nothing: it names ArkLib #1 (and says it supersedes the
closed ArkLib #3) and "Tracking: #12".

**Pull request 39 (symbolic fingerprints), for the fingerprint and collision bound.** Base
`feat/leanth-reuse`, the branch of the closed #18; the module is
`LeanerVM/Protocol/Generic/Fingerprint.lean`. The description says "Built on #18 for #33". The
owner's comment of 2026-09-28 says where it meets the spine (the fingerprint enters the weights
of `VirtualTerm`s; the collision bound is the bus phase's knowledge half). Proposed: the base
becomes `main` on rebase and the module moves to the folder the convention *Generic code*
assigns (its objects are CompPoly tables and Mathlib polynomials); the description is edited to
name the hole ("fingerprint and collision bound", Layer 5), the intention issue (#33), ArkLib
issue 901, the specification section (§5.2) at the pin, that it is written from the
specification, the ledger entry (the grand product absent upstream), and to absorb the owner's
comment, which then needs no successor. Title: nothing.

**Pull request 42 (honest sumcheck polynomials), for the sumcheck's definition and
completeness.** Base `main`; modules `LeanerVM/Protocol/Generic/HonestSumcheck.lean` and
`HonestSumcheckUpstream.lean`. Proposed: the modules move to the destination folder; the
description, which names #37 and ArkLib #1, gains the hole's name ("sumcheck: definition and
completeness", Layer 4) and the owner's comment of 2026-09-28 (the spine has no `Sumcheck.Def`;
a generic component is a `Component.Def` with its `Complete` and `Security`). Title: nothing.

**Pull request 43 (power batching), for batching by powers.** Base `feat/leanth-reuse`;
module `LeanerVM/Protocol/Generic/PowerBatching.lean`; description "Built on #18". Proposed:
rebase onto `main`, move the module, and edit the description to name the hole ("batching by
powers", Layer 4), #31, and the owner's comment of 2026-09-28: `pairing_batchWeight` is stated
over the same inner product as the spine's `Weight.pair`, and one of the two is to be restated
through the other so that two pairings do not coexist. Title: nothing.

[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: whether the statements of pull requests
39 and 43 fit the statement types the review fixes for the bus and opening phases, which
decides whether their descriptions promise a consumer that exists.]

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
  §8.2 says "The verifier samples $r_m\in\E$, the prover sends $c_0,c_1$ claiming …"
  (`doc/leanvm/body/08-end-to-end-protocol.tex:29` at `a386121f`), and the Rust verifier reads
  the two scalars ("`*v = vs.next_scalar()…`", `crates/lean_vm/src/cpu/mod.rs:746-749`), and the
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
  non-private declarations under `LeanerVM/Protocol/` at `b435631`, 198 are not in the list
  (`unlisted_public.py` on an export of `b435631`; 197 on the working tree at `144c5aa`), among them definitions the blueprint says later work reads:
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
  `architecture.md:273-275`: the completeness half of base proof extraction and completeness
  (T4) "composes T2 with the honest prover".
- **Classification**: a deliberate scope choice of the blueprint (witness-generator correctness
  (T2) is out of scope, `:147-148`), not written down as a deviation from `architecture.md`.
- **Proposed change**: one sentence in Layer 13: "`baseProver_complete` is existential in the
  witness (it composes leanISA's `constraintCompleteness`); the computable form through the
  witness generator (T2) is `architecture.md`'s, out of scope here."

### H.20 What was checked and found right

- **Severity**: note (negative results).
- **Evidence**: §B.10: every local Markdown link and anchor of the 24 Markdown files tracked at
  `b435631` resolves (150 links); every one of 81 citations into the pinned leanVM sources resolves to an
  existing range once its crate is known (22 are ambiguous as written: `transcript.rs`,
  `witness.rs`, `lib.rs`, `filler.rs`, and specification files that also exist under
  `doc/leanvm/drafts/`); 40 of 43 citations into the pinned libraries are at the cited place
  (the old pins); all 30 references to numbered acceptance tests point at the intended test;
  the spine's sketch in the blueprint (`:442-554`) agrees with the code; the Layer 8 sketch
  agrees with `PublicInput.lean`.
- **Proposed change**: none; the ambiguous citations would name their crate
  (`crates/fiat_shamir/src/transcript.rs`).

## Appendix: the probes

Every probe is a read-only Python script or shell command over text; no Lean was run. The
scripts are under `.claude/reports/blueprint-review/probes/docs-debt/` and are run from that
directory with `python3 <script>`. They read the working tree, so the recorded outputs below
were produced at `b435631`, before the merge of `144c5aa` into the checkout (a re-run today
reads the blueprint of `144c5aa`, which differs by 6 lines; where that changes a figure, the
dossier says so, for example `unlisted_public.py`: 198 at `b435631`, 197 at `144c5aa`, obtained
by running a copy of the script on `git archive b435631` in the scratchpad).

### `extract_codes.py`

Every letter-number code of the eight texts, counted per document (section D). Output: `codes.json` and the table below (`codes_table.txt`). The pattern skips codes inside backticks, so the counts are lower bounds (§D).

Command: `python3 extract_codes.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): every letter-number code in the proof-system documents, with counts and
line numbers per document. Documents: the blueprint, the status, the tracker body, the hole
comment, the other comments of the tracker, the three review handoffs of the proof system.
Also counted, for cross-family collisions: architecture.md, leanvm-target.md, leanth-reuse.md,
the two leanISA roadmap files, dependencies.md, development.md, docs/README.md."""
import re, os, json, collections, sys
root = "/home/scaraven/Documents/Verified-zkEVM/leanerVM"
P = os.path.join(root, ".claude/reports/blueprint-review/probes/docs-debt")
docs = collections.OrderedDict([
 ("blueprint", os.path.join(root,"docs/roadmap/protocol-blueprint.md")),
 ("status", os.path.join(root,"docs/roadmap/protocol-status.md")),
 ("tracker-body", os.path.join(P,"issue-12-body.md")),
 ("hole-comment", os.path.join(P,"issue-12-comment-5833669972.md")),
 ("tracker-other-comments", None),
 ("review-spine", os.path.join(root,"docs/reviews/protocol-spine.md")),
 ("review-layer1", os.path.join(root,"docs/reviews/protocol-layer1.md")),
 ("review-public-input", os.path.join(root,"docs/reviews/public-input-phase.md")),
 ("leanth-reuse", os.path.join(root,"docs/roadmap/leanth-reuse.md")),
 ("architecture", os.path.join(root,"docs/architecture.md")),
 ("leanvm-target", os.path.join(root,"docs/leanvm-target.md")),
 ("leanisa-blueprint", os.path.join(root,"docs/roadmap/leanisa-blueprint.md")),
 ("leanisa-status", os.path.join(root,"docs/roadmap/leanisa-status.md")),
 ("dependencies", os.path.join(root,"docs/dependencies.md")),
 ("development", os.path.join(root,"docs/development.md")),
 ("docs-README", os.path.join(root,"docs/README.md")),
])
def load(name, path):
    if path is None:
        out=[]
        for c in ["5749712916","5749874958","5813452703","5872015097"]:
            out += open(os.path.join(P,f"issue-12-comment-{c}.md")).read().split("\n")
        return out
    return open(path).read().split("\n")
code_re = re.compile(r"(?<![A-Za-z0-9_.^`/=\-\[])([A-Z])(\d{1,2})(?![A-Za-z0-9_\]]|\.\d|\^|/)")
# hole S standing alone
holeS_re = re.compile(r"(?:hole \*{0,2}S\*{0,2}\b|\(S\)|\bS, I1\b|\| S \||\*\*S — |### S:|\bS and C1\b|, S\)|, S \||\bG2, S\b)")
res = collections.defaultdict(lambda: collections.defaultdict(list))
for name, path in docs.items():
    ls = load(name, path)
    infence = False
    for i, l in enumerate(ls, 1):
        for m in code_re.finditer(l):
            code = m.group(1)+m.group(2)
            res[code][name].append(i)
        for m in holeS_re.finditer(l):
            res["S(hole)"][name].append(i)
json.dump({k:{d:v for d,v in dv.items()} for k,dv in res.items()}, open(os.path.join(P,"codes.json"),"w"), indent=0)
def key(c):
    m = re.match(r"([A-Z])(\d+)", c)
    return (m.group(1), int(m.group(2))) if m else ("S", -1)
core = ["blueprint","status","tracker-body","hole-comment","tracker-other-comments","review-spine","review-layer1","review-public-input"]
others = [d for d in docs if d not in core]
print("code | " + " | ".join(core) + " | core total || " + " | ".join(others))
for c in sorted(res, key=key):
    row = [str(len(res[c].get(d, []))) for d in core]
    tot = sum(len(res[c].get(d, [])) for d in core)
    row2 = [str(len(res[c].get(d, []))) for d in others]
    if tot == 0 and sum(map(int,row2)) == 0: continue
    print(f"{c} | " + " | ".join(row) + f" | {tot} || " + " | ".join(row2))
```

Output:

```text
code | blueprint | status | tracker-body | hole-comment | tracker-other-comments | review-spine | review-layer1 | review-public-input | core total || leanth-reuse | architecture | leanvm-target | leanisa-blueprint | leanisa-status | dependencies | development | docs-README
A1 | 3 | 9 | 2 | 0 | 1 | 9 | 3 | 5 | 32 || 3 | 0 | 0 | 0 | 2 | 0 | 0 | 1
A2 | 7 | 9 | 2 | 3 | 2 | 8 | 3 | 5 | 39 || 7 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A3 | 1 | 6 | 1 | 0 | 0 | 11 | 2 | 3 | 24 || 5 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A4 | 1 | 4 | 0 | 0 | 0 | 6 | 3 | 2 | 16 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A5 | 4 | 2 | 1 | 1 | 0 | 7 | 2 | 0 | 17 || 1 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A6 | 2 | 3 | 1 | 2 | 0 | 5 | 3 | 0 | 16 || 2 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A7 | 2 | 2 | 1 | 1 | 0 | 0 | 0 | 0 | 6 || 3 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A8 | 4 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 7 || 2 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A9 | 1 | 2 | 1 | 1 | 0 | 0 | 0 | 0 | 5 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A10 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A11 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A12 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A13 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A14 | 0 | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A15 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A16 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A17 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A18 | 0 | 3 | 1 | 0 | 0 | 0 | 0 | 0 | 4 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A19 | 0 | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
B0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
B1 | 0 | 2 | 0 | 0 | 0 | 2 | 4 | 5 | 13 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
B2 | 0 | 1 | 0 | 0 | 0 | 2 | 5 | 2 | 10 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
B3 | 0 | 1 | 0 | 0 | 0 | 0 | 2 | 2 | 5 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
B4 | 0 | 1 | 0 | 0 | 0 | 0 | 3 | 0 | 4 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
B6 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
C1 | 5 | 9 | 5 | 4 | 3 | 6 | 4 | 5 | 41 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C2 | 0 | 2 | 1 | 0 | 0 | 2 | 2 | 2 | 9 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C3 | 0 | 1 | 1 | 0 | 0 | 0 | 1 | 2 | 5 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C4 | 0 | 1 | 1 | 0 | 0 | 0 | 1 | 2 | 5 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C5 | 1 | 1 | 0 | 0 | 0 | 0 | 1 | 0 | 3 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C6 | 1 | 1 | 0 | 0 | 0 | 0 | 1 | 0 | 3 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C7 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C8 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 9 | 1 | 0 | 0
C9 | 0 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | 3 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
C10 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 4 | 0 | 0 | 0
C11 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
D1 | 0 | 2 | 0 | 0 | 0 | 0 | 3 | 0 | 5 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D2 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D4 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D5 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 1 | 1 | 0 | 0 | 0
D7 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D8 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D9 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D10 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D11 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D12 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D13 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D14 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D15 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D16 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D17 | 0 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
E2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
E3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
E4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
E5 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 1 | 7 | 0 | 0 | 0
E6 | 0 | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 7 | 1 | 0 | 0
E7 | 0 | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 3 || 0 | 0 | 0 | 0 | 3 | 0 | 0 | 0
E8 | 0 | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 3 || 0 | 0 | 0 | 2 | 5 | 0 | 0 | 0
E9 | 0 | 1 | 1 | 0 | 0 | 2 | 0 | 0 | 4 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E10 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E11 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E12 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 2 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E13 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 2 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E14 | 0 | 3 | 0 | 0 | 0 | 0 | 0 | 1 | 4 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E15 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E16 | 0 | 5 | 0 | 0 | 0 | 0 | 0 | 1 | 6 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E17 | 0 | 3 | 0 | 0 | 0 | 0 | 1 | 2 | 6 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E18 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F1 | 4 | 3 | 1 | 1 | 0 | 0 | 0 | 0 | 9 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
F2 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
F3 | 4 | 2 | 1 | 1 | 0 | 0 | 0 | 0 | 8 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
F4 | 1 | 2 | 0 | 1 | 0 | 0 | 0 | 0 | 4 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
F5 | 3 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 6 || 0 | 0 | 0 | 0 | 4 | 0 | 0 | 0
F6 | 4 | 3 | 2 | 0 | 0 | 0 | 0 | 0 | 9 || 0 | 0 | 0 | 0 | 6 | 0 | 0 | 0
F7 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 4 | 0 | 0 | 0
F8 | 2 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 5 || 0 | 0 | 0 | 0 | 5 | 0 | 0 | 1
F9 | 0 | 2 | 1 | 0 | 0 | 0 | 0 | 0 | 3 || 0 | 0 | 0 | 0 | 6 | 0 | 0 | 0
F10 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 7 | 0 | 0 | 0
F11 | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F12 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F13 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F14 | 0 | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F15 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F16 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F17 | 0 | 4 | 0 | 0 | 0 | 0 | 1 | 2 | 7 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F18 | 0 | 5 | 0 | 0 | 0 | 0 | 0 | 2 | 7 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F64 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 2 | 0 | 0 | 0 | 0
G1 | 7 | 8 | 7 | 3 | 1 | 0 | 0 | 0 | 26 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
G2 | 3 | 4 | 4 | 1 | 0 | 0 | 0 | 0 | 12 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
G3 | 2 | 7 | 5 | 1 | 0 | 0 | 0 | 0 | 15 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
G4 | 2 | 5 | 4 | 1 | 0 | 0 | 0 | 0 | 12 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
G5 | 2 | 4 | 4 | 4 | 0 | 0 | 0 | 0 | 14 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
G6 | 5 | 2 | 2 | 4 | 1 | 0 | 0 | 0 | 14 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H1 | 0 | 2 | 0 | 0 | 0 | 5 | 0 | 16 | 23 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H2 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | 7 | 10 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H3 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | 8 | 12 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H4 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | 4 | 8 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H5 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | 8 | 12 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H6 | 0 | 2 | 0 | 0 | 0 | 7 | 0 | 9 | 18 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
I1 | 3 | 5 | 6 | 1 | 2 | 9 | 0 | 0 | 26 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
I2 | 5 | 8 | 11 | 6 | 3 | 15 | 1 | 0 | 49 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
I3 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | 0 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
K1 | 4 | 8 | 9 | 3 | 1 | 0 | 0 | 0 | 25 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
K2 | 4 | 4 | 5 | 3 | 1 | 0 | 0 | 0 | 17 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
K3 | 4 | 7 | 7 | 6 | 0 | 5 | 0 | 0 | 29 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
K4 | 2 | 1 | 2 | 3 | 0 | 2 | 0 | 0 | 10 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
L1 | 5 | 6 | 7 | 0 | 0 | 0 | 2 | 0 | 20 || 0 | 0 | 0 | 0 | 7 | 0 | 0 | 0
L2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
L3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
M3 | 7 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 9 || 1 | 0 | 3 | 8 | 3 | 0 | 0 | 1
P1 | 4 | 5 | 4 | 3 | 1 | 2 | 0 | 2 | 21 || 0 | 0 | 0 | 1 | 6 | 0 | 0 | 0
P2 | 4 | 2 | 3 | 4 | 0 | 0 | 0 | 0 | 13 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
P3 | 4 | 6 | 3 | 3 | 1 | 0 | 0 | 2 | 19 || 0 | 0 | 0 | 0 | 5 | 0 | 1 | 0
P4 | 4 | 2 | 2 | 4 | 0 | 0 | 0 | 0 | 12 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
P5 | 2 | 15 | 3 | 3 | 3 | 7 | 0 | 2 | 35 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
P6 | 2 | 4 | 4 | 3 | 2 | 4 | 0 | 0 | 19 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
P7 | 2 | 6 | 5 | 4 | 0 | 1 | 0 | 2 | 20 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
P8 | 5 | 2 | 3 | 4 | 0 | 2 | 0 | 0 | 16 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
P17 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
R1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 5 | 0 | 0 | 0
R2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 3 | 0 | 0 | 0
R3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 3 | 0 | 0 | 0
R4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R5 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R6 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R8 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R9 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R11 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R12 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R13 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R16 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R17 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R18 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R19 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R20 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R21 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R22 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R23 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R24 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 3 | 0 | 0 | 0
R25 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
R26 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R27 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R28 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
S(hole) | 7 | 4 | 4 | 3 | 1 | 1 | 0 | 7 | 27 || 29 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 4 | 0 | 0 | 1 | 0 | 0 | 0
S2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 6 | 0 | 0 | 1 | 0 | 0 | 0
S3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 2 | 0 | 0 | 1 | 0 | 0 | 0
S4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 5 | 0 | 0 | 1 | 0 | 0 | 0
S5 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
S6 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
S7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
S8 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
S9 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
S10 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S11 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S12 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S13 | 0 | 2 | 1 | 0 | 0 | 5 | 0 | 0 | 8 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S14 | 0 | 2 | 1 | 0 | 0 | 1 | 0 | 0 | 4 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S15 | 0 | 2 | 0 | 0 | 0 | 0 | 1 | 0 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S16 | 0 | 2 | 0 | 0 | 0 | 0 | 1 | 0 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
T1 | 4 | 1 | 2 | 0 | 0 | 0 | 0 | 0 | 7 || 0 | 11 | 6 | 8 | 11 | 0 | 0 | 0
T2 | 2 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 3 || 0 | 5 | 2 | 3 | 4 | 0 | 0 | 0
T3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 1 | 5 | 3 | 0 | 0 | 0 | 0 | 0
T4 | 11 | 1 | 2 | 3 | 0 | 4 | 0 | 0 | 21 || 1 | 5 | 2 | 0 | 0 | 0 | 0 | 0
T5 | 5 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 6 || 0 | 4 | 2 | 0 | 0 | 0 | 0 | 0
T6 | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 4 || 2 | 11 | 4 | 0 | 0 | 0 | 0 | 0
T7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 5 | 4 | 0 | 0 | 0 | 0 | 0
T8 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 6 | 2 | 1 | 0 | 0 | 0 | 0
```

### `code_contexts.py`

Every occurrence of the given codes with its context, for classification by meaning by hand (§D.3). Output: `ctx_A.txt`, `ctx_C.txt`, `ctx_F.txt`, `ctx_I.txt`, `ctx_P.txt`, `ctx_misc.txt` (not reproduced: they are the texts themselves, cut into windows).

Command: `python3 code_contexts.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): print every occurrence of the given codes in the core documents with
its document, line and a window of context, for manual classification by meaning."""
import re, os, sys
root = "/home/scaraven/Documents/Verified-zkEVM/leanerVM"
P = os.path.join(root, ".claude/reports/blueprint-review/probes/docs-debt")
docs = [("blueprint","docs/roadmap/protocol-blueprint.md"),("status","docs/roadmap/protocol-status.md"),
 ("tracker-body",P+"/issue-12-body.md"),("hole-comment",P+"/issue-12-comment-5833669972.md"),
 ("c-5749712916",P+"/issue-12-comment-5749712916.md"),("c-5749874958",P+"/issue-12-comment-5749874958.md"),
 ("c-5813452703",P+"/issue-12-comment-5813452703.md"),("c-5872015097",P+"/issue-12-comment-5872015097.md"),
 ("review-spine","docs/reviews/protocol-spine.md"),("review-layer1","docs/reviews/protocol-layer1.md"),
 ("review-public-input","docs/reviews/public-input-phase.md")]
codes = sys.argv[1:]
for code in codes:
    rx = re.compile(r"(?<![A-Za-z0-9_.^`/=\-\[])%s(?![A-Za-z0-9_\]]|\.\d|\^|/)" % re.escape(code))
    print("=================", code)
    for name, p in docs:
        path = p if p.startswith("/") else os.path.join(root, p)
        for i, l in enumerate(open(path).read().split("\n"), 1):
            for m in rx.finditer(l):
                s = max(0, m.start()-70); e = min(len(l), m.end()+60)
                print(f"{name}:{i}: …{l[s:e]}…")
```

### `check_anchors.py`

Local Markdown links and their anchors, computed the GitHub way (§B.10).

Command: `python3 check_anchors.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): Markdown links with anchors in the tracked documentation, including
links broken across lines (which scripts/check-docs.py, a per-line matcher, does not see).
Anchors are computed the GitHub way (lowercase, punctuation dropped, spaces to hyphens)."""
import re, os, subprocess
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM"
files=subprocess.run(["git","ls-files","*.md"],cwd=root,capture_output=True,text=True).stdout.split()
def anchors(path):
    out=set(); infence=False
    for l in open(path,encoding="utf-8").read().split("\n"):
        if l.startswith("```"): infence=not infence
        if infence: continue
        m=re.match(r"^(#{1,6})\s+(.*)$",l)
        if m:
            t=m.group(2).strip()
            t=re.sub(r"\[([^\]]*)\]\([^)]*\)",r"\1",t)
            t=t.replace("`","")
            a=re.sub(r"[^\w\- ]","",t.lower(),flags=re.UNICODE).replace(" ","-")
            out.add(a)
    return out
link=re.compile(r"\[([^\]]*)\]\(([^)\s]+)\)",re.S)
n=0; bad=[]; multiline=0
for f in files:
    p=os.path.join(root,f); txt=open(p,encoding="utf-8").read()
    for m in link.finditer(txt):
        target=m.group(2)
        if target.startswith("http") or target.startswith("mailto"): continue
        line=txt[:m.start()].count("\n")+1
        if "\n" in m.group(1): multiline+=1
        path,_,frag=target.partition("#")
        tp=p if path=="" else os.path.normpath(os.path.join(os.path.dirname(p),path))
        n+=1
        if not os.path.exists(tp):
            bad.append(f"{f}:{line}: missing file {target}"); continue
        if frag and tp.endswith(".md"):
            if frag not in anchors(tp):
                bad.append(f"{f}:{line}: missing anchor #{frag} in {os.path.relpath(tp,root)}")
print(f"{len(files)} tracked Markdown files, {n} local links checked ({multiline} span two lines), {len(bad)} broken")
for b in bad: print("  ",b)
```

Output:

```text
24 tracked Markdown files, 150 local links checked (0 span two lines), 0 broken
```

### `check_interface_names.py`

Each name of the blueprint's list "Interfaces supplied to later work" looked up under `LeanerVM/` (§B.5). Output `interface_names.out` (195 lines); reproduced: its summary line and the 64 absent names.

Command: `python3 check_interface_names.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): for each name in the blueprint's 'Interfaces supplied to later work'
list (docs/roadmap/protocol-blueprint.md:1366-1416), report whether a declaration with that
final name component exists under LeanerVM/ in the working tree (main at b435631).
DECL   = a def/theorem/structure/abbrev/instance/inductive whose declared name ends with the
         final component was found (the namespace is not resolved: see the file shown)
FIELD  = only a structure field of that name was found
ABSENT = neither."""
import re, os, glob
root = "/home/scaraven/Documents/Verified-zkEVM/leanerVM"
lines = open(os.path.join(root, "docs/roadmap/protocol-blueprint.md")).read().split("\n")
block = lines[1365:1416]
group = None
names = []
for l in block:
    m = re.match(r"^([A-Z][A-Za-z ()]+):\s+(.*)$", l)
    if m:
        group = m.group(1).strip(); rest = m.group(2)
    else:
        rest = l.strip()
    rest = rest.replace("(each with .Holds)", " ").replace("(and their .append)", " ").replace("(Layer 2)", " ")
    rest = rest.replace("Component.Security.{witMid, extractor, kSF, rbr}",
                        "Component.Security.witMid Component.Security.extractor Component.Security.kSF Component.Security.rbr")
    for tok in rest.split():
        names.append((group, tok))
files = [f for f in glob.glob(os.path.join(root, "LeanerVM/**/*.lean"), recursive=True)]
src = {f: open(f).read().split("\n") for f in files}
KW = r"(?:def|theorem|lemma|structure|inductive|abbrev|instance|class|opaque)"
def find(short):
    decl = re.compile(r"(?:^|\s)%s\s+(?:[^\s.]+\.)*%s(?=\s|$|\{|\(|\[|:)" % (KW, re.escape(short)))
    fld = re.compile(r"^\s+%s\s*:(?!=)" % re.escape(short))
    d, f = [], []
    for fn, ls in src.items():
        for i, l in enumerate(ls, 1):
            if decl.search(l): d.append(f"{os.path.relpath(fn, root)}:{i}: {l.strip()[:90]}")
            elif fld.search(l): f.append(f"{os.path.relpath(fn, root)}:{i}: {l.strip()[:90]}")
    return d, f
seen = set(); counts = {"DECL":0, "FIELD":0, "ABSENT":0}
for g, n in names:
    if (g, n) in seen: continue
    seen.add((g, n))
    d, f = find(n.split(".")[-1])
    status = "DECL" if d else ("FIELD" if f else "ABSENT")
    counts[status] += 1
    print(f"{status:7} | {g:20} | {n:68} | {(d or f or [''])[0]}")
print(counts)
```

Output:

```text
ABSENT  | Spine                | Ensemble.toM3                                                        | 
ABSENT  | Protocol (generic)   | Virtual                                                              | 
ABSENT  | Protocol (generic)   | sumcheck                                                             | 
ABSENT  | Protocol (generic)   | sumcheck_rbrKnowledgeSoundness                                       | 
ABSENT  | Protocol (generic)   | batchClaims                                                          | 
ABSENT  | Protocol (generic)   | fingerprint                                                          | 
ABSENT  | Protocol (generic)   | sideProduct                                                          | 
ABSENT  | Protocol (generic)   | sideProduct_poly_eq_iff                                              | 
ABSENT  | Protocol (generic)   | sideProduct_collision                                                | 
ABSENT  | Protocol (generic)   | ProductTree                                                          | 
ABSENT  | Protocol (generic)   | gkr                                                                  | 
ABSENT  | Protocol (generic)   | gkrError                                                             | 
ABSENT  | Protocol (generic)   | gkr_rbrKnowledgeSoundness                                            | 
ABSENT  | Protocol (generic)   | openingPhase                                                         | 
ABSENT  | Protocol (generic)   | encode                                                               | 
ABSENT  | Protocol (generic)   | encode_column_weight                                                 | 
ABSENT  | Protocol (generic)   | whirOpen                                                             | 
ABSENT  | Protocol (generic)   | whirError                                                            | 
ABSENT  | Protocol (generic)   | whirOpen_rbrSoundness                                                | 
ABSENT  | Protocol (generic)   | McaJohnson                                                           | 
ABSENT  | Protocol (generic)   | merkleRoot                                                           | 
ABSENT  | Protocol (generic)   | merkleVerify                                                         | 
ABSENT  | Protocol (generic)   | blake2sBytes                                                         | 
ABSENT  | Arithmetization      | Expression.toMvPolynomial                                            | 
ABSENT  | Arithmetization      | degreeBound                                                          | 
ABSENT  | Arithmetization      | M3Table                                                              | 
ABSENT  | Arithmetization      | Component.toM3                                                       | 
ABSENT  | Arithmetization      | Ensemble.toM3                                                        | 
ABSENT  | Arithmetization      | toM3_constraints_iff                                                 | 
ABSENT  | Arithmetization      | toM3_flushes_eq                                                      | 
ABSENT  | Protocol (leanVM)    | Sizes                                                                | 
ABSENT  | Protocol (leanVM)    | Sizes.Admissible                                                     | 
ABSENT  | Protocol (leanVM)    | leanIsaInstance                                                      | 
ABSENT  | Protocol (leanVM)    | stackOf                                                              | 
ABSENT  | Protocol (leanVM)    | witnessOf                                                            | 
ABSENT  | Protocol (leanVM)    | satisfiedBy_witnessOf                                                | 
ABSENT  | Protocol (leanVM)    | m3Holds_stackOf                                                      | 
ABSENT  | Protocol (leanVM)    | witnessOf_stackOf                                                    | 
ABSENT  | Protocol (leanVM)    | busPhase                                                             | 
ABSENT  | Protocol (leanVM)    | leaf_decomposition                                                   | 
ABSENT  | Protocol (leanVM)    | tableSumcheck                                                        | 
ABSENT  | Protocol (leanVM)    | tableSummand                                                         | 
ABSENT  | Protocol (leanVM)    | FlockInterface                                                       | 
ABSENT  | Protocol (leanVM)    | piopError_le                                                         | 
ABSENT  | Protocol (leanVM)    | leanVmIopp                                                           | 
ABSENT  | Protocol (leanVM)    | FsState                                                              | 
ABSENT  | Protocol (leanVM)    | Proof                                                                | 
ABSENT  | Protocol (leanVM)    | verify                                                               | 
ABSENT  | Protocol (leanVM)    | settleFixedClaims                                                    | 
ABSENT  | Protocol (leanVM)    | verify_iff_compiled                                                  | 
ABSENT  | Protocol (leanVM)    | FiatShamirSecurity                                                   | 
ABSENT  | Protocol (leanVM)    | BcsSecurity                                                          | 
ABSENT  | Protocol (leanVM)    | verify_knowledgeSound                                                | 
ABSENT  | Protocol (leanVM)    | niError                                                              | 
ABSENT  | Protocol (leanVM)    | baseVerifier_extractsExecution                                       | 
ABSENT  | Protocol (leanVM)    | baseProver_complete                                                  | 
ABSENT  | Parameters           | initialFold                                                          | 
ABSENT  | Parameters           | subsequentFold                                                       | 
ABSENT  | Parameters           | initialReduction                                                     | 
ABSENT  | Parameters           | subsequentReduction                                                  | 
ABSENT  | Parameters           | residualMaxLog                                                       | 
ABSENT  | Parameters           | queryGrindingBits                                                    | 
ABSENT  | Parameters           | ladder                                                               | 
ABSENT  | Parameters           | novelBasis                                                           | 
{'DECL': 127, 'FIELD': 3, 'ABSENT': 64}
```

### `unlisted_public.py`

Non-private declarations under `LeanerVM/Protocol/` that the interface list omits (§B.5, item 1; finding H.13). Output `unlisted_public.out`; reproduced: its per-file summary.

Command: `python3 unlisted_public.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): non-private declarations under LeanerVM/Protocol/ whose final name
component does not occur anywhere in the blueprint's interface list (lines 1366-1416).
The blueprint says 'Everything not listed is a proof, a helper, or a test.'"""
import re, os, glob
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM"
bp=open(os.path.join(root,"docs/roadmap/protocol-blueprint.md")).read().split("\n")
listed=" ".join(bp[1365:1416])
listed_names=set(t.split(".")[-1].strip("{},()") for t in listed.split())
whole=" ".join(bp)
KW=r"(def|theorem|lemma|structure|inductive|abbrev|instance|class)"
rx=re.compile(r"^(?P<mods>(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public)\s+)*)"+KW+r"\s+(?P<name>[^\s:({\[]+)")
tot=0; unl=[]; perfile={}
for f in sorted(glob.glob(os.path.join(root,"LeanerVM/Protocol/**/*.lean"),recursive=True)):
    rel=os.path.relpath(f,root)
    for i,l in enumerate(open(f).read().split("\n"),1):
        m=rx.match(l)
        if not m or "private" in m.group("mods"): continue
        kind=m.group(2); name=m.group("name")
        if kind=="instance" and name in (":",): continue
        short=name.split(".")[-1]
        tot+=1
        perfile.setdefault(rel,[0,0])[0]+=1
        if short not in listed_names:
            inbp = short in whole
            unl.append((rel,i,kind,name,inbp)); perfile[rel][1]+=1
print(f"non-private declarations under LeanerVM/Protocol: {tot}; not in the interface list: {len(unl)}")
for rel,(a,b) in perfile.items(): print(f"  {rel}: {a} declarations, {b} unlisted")
print()
for rel,i,kind,name,inbp in unl:
    if kind in ("def","structure","abbrev","inductive","class") :
        print(f"  {rel}:{i}: {kind} {name}" + ("" if inbp else "   [name appears nowhere in the blueprint]"))
```

Output:

```text
non-private declarations under LeanerVM/Protocol: 333; not in the interface list: 198
  LeanerVM/Protocol/BlockClaims.lean: 8 declarations, 7 unlisted
  LeanerVM/Protocol/ClaimWeights.lean: 4 declarations, 2 unlisted
  LeanerVM/Protocol/Field.lean: 11 declarations, 7 unlisted
  LeanerVM/Protocol/FixedColumns.lean: 13 declarations, 6 unlisted
  LeanerVM/Protocol/Padding.lean: 6 declarations, 2 unlisted
  LeanerVM/Protocol/PublicInput.lean: 21 declarations, 18 unlisted
  LeanerVM/Protocol/Spine/Compose.lean: 19 declarations, 0 unlisted
  LeanerVM/Protocol/Spine/Instance.lean: 22 declarations, 4 unlisted
  LeanerVM/Protocol/Spine/Phase.lean: 6 declarations, 0 unlisted
  LeanerVM/Protocol/Spine/Seams.lean: 23 declarations, 2 unlisted
  LeanerVM/Protocol/Spine/Toy.lean: 11 declarations, 6 unlisted
  LeanerVM/Protocol/Stack.lean: 9 declarations, 3 unlisted
  LeanerVM/Protocol/ToArkLib/Component.lean: 9 declarations, 3 unlisted
  LeanerVM/Protocol/ToArkLib/GuardedVerdict.lean: 2 declarations, 2 unlisted
  LeanerVM/Protocol/ToArkLib/KeepOracles.lean: 2 declarations, 2 unlisted
  LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean: 25 declarations, 23 unlisted
  LeanerVM/Protocol/ToArkLib/Oracles.lean: 3 declarations, 1 unlisted
  LeanerVM/Protocol/ToArkLib/PassThrough.lean: 11 declarations, 8 unlisted
  LeanerVM/Protocol/ToArkLib/Refinement.lean: 5 declarations, 2 unlisted
  LeanerVM/Protocol/ToArkLib/SendOracle.lean: 17 declarations, 16 unlisted
  LeanerVM/Protocol/ToCompPoly/AmbientStacking.lean: 10 declarations, 9 unlisted
  LeanerVM/Protocol/ToCompPoly/BitProductTable.lean: 13 declarations, 9 unlisted
  LeanerVM/Protocol/ToCompPoly/Multilinear.lean: 43 declarations, 35 unlisted
  LeanerVM/Protocol/ToCompPoly/Stacking.lean: 38 declarations, 29 unlisted
  LeanerVM/Protocol/ToVCVio/UniformSample.lean: 2 declarations, 2 unlisted

  LeanerVM/Protocol/BlockClaims.lean:69: def ambientPoint   [name appears nowhere in the blueprint]
  LeanerVM/Protocol/BlockClaims.lean:73: def weight
  LeanerVM/Protocol/BlockClaims.lean:78: def IsValid   [name appears nowhere in the blueprint]
  LeanerVM/Protocol/Field.lean:65: structure rather
  LeanerVM/Protocol/Field.lean:74: def finEquivK   [name appears nowhere in the blueprint]
  LeanerVM/Protocol/Field.lean:86: def limbsEquiv   [name appears nowhere in the blueprint]
  LeanerVM/Protocol/FixedColumns.lean:56: def idxColumnEval
  LeanerVM/Protocol/FixedColumns.lean:75: def bytecodeSlotColumn   [name appears nowhere in the blueprint]
  LeanerVM/Protocol/FixedColumns.lean:108: def bytecodeColumnEval
  LeanerVM/Protocol/PublicInput.lean:65: def linePoint
  LeanerVM/Protocol/PublicInput.lean:99: def pSpec
  LeanerVM/Protocol/PublicInput.lean:111: def error
  LeanerVM/Protocol/PublicInput.lean:119: def lineValue
```

### `check_leanvm_citations.py`

Every citation `file:line` into the pinned leanVM sources in the blueprint and the status: the candidate files at `a386121f` and whether the cited range lies inside each (§B.10). The check is range-in-file and a look at the first cited line, not a reading of the content. Output `leanvm_citations.out`; reproduced: its two summary lines. Its "unresolved or out of range" counts candidates in other crates or in `doc/leanvm/drafts/`; a regrouping of the output by citation (below) finds that every one of the 89 citation groups has at least one candidate in range.

Command: `python3 check_leanvm_citations.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): every citation `file.ext:N[-M][, N-M]` into the pinned leanVM sources in
the blueprint and the status. Reports: the file resolved in the leanVM checkout (at the pin),
its length, whether each cited range lies inside it, and the first cited line (trimmed)."""
import re, os, sys, subprocess, collections
lv="/home/scaraven/Documents/leanEthereum/leanVM"
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM"
allfiles=subprocess.run(["git","ls-files"],cwd=lv,capture_output=True,text=True).stdout.split("\n")
def resolve(path):
    path=path.strip("`")
    c=[f for f in allfiles if f.endswith("/"+path) or f==path]
    if not c:
        base=os.path.basename(path)
        c=[f for f in allfiles if os.path.basename(f)==base and (os.path.dirname(path)=="" or os.path.dirname(path).split("/")[-1] in f)]
    return c
rx=re.compile(r"`?((?:[A-Za-z0-9_\-]+/)*[A-Za-z0-9_\-]+\.(?:rs|py|tex)):(\d+(?:[-–]\d+)?(?:, ?\d+(?:[-–]\d+)?)*)`?")
for doc in ["docs/roadmap/protocol-blueprint.md","docs/roadmap/protocol-status.md"]:
    print("=====",doc)
    seen=collections.OrderedDict()
    for i,l in enumerate(open(os.path.join(root,doc)).read().split("\n"),1):
        for m in rx.finditer(l):
            seen.setdefault((m.group(1),m.group(2)),[]).append(i)
    bad=0; amb=0; n=0
    for (path,ranges),lines in seen.items():
        n+=1
        c=resolve(path)
        if len(c)==0:
            print(f"  UNRESOLVED {path}:{ranges}  (doc lines {lines})"); bad+=1; continue
        if len(c)>1:
            amb+=1
            print(f"  AMBIGUOUS  {path}:{ranges} -> {c}  (doc lines {lines})"); 
        for f in c[:3]:
            ls=open(os.path.join(lv,f),errors="replace").read().split("\n")
            for r in re.split(r", ?",ranges):
                a=r.replace("–","-").split("-"); lo=int(a[0]); hi=int(a[-1])
                ok = 1<=lo<=hi<=len(ls)
                first=ls[lo-1].strip()[:80] if lo<=len(ls) else ""
                flag="ok " if ok else "OUT"
                if not ok: bad+=1
                print(f"  {flag} {f}:{r} [{len(ls)} lines] (doc {lines[0]}) | {first}")
    print(f"  -- {n} distinct citations, {bad} unresolved or out of range, {amb} ambiguous")
```

Output:

```text
===== docs/roadmap/protocol-blueprint.md
  -- 38 distinct citations, 2 unresolved or out of range, 4 ambiguous
===== docs/roadmap/protocol-status.md
  -- 43 distinct citations, 12 unresolved or out of range, 18 ambiguous
```

### `check_lib_citations.py`

Every library declaration the blueprint cites with a file and line, looked up in `.lake/packages/` at the old pins (§B.10).

Command: `python3 check_lib_citations.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): the blueprint's citations into the pinned libraries
(docs/roadmap/protocol-blueprint.md:234-251, 273-279, 290-295). For each (file, cited lines,
declaration names) report where the declaration actually is in the pinned sources under
.lake/packages/."""
import re, os
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM/.lake/packages"
A="Arklib/ArkLib/"; C="CompPoly/CompPoly/"; CL="Clean/Clean/"; V="VCVio/VCVio/"
checks=[
 (A+"OracleReduction/ProtocolSpec/Basic.lean", "", ["ProtocolSpec","Direction","MessageIdx","ChallengeIdx","FullTranscript","Transcript"]),
 (A+"OracleReduction/OracleInterface.lean","53-73",["OracleInterface"]),
 (A+"OracleReduction/OracleInterface.lean","93 (status E8)",["instDefault"]),
 (A+"OracleReduction/Basic.lean","222-669",["Prover","Verifier","OracleVerifier","Reduction","OracleReduction","OracleProof"]),
 (A+"OracleReduction/Basic.lean","1011 (status)",["PureForm"]),
 (A+"OracleReduction/Security/Basic.lean","89-103, 460-469",["completeness","perfectCompleteness"]),
 (A+"OracleReduction/Security/Basic.lean","248-359",["knowledgeSoundness","Straightline"]),
 (A+"OracleReduction/Security/Basic.lean","193 (status)",["perfectCompleteness_of_run_support"]),
 (A+"OracleReduction/Security/RoundByRound.lean","77-190, 416, 534, 606, 553",["KnowledgeStateFunction","RoundByRound","rbrKnowledgeSoundness","rbrKnowledgeSoundnessWorstCase","rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness","rbrKnowledgeSoundnessWorstCaseWith"]),
 (A+"OracleReduction/Security/Implications.lean","85",["rbrKnowledgeSoundness_implies_rbrSoundness","rbrKnowledgeSoundness_implies_knowledgeSoundness","rbrSoundness_implies_soundness"]),
 (A+"OracleReduction/Composition/Sequential/Append/Basic.lean","709",["append"]),
 (A+"OracleReduction/Composition/Sequential/General.lean","255",["seqCompose"]),
 (A+"OracleReduction/Composition/Sequential/Completeness.lean","",["seqCompose_perfectCompleteness_of_pure"]),
 (A+"OracleReduction/Composition/Sequential/Append/Completeness.lean","",["append_perfectCompleteness_of_pure_verifiers","append_perfectCompleteness_of_guarded_verifiers"]),
 (A+"OracleReduction/Composition/Sequential/GuardedNary.lean","",["seqCompose_completeness_of_guarded_verifiers"]),
 (A+"OracleReduction/Composition/Sequential/Append/RoundByRound.lean","37",["append_rbrSoundnessWorstCase_of_pure_first"]),
 (A+"OracleReduction/Composition/Sequential/Append/StateFunction.lean","292, 75",["append"]),
 (A+"OracleReduction/Composition/Sequential/Append/Security.lean","(status: 4 sorries)",["append_knowledgeSoundness","append_rbrKnowledgeSoundness"]),
 (A+"OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean","112 (status)",["GuardedForm"]),
 (A+"ProofSystem/Sumcheck/Spec/General.lean","171",["reduction"]),
 (A+"ProofSystem/Sumcheck/Spec/SingleRound.lean","130-144",["StatementRound","relationRound","verifier_rbrKnowledgeSoundness"]),
 (A+"ProofSystem/Sumcheck/Spec/Domain.lean","",["Domain"]),
 (A+"Data/MvPolynomial/Multilinear.lean","",["MLE","eqPolynomial","eqTilde","eqTilde_append","MLE_eq_zero_iff","MLEEquivFin"]),
 (A+"ToCompPoly/Multilinear/Basic.lean","56",["eval_eq_MvPolynomial_MLE"]),
 (A+"Data/MvPolynomial/SchwartzZippelCounting.lean","",["schwartz_zippel_counting","prob_eval_zero_le_div"]),
 (A+"OracleReduction/FiatShamir/Basic.lean","114-138",["fiatShamir","fsChallengeOracle","fiatShamir_completeness"]),
 (A+"Commitments/Functional/Basic.lean","",["Scheme","binding","perfectCorrectness_of_opening_perfectCompleteness","extractability"]),
 (A+"ProofSystem/ToyProblem/Codegen.lean","",[]),
 (A+"Data/Fin/Basic.lean","93 (status)",["induction_two"]),
 (A+"OracleReduction/Execution.lean","642, 663, 343 (status)",["run_of_verifier_first","run_of_prover_first","support_run_pure_verifier"]),
 (V+"OracleComp/Constructions/SampleableType.lean","44; 225 (status)",["SampleableType","probEvent_uniformSample"]),
 (V+"OracleComp/SimSemantics/OptionT/Basic.lean","49, 214 (status)",["simulateQ_optionT_bind_run","simulateQ_optionT_failure"]),
 (C+"Multilinear/Basic.lean","47; 410-632; status 475,499,520,543,600,632,482,512",["CMlPolynomialEval","evalMle","evalMleLayer","evalMle_succ","eval₂Mle","eval_mle_eq_eval","eqTilde","eqTilde_eq_prod","eqTilde_append","lagrangeBasis","evalMleLayer_get"]),
 (C+"Multilinear/Equiv.lean","",["toMvPolynomialDeg1","equivMvPolynomialDeg1"]),
 (C+"Multivariate/CMvPolynomial.lean","55-85; 231 (review)",["totalDegree"]),
 (C+"Fields/Binary/BF64/Ext3.lean","171, 199 (status)",["card_ext3"]),
 (C+"Fields/Binary/BF64/Impl.lean","391 (status)",["Fintype"]),
 (CL+"Circuit/Expression.lean","6-90; 71",["Expression","eval","fromArray"]),
 (CL+"Air/FlatComponent.lean","21; 151-186",["operations","Table","Constraints","environment"]),
 (CL+"Circuit/Operations.lean","404-432; 168-182",["constraints","interactions","constraintsHold_iff_forall_mem"]),
 (CL+"Circuit/Channel.lean","101-105, 305-329",["AbstractInteraction","Interaction"]),
 (CL+"Air/FlatEnsemble.lean","19-25; 361; 342; 353-360",["EnsembleWitness","Statement","BalancedChannels"]),
 (CL+"Circuit/WitnessGeneration.lean","82",["witgen"]),
]
KW=r"(?:def|theorem|lemma|structure|inductive|abbrev|instance|class|opaque)"
for f,cited,names in checks:
    p=os.path.join(root,f)
    if not os.path.exists(p):
        print(f"MISSING FILE  {f}   (cited {cited})"); continue
    ls=open(p).read().split("\n")
    print(f"{f}  [{len(ls)} lines]  cited: {cited}")
    for n in names:
        rx=re.compile(r"(?:^|\s)%s\s+(?:[^\s.]+\.)*%s(?=\s|$|\{|\(|\[|:)"%(KW,re.escape(n)))
        hits=[i for i,l in enumerate(ls,1) if rx.search(l)]
        sor=""
        print(f"    {n}: decl at {hits[:8] if hits else 'NOT FOUND as a declaration'}")
    ns=sum(1 for l in ls if re.search(r"\bsorry\b",l))
    if ns: print(f"    (lines containing 'sorry': {ns})")
```

Output:

```text
Arklib/ArkLib/OracleReduction/ProtocolSpec/Basic.lean  [976 lines]  cited: 
    ProtocolSpec: decl at [31]
    Direction: decl at NOT FOUND as a declaration
    MessageIdx: decl at [52]
    ChallengeIdx: decl at [57]
    FullTranscript: decl at [105]
    Transcript: decl at [262]
Arklib/ArkLib/OracleReduction/OracleInterface.lean  [410 lines]  cited: 53-73
    OracleInterface: decl at [55]
Arklib/ArkLib/OracleReduction/OracleInterface.lean  [410 lines]  cited: 93 (status E8)
    instDefault: decl at [93]
Arklib/ArkLib/OracleReduction/Basic.lean  [1025 lines]  cited: 222-669
    Prover: decl at [223]
    Verifier: decl at [248]
    OracleVerifier: decl at [323]
    Reduction: decl at [625]
    OracleReduction: decl at [633]
    OracleProof: decl at [669]
    (lines containing 'sorry': 2)
Arklib/ArkLib/OracleReduction/Basic.lean  [1025 lines]  cited: 1011 (status)
    PureForm: decl at [1011]
    (lines containing 'sorry': 2)
Arklib/ArkLib/OracleReduction/Security/Basic.lean  [766 lines]  cited: 89-103, 460-469
    completeness: decl at [89, 460, 537, 566]
    perfectCompleteness: decl at [103, 469, 542, 575]
    (lines containing 'sorry': 1)
Arklib/ArkLib/OracleReduction/Security/Basic.lean  [766 lines]  cited: 248-359
    knowledgeSoundness: decl at [344, 500, 553, 593]
    Straightline: decl at [248]
    (lines containing 'sorry': 1)
Arklib/ArkLib/OracleReduction/Security/Basic.lean  [766 lines]  cited: 193 (status)
    perfectCompleteness_of_run_support: decl at [193]
    (lines containing 'sorry': 1)
Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean  [903 lines]  cited: 77-190, 416, 534, 606, 553
    KnowledgeStateFunction: decl at [164, 719, 789]
    RoundByRound: decl at [77]
    rbrKnowledgeSoundness: decl at [416, 738, 777, 809]
    rbrKnowledgeSoundnessWorstCase: decl at [534]
    rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness: decl at [606]
    rbrKnowledgeSoundnessWorstCaseWith: decl at [553]
Arklib/ArkLib/OracleReduction/Security/Implications.lean  [417 lines]  cited: 85
    rbrKnowledgeSoundness_implies_rbrSoundness: decl at [87]
    rbrKnowledgeSoundness_implies_knowledgeSoundness: decl at [223]
    rbrSoundness_implies_soundness: decl at [79]
    (lines containing 'sorry': 12)
Arklib/ArkLib/OracleReduction/Composition/Sequential/Append/Basic.lean  [724 lines]  cited: 709
    append: decl at [58, 212, 236, 243, 619, 709]
Arklib/ArkLib/OracleReduction/Composition/Sequential/General.lean  [553 lines]  cited: 255
    seqCompose: decl at [42, 80, 109, 140, 187, 255]
    (lines containing 'sorry': 3)
Arklib/ArkLib/OracleReduction/Composition/Sequential/Completeness.lean  [82 lines]  cited: 
    seqCompose_perfectCompleteness_of_pure: decl at [66]
Arklib/ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean  [273 lines]  cited: 
    append_perfectCompleteness_of_pure_verifiers: decl at [163, 259]
    append_perfectCompleteness_of_guarded_verifiers: decl at NOT FOUND as a declaration
Arklib/ArkLib/OracleReduction/Composition/Sequential/GuardedNary.lean  [94 lines]  cited: 
    seqCompose_completeness_of_guarded_verifiers: decl at [45]
Arklib/ArkLib/OracleReduction/Composition/Sequential/Append/RoundByRound.lean  [145 lines]  cited: 37
    append_rbrSoundnessWorstCase_of_pure_first: decl at [37]
Arklib/ArkLib/OracleReduction/Composition/Sequential/Append/StateFunction.lean  [692 lines]  cited: 292, 75
    append: decl at [39, 75, 292]
Arklib/ArkLib/OracleReduction/Composition/Sequential/Append/Security.lean  [197 lines]  cited: (status: 4 sorries)
    append_knowledgeSoundness: decl at [58, 148]
    append_rbrKnowledgeSoundness: decl at [94, 180]
    (lines containing 'sorry': 4)
Arklib/ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean  [674 lines]  cited: 112 (status)
    GuardedForm: decl at [112]
Arklib/ArkLib/ProofSystem/Sumcheck/Spec/General.lean  [238 lines]  cited: 171
    reduction: decl at [172]
Arklib/ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean  [1285 lines]  cited: 130-144
    StatementRound: decl at [130]
    relationRound: decl at [144]
    verifier_rbrKnowledgeSoundness: decl at [729, 1091]
    (lines containing 'sorry': 15)
MISSING FILE  Arklib/ArkLib/ProofSystem/Sumcheck/Spec/Domain.lean   (cited )
Arklib/ArkLib/Data/MvPolynomial/Multilinear.lean  [427 lines]  cited: 
    MLE: decl at [151]
    eqPolynomial: decl at [88]
    eqTilde: decl at [95]
    eqTilde_append: decl at [116]
    MLE_eq_zero_iff: decl at [252]
    MLEEquivFin: decl at [421]
Arklib/ArkLib/ToCompPoly/Multilinear/Basic.lean  [88 lines]  cited: 56
    eval_eq_MvPolynomial_MLE: decl at [56]
Arklib/ArkLib/Data/MvPolynomial/SchwartzZippelCounting.lean  [215 lines]  cited: 
    schwartz_zippel_counting: decl at [30]
    prob_eval_zero_le_div: decl at [131]
Arklib/ArkLib/OracleReduction/FiatShamir/Basic.lean  [180 lines]  cited: 114-138
    fiatShamir: decl at [114, 130, 140]
    fsChallengeOracle: decl at NOT FOUND as a declaration
    fiatShamir_completeness: decl at [163]
    (lines containing 'sorry': 1)
Arklib/ArkLib/Commitments/Functional/Basic.lean  [364 lines]  cited: 
    Scheme: decl at [67]
    binding: decl at [220]
    perfectCorrectness_of_opening_perfectCompleteness: decl at [128]
    extractability: decl at [250]
Arklib/ArkLib/ProofSystem/ToyProblem/Codegen.lean  [102 lines]  cited: 
Arklib/ArkLib/Data/Fin/Basic.lean  [356 lines]  cited: 93 (status)
    induction_two: decl at [93]
    (lines containing 'sorry': 1)
Arklib/ArkLib/OracleReduction/Execution.lean  [726 lines]  cited: 642, 663, 343 (status)
    run_of_verifier_first: decl at [642]
    run_of_prover_first: decl at [653, 663]
    support_run_pure_verifier: decl at [343]
    (lines containing 'sorry': 1)
VCVio/VCVio/OracleComp/Constructions/SampleableType.lean  [757 lines]  cited: 44; 225 (status)
    SampleableType: decl at [44, 270]
    probEvent_uniformSample: decl at [225]
VCVio/VCVio/OracleComp/SimSemantics/OptionT/Basic.lean  [264 lines]  cited: 49, 214 (status)
    simulateQ_optionT_bind_run: decl at [49]
    simulateQ_optionT_failure: decl at [214]
CompPoly/CompPoly/Multilinear/Basic.lean  [1106 lines]  cited: 47; 410-632; status 475,499,520,543,600,632,482,512
    CMlPolynomialEval: decl at [47]
    evalMle: decl at [499]
    evalMleLayer: decl at [475]
    evalMle_succ: decl at [512]
    eval₂Mle: decl at [520]
    eval_mle_eq_eval: decl at [586]
    eqTilde: decl at [543]
    eqTilde_eq_prod: decl at [600]
    eqTilde_append: decl at [632]
    lagrangeBasis: decl at [410]
    evalMleLayer_get: decl at [482]
CompPoly/CompPoly/Multilinear/Equiv.lean  [358 lines]  cited: 
    toMvPolynomialDeg1: decl at [183, 342]
    equivMvPolynomialDeg1: decl at [200]
CompPoly/CompPoly/Multivariate/CMvPolynomial.lean  [304 lines]  cited: 55-85; 231 (review)
    totalDegree: decl at [231]
CompPoly/CompPoly/Fields/Binary/BF64/Ext3.lean  [203 lines]  cited: 171, 199 (status)
    card_ext3: decl at [199]
CompPoly/CompPoly/Fields/Binary/BF64/Impl.lean  [459 lines]  cited: 391 (status)
    Fintype: decl at NOT FOUND as a declaration
Clean/Clean/Circuit/Expression.lean  [212 lines]  cited: 6-90; 71
    Expression: decl at [12]
    eval: decl at [86]
    fromArray: decl at [71]
Clean/Clean/Air/FlatComponent.lean  [519 lines]  cited: 21; 151-186
    operations: decl at [21]
    Table: decl at [151]
    Constraints: decl at [184, 496]
    environment: decl at [163]
Clean/Clean/Circuit/Operations.lean  [1314 lines]  cited: 404-432; 168-182
    constraints: decl at [68, 404]
    interactions: decl at [78, 428]
    constraintsHold_iff_forall_mem: decl at [176]
Clean/Clean/Circuit/Channel.lean  [427 lines]  cited: 101-105, 305-329
    AbstractInteraction: decl at [101]
    Interaction: decl at [305]
Clean/Clean/Air/FlatEnsemble.lean  [544 lines]  cited: 19-25; 361; 342; 353-360
    EnsembleWitness: decl at [19]
    Statement: decl at [361]
    BalancedChannels: decl at [342]
Clean/Clean/Circuit/WitnessGeneration.lean  [108 lines]  cited: 82
    witgen: decl at [55, 82]
```

### `vocab_counts.py`

Whole-word counts of the competing terms (§C).

Command: `python3 vocab_counts.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): occurrences of competing terms, per document (case-insensitive,
whole words)."""
import re, os
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM"
P=os.path.join(root,".claude/reports/blueprint-review/probes/docs-debt")
docs=[("blueprint","docs/roadmap/protocol-blueprint.md"),("status","docs/roadmap/protocol-status.md"),
("tracker",P+"/issue-12-body.md"),("holes",P+"/issue-12-comment-5833669972.md"),
("rev-spine","docs/reviews/protocol-spine.md"),("rev-L1","docs/reviews/protocol-layer1.md"),("rev-PI","docs/reviews/public-input-phase.md"),
("arch","docs/architecture.md"),("reuse","docs/roadmap/leanth-reuse.md")]
terms=[
 ("roadmap",r"\broadmaps?\b"),("blueprint",r"\bblueprints?\b"),
 ("hole(s)",r"\bholes?\b"),("layer(s)",r"\blayers?\b"),("unit(s) of work",r"\bunits? of work\b|\bunit\b"),("slice(s)",r"\bslices?\b"),("leaf/leaves",r"\bleaf\b|\bleaves\b"),("half/halves",r"\bhalf\b|\bhalves\b"),
 ("dashboard",r"\bdashboard\b"),("tracker",r"\btracker\b"),("tracking issue",r"\btracking issue\b"),
 ("ledger",r"\bledger\b"),("upstream ledger",r"\bupstream ledger\b"),("upstream watch",r"\bupstream[- ]watch\b"),
 ("seam(s)",r"\bseams?\b"),("interface(s)",r"\binterfaces?\b"),("boundary",r"\bboundar(?:y|ies)\b"),
 ("phase(s)",r"\bphases?\b"),("reduction(s)",r"\breductions?\b"),("component(s)",r"\bcomponents?\b"),("stage(s)",r"\bstages?\b"),
 ("stack",r"\bstack\b"),("stacked",r"\bstacked\b"),("oracle",r"\boracle\b"),("committed column/polynomial",r"\bcommitted (?:column|polynomial)\b"),
 ("limb(s)",r"\blimbs?\b"),("lane(s)",r"\blanes?\b"),
 ("claim pool",r"\bclaim pool\b"),("pool/pooled",r"\bpool(?:ed|s)?\b"),
 ("landed/lands",r"\bland(?:ed|s)\b"),("built",r"\bbuilt\b"),("on `main`",r"on `main`"),("merged",r"\bmerged\b"),("claimed",r"\bclaimed\b"),("met",r"\bmet\b"),
 ("the wall",r"\bthe wall\b|\*The wall\*"),
 ("adaptor",r"\badaptor\b"),("adapter",r"\badapter\b"),("bridge",r"\bbridge\b"),("refinement",r"\brefinement\b"),
 ("oracle protocol",r"\boracle protocol\b"),("PIOP/piop",r"piop"),("IOR",r"\bIOR\b"),("IOPP",r"\bIOPP\b|Iopp"),
 ("flush(es)",r"\bflush(?:es)?\b"),("interaction(s)",r"\binteractions?\b"),
 ("side",r"\bsides?\b"),("direction",r"\bdirections?\b"),
 ("public input",r"\bpublic[- ]input\b"),("public statement",r"\bpublic statement\b"),("public words",r"\bpublic words?\b"),("public line(s)",r"\bpublic lines?\b"),
 ("pin/pinned",r"\bpin(?:ned|s)?\b"),
 ("Category A/B",r"\bCategory [AB]\b"),
 ("finding(s)",r"\bfindings?\b"),("decision(s)",r"\bdecisions?\b"),("acceptance test",r"\bacceptance tests?\b"),
 ("M3",r"\bM3\b"),
]
print("term | "+" | ".join(d for d,_ in docs))
for name,rx in terms:
    row=[]
    for d,p in docs:
        path=p if p.startswith("/") else os.path.join(root,p)
        row.append(str(len(re.findall(rx,open(path).read(),flags=re.I))))
    print(f"{name} | "+" | ".join(row))
```

Output:

```text
term | blueprint | status | tracker | holes | rev-spine | rev-L1 | rev-PI | arch | reuse
roadmap | 25 | 16 | 13 | 2 | 9 | 7 | 7 | 1 | 22
blueprint | 5 | 3 | 3 | 11 | 16 | 9 | 12 | 0 | 3
hole(s) | 48 | 19 | 29 | 21 | 18 | 1 | 4 | 0 | 0
layer(s) | 172 | 57 | 20 | 40 | 27 | 13 | 21 | 9 | 40
unit(s) of work | 29 | 1 | 2 | 2 | 4 | 0 | 2 | 0 | 0
slice(s) | 9 | 4 | 1 | 3 | 8 | 1 | 0 | 0 | 4
leaf/leaves | 26 | 10 | 5 | 5 | 7 | 5 | 0 | 0 | 1
half/halves | 10 | 12 | 8 | 9 | 10 | 2 | 1 | 0 | 4
dashboard | 7 | 2 | 0 | 1 | 0 | 1 | 0 | 0 | 0
tracker | 2 | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 0
tracking issue | 1 | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0
ledger | 24 | 10 | 5 | 8 | 1 | 0 | 1 | 0 | 12
upstream ledger | 2 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0
upstream watch | 3 | 1 | 2 | 5 | 0 | 0 | 0 | 0 | 0
seam(s) | 62 | 14 | 20 | 23 | 46 | 1 | 16 | 0 | 2
interface(s) | 28 | 3 | 5 | 5 | 3 | 1 | 1 | 12 | 3
boundary | 17 | 0 | 2 | 4 | 11 | 0 | 0 | 12 | 3
phase(s) | 131 | 67 | 32 | 33 | 69 | 9 | 31 | 0 | 4
reduction(s) | 17 | 7 | 0 | 3 | 1 | 0 | 3 | 0 | 2
component(s) | 60 | 17 | 10 | 6 | 27 | 0 | 8 | 8 | 10
stage(s) | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 2
stack | 41 | 7 | 4 | 3 | 16 | 10 | 12 | 1 | 7
stacked | 6 | 8 | 2 | 0 | 0 | 0 | 0 | 2 | 0
oracle | 51 | 9 | 2 | 4 | 12 | 1 | 1 | 7 | 7
committed column/polynomial | 2 | 0 | 1 | 0 | 1 | 0 | 0 | 0 | 1
limb(s) | 24 | 13 | 1 | 6 | 20 | 1 | 10 | 0 | 0
lane(s) | 5 | 1 | 0 | 1 | 0 | 0 | 0 | 1 | 0
claim pool | 5 | 1 | 0 | 2 | 0 | 0 | 2 | 0 | 1
pool/pooled | 19 | 12 | 1 | 12 | 6 | 0 | 33 | 0 | 2
landed/lands | 9 | 9 | 13 | 4 | 4 | 1 | 2 | 0 | 0
built | 8 | 5 | 0 | 2 | 3 | 2 | 0 | 0 | 1
on `main` | 0 | 10 | 5 | 2 | 0 | 1 | 1 | 0 | 1
merged | 1 | 16 | 4 | 1 | 0 | 0 | 1 | 0 | 4
claimed | 7 | 5 | 7 | 0 | 1 | 1 | 3 | 2 | 0
met | 0 | 7 | 0 | 0 | 13 | 15 | 11 | 0 | 0
the wall | 7 | 4 | 2 | 1 | 0 | 6 | 0 | 0 | 0
adaptor | 29 | 11 | 8 | 6 | 10 | 3 | 3 | 0 | 0
adapter | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 2
bridge | 11 | 1 | 1 | 0 | 1 | 0 | 0 | 6 | 4
refinement | 13 | 4 | 2 | 2 | 10 | 0 | 0 | 2 | 3
oracle protocol | 11 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0
PIOP/piop | 55 | 7 | 8 | 6 | 22 | 0 | 0 | 0 | 3
IOR | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
IOPP | 5 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0
flush(es) | 12 | 2 | 1 | 1 | 8 | 0 | 0 | 0 | 0
interaction(s) | 8 | 10 | 1 | 0 | 0 | 0 | 0 | 5 | 1
side | 12 | 2 | 0 | 1 | 2 | 2 | 1 | 0 | 0
direction | 6 | 1 | 1 | 0 | 5 | 0 | 0 | 6 | 0
public input | 12 | 23 | 1 | 4 | 8 | 0 | 3 | 6 | 1
public statement | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
public words | 6 | 4 | 0 | 0 | 0 | 0 | 3 | 0 | 0
public line(s) | 4 | 4 | 4 | 1 | 3 | 0 | 2 | 0 | 0
pin/pinned | 31 | 44 | 14 | 5 | 27 | 11 | 25 | 6 | 13
Category A/B | 9 | 0 | 2 | 4 | 5 | 0 | 2 | 0 | 0
finding(s) | 18 | 30 | 3 | 5 | 10 | 7 | 10 | 0 | 2
decision(s) | 4 | 10 | 6 | 4 | 10 | 1 | 4 | 1 | 4
acceptance test | 13 | 4 | 1 | 7 | 3 | 3 | 4 | 0 | 4
M3 | 9 | 0 | 1 | 0 | 1 | 0 | 0 | 0 | 1
```

### `coverage_from_blueprint.py`

The blueprint's hole table read as a coverage check: which of each hole's "Produces" names are declared (§E.4, §B.5 item 6).

Command: `python3 coverage_from_blueprint.py`

```python
#!/usr/bin/env python3
"""Feasibility probe (read-only): derive the coverage table from the repository instead of
maintaining it by hand. Input: the blueprint's table 'The holes'
(docs/roadmap/protocol-blueprint.md:595-615), column 'Produces'. For every name in backticks
there, look for a declaration of that name under LeanerVM/. Output: per unit, how many of the
produced names are declared. No Lean is run; the repository forbids `sorry`, so a declared
theorem is a proved one."""
import re, os, glob
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM"
bp=open(os.path.join(root,"docs/roadmap/protocol-blueprint.md")).read().split("\n")
rows=[l for l in bp[596:615] if l.startswith("|")]
src={f:open(f).read().split("\n") for f in glob.glob(os.path.join(root,"LeanerVM/**/*.lean"),recursive=True)}
KW=r"(?:def|theorem|lemma|structure|inductive|abbrev|instance|class|opaque)"
def declared(name):
    short=name.split(".")[-1]
    rx=re.compile(r"(?:^|\s)%s\s+(?:[^\s.]+\.)*%s(?=\s|$|\{|\(|\[|:)"%(KW,re.escape(short)))
    return any(rx.search(l) for ls in src.values() for l in ls)
print(f"{'code':8} {'unit':58} declared/produced   missing")
for r in rows:
    cells=[c.strip() for c in r.strip().strip("|").split(" | ")]
    code,unit,produces=cells[0],cells[1],cells[2]
    names=[n for n in re.findall(r"`([^`]+)`",produces) if re.match(r"^[A-Za-z_][\w.₂']*$",n) and "/" not in n]
    have=[n for n in names if declared(n)]
    miss=[n for n in names if n not in have]
    print(f"{code:8} {unit[:58]:58} {len(have):2}/{len(names):2}              {', '.join(miss)[:90]}")
```

Output:

```text
code     unit                                                       declared/produced   missing
S        the spine                                                   0/ 0              
G1       virtual sumcheck, `Sumcheck.Def` and completeness (Layer 4  0/ 3              Virtual, sumcheck, sumcheck_perfectCompleteness
G2       sumcheck rbr knowledge, `Sumcheck.Security` (Layer 4, A1)   0/ 1              sumcheck_rbrKnowledgeSoundness
G3       batching by powers, `Batch.Def` and `Security` (Layer 4)    0/ 1              batchClaims
G4       fingerprint, Lemma 5.1, the collision bound (Layer 5)       0/ 4              fingerprint, sideProduct, sideProduct_poly_eq_iff, sideProduct_collision
G5, G6   GKR: `Gkr.Def` and completeness; `Gkr.Security` (Layer 5)   0/ 2              gkr, gkrError
L1       Layer 1: tables, stacking, the fixed columns               15/15              
I1       Clean components as polynomials (Layer 2)                   0/ 4              Expression.toMvPolynomial, degreeBound, Component.toM3, Ensemble.toM3
I2       the adaptor (Layer 3)                                       0/ 6              leanIsaInstance, stackOf, witnessOf, satisfiedBy_witnessOf, m3Holds_stackOf, witnessOf_sta
P1, P2   the bus phase (Layer 6)                                     1/ 4              busPhase, leaf_decomposition, busError
P3, P4   the table sumcheck phase (Layer 7)                          1/ 4              tableSummand, tableSummand_target, tableSumcheck
P5       the public-input phase (Layer 8)                            1/ 1              
P6       the Flock phase at the flock seam (Layer 9)                 1/ 3              limbColumns, flockError_le
P7, P8   the claim pool and the opening phase (Layer 10)             3/ 4              openingPhase
C1       the knowledge-soundness append (ledger A2)                  2/ 2              
K1       WHIR over binary Reed–Solomon codes (Layer 11)              0/ 4              encode, whirOpen, whirOpen_rbrSoundness, McaJohnson
K2       Merkle, BLAKE2s bytes, the WHIR parameters (Layer 11)       0/ 4              merkleRoot, merkleVerify, blake2sBytes, ladder
K3       transcript, `Proof`, `verify`, `verify_iff_compiled`, the   0/ 0              
K4       T4 (Layer 13)                                               0/ 2              baseVerifier_extractsExecution, baseProver_complete
```

Regrouping of `leanvm_citations.out` by citation (run in this directory):

```python
import re,collections
cur=None; groups=collections.defaultdict(list)
for l in open("leanvm_citations.out"):
    if l.startswith("====="): cur=l.strip(); continue
    m=re.match(r"\s+(ok|OUT|MISSING|\?\?)\s+(\S+?):(\S+)\s.*\(doc (\d+)\)",l)
    if m:
        st,path,rng,doc=m.groups()
        groups[(cur,doc,path.split("/")[-1],rng)].append(st)
bad=[k for k,v in groups.items() if "ok" not in v]
print(len(groups),"citation groups;", len(bad),"with no resolving candidate")
```

Output: `89 citation groups; 0 with no resolving candidate`.

### Shell probes of the second pass

Run from the repository root unless stated.

```sh
# the independent recount of thirteen codes (section D); OC is the four other comments concatenated
for c in L1 G4 P5 K2 A4 C1 A18 F17 E16 S16 T4 I2 E7; do printf "%-4s" $c
  for f in docs/roadmap/protocol-blueprint.md docs/roadmap/protocol-status.md $P/issue-12-body.md \
           $P/issue-12-comment-5833669972.md $OC docs/reviews/protocol-spine.md \
           docs/reviews/protocol-layer1.md docs/reviews/public-input-phase.md; do
    printf " %3s" $(grep -oP "(?<![A-Za-z0-9_])$c(?![A-Za-z0-9_])" $f | wc -l); done; echo; done
```

```text
L1     6   6   7   0   0   0   2   0
G4     2   5   4   1   0   0   0   0
P5     2  15   3   3   3   7   0   3
K2     4   4   5   3   1   0   0   0
A4     1   4   0   0   0   6   3   2
C1     5   9   5   4   3   6   4   5
A18    0   3   1   0   0   0   0   0
F17    0   4   0   0   0   0   1   2
E16    0   5   0   0   0   0   0   1
S16    0   2   0   0   0   0   1   0
T4    11   1   2   3   0   4   0   0
I2     5   8  11   6   3  15   1   0
E7     0   1   1   0   0   1   0   0
(order: BP ST TB HC OC RS RL RP)
```

```sh
grep -rn "import LeanerVM.Arithmetization" LeanerVM/Protocol        # at b435631 and at 144c5aa
```

```text
LeanerVM/Protocol/Basic.lean:3:public import LeanerVM.Arithmetization.Basic
LeanerVM/Protocol/FixedColumns.lean:11:public import LeanerVM.Arithmetization.Bytecode
```

```sh
# VCVio at its former pin, read before the upgrade replaced the package (section B.9)
(cd .lake/packages/VCVio && git rev-parse --short HEAD)             # f9dc47d9 at the time
find .lake/packages/VCVio/VCVio/CryptoFoundations/MerkleTree -name '*.lean' | wc -l    # 19
grep -rn sorry .lake/packages/VCVio/VCVio/CryptoFoundations/MerkleTree | wc -l         # 0
# ArkLib's distance from the former pin, in the sibling checkout
(cd ../ArkLib && git rev-parse --short origin/main && git rev-list --count dca90385..origin/main \
  && git rev-list --count dca90385..66f39b4)                        # 7653a901e, 347, 246
# the tracker texts, re-read without writing
gh issue view 12 --json body -q .body | diff - probes/docs-debt/issue-12-body.md   # a trailing newline only
gh api repos/Verified-zkEVM/leanerVM/issues/comments/5833669972 -q .updated_at       # 2026-09-28T14:28:11Z
gh pr list --state open --json number,labels                        # 39, 42, 43; no labels
```
