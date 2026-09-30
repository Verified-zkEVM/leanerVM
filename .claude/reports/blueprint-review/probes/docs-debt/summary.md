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
