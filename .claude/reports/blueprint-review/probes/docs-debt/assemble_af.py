#!/usr/bin/env python3
"""Assemble sections 'Objects' and A to F of the dossier from the earlier draft, with the
corrections found on re-checking. Writes af.md next to this script."""
import re, os
P = os.path.dirname(os.path.abspath(__file__))
lines = open(os.path.join(P, "dossier-part1.txt"), encoding="utf-8").read().split("\n")
# Objects (line 75) to the end of F.3 (line 1090), 1-based inclusive
body = lines[74:1091]
SECTION_D = range(424 - 75, 735 - 75)      # 0-based indices into body covering section D
QUOTED = {229 - 75, 305 - 75}              # rows whose codes are quotations
sec = re.compile(r"(?<![`\w.])(section )?\b(B(?:10|[1-9])|D[1-4]|E[1-7]|F[1-3]|G[1-4])\b(?![`\w])")
def fix_refs(i, l):
    if i in SECTION_D or i in QUOTED:
        return l
    if l.startswith("### "):
        return re.sub(r"^### ([A-H])(\d{1,2})\. ", r"### \1.\2 ", l)
    def rep(m):
        s = m.group(2)
        return "§" + s[0] + "." + s[1:]
    return sec.sub(rep, l)
body = [fix_refs(i, l) for i, l in enumerate(body)]
text = "\n".join(body)

def sub1(old, new, count=1):
    global text
    n = text.count(old)
    assert n >= 1, ("not found", old[:80])
    text = text.replace(old, new, count)

# --- corrections ---
sub1("| 14 | `:212`, heading \"Decisions pending\", over a section of which 60 lines out of 66 are decisions taken |",
     "| 14 | `:212`, heading \"Decisions pending\", over a section of which 58 lines out of 66 (`:212-269`) are decisions taken |")
sub1("rule is that a decision taken is \"removed from the status file and the dashboard\" (`protocol-blueprint.md:1506-1507`) |",
     "rule is that a decision taken is \"removed from the status file and the dashboard\" (`protocol-blueprint.md:1506-1507`) |\n"
     "| 15 | `:179`: ArkLib's coding-theory track, \"the #907 slices landing on `main`\"; the hole comment says the same, \"landing daily on `main`\" (`issue-12-comment-5833669972.md:154`) | ArkLib issue 907 was closed as completed on 2026-09-26 (`probes/docs-debt/upstream/ArkLib-907.json`) |")
sub1("| 8 | `:176`: \"Consumes: the spine's six `ProtocolSpec`s\"",
     "| 8 | `:178`: \"Consumes: the spine's six `ProtocolSpec`s\"")
sub1("the directory `.lake/packages/VCVio/VCVio/CryptoFoundations/MerkleTree/` holds sixteen modules\n(`Inductive/{Defs,Completeness,Binding,Extractability,Extractor,QueryBound,Uniqueness}.lean`,\n`Inductive/Batch/`, `Addressed/`, `Vector/`), with no `sorry` in any of them",
     "the directory `.lake/packages/VCVio/VCVio/CryptoFoundations/MerkleTree/` holds nineteen modules\n(`Inductive/{Defs,Completeness,Binding,Extractability,Extractor,QueryBound,Uniqueness}.lean`,\nfour under `Inductive/Batch/`, six under `Addressed/`, two under `Vector/`), with no `sorry` in any of them")
sub1("| Local Markdown links and anchors, 24 tracked files | `check_anchors.py`, anchors computed as GitHub does | 150 links, 0 broken |",
     "| Local Markdown links and anchors, all 115 tracked Markdown files (`git ls-files '*.md'`) | `check_anchors.py`, anchors computed as GitHub does | 150 links, 0 broken |")
sub1("`StateMsg` and `leanIsaTables` exist nowhere (§B.5) |",
     "`StateMsg` and `leanIsaTables` exist nowhere (§B.5) |\n"
     "| The import rule of the proof system (acceptance test 25's own witness) | `grep -rn 'import LeanerVM.Arithmetization' LeanerVM/Protocol` | two lines: `FixedColumns.lean:11`, an exception the convention lists, and `Basic.lean:3`, which it does not (§B.5, item 12) |")

# B.5: two new rows after row 11
sub1("| 11 | `docs/README.md:38-47`: three handoffs \"whose findings the branch now meets\" | the three branches are merged |",
     "| 11 | `docs/README.md:38-47`: three handoffs \"whose findings the branch now meets\" | the three branches are merged |\n"
     "| 12 | convention *The wall*, `:331`: \"imports nothing from `LeanerVM/Arithmetization/`; the only exceptions are the fixed columns (`FixedColumns.lean`, Layer 1), the Clean bridge (Layer 2), the adaptor (Layer 3), the compiled verifier (Layer 12) and T4 (Layer 13)\"; acceptance test 25, `:1343-1344`: the `grep` \"lists the exceptions of convention *The wall* only\" | `LeanerVM/Protocol/Basic.lean:3` is `public import LeanerVM.Arithmetization.Basic`. The module is an empty placeholder (a docstring and an empty `public section`) that nothing under `LeanerVM/` or `tests/` imports, so no phase sees the arithmetization through it; but the `grep` the blueprint names as the witness of the import rule returns it, and the rule as written is false of `main` |\n"
     "| 13 | convention *Generic code*, `:329`: \"Comments everywhere are brief and self-contained: they cite the specification, never this roadmap\" | `LeanerVM/Protocol/Field.lean:18` \"Protocol roadmap Layer 0 (`docs/roadmap/protocol-blueprint.md`)\", `:29` \"(leanISA status finding P3)\", `:31` \"every error bound of the roadmap\", `:37` \"(roadmap convention *The oracle*)\", `:37, 66` \"Layer 11\"; `tests/LeanerVMTests/Protocol/Field.lean:9` \"Protocol Layer 0 tests\". Layer 0 predates the rule (merged 2026-09-11 in `51021d9`); every later module of `LeanerVM/Protocol/` follows it (the same `grep` over the other 24 files finds nothing) |")

# B.2: the Layer 1 review's GitHub edit that never happened
sub1("| 11 | rendered body: \"ArkLib #1\"",
     "| 11 | rendered body: \"ArkLib #1\"")
sub1("### B.3 The hole comment, against the blueprint and the code",
     "The Layer 1 review left exactly these two edits for GitHub: \"On GitHub: the L1 line and the open\n"
     "pull request table of the dashboard #12\" (`docs/reviews/protocol-layer1.md:211`). Neither was made\n"
     "(items 1 and 3 above): a review handoff whose tracker edits are not applied leaves the tracker\n"
     "wrong while the handoff's disposition table reads \"met\".\n\n"
     "### B.3 The hole comment, against the blueprint and the code")

# D: method note and corrected counts
sub1("Source of the counts: `extract_codes.py` over the eight documents (blueprint, status, tracker\nbody, hole comment, the four other comments, the three handoffs), and `code_contexts.py`, whose\noutput was read occurrence by occurrence for every code with more than one meaning.",
     "Source of the counts: `extract_codes.py` over the eight documents (blueprint, status, tracker\nbody, hole comment, the four other comments, the three handoffs), and `code_contexts.py`, whose\noutput was read occurrence by occurrence for every code with more than one meaning.\n\n"
     "Re-check (this dossier's second pass). The script's pattern skips a code written inside\n"
     "backticks or followed by `/` (for example `` `L1` `` at `protocol-blueprint.md:591`), so every\n"
     "count below is a lower bound. An independent count with a plain whole-word pattern over the same\n"
     "eight texts, for thirteen codes across the families (`L1`, `G4`, `P5`, `K2`, `A4`, `C1`, `A18`,\n"
     "`F17`, `E16`, `S16`, `T4`, `I2`, `E7`), agrees on 102 of 104 cells; the two differences are\n"
     "corrected below (`L1`: 6 in the blueprint, not 5; `P5`: 3 in the public-input handoff, not 2).\n"
     "The \"defined at\" line of each of those thirteen codes was read at the cited line and is right.")
sub1("| `L1` | tables and stacking (Layer 1): hypercube tables, stacking, the fixed columns | blueprint:603; no section in the hole comment | 20: BP 5, ST 6, TB 7, RL 2 |",
     "| `L1` | tables and stacking (Layer 1): hypercube tables, stacking, the fixed columns | blueprint:603; no section in the hole comment | 21: BP 6, ST 6, TB 7, RL 2 |")
sub1("| `P5` | public-input phase, both halves (Layer 8) | blueprint:608; hole comment:89 | 35: BP 2, ST 15, TB 3, HC 3, OC 3, RS 7, RP 2 |",
     "| `P5` | public-input phase, both halves (Layer 8) | blueprint:608; hole comment:89 | 36: BP 2, ST 15, TB 3, HC 3, OC 3, RS 7, RP 3 |")
sub1("The machine count over the eight documents: 128 distinct letter-number codes, 1036\noccurrences,",
     "The machine count over the eight documents: at least 128 distinct letter-number codes and at\nleast 1036 occurrences,")
# D.3: collisions in the wild
sub1("**Numbered things that collide across the two roadmaps.**",
     "**Collisions already in the trackers.** The body of intention issue 28 says \"Tracks #12, Layer\n"
     "2/C1\", where `C1` is the ledger entry on Clean's expressions, not the unit of work that `C1`\n"
     "names on the checklist of issue 12. Issue 23 says \"the bump also has to survive P3, the eager\n"
     "`Fintype BF64`\", the leanISA finding, while `P3` on issue 12 is the table sumcheck's definition.\n"
     "Issue 4 cites \"decision 15\" (leanISA's: fixed columns after Clean pull request 446), while the\n"
     "proof system's decision 15 is the public-input transcript. `docs/dependencies.md:87` cites\n"
     "\"finding C8\" without saying which status file. The body of intention issue 31 uses a private\n"
     "code, \"P05 depends only on #18's multilinear API\".\n\n"
     "**Numbered things that collide across the two roadmaps.**")
# markers
text = text.replace("[ORCHESTRATOR]", "[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR]")
text = text.replace("[ORCHESTRATOR: ", "[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: ")
text = text.replace("[ORCHESTRATOR: rows for the findings", "[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: rows for the findings")
open(os.path.join(P, "af.md"), "w", encoding="utf-8").write(text + "\n")
print("ok", len(text.split("\n")), "lines")
