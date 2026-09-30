# Dossier: the documentation debt of the proof system

Task `docs-debt`. Reviewed: leanerVM `main` at `b435631`; the tracker (issue 12 of
`Verified-zkEVM/leanerVM`) and the related issues and pull requests as they stood on
2026-09-29/30, read with `gh` only. Nothing was edited, posted or committed. No Lean was run:
every probe is a Python script or a `grep` over text, listed in the appendix.

Conventions of this dossier. Things are named in words; a letter-number code appears only in
parentheses after the name, or as data in the tables of section D, whose subject is the codes.
The dossier's own sections are written §B.5 and so on, never as a bare letter and number.
Citations are `file:line` of the working tree at `b435631`; for the tracker they are lines of
the raw texts saved under `.claude/reports/blueprint-review/probes/docs-debt/`
(`issue-12-body.md` for the body, `issue-12-comment-5833669972.md` for the "hole comment").
"BP", "ST", "TB", "HC", "OC", "RS", "RL", "RP" in tables abbreviate the blueprint, the status,
the tracker body, the hole comment, the other comments, and the handoffs of the reviews of the
spine, of Layer 1 and of the public-input phase.

SUMMARY_PLACEHOLDER

## How this dossier was made, and what the second pass re-checked

An earlier agent wrote sections A to F and the start of G (`probes/docs-debt/dossier-part1.txt`)
and was interrupted. This pass re-checked that draft against the sources before relying on it,
corrected it, completed §G, and wrote §H and the summary.

**Re-checked, and right.** Every one of the 64 contradictions of §B.1 to §B.9 was read against
both sides at the cited lines (the blueprint, the status, the saved tracker texts, the leanISA
blueprint and status, `architecture.md`, `leanvm-target.md`, `README.md`, `docs/README.md`,
`CONTRIBUTING.md`, the pinned specification's `05-arithmetization.tex:36, 40` and
`preamble/theorems.tex:4-5`, the VCVio pin's `CryptoFoundations/MerkleTree/`). The live state of
GitHub was read again on 2026-09-29/30: the body of issue 12 and the hole comment are unchanged
since 2026-09-28 14:28 UTC (a `diff` against the saved copies differs by a trailing newline only);
the open pull requests are 39, 42, 43, unlabelled; issues 27, 32, 35, 36 are closed and 28 to 31,
33, 37 open; issue 34 is not an intention issue but a merged pull request on the semantics. The
ArkLib figure (347 commits past the pin at `origin/main` `7653a901e`, 246 at `66f39b4`) was
recounted with `git rev-list --count` in the sibling checkout. The Lean snippets of "Objects named
in this dossier" were compared line by line with the files at the cited lines. The probes
`check_anchors.py` and `check_interface_names.py` were re-run and give the same numbers.

**Re-checked in section D.** Thirteen codes across the families (units of work, ledger entries,
ArkLib, specification, Rust, Lean-environment findings, target theorems) were recounted with an
independent whole-word pattern over the eight texts, and their "defined at" lines read.

**Corrected.**
- §B.3, item 8: the hole comment's "the spine's six `ProtocolSpec`s" is at `:178`, not `:176`.
- §B.9: VCVio's Merkle-tree directory at the pin holds nineteen modules, not sixteen.
- §B.10: the anchor probe covers all 115 tracked Markdown files, not 24.
- §B.1, item 14: 58 of the 66 lines of "Decisions pending" are decisions taken, not 60.
- Section D: the code counts are lower bounds (the pattern skips codes in backticks); two cells
  corrected.
- The earlier draft's proposed status text said that no proof-system module other than
  `FixedColumns.lean` imports the arithmetization. That is false: `LeanerVM/Protocol/Basic.lean:3`
  does. Added as §B.5, item 12 and a finding; the proposed text in §G.3 is corrected.
- The earlier summary announced findings (major 4, minor 17, note 5) for a section H that did not
  exist. §H is written from scratch; its counts are in the summary.

**Added.** §B.1, item 15 (ArkLib issue 907 closed); §B.2, the Layer 1 review's two GitHub edits
never applied; §B.5, items 12 and 13 (the import rule's witness; the Layer 0 module's comments);
§D.3, codes that already collide in the trackers.

## Objects named in this dossier
