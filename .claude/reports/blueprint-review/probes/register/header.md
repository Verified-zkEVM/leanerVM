# Register of the review's findings and negative results (task `register`)

**What this is.** One consolidated index of every finding, every negative result and every
unverified claim of the review's dossiers, so that the report can be written from one table.
It is an index and a summary, never the only record: every row points to the dossier section
that states it in full, and the dossier's text governs where the two differ. No Lean was run
for this register, no tracked file was edited, nothing was posted.

**Object and revisions.** The object of the review is leanerVM `main` at `b435631`; leanVM at
the pin `a386121f` (read, since 2026-09-30, with `git show a386121f:<path>`: the leanVM
checkout has moved, brief §8). Library citations name their revision: old pins ArkLib
`dca90385`, CompPoly `3468b38c`, Clean `93c9d1ef`, VCVio `f9dc47d9` (those of `b435631`); new
pins after `144c5aa` ArkLib `7653a901`, CompPoly `572f9973`, Clean `42fe4b26`, VCVio `a4232d08`.
Blueprint line numbers are at `b435631` (they are +4 at `HEAD` after line 51). Lean probe
outputs are at the old pins unless a row says otherwise.

**Vocabulary.** blueprint (`docs/roadmap/protocol-blueprint.md`), status
(`protocol-status.md`), tracker (issue #12 and its hole comment), spine, phase, seam, hole,
layer; the deployed protocol (the Rust and Python verifiers at the pin) against the
specification (the tex). Letter codes appear only in parentheses after a name.

**Status column.** `cited-checked`: a citation check (`verify-gt-*.md`) covered the row's
citations; corrections it made are applied and marked "corrected by the check".
`probe-run`: a Lean or Python probe that ran supports it (at the old pins unless stated).
`paper`: the argument is a reading or a proof on paper only. `unverified`: the dossier says a
part is unverified. Several tags may apply; the text in parentheses says which part.

**Merging.** A finding stated by two or more dossiers is one row that cites every dossier and
shows each dossier's severity; the row sits at the highest. Findings that are merely related
are separate rows with a "Related" note. Where dossiers disagree, each position is a row and
the note says `DISAGREEMENT` and names both.

## Dossiers processed

| Dossier | State when read | Citation check | Its own count of findings | Notes |
|---|---|---|---|---|
| `gt-table-pub.md` | complete | `verify-gt-table-pub.md`: 301 citations, 294 OK, 2 wrong line, 4 not supported (theorem numbering), 1 could not check (probes not re-runnable) | 3 major, 6 minor, 3 notes | corrections: Corollary 3.9 (not 3.7), Fact 3.10 (not 3.8), Theorem B.7 `thm:rbr` (not B.2), `leanisa-blueprint.md:612-613` |
| `gt-bus.md` | complete | `verify-gt-bus.md`: 314 rows, 300 OK, 3 wrong line, 9 not supported, 2 could not check; "no finding weakened" | 5 major (one of the status), 9 minor, 3 notes | corrections: Lemma 6.3 (not 6.2); the Python caps' provenance; `appendGuarded` is leanerVM's; two arithmetic slips in §D |
| `gt-flock-ring.md` | complete | `verify-gt-flock-ring.md`: about 381, 375 OK, 1 wrong line, 3 misquoted (abbreviations), 2 not supported; "none changes a conclusion" | 4 major, 7 minor, 5 notes | the check: "no verifier takes an inverse" is literally false (constants are inverted) |
| `code-spine.md` | complete | none | 2 major, 5 minor, 3 notes (section F and the summary) | two more rows taken from §E.1 and §E.2 |
| `code-pubinput.md` | complete | none | 2 major, 3 minor, 1 note | probe environment lost at 09:18 (§C.9) |
| `code-layer1.md` | complete | none | 2 major, 7 minor, notes (§G.10) | two notes of §G.10 are negative results (Part 2) |
| `lib-arklib.md` | complete | none | 1 critical (as a warning), 3 major, 2 minor, 2 notes | one more minor from §F.5 (status dates) |
| `lib-others.md` | complete | none | 5 minor, 5 notes | — |
| `docs-debt.md` | complete (second pass re-checked the first draft) | none | 3 major, 13 minor, 4 notes | its §H.20 (what was found right) is in Part 2 |
| `literature.md` | complete | none | 4 major, 7 minor, 4 notes | findings in §A.4, §B.4, §C.4, §D.3, §E.6, §F.3, §G.5 |
| `boundary-adaptor.md` | complete (read after the coordinator's note) | none | 9 major, 6 minor, 3 notes | two probes re-run at the new pins after a rebuild |
| `gt-opening-compile.md` | in progress when read (no findings section yet); skipped | — | — | skipped with this note; to be added when complete |

The working extraction, one block per dossier, is kept at
`.claude/reports/blueprint-review/probes/register/staging.md`; the data and the script that
render this file are `rows.py`, `header.md`, `footer.md` and `render.py` in the same folder.
