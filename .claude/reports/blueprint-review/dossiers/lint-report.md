# Lint pass over the LaTeX sources of the report (lint-report)

Status: in progress; sections are appended as they are done. Counts at the top are filled last.

Object: `tex/main.tex`, `tex/preamble.tex`, `tex/sections/*.tex`, `tex/sections/gen/*.tex` as they
stood at 11:05 on 2026-09-30 (no source newer than `tex/build/main.log`, 11:03). Paths below are
relative to `.claude/reports/blueprint-review/tex/` unless absolute. Page numbers are the printed
ones; the PDF's physical page is the printed one plus one (the title page is unnumbered).

How it was run (all scratch work under `probes/lint-report/`):

- One LuaLaTeX pass with an unwrapped log, under its own job name so that `build/main.*` was not
  touched: `cp build/main.{aux,toc,out} build/lintjob.{aux,toc,out}` then
  `max_print_line=100000 lualatex -jobname=lintjob -interaction=nonstopmode -halt-on-error -output-directory=build main.tex`
  (exit 0, 527 pages, byte-identical size to `report.pdf`). `probes/lint-report/parselog.py` and
  `parsewarn.py` attribute every box and warning to its input file and page
  (`probes/lint-report/boxes.tsv`).
- `probes/lint-report/codes.py` + `classify.py` (letter codes, `codes-class.tsv`), `layer.py`
  (every "Layer N", `layer.tsv`, `layer-by-file.txt`), `vocab.py` (vocabulary, `vocab.tsv`),
  `ctx.py` (context printer). All skip `leancode`/`srccode`/`shellcode`/`Verbatim` bodies and
  whole-line comments, and skip the six `gen/index-*.tex` files, which nothing inputs.
- `pdftotext -layout report.pdf` for the rendered text; `pdftoppm -r 60` (and `-r 90/110` crops
  of the running heads) for the pages named below, looked at one by one.

## 3. Placeholders and markers

**Orchestrator markers left in the text (27, plus one sentence that announces them).** Every
one is printed in bold in the PDF. They are addressed to the orchestrator ("TO BE INSERTED BY THE
ORCHESTRATOR"), so they read as unfinished work in a final report. Fix for each: either write the
sentence it asks for, or replace the marker by a pointer to the change or register row that
carries the technical content, for example `(see \cref{ch:changes}, row for Layer 10, and
\code{R18})`; appendix A (`ch:changes`) already lists the technical changes.

| file:line | where | what it waits for |
| --- | --- | --- |
| `sections/gen/docs-proposal.tex:313` | table "units of work", row sumcheck: definition and completeness | "one sentence, after the review of Layer 4" |
| `docs-proposal.tex:314` | row sumcheck: knowledge soundness | (bare marker) |
| `docs-proposal.tex:317` | row grand-product GKR: definition and completeness | (bare) |
| `docs-proposal.tex:318` | row grand-product GKR: knowledge soundness | (bare) |
| `docs-proposal.tex:319` | row bus phase: definition and completeness | (bare) |
| `docs-proposal.tex:320` | row bus phase: knowledge soundness | (bare) |
| `docs-proposal.tex:321` | row table sumcheck: definition and completeness | (bare) |
| `docs-proposal.tex:322` | row table sumcheck: knowledge soundness | (bare) |
| `docs-proposal.tex:325` | row opening phase: definition and completeness | "pending the question of specification section 8.5" (the review answered it: `R18`) |
| `docs-proposal.tex:326` | row opening phase: knowledge soundness | (bare) |
| `docs-proposal.tex:327` | row WHIR opening | (bare) |
| `docs-proposal.tex:328` | row Merkle trees, byte hasher, WHIR parameters | "see sec:docs-merkle on VCVio's Merkle trees" |
| `docs-proposal.tex:329` | row transcript, proof object, compiled verifier | (bare) |
| `docs-proposal.tex:330` | row the base theorems | "see sec:docs-leanisa on the program hypothesis" |
| `docs-proposal.tex:381` | after the table of findings against the sources | "rows ... once the other agents' findings are merged into the register" (the register is merged: fill from appendix F or delete) |
| `sections/gen/findings-docs.tex:36` | a finding box | the alternative "verify deciding the program condition" |
| `findings-docs.tex:67` | a finding box | "the message schedules, errors and internal relations of each phase, and the opening phase's schedule against specification §8.5" |
| `findings-docs.tex:110` | a finding box | "which ledger rows ... stay" |
| `findings-docs.tex:237` | a finding box | "that decision, from the review of Layer 11 or the library review" |
| `sections/gen/docs-texts.tex:226` | appendix D, the holes table | "the names and shapes of the generic components of Layers 4 and 5" |
| `docs-texts.tex:257` | appendix D | the `(prog) (s)` sentence |
| `docs-texts.tex:367` | appendix D, status head | `#print axioms` record at `b435631` |
| `docs-texts.tex:392` | appendix D, status | which rows of the upstream watch and ledger the upgrade settles |
| `docs-texts.tex:482` | appendix D, tracker body | holes the review adds, splits, renames or removes |
| `docs-texts.tex:524` | appendix D, hole-comment map | statement types and the opening schedule |
| `docs-texts.tex:571` | appendix D, issue paragraphs | whether Clean pin `42fe4b26` contains Clean #446 |
| `docs-texts.tex:612` | appendix D, issue paragraphs | whether pull requests 39 and 43 fit the review's statement types |
| `docs-texts.tex:7` | appendix D intro | announces the marker; keep only if markers stay, else delete the sentence |

In appendix D the chapter's own intro (`sections/d-tracker-drafts.tex:7-8`) says "the place is
marked in bold; \cref{ch:changes} lists those changes": if the markers are to stay there as
deliberate hand-offs to the owner, reword them to "**To be revised after the change of
appendix A, row ...**" and drop "BY THE ORCHESTRATOR". The 15 markers of chapter 12
(`docs-proposal.tex`, `findings-docs.tex`) have no such announcement and must be filled.

**`[fragment pending]` fallbacks (none printed).** Every `\InputIfFileExists` target exists (all
41 checked; `pdftotext` finds no "pending]", "being typeset" or "inserted here when" in the PDF).
All four `\if…ready` switches in `main.tex:7-10` are on. The fallbacks are therefore dead code,
but dangerous: if a fragment is renamed, the final PDF silently prints "[fragment pending]"
without a build error. Fix: replace every `\InputIfFileExists{X}{}{…}` by `\input{X}` and delete
the four switches and their `\else` branches (`main.tex:7-10`, `06-obligations.tex:10`,
`08-faithfulness.tex:93-99`, `13-drift.tex:124`, `a-proposed-changes.tex:8`, `b-probes.tex:13,19-21`,
`f-register.tex:8`, and the fallbacks in `03-libraries`, `04-catalogue`, `08-faithfulness`,
`10-auditability:111-112`, `12-documentation`, `13-drift:118-123`, `b-probes`, `c-code-index`,
`d-tracker-drafts`).

**"TODO", "XXX", "???", "to be written", "pending" in the text (no fault).** Every remaining hit
is quoted content, not a marker: `TODO` quoted from sources (`docs-codes.tex:120`,
`docs-proposal.tex:250-251`, `code-index.tex:82-83`, `findings-libraries.tex:109`,
`analysis-opening.tex:156,714`, `disagreements-opening.tex:41`, `transcript-bus.tex:60`,
`transcript-opening.tex:686`, `lib-arklib-security.tex:438`, `register.tex:228`,
`lib-clean.tex:123` inside a Lean excerpt); "to be written" means "Lean to be written"
(`boundary-statements.tex:48`, `analysis-opening.tex:47`, `08-faithfulness.tex:105`,
`changes.tex:1158`); "pending" is quoted (`docs-contradictions.tex:36,55`, `docs-texts.tex:21,49,387,407`,
`docs-inventory.tex:35`, `changes.tex:129`) or an identifier (`glue_pending`). No "XXX", "???" or
"FIXME" anywhere; no "??" (undefined reference) in the PDF text.

## 4. Layout

### 4.1 Overfull `\hbox` over 20pt (18 boxes at 11 places)

Measured from the unwrapped log (`probes/lint-report/boxes.tsv`); page = printed page.

| file:lines | page | width | cause | fix |
| --- | --- | --- | --- | --- |
| `sections/02-protocol-map.tex:191-192` | 20 | **299.2pt** and 46.2pt | table `tab:map-where`: `\file{Spine/\{Instance,Seams,Phase,Compose,Toy\}.lean}` and `\file{ToArkLib/\{Component,…,KeepOracles\}.lean}` are single unbreakable detokenized tokens; the cell runs 10 cm into the margin and prints literal `\{` `\}` (visible on physical page 21) | write `\file{Spine/}: \file{Instance}, \file{Seams}, \file{Phase}, \file{Compose}, \file{Toy}; \file{ToArkLib/}: \file{Component}, \file{KnowledgeAppend}, …` (one `\file` per name) |
| `sections/gen/conformance.tex:269-270` | 267 | 75.7pt | justified paragraph with long unbreakable `\texttt` names (`Blocks.selectorWeight` …) | `\begin{sloppypar}…\end{sloppypar}`, or the global fix below |
| `sections/gen/conformance.tex:50-51` | 259 | 70.3pt, 36.4pt | same, list of names (`sendOracleComplete`, …) runs into the margin (seen on physical page 260) | same |
| `sections/gen/surface.tex:44-45` | 293 | 51.1pt, 26.3pt | item **K** of the method list: long names | same |
| `sections/gen/surface.tex:215-216` | 296 | 46.9, 31.7, 29.1pt (and 11.5, 13.6pt at 215-218) | the ArkLib and VCVio name lists (`OracleOutputEmbedding`, `ChallengeIdx.sumEquiv`) | same |
| `sections/gen/probes-code.tex:2123-2124` | 420 | 41.0pt, 26.5pt | a Lean signature typeset as `\texttt` with a per-letter `\allowbreak` still overflows | set it as a `leancode` block |
| `sections/10-auditability.tex:73-76` | 292 | 37.7pt | item 4: `\code{outputPure\_of\_def}` is one unbreakable token (and prints its backslashes, see 7.2) | `\code{outputPure_of_def}` inside `\begin{sloppypar}` or reword |
| `sections/gen/conformance.tex:232-233` | 266 | 35.1pt | `\texttt{[propext, Classical.choice, …]}` | `leancode` or sloppypar |
| `sections/01-scope-method.tex:14-29` | 14 | 26.6pt | table `tab:revisions` (`llll`) wider than the text | `\begin{tabularx}{\linewidth}{@{}llX X@{}}` or `p{}` columns for "Where it was read" and "Role" |
| `sections/gen/probes-code.tex:318-319`, `:209-210` | 390, 388 | 24.0pt each (and 11.2pt) | name lists (`Extractor.RoundByRound…`) | sloppypar |
| `sections/gen/catalogue-spine.tex:826-827` | 92 | 20.2pt | `\texttt{(input, q)}` and names at a line end | sloppypar |

**Global fix that removes most of the 36 smaller overfull boxes as well** (0.2pt to 19.4pt, listed
in `boxes.tsv`; the largest are `catalogue-spine.tex:5-6` 19.4pt, `statements-spine.tex:127-128`
15.6pt, `transcript-table-pub.tex:80-81` 14.0pt, `02-protocol-map.tex:166-168` 13.4pt (the
figure `fig:phases` is 13pt wider than the text), `probes-rerun.tex:26` 10.6pt): add
`\setlength{\emergencystretch}{3em}` to `preamble.tex` (the obligations fragment already sets it
locally). Tables whose `p{}` widths plus column gaps exceed the line: `07-tcb.tex:90`
(`0.30+0.36+0.30`, 5.8pt over: use `0.28+0.34+0.30`), `gen/surface.tex:10-29` (4.8pt),
`gen/probes-rerun.tex:9-33` (8.7pt).

### 4.2 Underfull boxes

No `Underfull \vbox` anywhere (0 in the log). 481 `Underfull \hbox`, which print as stretched
word spacing. 318 of them sit in justified narrow `p{}` columns of the library chapter:
`gen/lib-arklib-pins.tex` 150 (pages 66-72; tables at `:13`, `:64`, `:214`, `:500`),
`gen/lib-lean.tex` 57 (the table at `:13`, page 42, visibly gappy on physical page 43),
`gen/layer0-audit.tex` 45 (`:59`, `:444`), `gen/lib-arklib-security.tex` 37,
`gen/lib-comppoly.tex` 29. Fix: in those column specs use
`>{\raggedright\arraybackslash}p{…}` as the other generated tables already do.

### 4.3 Doubled and mis-levelled headings (the table of contents shows 28 of them)

The chapter file writes `\section{X}` and then inputs a fragment that opens with its own
`\section{X'}`; the result is an empty section followed by a sibling with nearly the same title
(physical pages 43 and 67 show two headings one under the other). From `build/main.toc`:

- Chapter 3: 3.1/3.2, 3.3/3.4, 3.5/3.6, 3.7/3.8, 3.9/3.10, 3.11/3.12, 3.13/3.14, 3.15/3.16
  (3.15 and 3.16 have the same title "Layer 0 of the proof system, audited").
- Chapter 4: 4.1/4.2, 4.3/4.4, 4.5/4.6, 4.7/4.8.
- Chapter 10: 10.4 "The measured tables" / 10.5 "The audit surface, measured".
- Appendix B: B.1/B.2, B.3/B.4. Appendix F: chapter F and F.1 both "The register of findings".
- Chapter 8 and 13: the fragments' sections are **siblings** of the section they belong to:
  8.4 (empty) then 8.5-8.7; 8.8 then 8.9-8.11; 8.12 then 8.13-8.15; 8.16 then 8.17-8.20; 8.21
  then 8.22-8.25; 8.26 then 8.27-8.28; 8.29 then 8.30; 13.3 then 13.4-13.7. The chapter's own
  paragraph "The review's verdict on the GKR round error" (`08-faithfulness.tex:67-77`) therefore
  lands inside 8.7 (the bus findings) instead of 8.4.

Fix: for chapters 3, 4, 10 and appendices B and F, delete the chapter file's `\section` line and
move its `\label` into the fragment's first `\section` (for example
`03-libraries.tex:26` `\label{sec:lib-security}` onto `gen/lib-arklib-security.tex`'s heading);
for chapters 8 and 13, have the generators emit `\subsection` (and demote their subsections), so
that 8.5-8.7 become 8.4.1-8.4.3, and so on. The labels `sec:faith-*`, `sec:lib-*`,
`sec:cat-statements`, `sec:aud-tables` keep working either way.

### 4.4 Floats far from their first reference

Only eight floats exist (`\begin{table}`/`\begin{figure}`); the other 128 tables are
`longtable`s, placed in the flow.

- `fig:chain` (`sections/fig-chain.tex`, input at `02-protocol-map.tex:30`, set on page 18): no
  reference in chapter 2; its **first and only** reference is `13-drift.tex:11`, page 336
  (318 pages later). Fix: add "\Cref{fig:chain} shows the chain from the compiled verifier to the
  semantics." at the end of section 2.1 (after `02-protocol-map.tex:28`), or move the `\input`
  to chapter 13.
- `fig:phases` (`02-protocol-map.tex:116-170`, `[p]`, set on page 21): referenced at
  `02-protocol-map.tex:34` on page 17, four pages earlier, because the environment sits after the
  whole of section 2.2. Fix: move the `figure` environment to just after the paragraph at
  `:34-38`.
- `tab:gen-table-pub-counts` and `tab:gen-table-pub-accepts` (`gen/transcript-table-pub.tex:134`,
  `:333`, `[h]`, pages 174 and 177) are never referenced: add a reference or leave as is (note).
- `tab:revisions`, `tab:map-where`, `tab:reg-count-severity`, `tab:reg-count-subject`: on the page
  of their first reference (checked).

### 4.5 Landscape tables: intro alone on a page, and an orphaned heading

Each `landscape` environment forces a page break, so the heading and intro before it end a page
of their own. Pages found by comparing each run of rotated pages (from `pdfinfo`) with the fill
of the page before it (nonblank lines, header and footer included; a full page has about 52):

| page (printed) | lines | what is alone there | source |
| --- | --- | --- | --- |
| 186 | 4 | heading 8.13.2 "The messages, in order" + two lines, rest of the page empty (physical 187 viewed) | `gen/transcript-flock-ring.tex:73-78` |
| 491 | 4 | the last three lines of the F.1 intro (`Columns: …`) | `gen/register.tex:17-21` |
| 376 | 6 | heading A.2 + its four-line intro | `gen/changes.tex:1291-1301` |
| 145 | 13 | heading 6.3 and 6.3.1 + intro, before table 6.3 | `gen/obligations.tex:448-459` |
| 338 | 19 | 13.3 intro + heading 13.4 + its "Short forms" paragraph | `13-drift.tex:109-118`, `gen/checks-bus.tex:1-20` |
| 341 | 19 | end of 13.4 + heading 13.5 + its short forms | `gen/checks-table-pub.tex:1-20` |
| 344 | 30 | end of 13.5 + heading 13.6 + short forms | `gen/checks-flock-ring.tex:1-25` |
| 347 | 21 | end of 13.6 + heading 13.7 + intro | `gen/checks-opening.tex:1-24` |
| 409 | 15 | **orphaned heading** "B.2.3.3 Results so far (C.2)" at the foot of the page; its content starts after the landscape pages | `gen/probes-code.tex:1561-1563` |

Fix for all: put the intro inside the landscape environment (move `\begin{landscape}` above the
subsection heading and its short-forms paragraph), or float the table to the end of the
subsection; for page 409 at least add `\needspace{8\baselineskip}` or move the heading inside
the landscape block.

### 4.6 Longtables and repeated headers

128 `longtable`s; every one has `\endhead` except `gen/obligations.tex:589-605`
(`tab:obl-arrows`, `\endfirsthead` only). It fits on one page (149), so the missing repeat has
no effect today; add `\endhead` for safety. Rendered continuation pages checked: A.1
(physical 358) and 12.1 (physical 306) repeat their header row.

### 4.7 Narrow columns and letter-by-letter breaks

No column breaks words letter by letter in a way that hurts reading on the pages viewed (21, 34,
43, 67, 73, 80, 260, 294, 306, 340, 358). The narrowest columns (`p{0.029\linewidth}`,
`p{0.035\linewidth}`) hold row numbers only. The per-letter `\allowbreak` that the generators put
into long `\texttt` names makes identifiers break mid-word without a hyphen in running text
(physical page 260: "Component.Securi / ty.{witMid…"; "rbrKnowledgeSoundnessWorstCaseWith_ /
of_guarded_first" on page 66). That is a design choice; a break only after `.` and `_` (as `\bndc`
does, `gen/obligations.tex:5-27`) would read better.

### 4.8 Running heads

The right head is `\leftmark` ("Chapter N. Title"). On every page of chapter 13 (portrait and
landscape, pages 336-354) it **overlaps the left head**: "…proof-system blueprint" and
"Chapter 13. Keeping the Lean verifier from drifting away from the deployed one" print on top of
each other (crop of physical page 339 viewed). No other chapter or appendix title is long
enough (appendix D, the next longest, checked on physical page 474). Fix: a short title,
`\chapter[Keeping the Lean verifier tied to the deployed one]{Keeping the Lean verifier from drifting away from the deployed one}`
or `\chaptermark{Drift from the deployed verifier}` after the `\chapter`. On landscape pages the
heads stay on the portrait edge (standard `pdflscape` behaviour, readable when the page is turned).
The summary pages have an empty right head (`\chapter*` sets no mark): add
`\markboth{Summary}{Summary}` after `00-summary.tex:1`.

### 4.9 Other layout warnings

- `tcolorbox` "Using nobreak failed" at `gen/lib-comppoly.tex:136`, `:206` and
  `gen/lib-arklib-objects.tex:190` (pages 30, 31, 47): a snippet's source line may be separated
  from its box; check those three pages.
- `'h' float specifier changed to 'ht'` at `gen/transcript-table-pub.tex` (page 176): use `[htbp]`.
- `Font shape TU/DejaVuSansMono(0)/m/it undefined` (first at `gen/lib-arklib-security.tex`,
  page 56; also `analysis-opening.tex:6-24`): code inside `\emph` or italic text is set upright
  without warning in the PDF. Fix in `preamble.tex:29`: add
  `ItalicFont={DejaVu Sans Mono Oblique}` (or `FakeSlant=0.2`) to `\setmonofont`.

## 5. References

Negative results first. The log has no undefined reference, no "multiply defined" label and no
"Rerun" request; the PDF text has no "??". The aux file resolves 811 labels; every `ch:` label
sits on a chapter or appendix, every `tab:` on a table, every `fig:` on a figure, every `f:` on a
finding box, every `sec:` on a sectioning unit (checked by script against the anchor type). No
chapter or section is titled "Test". All four `\if…ready` switches are on, so no label lives in a
switched-off branch; the one label in an `\else` branch (`\label{sec:reg}` at `f-register.tex:8`)
is inactive and the same label is defined, once, at `gen/register.tex:5`. The labels that stand
alone at the top of a fragment (`gen/changes.tex:5`, `gen/docs-codes.tex:4`,
`gen/docs-contradictions.tex:4`, `gen/docs-inventory.tex:3`, `gen/docs-texts.tex:4`,
`gen/docs-vocabulary.tex:3`, `gen/findings-docs.tex:3`, `gen/probes-boundary.tex:34`,
`gen/probes-rerun.tex:1`, `gen/register.tex:5`) attach to the heading the chapter file writes just
before the input, as their comments say; checked in the aux.

Faults:

1. **`sec:faith-conformance` sits on the wrong object** (major for navigation).
   `08-faithfulness.tex:114` places `\label{sec:faith-conformance}` *after*
   `\InputIfFileExists{sections/gen/conformance}`, so it takes the last counter the fragment
   stepped: it resolves to **8.27.3.4 "Elsewhere in the blueprint, touching Layer 1 (F.4)",
   page 268**, not to 8.27 "The code against the blueprint" (page 258). Both references go wrong:
   `04-catalogue.tex:11` ("compared with this catalogue in \cref{sec:faith-conformance}") and
   `08-faithfulness.tex:58`. Fix: delete `08-faithfulness.tex:114` and add
   `\label{sec:faith-conformance}` to the `\section{The code against the blueprint}` line of
   `gen/conformance.tex`.
2. **`sec:faith-table` and `sec:faith-pub` on one heading** (`08-faithfulness.tex:79`). Intended
   (the section treats both phases), and both resolve to 8.8. But the two references to
   `sec:faith-pub` (`05-phases.tex:159`, `09-nonvacuity.tex:171`) point the reader to "the repair,
   pooling the values sent", which is neither at 8.8's head nor in its first five pages (the table
   sumcheck). Fix: cite the finding boxes instead,
   `\cref{f:table-pub-public-input-check,f:code-pub-check-on-public-input-message}`, or add
   `\label{sec:faith-pub}` to `gen/transcript-table-pub.tex:188` (`\subsection{The public input}`)
   and drop it from `08-faithfulness.tex:79`.
3. **`\cref{ch:options}` for the comparable verification efforts** (`e-brief-review.tex:50`):
   chapter 11 does not mention them. The only place the report speaks of them is the register's
   negative result N91 (`gen/register.tex:762`, "matches the only published plan (SP1) and
   [KSHC26]'s obligations"). Fix: `\cref{sec:reg-negative}` (row N91), or drop the reference.
4. **Labels on unnumbered paragraphs.** `sec:gen-pubinput-B1` and `sec:gen-pubinput-B2`
   (`gen/conformance.tex:144`, `:175`) are on `\paragraph`s and resolve to the enclosing 8.27.2.1;
   nothing references them (note). The 155 `obl:node-*` labels (`\phantomsection` in
   `gen/obligations.tex`) are never referenced either (note; harmless).
5. **Dossier section codes in headings and finding titles that collide with the report's
   appendix letters.** 57 headings (chapter 4, 8, 10 and appendix B) end with the source dossier's
   section code in parentheses: "(C.1)" … "(C.7)", "(E.1)", "(B)", "(F)", "(D.2)", "(I.5)", "(J)",
   and 19 of the 156 finding-box titles end with "(G.1)", "(G.4)", "(G.6)" … (for example
   `gen/findings-code.tex:149`, `:200`, `:331`). In this report A to F are **appendices**: "B.2.3
   The public-input phase: mutation probes (C)" sits in appendix B and "(C)" reads as appendix C;
   `gen/conformance.tex:50` says "the fourteen of these that section B counts as load-bearing" (dossier section B, not appendix B);
   `gen/probes-code.tex` has "Three facts behind sections B and C.7 (D.7)". The dossiers are not
   part of the report, so the codes cannot be followed. Fix: drop the dossier codes from headings
   and finding titles (the generators can keep them in a `%` comment), and replace "section B/C/D"
   in running text by `\cref` to the report's own section. Full list of the 57 headings:
   `probes/lint-report/headings-dossier-codes.txt`.

## 6. Front matter

1. **Bibliography: `refs.bib` is empty (0 bytes) while the text cites 15 works by key.**
   `main.tex:57-58` has `\bibliographystyle{alpha}` `\bibliography{refs}`; no source has a
   `\cite`; the log says "No file main.bbl." (BibTeX never ran), so today nothing is printed. If
   BibTeX is run it stops on "I found no \citation commands" and the next LuaLaTeX pass prints an
   empty "Bibliography" chapter with an "Empty thebibliography" warning. Meanwhile the text uses
   alpha-style keys that no list resolves: [BCHKS25] (9 times), [CY24] (8), [BGKTTZ23] (4),
   [CMS19] (4), [CO25] (3), [KRS25], [Fen26], [Hab25] (2 each), [BRW26], [CCHLRR19], [Tha13],
   [STW24], [BCS16], [KSHC26] (1 each), and ABF26 unbracketed (`gen/lib-arklib-security.tex:331`);
   in `gen/analysis-opening.tex`, `gen/changes.tex`, `gen/obligations.tex`, `gen/register.tex`,
   `gen/transcript-opening.tex`, `gen/lib-arklib-security.tex`. All fifteen are defined in
   `dossiers/literature.md`. Fix: write `refs.bib` from `dossiers/literature.md` and turn each
   `[KEY]` into `\cite{KEY}`; failing that, delete `main.tex:57-58` and add an unnumbered
   "References" section listing the fifteen keys with their titles.
2. **Table of contents depth.** `preamble.tex:111` sets `tocdepth` 2: 5 parts, 20 chapters, 136
   sections and 199 subsections, ten pages (physical 4-13), 28 of the entries doubled (section
   4.3). Fix: `\setcounter{tocdepth}{1}` (about 160 entries, four pages), after the doubled
   headings are removed.
3. **Title page** (physical page 1, viewed). "Review session of 29 September 2026" and the date
   line "leanerVM main at b435631 · leanVM pinned at a386121f" say nothing of the upgrade the
   report assesses (`144c5aa`) and the session ran into 30 September (the upgrade merged
   2026-09-29 22:31 UTC; the probes re-ran on 09-30). Fix (`main.tex:14-15`):
   `Review session of 29 and 30 September 2026`, and a third line
   `upgrade to main at 144c5aa assessed in section 2.4`.
4. **Summary** (`00-summary.tex:1`): `\chapter*{Summary}\addcontentsline{toc}{chapter}{Summary}`
   is right; add `\markboth{Summary}{Summary}` so the page-2 head is not blank. It precedes the
   table of contents, which is fine for a report meant to be read from the summary.
5. **Page numbering**: arabic from the summary (page 1) through the table of contents (pages
   3-12); the body starts on page 13. Optional: `\pagenumbering{roman}` before the summary and
   `\pagenumbering{arabic}` before `\part{The map}`.
6. **Running heads on landscape pages**: see 4.8 (standard; the only fault is chapter 13's
   overlap, in both orientations).

## 7. Encoding and rendering of code names

1. **No missing characters.** `\tracinglostchars` is 2 at this LaTeX release (checked with a
   one-line test document), and the log has 0 "Missing character" lines; `pdftotext` shows no
   replacement glyphs. No `\label`, `\ref` target or file name contains a non-ASCII character
   (script over all sources; `find` over `tex/`).
2. **Escapes printed literally inside `\code`, `\lean` and `\file`.** These macros are
   `\texttt{\detokenize{#1}}` (`preamble.tex:56-58`), so `\_`, `\ `, `\{`, `\}` and `\#` inside
   them print their backslash, and a `#` prints doubled. 22 occurrences, all visible in the PDF
   text (for example "##print\ axioms", "Phases.Security\ I", "no\_security", "\#guard"):

   | file:line | as written | prints | write instead |
   | --- | --- | --- | --- |
   | `02-protocol-map.tex:191` (2) | `\file{Spine/\{Instance,…\}.lean}`, `\file{ToArkLib/\{…\}.lean}` | `Spine/\{…\}` | see 4.1 |
   | `07-tcb.tex:14`, `11-options.tex:123`, `13-drift.tex:154` | `\lean{\#guard}` | `\#guard` | `\texttt{\#guard}` |
   | `09-nonvacuity.tex:129`, `10-auditability.tex:43` | `\lean{#print\ axioms}` | `##print\ axioms` | `\texttt{\#print axioms}` |
   | `09-nonvacuity.tex:58`, `:70` | `\lean{Phases.Security\ I}` | `Phases.Security\ I` | `\lean{Phases.Security I}` |
   | `09-nonvacuity.tex:62` | `\lean{piopError\ P}` | backslash | `\lean{piopError P}` |
   | `10-auditability.tex:60`, `11-options.tex:15` | `\lean{piopError\ I}` | backslash | `\lean{piopError I}` |
   | `09-nonvacuity.tex:78`, `gen/probes-rerun.tex:21` | `\code{no\_security}` | `no\_security` | `\code{no_security}` |
   | `09-nonvacuity.tex:163`, `13-drift.tex:145` | `\code{not\_rbr}` | `not\_rbr` | `\code{not_rbr}` |
   | `13-drift.tex:145` | `\code{not\_perfectCompleteness}` | backslash | `\code{not_perfectCompleteness}` |
   | `10-auditability.tex:74` | `\code{outputPure\_of\_def}` | backslashes | `\code{outputPure_of_def}` |
   | `13-drift.tex:28` | `\lean{SatisfiedBy.word0\_eq}` | backslash | `\lean{SatisfiedBy.word0_eq}` |
   | `gen/probes-rerun.tex:5` | `\lean{Pr\{let x ← c\}[P x]}` | `Pr\{…\}` | `\texttt{Pr\{let x ← c\}[P x]}` |
   | `gen/probes-rerun.tex:15` | `\code{not\_complete}` | backslash | `\code{not_complete}` |
   | `gen/probes-rerun.tex:26` | `\lean{\#synth}` | `\#synth` | `\texttt{\#synth}` |

   (Found by a script over every `\lean`/`\code`/`\file`/`\bndc` argument outside verbatim;
   `\bndc` un-doubles `#` itself and has no such case. The generated fragments that use
   `\texttt{…\_\allowbreak{}…}` are correct.)
3. **Italic monospace missing**: see 4.9 (emphasis on code silently lost).

