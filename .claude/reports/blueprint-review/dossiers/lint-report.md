# Lint pass over the LaTeX sources of the report (lint-report)

## Summary

Examined: `tex/main.tex`, `tex/preamble.tex`, the 22 files under `tex/sections/` and the 58
generated fragments under `tex/sections/gen/` (the six `index-*.tex` among them are input by
nothing and were skipped), the build log (re-run unwrapped under a separate job name, identical 527-page
output) and the PDF (text extraction; pages viewed as images where a fault was suspected). No
`.tex` file was edited.

Counts per group (details in sections 1 to 7 below, in the order of the task):

| group | faults | of which serious |
| --- | --- | --- |
| 1. Letter codes | 804 violations and 363 to check by hand among 2,940 occurrences (1,773 allowed) | 78 own row codes that collide (T4, R2, R4, P1, P2, G1-G3, U, C1); 71 dossier codes in the obligations tree; 32 "Layer N" in headings |
| 2. Vocabulary | about 80 items: "roadmap" for the blueprint 11, "unit of work" 7 places, "pin" as a verb 23 and a definition that misses VCVio and Mathlib, "Category B" unexplained 15, four objects with two or more names, "the Rust" for the verifier 16, "the spec" 1; no fault for "dashboard", "slice", "PIOP" | none serious |
| 3. Placeholders | 27 "TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR" markers printed in bold (19 in chapter 12, 8 in appendix D) + 1 sentence announcing them; 55 dead `[fragment pending]` fallbacks (none printed) | the 27 markers |
| 4. Layout | 18 overfull boxes over 20pt at 11 places (worst 299pt), 36 smaller; 0 underfull vbox; 481 underfull hbox (318 in five library tables); 16 empty or duplicate sections and 24 fragment sections one level too high; 2 figures far from their reference; 9 landscape intros alone on a page (one orphaned heading); 1 running head overlapping on 19 pages; 1 longtable without `\endhead` (no effect today); 5 minor warnings | the 299pt table cell, the doubled headings, the chapter-13 running head |
| 5. References | 1 label on the wrong object (`sec:faith-conformance`), 1 label pair whose references land badly, 1 `\cref` to a chapter that does not treat the subject, 57 headings and 19 finding titles carrying dossier section codes that read as appendix letters; 0 undefined, 0 multiply defined | `sec:faith-conformance` |
| 6. Front matter | empty `refs.bib` while 15 works are cited by key; table of contents ten pages deep at depth 2; title page silent on `144c5aa` and on 30 September; blank head on the summary | the bibliography |
| 7. Encoding | 0 missing characters, 0 non-ASCII labels or file names; 22 backslashes or doubled `#` printed from `\code`/`\lean`/`\file`; italic monospace missing | the 22 printed escapes |

The ten items that matter most:

1. **The report's own row codes collide** (1.1): the transcript and check tables label rows T0-T12,
   P0-P4, R1-R5, G1-G2, U0-U7, C1-C2, …; in chapter 8 "T4" is both step 4 of the table sumcheck
   and the base theorem, "R2"/"R4" are both opening checks and register rows, "P1"/"P2" both
   transcript steps and bus-phase holes, "G1"-"G3" both grinding checks and holes. Number rows
   1…n and cite "check 9 of table 13.1".
2. **27 orchestrator markers are printed** (3): `gen/docs-proposal.tex:313-330,381`,
   `gen/findings-docs.tex:36,67,110,237`, `gen/docs-texts.tex:226,257,367,392,482,524,571,612`.
3. **`\label{sec:faith-conformance}` sits on the wrong object** (5.1): `08-faithfulness.tex:114`,
   after the input, resolves to 8.27.3.4 (page 268) instead of 8.27 (page 258); both references
   (`04-catalogue.tex:11`, `08-faithfulness.tex:58`) mislead.
4. **No bibliography** (6.1): `refs.bib` is 0 bytes and nothing is `\cite`d, yet [BCHKS25], [CY24],
   [BGKTTZ23], [CMS19], [CO25] and ten more keys appear in the text; all are in
   `dossiers/literature.md`.
5. **Doubled headings** (4.3): chapter files and fragments both open a `\section`, giving empty
   sections and near-duplicate titles (3.15 and 3.16 are both "Layer 0 of the proof system,
   audited"); in chapters 8 and 13 the fragments' sections become siblings of their parent.
6. **A table cell 299pt too wide** (4.1): `02-protocol-map.tex:191`, `tab:map-where`, the
   `\file{Spine/\{Instance,…\}.lean}` cell runs 10 cm into the margin and prints `\{ \}`; 17 other
   overfull boxes exceed 20pt (a global `\emergencystretch` fixes most).
7. **22 escape artifacts in the PDF** (7.2): "##print\ axioms", "Phases.Security\ I",
   "no\_security", "\#guard", … from `\lean{…\ …}`, `\code{…\_…}`, `\lean{\#…}` in chapters 7, 9, 10,
   11, 13 and `gen/probes-rerun.tex`.
8. **The running head overlaps on every page of chapter 13** (4.8): give the chapter a short title.
9. **Bare codes in headings and prose** (1.2-1.7, 5.5): 32 headings with "Layer N", 57 headings
   and 19 finding titles ending in dossier section codes "(C.7)", "(E.3)", "(D)" that read as
   appendices C, E, D; 71 two-letter dossier codes in the obligations tree, which even cites
   "register (GB1, GB2, GB11)" though the register numbers R1-R140; 57 bare "acceptance test N"
   and 48 bare T1-T8; about 30 bare "Layer N" in the hand-written chapters (each with its fix in 1.7).
10. **Pages left nearly empty before landscape tables** (4.5): page 186 (4 lines), 491 (4), 376
    (6), 145, 338, 341, 344, 347, and an orphaned heading at the foot of page 409; and
    `fig:chain` is referenced only from page 336, 318 pages after it (4.4).

## Method

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

## 1. Letter codes

### 1.0 How the occurrences were classified, and the totals

Every token of the families `[A-Z][0-9]{1,2}`, `T1`–`T8`, `Layer N`/`Layers N…`/`Layer~N`,
`hole X`, `decision N` and `acceptance test N` outside verbatim blocks and whole-line comments,
plus the two-letter dossier codes of the obligations tree (`CS1`, `TP4`, `GB11`, `FR7`, …): 2,940
occurrences. The full per-occurrence table, with verdict, the surrounding text and the
replacement phrase, is `probes/lint-report/codes-verdict.tsv`; the per-file line lists are
`probes/lint-report/perfile.md` (reproduced in 1.8).

| verdict | count | rule applied |
| --- | ---: | --- |
| allowed: register row number | 673 | `R1`…`R140` as row keys and in `\code{Rn}` references; `N1`…`N115` and `U1`…`U58`, the register's own row keys for negative results and unverified items (same design as `R`) |
| allowed: code inventory | 553 | `gen/docs-codes.tex`, `gen/code-index.tex`, and the five mapping tables of `gen/docs-proposal.tex` (lines 133-160, 167-205, 208-236, 238-283, 290-380) |
| allowed: parenthesised right after a name | 307 | "(Layer 12)", "(T4)", "(acceptance test 10)" directly after the words naming the thing |
| allowed: quotation | 206 | inside ``…'' or `\enquote{…}` quoting a document |
| allowed: subject matter | 23 | chapter 12 and appendix D discussing the documents' codes as codes |
| allowed: identifier or file name | 11 | inside `\code`/`\lean`/`\file` (probe files `P2Relation`, `P4Junk`, …) |
| **violation** | **804** | 381 "Layer N" in running text, 32 "Layer N" in headings, 78 own row codes (1.1), 71 two-letter dossier codes (1.2), 242 other bare codes (among them 48 T1–T8, 57 "acceptance test N", 33 dossier locators "gt-bus G1", and the prose references to the own row codes) |
| check by hand | 363 | 174 "Layer N" table cells (allowed only in an index column such as the "Blueprint" column of `tab:map-where`) and 189 codes inside a parenthetical but not right after a name (87 "Layer N", 102 others; for example "(the spine, Layers 0 and 1, the public-input phase)") |

Other tokens matched by the families and allowed: citation keys (`[CY24]`, `[BCHKS25]`, …; see
6.1), `BF64` (a type), `SP1` (a zkVM's name, `gen/register.tex:762`), "Ethereum L1"
(`gen/conformance.tex:173`, better written "Ethereum's layer 1"), `M3` inside `M3Holds`,
`toM3` and in the blueprint's heading "the M3 instance" (a name, not a code).

The **replacement phrases** come from the report's own drafted index of names
(`gen/docs-proposal.tex:290-380`, table `tab:docs-index-draft`) and, for the target theorems it
omits, from `docs/architecture.md:63-70` at `b435631`:

| code | name to write (code in parentheses on first mention) |
| --- | --- |
| Layer 0 … 13 | the field instances (0); tables and stacking (1); Clean expressions as polynomials (2); the adaptor (3); the sumcheck and batching components (4); fingerprints and the grand-product GKR (5); the bus phase (6); the table sumcheck (7); the public-input phase (8); the Flock phase (9); the claim pool and the opening (10); WHIR and Merkle trees (11); the compilation and the executable verifier (12); the base theorems and fixtures (13) |
| T1 … T8 | arithmetization and ISA equivalence; witness-generator correctness; exact guest correctness; base proof extraction and completeness (the proof system's target theorem); recursive-verifier correctness; recursion extraction; end-to-end soundness; end-to-end completeness |
| acceptance tests 1 … 28 | fingerprint degree; padding leaves are 1; the nonzero count root is load-bearing; one root, not two; domain separators; zerocheck point recycling; back-loaded padding; degree three, three scalars; shared bus powers; top limb of the public input; joint list binding; absorb before squeeze; index column bit order; bytecode slot bits; selector alignment; variable order; radix and parity; counts in the count tree; the extractor reads the stack; no exceptional challenge; sizes are parameters; tags, not labels; numeric error; the extractor computes; the import rule holds; seams are the contract; the toy instance is honest; the bus seam bounds the degree |
| decisions 1 … 15 | heights are powers of two; statement and parameters; where the zerocheck is charged; where generic code lives; an end-to-end run of the honest prover; the witness is the stack; phases over an abstract instance; five clauses, caps outside; balance is a permutation; worst-case round-by-round knowledge soundness; extractors are computable definitions; the strong Flock predicate; public lines, not cells; the degree bound belongs to the instance; the public-input transcript |
| holes S, C1, L1, I1, I2, G1–G6, P1–P8, K1–K4 | the spine; the knowledge-soundness composition; tables and stacking; Clean expressions as polynomials; the adaptor; sumcheck (definition and completeness / knowledge soundness); batching by powers; fingerprint and collision bound; grand-product GKR (two halves); bus phase (two halves); table sumcheck (two halves); the public-input phase; the Flock phase; opening (two halves); the WHIR opening; Merkle trees, byte hasher, WHIR parameters; transcript, proof object, compiled verifier; the base theorems |

### 1.1 The report's own row codes collide with each other and with the documents' codes (major)

The transcript and check tables number their rows with letter codes of their own, the very thing
the report's rule forbids ("your own findings get a short descriptive name, not a code"), and
the codes collide inside the same chapter:

| table | row codes | source |
| --- | --- | --- |
| the setup, commitment and bus transcript (8.5) | S0–S6, C1–C2, U0–U7 | `gen/transcript-bus.tex:57-150` |
| the table sumcheck and public-input transcript (8.9) | T0–T12, P0–P4 | `gen/transcript-table-pub.tex:53-123`, `:203-223` |
| the checks of the setup, commitment and bus (13.4) | B1–B17 | `gen/checks-bus.tex:35-165` |
| the checks of the opening and compilation (13.7) | R1–R5, G1–G2, M1–M7, W1–W8 | `gen/checks-opening.tex:74-257` |

Collisions that a reader meets:

- **T4** is "step 4, the number of rounds" (`gen/findings-table-pub.tex:125`) and the proof
  system's target theorem (`gen/findings-opening.tex:104,107,120`, `gen/analysis-opening.tex:76`),
  both in chapter 8; T1–T8 are the target theorems throughout (`docs/architecture.md`).
- **R2, R4** are opening checks (`gen/checks-opening.tex:169,277`,
  `gen/disagreements-opening.tex:56`: "the canonical encodings (…; R2), full consumption (R4)") and
  register rows R2 ("the bus seam admits statements…") and R4 (cited in `11-options.tex:49`).
- **P1, P2** are public-input steps (`gen/transcript-table-pub.tex:141`: "2 (step P2) & 1 (step
  P1)") and the tracker's holes for the bus phase (`gen/findings-bus.tex:257,373,418`).
- **G1, G2** are the grinding checks (`gen/checks-opening.tex:275,277`,
  `gen/disagreements-opening.tex:55`) and the sumcheck holes, and "gt-bus G1" is the bus
  dossier's first finding (`gen/register.tex:55`); **G3** is the batching hole
  (`gen/transcript-opening.tex:307`, `gen/findings-opening.tex:47`).
- **U1–U7** are bus transcript steps and the register's unverified items U1–U58.
- **C1** is the commitment step and the hole "the knowledge-soundness composition" and a ledger
  entry; **S0–S6** sit beside the status file's findings S11, S12
  (`gen/findings-bus.tex:403,409`, `gen/disagreements-opening.tex:103`).

References to these row codes from running text (each to be rewritten with the fix):
`gen/checks-bus.tex:64,71,83,124,175`; `gen/checks-table-pub.tex:78,84,105,111`;
`gen/checks-opening.tex:17,41,53,67,100,169,207,219,274-279`;
`gen/transcript-bus.tex:76,159,161,349,358`; `gen/transcript-table-pub.tex:59,141,209,252,254`;
`gen/disagreements-bus.tex:46-48,61`; `gen/disagreements-table-pub.tex:33,37,42`;
`gen/disagreements-opening.tex:54-56,68`; `gen/findings-bus.tex:173,323-324`;
`gen/findings-table-pub.tex:25,125,183`; `gen/findings-opening.tex:22,274`;
`gen/analysis-opening.tex:266`; `gen/transcript-opening.tex:784,857`; `gen/obligations.tex:143`
(check M7), `:225-226` (B12, B13).

**Fix.** Number each table's rows 1, 2, 3 … (numbers collide with no code) and cite "step 4 of
\cref{tab:gen-table-pub-transcript-table}", "check 9 of \cref{tab:gen-bus-checks}"; in prose name
the check and give the number in parentheses: "the stacking window (check 9 of table 13.1)",
"full consumption of the stream (check 4 of table 13.7)".

### 1.2 The obligations tree cites dossier codes the report does not define (major for navigation)

`gen/obligations.tex` cites other dossiers' findings with two-letter codes invented by the
obligations dossier: CS (code-spine), TP (gt-table-pub), GB (gt-bus), FR (gt-flock-ring), LT
(literature), DD (docs-debt), AK (lib-arklib), LO (lib-others), PI (code-pubinput); 71
occurrences on lines 114-115, 134-136, 143, 145, 147, 153, 157, 175-176, 188-189, 196-198,
203-204, 208-209, 220, 228-233, 240, 245, 252, 254, 271-273, 278-284, 307, 313, 329, 368, 400,
439, 567-569, 576, 632, 638, 679, 734. Line 220 even says "register (GB1, GB2, GB11)", but the
report's register numbers its rows R1–R140; no GB-code exists in it. The same fragment and the
register's "Where stated" column also cite dossier findings as "gt-bus G1, G2, G8, G11" (33
times: `gen/obligations.tex` 16, `gen/register.tex` 17), which reads as the sumcheck holes G1, G2.
Fix: replace each two-letter code by the register row that states the finding (for example CS1,
"the declared error is unconstrained", is `\code{R5}`) or by `\cref{f:…}` to its finding box; write
dossier locators as the register does elsewhere, "gt-bus §G.1".

### 1.3 The documents' codes used as names in running text (minor; each a one-line fix)

| file:line | text | write instead |
| --- | --- | --- |
| `gen/boundary-chain.tex:225` | "owed by the phases (holes P1 to P8; the public-input phase, P5, built)" | "owed by the four phase holes (P1 to P8); the public-input phase (P5) is built" |
| `gen/changes.tex:224` | "Round-by-round to plain (A3):" | allowed (parenthesised after the name) |
| `gen/changes.tex:541,546,553` | "Table, rows G4, P6, P7--P8", "rows P6 and K3", "row K3" | "rows 'fingerprint and collision bound' (G4), 'the Flock phase' (P6), 'opening' (P7-P8)" and so on |
| `gen/changes.tex:562-568` | "K3 gains the Merkle compilation…; K1 the K-valuedness lemma…; L1 the strided reader…; I1 …; I2 …; P5 …; G1 …" | name each hole first: "transcript, proof object, compiled verifier (K3) gains …" |
| `gen/changes.tex:1235` | "the protocol status's F3 is another finding" | "the status file's finding 'one root for push and pull' (F3) is another finding" |
| `gen/changes.tex:1241` | "between K1 and K3" | "between the WHIR opening (K1) and the compiled verifier (K3)" |
| `gen/findings-bus.tex:214` | quotation of `st:164` "Finding F9 …" | allowed (quotation) |
| `gen/findings-bus.tex:426` | "the status file's finding on the seed, F14" | "(F14)" in parentheses |
| `gen/findings-code.tex:139` | "which the review's A6 reads as" | "which the earlier review's item on the toy (A6) reads as" |
| `gen/findings-code.tex:169` | "The status finding (F18)" | allowed |
| `gen/findings-flock-ring.tex:365` | "Owned by #3 (F5)" in a quoted ledger row | allowed (inside the quoted row) |
| `gen/findings-libraries.tex:88-93` | change box "the ledger's actions for rows A2 and A3", "A2: …", "A3: …" | "the ledger rows on the knowledge-soundness composition (A2) and round-by-round to plain (A3)"; inside the box "Composition (A2): …" |
| `gen/findings-libraries.tex:103,122`, `gen/register.tex:240` | "ledger row A5" | "the ledger row on the named interfaces (A5)" |
| `gen/findings-libraries.tex:324` | "Recorded as leanISA status finding E6" | "recorded in the leanISA status (finding E6)" |
| `gen/obligations.tex:308` | "the blueprint's ledger row A1 omits" | "the ledger row on the admitted sumcheck round (A1) omits" |
| `gen/lib-clean.tex:400-401` | "the 'Clean bridge is plain' convention (leanISA status finding C8) retires" | allowed (parenthesised after the name) |
| `gen/transcript-opening.tex:732` | "the status file's finding F13)" | "(F13)" after the finding's name |
| `gen/register.tex:325` | "(…, K1, a new list-binding hole, L1, I1, I2, P5, G1, S)" | hole names, codes in parentheses |
| `gen/register.tex:604` | "ties put the shared columns first (F17)" | allowed |
| `gen/register.tex:640,644,646,648`, `gen/probes-code.tex:13,303` | "probe P1", "probe P2", "probe P3a", "probes P3b, P1", "P1 to P6, with P3 in three files" | the probe file names (`P1Axioms`, `P2Relation`, `P3aSeams`, `P3bCommit`, `P3cExtractor`, `P4Junk`, `P5PassThrough`, `P6Surface`); "P1" … "P6" alone collide with the phase holes |
| `gen/register.tex:1014` | "The check corrected G1's wording" | "corrected the wording of the bus dossier's finding on the normalized GKR (gt-bus §G.1)" |
| `09-nonvacuity.tex:168` | "(pooling the lines' values, item H1 of that review)" | allowed (parenthesised after "its own compression") |

### 1.4 Target-theorem codes T1–T8 used bare (48, all in generated fragments)

`gen/analysis-opening.tex:76`; `gen/boundary-chain.tex:49,220,383`;
`gen/boundary-statements.tex:397`; `gen/changes.tex:358,503,504,692,1223` and `:1032` (the
heading "Layer 13: T4 and the fixtures" quotes the blueprint's heading; name it anyway);
`gen/checks-table-pub.tex:84` (T12 is a transcript step, see 1.1); `gen/findings-boundary.tex:464,498,510`;
`gen/findings-opening.tex:104,107,120`;
`gen/obligations.tex:95 (twice),103,114 (four times),115 (twice),398,399,400 (twice),425,613,629 (twice),630,632,638 (twice),681`;
`gen/probes-code.tex:2134,2168`; `gen/register.tex:97,780`; `gen/statements-spine.tex:129` (the
heading "Refinement and what T4 needs (C.7)"), `:142 (twice)`; `gen/surface.tex:228`. The
chapter files use none bare. Fix: "the base theorem (T4)" on first mention in a paragraph, "the
base theorem" after; "T1-S", "T1-C" become "constraint soundness (T1-S)", "constraint
completeness (T1-C)".

### 1.5 "acceptance test N" used bare (57 outside the chapter-12 index table)

Hand-written chapters: `05-phases.tex:185` ("The blueprint's acceptance test 20 attributes this
inverse…" → "The blueprint's acceptance test 'no exceptional challenge' (acceptance test 20)
attributes…"); `09-nonvacuity.tex:150` ("the risk that acceptance test 24 guards against" →
"the risk that the acceptance test 'the extractor computes' (24) guards against");
`11-options.tex:47` ("acceptance test 20 rewritten" → "the acceptance test 'no exceptional
challenge' (20) rewritten"); `13-drift.tex:92` ("the blueprint's acceptance test 10 is a test on
the pool" → "the blueprint's acceptance test 'top limb of the public input' (10) is…").
Generated fragments: `gen/analysis-opening.tex:433,453` (453 is a heading), `gen/boundary-chain.tex:146`,
`gen/boundary-statements.tex:120`, `gen/conformance.tex:79,297`, `gen/findings-boundary.tex:290`,
`gen/findings-bus.tex:102,326,329,362`, `gen/findings-code.tex:63,75,90,186,363`,
`gen/findings-docs.tex:149,153,209 (2)`, `gen/findings-flock-ring.tex:186,334` (both are
`\begin{change}{acceptance test N}` titles), `gen/findings-opening.tex:222,230,358`,
`gen/findings-table-pub.tex:235`, `gen/obligations.tex:147,196,224,225,226,241,263,272,329,496,669,675`,
`gen/probes-code.tex:52,251,2170` (2170 is a heading), `gen/register.tex:148,175,368,384,392,606,1040`,
`gen/statements-spine.tex:115`, `gen/surface.tex:228,287,289`, `gen/transcript-opening.tex:854`.
Headings in the table of contents: "8.19.2.1 The blueprint's piopError_le and acceptance test
23", "8.27.1.3 Acceptance tests 24 to 28 against the code (E.3)", "8.27.3.2 Acceptance tests 7,
13, 14, 15 (F.2)", "B.2.4.2 In the tests: acceptance test 10's witness exists today (D.2)".

### 1.6 "decision N" and "hole X" used bare (minor)

- Decisions: `gen/changes.tex:512` (quoted: allowed), `gen/conformance.tex:203` ("the status'
  decision 15" → "the status's decision on the public-input transcript (15)"),
  `gen/findings-boundary.tex:300` ("decision 12" → "the leanISA decision on the strong Flock
  predicate (12)" — check which roadmap's 12 is meant), `:484` ("decision 14"),
  `gen/findings-code.tex:201` ("decision 15"). The numbering discussions in
  `gen/docs-contradictions.tex:246` and `gen/findings-docs.tex:189` are subject matter (allowed).
  Beware: `gen/docs-texts.tex:560` notes that "decision 15" means two things (leanISA's and the
  proof system's); every bare "decision N" should say whose.
- Holes: `gen/boundary-chain.tex:225` ("holes P1 to P8"), `gen/obligations.tex:371` (heading
  "…(hole I1; not built)": parenthesised after the name, allowed), `gen/changes.tex:903`,
  `gen/docs-contradictions.tex:135`, `gen/findings-docs.tex:180` (all three quote "closes hole C1":
  allowed), `gen/docs-texts.tex:242` (quote: allowed).

### 1.7 "Layer N" (413 violations: 381 in running text, 32 in headings; 174 table cells and 87 embedded parentheticals to check)

**Headings** (they reach the table of contents and the running heads):
`03-libraries.tex:32` "Layer 0 of the proof system, audited" → "The field instances (Layer 0),
audited"; `04-catalogue.tex:19` "Layer 1: tables, stacking, …" → "Tables and stacking (Layer 1):
…"; `08-faithfulness.tex:111` "The code as built: the spine, Layer 1, the public-input phase" →
"…the spine, tables and stacking, the public-input phase"; `08-faithfulness.tex:117` "The
libraries and Layer 0" → "The libraries and the field instances"; `b-probes.tex:9` "The spine,
the public-input phase, Layer 1" → "…, tables and stacking"; `05-phases.tex:195,225` (paragraph
text on the heading line); generated: `gen/catalogue-layer1.tex:3,5`, `gen/layer0-audit.tex:4,60,439,445`,
`gen/conformance.tex:236,240,291`, `gen/findings-code.tex:232`, `gen/findings-libraries.tex:6`,
`gen/obligations.tex:345,362,371`, `gen/probes-code.tex:2205`, `gen/surface.tex:245`,
`gen/boundary-statements.tex:256`, `gen/transcript-opening.tex:612,616,861,865`,
`gen/docs-inventory.tex:5`.

**Hand-written chapters** (each with its fix):

| file:line | text | write instead |
| --- | --- | --- |
| `00-summary.tex:6` | "the spine (…), Layer 0, Layer 1 and the public-input phase" | "the spine (…), the field instances and the tables and stacking (Layers 0 and 1) and the public-input phase" |
| `00-summary.tex:25` | "in Layer 1's transcriptions" | "in the transcriptions of tables and stacking (Layer 1)" |
| `01-scope-method.tex:124` | "(the spine, Layers 0 and 1, the public-input phase)" | "(the spine, the field instances and tables and stacking, the public-input phase)" |
| `05-phases.tex:195` | "Its Layer 9 makes the eighteen limb claims an input" | "Its Flock phase (Layer 9) makes…" |
| `05-phases.tex:225-229` | "Layer 10 runs a sumcheck…; Layer 11 then runs WHIR…; the refinement theorem of Layer 12…; the oracle interface of Layer 0" | "The blueprint's opening (Layer 10) runs…; its WHIR section (Layer 11)…; the refinement theorem of the compilation (Layer 12)…; the oracle interface of the field instances (Layer 0)" |
| `07-tcb.tex:85` | "the polynomial bridge of Layer 2" | "the polynomial bridge from Clean (Layer 2)" |
| `08-faithfulness.tex:44` (table cell) | "Layer 1 has no reader for the limb columns …; the blueprint assigns the strided reader to Layer 3 …; Layer 1's lemmas" | "Tables and stacking (Layer 1) has no reader…; to the adaptor (Layer 3)…; from its lemmas" |
| `10-auditability.tex:22` | "Layer 0's oracle interface of the stack" | "the evaluation oracle of the stack (Layer 0)" |
| `10-auditability.tex:32` | "Layer 1 has 143 public declarations" | "Tables and stacking (Layer 1) has 143 public declarations" |
| `10-auditability.tex:90` | "The executable verifier of Layer 12" | "The executable verifier (Layer 12)" |
| `11-options.tex:23-24` | "Cost: Layer 0's interface, the opening phase and Layers 11 and 12 as sketched" | "Cost: the oracle interface (Layer 0), the opening phase, and the WHIR and compilation sketches (Layers 11 and 12)" |
| `11-options.tex:46` | "Layer 9's interface replaced by the spine's slot" | "the Flock interface (Layer 9) replaced by…" |
| `11-options.tex:57` | "Cost: Layers 4 to 6 as sketched" | "Cost: the sumcheck, GKR and bus-phase sketches (Layers 4 to 6)" |
| `11-options.tex:63-64` | "as a Layer 1 lemma and a Layer 3 reader. Cost: Layers 1 to 3 as sketched" | "as a lemma of tables and stacking and a reader in the adaptor. Cost: the sketches of tables and stacking, the polynomial bridge and the adaptor (Layers 1 to 3)" |
| `11-options.tex:74` | "Layers 11 to 13 rewritten" | "the WHIR, compilation and base-theorem sketches (Layers 11 to 13) rewritten" |
| `13-drift.tex:61` | "the report's recommendations for Layer 3" | "…for the adaptor (Layer 3)" |
| `e-brief-review.tex:39` | "(it predated Layer~1 and the public-input phase)" | "(it predated tables and stacking and the public-input phase)" |
| `02-protocol-map.tex:189-203` (table cells) | column "Blueprint": "Layer 0" … "Layer 13" | allowed: an index column beside the name in the first column |

The generated fragments carry the rest (per-file line lists in 1.8; the largest:
`gen/changes.tex` 51, `gen/register.tex` 38, `gen/findings-code.tex` 30, `gen/findings-docs.tex`
24, `gen/obligations.tex` 24, `gen/transcript-opening.tex` 24, `gen/findings-bus.tex` 23,
`gen/findings-opening.tex` 19, `gen/findings-boundary.tex` 16, `gen/findings-table-pub.tex` 16,
`gen/conformance.tex` 16, `gen/findings-flock-ring.tex` 15, `gen/boundary-statements.tex` 13). A
mechanical rule serves them: on the first "Layer N" of a paragraph write "⟨name⟩ (Layer N)", later
ones "⟨name⟩"; in the register's "Short name" column write the name only.

### 1.8 Every non-allowed occurrence, per file (line numbers; token where it is not "Layer N")

From `probes/lint-report/codes-verdict.tsv`, which gives each occurrence with its surrounding text and a replacement phrase. *heading* and *violation* need the fix; *check* items are allowed when they sit in an index column or right after the name they label. The list is the script's; where 1.1 to 1.7 judge an item by hand (for example `gen/lib-clean.tex:401`, `gen/findings-boundary.tex:470`), the hand judgment governs.

- `00-summary.tex`: *violation* Layer (3): 6, 25
- `01-scope-method.tex`: *check (parenthetical)* Layer (1): 124
- `02-protocol-map.tex`: *check (cell)* Layer (14): 189, 190, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203; *check (parenthetical)* Layer (5): 165, 179, 180, 181
- `03-libraries.tex`: *heading* Layer (1): 32
- `04-catalogue.tex`: *heading* Layer (1): 19
- `05-phases.tex`: *heading* Layer (2): 195, 225; *violation* Layer (3): 226, 229; *violation* acceptance test (1): 185 acceptance test 20
- `07-tcb.tex`: *violation* Layer (1): 85
- `08-faithfulness.tex`: *heading* Layer (2): 111, 117; *check (cell)* Layer (3): 44
- `09-nonvacuity.tex`: *violation* acceptance test (1): 150 acceptance test 24; *check (parenthetical)* code (1): 168 H1
- `10-auditability.tex`: *violation* Layer (4): 22, 32, 90, 112
- `11-options.tex`: *violation* Layer (8): 23, 24, 46, 57, 64, 74; *violation* acceptance test (1): 47 acceptance test 20
- `13-drift.tex`: *violation* Layer (1): 61; *violation* acceptance test (1): 92 acceptance test 10
- `b-probes.tex`: *heading* Layer (1): 9
- `e-brief-review.tex`: *check (parenthetical)* Layer (1): 39
- `gen/analysis-opening.tex`: *violation* Layer (3): 140, 362, 684; *violation* T (1): 76 T4; *violation* acceptance test (2): 433 acceptance test 20, 453 acceptance test 23; *check (parenthetical)* T (1): 87 T1; *check (parenthetical)* acceptance test (2): 83 acceptance test 24, 301 acceptance test 11; *check (parenthetical)* code (3): 266 M2, 266 M7, 331 K1
- `gen/boundary-chain.tex`: *violation* Layer (2): 95, 163; *violation* T (3): 49 T2, 220 T3, 383 T6; *violation* acceptance test (1): 146 acceptance test 23; *violation* hole (1): 225 holes P1; *violation* code (2): 225 P5, 225 P8; *check (cell)* Layer (7): 221, 233, 355, 358, 361; *check (parenthetical)* Layer (1): 221; *check (parenthetical)* T (1): 321 T3; *check (parenthetical)* acceptance test (1): 150 acceptance test 12; *check (parenthetical)* code (1): 361 F18
- `gen/boundary-relations.tex`: *violation* Layer (4): 53, 257, 385, 389; *check (cell)* Layer (2): 308, 309; *check (parenthetical)* Layer (1): 438; *check (parenthetical)* decision (1): 281 decision 12
- `gen/boundary-statements.tex`: *heading* Layer (1): 256; *violation* Layer (12): 47, 78, 191, 192, 241, 249, 279, 286, 295, 308; *violation* T (1): 397 T4; *violation* acceptance test (1): 120 acceptance tests 19; *check (parenthetical)* Layer (2): 175, 226
- `gen/catalogue-layer1.tex`: *heading* Layer (2): 3, 5; *violation* Layer (1): 28; *check (parenthetical)* Layer (1): 404; *check (parenthetical)* acceptance test (1): 455 acceptance test 7
- `gen/catalogue-pubinput.tex`: *violation* Layer (7): 13, 31, 33, 64, 84, 94, 104
- `gen/changes.tex`: *violation* Layer (51): 10, 279, 393, 394, 429, 504, 573, 604, 613, 623, 645, 680, 702, 708, 720, 734, 754, 787, 807, 816, 818, 825, 837, 863, 868, 878, 890, 908, 941, 954, 1032, 1091, 1191, 1210, 1426, 1486, 1520, 1524, 1529, 1546, 1579, 1602, 1609, 1611, 1620, 1623, 1635, 1638, 1648, 1653; *violation* T (6): 358 T7, 503 T4, 504 T4, 692 T4, 1032 T4, 1223 T4; *violation* code (19): 224 A3, 541 G4, 541 P6, 541 P7, 546 K3, 546 P6, 553 K3, 562 K3, 564 K1, 565 K1, 565 K3, 566 I1, 566 L1, 567 I2, 568 G1, 645 M3, 1235 F3, 1241 K1, 1241 K3; *check (cell)* Layer (7): 252, 461, 557, 713, 1004, 1085, 1459; *check (parenthetical)* Layer (13): 126, 183, 297, 397, 577, 701, 835, 876, 998, 1296, 1588, 1653; *check (parenthetical)* T (1): 1050 T4; *check (parenthetical)* code (1): 599 P3
- `gen/checks-bus.tex`: *own row code* code (18): 35 B1, 42 B2, 49 B3, 59 B4, 65 B5, 73 B6, 90 B7, 99 B8, 105 B9, 112 B10, 118 B11, 125 B9, 126 B12, 134 B13, 142 B14, 151 B15, 159 B16, 165 B17; *check (parenthetical)* code (1): 175 U7
- `gen/checks-opening.tex`: *violation* Layer (1): 278; *violation* code (13): 17 B1, 17 B10, 17 B17, 207 W5, 219 W5, 275 G1, 275 M1, 275 M7, 275 W2, 275 W5, 277 G1, 277 G2, 279 M6; *own row code* code (25): 74 R1, 80 R2, 89 R3, 95 R4, 101 R5, 110 G1, 124 G2, 133 M1, 139 M2, 154 M3, 160 M4, 166 M5, 169 R4, 172 M6, 183 M7, 197 W1, 205 W2, 216 W3, 226 W4, 235 W5, 244 W6, 251 W7, 257 W8, 277 R2, 277 R4; *check (parenthetical)* code (3): 67 B6, 276 B10, 276 B3
- `gen/checks-table-pub.tex`: *violation* T (1): 84 T12
- `gen/code-index.tex`: *violation* Layer (2): 10, 159; *check (cell)* Layer (2): 52
- `gen/conformance.tex`: *heading* Layer (3): 236, 240, 291; *violation* Layer (13): 87, 89, 148, 152, 173, 203, 285, 294, 295; *violation* acceptance test (2): 79 acceptance test 24, 297 acceptance test 25; *violation* decision (1): 203 decision 15; *violation* code (1): 173 L1; *check (cell)* Layer (20): 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 81; *check (parenthetical)* Layer (2): 50, 286
- `gen/disagreements-bus.tex`: *check (parenthetical)* code (1): 44 F14
- `gen/disagreements-opening.tex`: *violation* code (5): 54 M1, 54 M7, 54 W2, 54 W5, 103 S12; *check (cell)* Layer (3): 58, 104; *check (parenthetical)* code (3): 55 B10, 55 B3, 55 G2
- `gen/docs-codes.tex`: *check (cell)* Layer (14): 30, 39, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86
- `gen/docs-contradictions.tex`: *violation* Layer (3): 69, 109, 260; *check (cell)* Layer (16): 93, 95, 125, 126, 127, 128, 129, 130, 131, 132, 160, 180, 185, 187, 285
- `gen/docs-inventory.tex`: *heading* Layer (1): 5; *violation* Layer (2): 8, 49
- `gen/docs-proposal.tex`: *violation* Layer (1): 92; *check (cell)* Layer (28): 149, 303, 307, 308, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 342, 345
- `gen/docs-texts.tex`: *violation* Layer (6): 226, 257, 367, 432, 541; *check (cell)* Layer (12): 507, 508, 509, 510, 511, 512, 513, 515, 516, 517, 518; *check (parenthetical)* Layer (12): 482, 507, 508, 513, 515, 518, 574, 590, 601, 605, 609
- `gen/docs-vocabulary.tex`: *check (cell)* Layer (1): 33; *check (parenthetical)* Layer (1): 35
- `gen/findings-boundary.tex`: *violation* Layer (16): 83, 101, 107, 114, 117, 124, 264, 283, 289, 304, 309, 330, 368, 386, 438; *violation* T (3): 464 T4, 498 T7, 510 T7; *violation* acceptance test (1): 290 acceptance test 21; *violation* decision (2): 300 decision 12, 484 decision 14; *check (parenthetical)* Layer (2): 245, 510; *check (parenthetical)* T (1): 199 T2
- `gen/findings-bus.tex`: *violation* Layer (23): 43, 50, 52, 54, 71, 89, 106, 110, 149, 160, 198, 200, 256, 260, 266, 297, 304, 333, 336, 362, 366, 382, 418; *violation* acceptance test (4): 102 acceptance test 17, 326 acceptance test 10, 329 acceptance test 10, 362 acceptance test 28; *violation* code (5): 173 B8, 173 B9, 214 F9, 324 B17, 426 F14; *check (parenthetical)* code (1): 134 G6
- `gen/findings-code.tex`: *heading* Layer (1): 232; *violation* Layer (29): 24, 169, 174, 177, 178, 194, 195, 203, 211, 240, 245, 281, 286, 290, 331, 339, 351, 370, 376, 383, 403; *violation* acceptance test (5): 63 acceptance test 24, 75 acceptance test 24, 90 acceptance test 28, 186 acceptance test 10, 363 acceptance test 25; *violation* decision (1): 201 decision 15; *violation* code (2): 139 A6, 169 F18; *check (parenthetical)* Layer (6): 24, 131, 154, 279, 325, 339; *check (parenthetical)* code (3): 211 A4, 281 G7, 398 G15
- `gen/findings-docs.tex`: *violation* Layer (24): 10, 52, 55, 64, 73, 90, 149, 198, 209, 230, 235, 237, 249, 261, 275, 285; *violation* acceptance test (4): 149 acceptance test 25, 153 acceptance test 25, 209 acceptance test 14, 209 acceptance test 5; *violation* decision (3): 189 decisions 1, 189 decisions 1, 189 decisions 6; *violation* code (1): 117 A1; *check (parenthetical)* Layer (1): 73
- `gen/findings-flock-ring.tex`: *violation* Layer (15): 33, 37, 41, 45, 49, 61, 103, 104, 124, 134, 188, 365, 370, 410; *violation* acceptance test (2): 186 acceptance test 20, 334 acceptance test 23; *violation* code (1): 365 F5; *check (parenthetical)* code (1): 370 F5
- `gen/findings-libraries.tex`: *heading* Layer (1): 6; *violation* Layer (8): 9, 27, 28, 202, 209, 236, 239, 248; *violation* code (9): 88 A2, 88 A3, 89 A2, 89 A3, 91 A2, 93 A3, 103 A5, 122 A5, 324 E6; *check (parenthetical)* code (5): 82 A2, 162 A1, 253 P3, 266 P3, 270 P3
- `gen/findings-opening.tex`: *violation* Layer (19): 25, 33, 36, 52, 53, 54, 56, 178, 181, 239, 246, 262, 281, 282, 299, 317, 351, 378; *violation* T (3): 104 T4, 107 T4, 120 T4; *violation* acceptance test (3): 222 acceptance test 23, 230 acceptance test 23, 358 acceptance test 23; *violation* code (1): 274 M2; *check (parenthetical)* Layer (1): 87; *check (parenthetical)* code (1): 22 M6
- `gen/findings-table-pub.tex`: *violation* Layer (16): 69, 116, 117, 124, 165, 210, 211, 214, 247, 248, 255, 256, 288, 320, 366, 422; *violation* acceptance test (1): 235 acceptance test 6; *check (cell)* Layer (2): 261; *check (parenthetical)* Layer (1): 321; *check (parenthetical)* T (2): 25 T12, 183 T6; *check (parenthetical)* code (2): 25 P0, 25 P4
- `gen/layer0-audit.tex`: *heading* Layer (4): 4, 60, 439, 445; *violation* Layer (4): 6, 23, 275, 441; *check (cell)* Layer (2): 479, 484; *check (parenthetical)* code (1): 488 P3
- `gen/lib-arklib-security.tex`: *violation* Layer (3): 286, 524, 682
- `gen/lib-clean.tex`: *violation* Layer (2): 344; *violation* code (1): 401 C8; *check (parenthetical)* Layer (1): 391
- `gen/lib-comppoly.tex`: *check (parenthetical)* code (1): 583 P3
- `gen/lib-lean.tex`: *violation* Layer (1): 152
- `gen/obligations.tex`: *heading* Layer (6): 345, 362, 371; *violation* Layer (18): 45, 103, 162, 175, 208, 229, 230, 240, 241, 252, 256, 280, 315, 374, 727, 738, 767, 777; *violation* T (22): 95 T4, 95 T4, 103 T4, 114 T4, 114 T5, 114 T6, 114 T7, 115 T4, 115 T8, 398 T1, 399 T1, 400 T1, 400 T4, 425 T3, 613 T4, 629 T1, 629 T4, 630 T4, 632 T1, 638 T1, 638 T8, 681 T4; *violation* acceptance test (12): 147 acceptance test 11, 196 acceptance test 24, 224 acceptance test 1, 225 acceptance test 3, 226 acceptance test 4, 241 acceptance tests 7, 263 acceptance test 10, 272 acceptance test 20, 329 acceptance test 1, 496 acceptance test 23, 669 acceptance tests 7, 675 acceptance test 20; *violation* hole (1): 371 hole I1; *violation* code (33): 126 G4, 126 G9, 143 M7, 197 G4, 204 G10, 220 G1, 220 G11, 220 G2, 220 G8, 221 G10, 226 G13, 227 G1, 227 G12, 227 G2, 228 G6, 229 G3, 231 G7, 232 G10, 233 G8, 240 G16, 307 G1, 308 A1, 335 G1, 335 G12, 335 G2, 392 G4, 477 G2, 478 G1, 479 G12, 480 G6, 672 G11, 734 G10, 734 G7; *dossier code* code (71): 114 DD1, 115 DD19, 134 LT10, 135 LT13, 136 LT3, 143 LT10, 145 DD15, 147 LT2, 153 LT4, 157 LT7, 157 LT8, 175 LT14, 175 LT6, 176 AK5, 188 CS5, 189 AK2, 196 CS4, 197 CS1, 198 TP13, 203 CS8, 204 CS2, 204 TP1, 208 CS9, 209 AK1, 220 GB1, 220 GB11, 220 GB2, 228 GB6, 228 TP5, 229 GB3, 231 GB7, 232 GB10, 233 GB8, 240 TP2, 240 TP4, 240 TP6, 245 CS2, 245 TP1, 252 PI2, 252 TP3, 254 PI1, 271 FR1, 271 FR7, 271 TP7, 272 AK2, 272 FR12, 272 FR4, 273 FR5, 278 FR6, 279 FR9, 280 CS8, 280 FR3, 283 FR2, 284 FR14, 307 GB1, 313 TP4, 329 AK6, 368 LO4, 400 DD19, 439 LT13, 567 FR13, 567 LT2, 568 LT3, 569 LT1, 576 LT14, 632 DD19, 638 LT11, 679 DD15, 734 CS1, 734 TP1, 734 TP4; *check (cell)* Layer (4): 632, 669, 674, 712; *check (parenthetical)* Layer (20): 45, 80, 87, 118, 127, 209, 217, 230, 237, 249, 266, 280, 287, 292, 304, 318, 324, 332, 379, 758; *check (parenthetical)* T (4): 45 T4, 111 T4, 307 T6, 637 T6; *check (parenthetical)* hole (6): 224 hole G4, 304 holes G1, 318 hole G3, 324 hole G4, 332 holes G5, 379 hole I2; *check (parenthetical)* code (31): 80 P1, 140 M1, 140 M7, 142 M6, 143 M7, 160 W2, 160 W2, 161 W4, 161 W4, 163 G1, 163 W3, 193 A2, 225 B13, 225 B13, 226 B12, 226 B12, 229 A4, 279 A9, 304 G2, 308 A1, 309 A1, 332 G6, 337 G17, 433 P8, 665 G2, 667 G14, 668 G3, 668 G6, 672 P2, 673 P4, 676 P8
- `gen/probes-code.tex`: *heading* Layer (1): 2205; *violation* Layer (9): 188, 204, 280, 2196, 2511, 2693, 3008, 3085, 3151; *violation* T (2): 2134 T4, 2168 T4; *violation* acceptance test (3): 52 acceptance test 27, 251 acceptance test 24, 2170 acceptance test 10; *violation* code (2): 13 P3, 303 P1; *check (parenthetical)* Layer (6): 204, 2009, 2125, 3151; *check (parenthetical)* code (1): 3150 G7
- `gen/probes-rerun.tex`: *check (cell)* Layer (2): 23, 24
- `gen/register.tex`: *violation* Layer (38): 163, 165, 177, 180, 183, 185, 187, 188, 190, 197, 208, 210, 218, 222, 250, 253, 255, 263, 283, 285, 287, 288, 292, 303, 305, 308, 310, 313; *violation* T (2): 97 T4, 780 T4; *violation* acceptance test (7): 148 acceptance test 20, 175 acceptance test 17, 368 acceptance test 24, 384 acceptance test 10, 392 acceptance test 23, 606 acceptance tests 1, 1040 acceptance test 10; *violation* code (31): 55 G1, 59 G2, 61 G3, 63 G16, 107 G4, 113 G11, 117 G5, 240 A5, 278 M3, 320 F9, 325 G1, 325 I2, 325 P5, 362 G10, 370 G6, 376 G7, 378 G8, 380 G12, 398 G9, 460 G14, 466 G13, 490 G15, 494 G17, 604 F17, 640 P1, 644 P2, 646 P3a, 648 P1, 648 P3b, 768 M3, 1014 G1; *check (cell)* Layer (30): 61, 65, 77, 79, 105, 107, 111, 398, 432, 434, 436, 438, 440, 444, 540, 542, 544, 546, 608, 692, 698, 700, 702, 746, 804, 840, 906, 942, 997; *check (parenthetical)* Layer (8): 63, 67, 69, 133, 608, 1025, 1042, 1045; *check (parenthetical)* T (1): 372 T4; *check (parenthetical)* acceptance test (1): 1041 acceptance test 23; *check (parenthetical)* decision (1): 624 decision 12; *check (parenthetical)* code (9): 65 F18, 165 G1, 175 G2, 180 G3, 295 G4, 320 G5, 325 I1, 325 K1, 325 L1
- `gen/statements-spine.tex`: *violation* Layer (2): 89, 142; *violation* T (3): 129 T4, 142 T4, 142 T4; *violation* acceptance test (1): 115 acceptance test 24; *check (cell)* Layer (1): 43; *check (parenthetical)* Layer (1): 110
- `gen/surface.tex`: *heading* Layer (1): 245; *violation* Layer (6): 5, 31, 278, 280; *violation* T (1): 228 T4; *violation* acceptance test (3): 228 acceptance test 24, 287 acceptance test 14, 289 acceptance test 7; *check (cell)* Layer (4): 25, 26, 27, 28
- `gen/transcript-bus.tex`: *own row code* code (17): 57 S0, 63 S1, 68 S2, 72 S3, 76 S4, 80 S5, 84 S6, 88 C1, 93 C2, 118 U0, 122 U1, 126 U2, 130 U3, 134 U4, 138 U5, 142 U6, 150 U7; *check (parenthetical)* code (3): 76 B4, 76 B9, 349 U7
- `gen/transcript-opening.tex`: *heading* Layer (4): 612, 616, 861, 865; *violation* Layer (20): 198, 202, 204, 207, 221, 223, 237, 262, 285, 297, 306, 311, 314, 318, 323, 339, 635, 645, 660, 747; *violation* acceptance test (1): 854 acceptance test 8; *violation* code (1): 732 F13; *check (parenthetical)* code (3): 307 G3, 784 M2, 857 B15
- `gen/transcript-table-pub.tex`: *own row code* code (5): 203 P0, 209 P1, 213 P2, 217 P3, 223 P4; *own row code* T (13): 53 T0, 59 T1, 63 T2, 72 T3, 77 T4, 81 T5, 90 T6, 95 T7, 99 T8, 105 T9, 112 T10, 118 T11, 123 T12; *check (parenthetical)* code (2): 141 P1, 141 P2

## 2. Vocabulary

Scan: `probes/lint-report/vocab.py` over every source outside verbatim blocks (`vocab.tsv`); each
hit read in context.

**2.1 "roadmap" meaning the blueprint (11; minor).** `gen/changes.tex:140` ("not given by this
roadmap's per-statement theorems"), `:200` ("every interface and theorem of the roadmap is stated
in the `With` form"), `:1436` ("Rewrite without the roadmap"); `gen/findings-boundary.tex:535`
("the per-statement theorems of this roadmap"); `gen/findings-libraries.tex:35` ("Every interface
and theorem of this roadmap"); `gen/obligations.tex:434,435,437` ("O (this roadmap)");
`gen/findings-docs.tex:249` (finding title "…comments cite the roadmap…"), `:255`;
`gen/register.tex:540` (row R130's short name). Fix: "the blueprint". Allowed: the definition
`01-scope-method.tex:75`; "the Flock roadmap" and "the leanISA roadmap" (for example
`11-options.tex:139-143`, `gen/changes.tex:838`); "no roadmap has started"
(`gen/findings-flock-ring.tex:408`, `gen/register.tex:396`); "one per roadmap", "the other
roadmaps" (`gen/docs-proposal.tex:47,64,156`); quotations (`gen/docs-codes.tex:121`,
`gen/docs-contradictions.tex:35,190,315`, `gen/docs-texts.tex:398,553,564`,
`gen/findings-docs.tex:252`); ArkLib's file `05-roadmap.md`.

**2.2 "dashboard" (no violation).** 11 occurrences, every one inside a quotation of the documents
(`gen/changes.tex:401`, `gen/docs-contradictions.tex:27,36,69,233,240`, `gen/docs-texts.tex:380`,
`gen/findings-docs.tex:43,171,261`) or in the vocabulary inventory (`gen/docs-vocabulary.tex:23`).

**2.3 "unit of work" / "slice" meaning a hole (minor; one inconsistency inside chapter 12).**
"slice" never means a hole: every use is Lean's `slice`, a slice of a column or the 64 slice
claims of ring switching, or a quotation ("the #907 slices", "a slice of one"). "unit of work"
does: `gen/docs-proposal.tex:26,61,122 (twice),168` and the "Kind" column of the drafted index
(`:303-330`, 28 rows "unit of work", plus "blueprint, 'The units of work'"), and
`gen/obligations.tex:734` ("the plan's unit of work"). Chapter 12's own vocabulary
(`gen/docs-vocabulary.tex:24`) keeps "hole" and then excuses the proposal ("In
sec:docs-proposal-owners and sec:docs-proposal-codes below, 'unit of work' and 'unit' mean a
hole"). Fix: "hole" throughout the report's own voice, the proposed blueprint section "The holes",
and delete the excuse in `docs-vocabulary.tex:24`. The report's definition
(`01-scope-method.tex:89`, "hole & a unit of work the spine leaves open") is right.

**2.4 "PIOP" (no violation).** The acronym never appears as a word: only in identifiers
(`leanVmPiop`, `piop_*`, labels `*-piop-error*`) and in the vocabulary inventory
(`gen/docs-vocabulary.tex:34`). The report says "oracle protocol" and defines it once
(`01-scope-method.tex:79-81`, with "polynomial interactive oracle proof" as the literature's
term).

**2.5 "pin" for something that is not a revision recorded in `upstreams.json` (minor).**
(a) *As a verb, "to fix" or "to tie"* (23): `07-tcb.tex:78` ("Two theorems are meant to pin that
data to the arithmetization" → "tie"); `09-nonvacuity.tex:80` ("They pin the phases to leanVM's
by nothing" → "They tie"); `gen/changes.tex:393`; `gen/conformance.tex:42,218`;
`gen/findings-code.tex:200` (finding title "PublicLine.sent is pinned by prose only" → "is fixed
by prose only"), `:206`, `:278` and `:288` (title and change box "…is pinned by no statement…"),
`:326`; `gen/findings-table-pub.tex:416` (finding title "The spine's slot does not pin the
protocol" → "does not tie the phases to leanVM's protocol"); `gen/lib-comppoly.tex:556` ("pins the
new meaning" → "fixes"); `gen/obligations.tex:198,263,359,767`; `gen/probes-code.tex:184,2023`;
`gen/register.tex:386,432,482,1048` (short names of R55, R78, R101); `gen/transcript-opening.tex:634`
("must be pinned as transcribed content" → "recorded as"). The quotation
`gen/analysis-opening.tex:392` ("pin the shape") and `gen/docs-contradictions.tex:180` stay. The
labels `f:*-pinned*` need not change.
(b) *VCVio and Mathlib.* At `b435631`, `upstreams.json` records Lean, leanVM, CompPoly, Clean and
ArkLib only (`git show b435631:upstreams.json`); VCVio (`f9dc47d9`) and Mathlib are recorded in
`lake-manifest.json`; `upstreams.json` gains Mathlib, VCVio and PolyFun at `144c5aa`. The report's
definition (`01-scope-method.tex:101`: "pin & the revision of a dependency recorded in
upstreams.json") therefore does not cover its own use in `tab:revisions` (`:9-10`, `:23`, `:26`),
`02-protocol-map.tex:220-221` or `e-brief-review.tex:35`. Fix the definition: "the revision of a
dependency leanerVM builds against, as recorded in `upstreams.json` (for VCVio and Mathlib at
`b435631`, in `lake-manifest.json`; `upstreams.json` records them from `144c5aa`)".

**2.6 "Category A/B" without the words that explain it (15; minor).** `gen/changes.tex:353`
("none given (Category B wording)"), `:429` ("for leanISA the instance is Category B"), `:912`
("recorded as Category B"), `:946` ("(Category B)"); `gen/findings-code.tex:112`;
`gen/findings-table-pub.tex:143` ("The schedule is Category B"); `gen/obligations.tex:75,124,271,443,444,675`;
`gen/register.tex:404,408` (in the severity column: "minor (Category B)");
`gen/statements-spine.tex:110`. Fix: "transcribed data (the blueprint's Category B)"; in the
register's severity column drop it. Explained, allowed: `e-brief-review.tex:28`,
`gen/findings-flock-ring.tex:98,459`, `gen/findings-opening.tex:297,320,353`,
`gen/transcript-opening.tex:634,751` (all "transcribed content (the blueprint's Category B)"), and
the inventories (`gen/code-index.tex:251-252`, `gen/docs-codes.tex:45,144`,
`gen/docs-proposal.tex:153`, `gen/docs-vocabulary.tex:41`).

**2.7 One object, several names (minor).**
- The stack's oracle interface (`evalOracle`, `LeanerVM/Protocol/Field.lean:102` at `b435631`):
  "the evaluation oracle" (18), "the evaluation interface" (8: `gen/changes.tex:126,297,876`,
  `gen/findings-opening.tex:33`, `gen/register.tex:77`, `gen/transcript-opening.tex:223`,
  `gen/obligations.tex:664,745`), "the oracle interface of the stack" (5: `07-tcb.tex:27`,
  `10-auditability.tex:22`, `gen/changes.tex:1485`, `gen/layer0-audit.tex:7,294`), "the oracle
  interface of Layer 0" (`05-phases.tex:229`). And its proposed replacement: "the inner-product
  oracle" (10) and "the inner-product interface" (9). Fix: "the evaluation oracle of the stack
  (`evalOracle`)" once, "the evaluation oracle" after; "the inner-product oracle".
- The table sumcheck: "table sumcheck" (128), "table sumcheck phase" (18) and "table phase" (21:
  `08-faithfulness.tex:36`, `gen/changes.tex:1509,1513`, `gen/findings-bus.tex:313,433,437`,
  `gen/findings-code.tex:87`, `gen/surface.tex:243`, `gen/statements-spine.tex:77,80,81`,
  `gen/conformance.tex:74,109`, `gen/obligations.tex:204`, `gen/register.tex:47,142,143,1012`).
  Fix: "the table sumcheck". "zerocheck" is consistent: it always names the constraints' zero
  claim or Flock's zerocheck, never the phase (no "zerocheck phase" anywhere).
- The Flock phase: "Flock phase" (58) and "BLAKE2s validity" (12, including the headings
  `05-phases.tex:164`, `08-faithfulness.tex:85`, the 13.6 heading and the node of `fig:phases`,
  `02-protocol-map.tex:134`). The brief's word is "Flock". Fix: introduce "the Flock phase
  (BLAKE2s validity)" once in 2.2 and use "the Flock phase" in headings.
- "the spec" once: `gen/statements-spine.tex:40` ("the spec's Theorem 5.1") → "the
  specification's". ("the tex" in `e-brief-review.tex:11,24` names the source file; fine.)

**2.8 "the Rust" standing for the deployed verifier (16; minor).** `08-faithfulness.tex:18`
("a place where the specification, the Rust and the Python do not say the same thing" → "the
Rust verifier and the Python verifier"); `e-brief-review.tex:20` ("the Rust and the Python
verifier" → "the Rust verifier and the Python verifier"); `gen/boundary-chain.tex:271` ("the Rust
rejects"); `gen/conformance.tex:233` ("a verify written from the Rust"); `gen/findings-bus.tex:185`,
`:330` ("the Rust's rejections"), `:332`; `gen/findings-opening.tex:388` ("the Rust's rejection
set"); `gen/findings-table-pub.tex:159` ("proofs the Rust accepts"); `gen/obligations.tex:440`;
`gen/disagreements-opening.tex:68` and `gen/checks-opening.tex:153` ("larger than the Rust's");
`gen/checks-table-pub.tex:131` ("the Rust's rejection"); the captions of
`gen/disagreements-bus.tex:25`, `gen/disagreements-opening.tex:26`,
`gen/disagreements-table-pub.tex:21` ("between the specification, the Rust and the Python").
Fix: "the Rust verifier". Most of the other uses of "the Rust" (163 hits in all) mean the Rust code ("the Rust's
parameters", `05-phases.tex:190,264`; "transcribed from the Rust", `11-options.tex:142`; "those of
the Rust and of the specification", `02-protocol-map.tex:18`); "the Rust code" would be clearer
but they are not the fault the rule targets.

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
appendix A, row ...**" and drop "BY THE ORCHESTRATOR". The 19 markers of chapter 12
(`docs-proposal.tex`, `findings-docs.tex`) have no such announcement and must be filled.

**`[fragment pending]` fallbacks (none printed).** Every `\InputIfFileExists` target exists (all
55 checked; `pdftotext` finds no "pending]", "being typeset" or "inserted here when" in the PDF).
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

### 4.3 Doubled and mis-levelled headings (16 empty or duplicate sections; 24 sections one level too high)

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
   sections and 199 subsections, ten pages (physical 4-13), 16 of the section entries empty or
   duplicate (section 4.3). Fix: `\setcounter{tocdepth}{1}` (about 160 entries, four pages), after the doubled
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

## 8. Other editorial points found on the way (notes)

- `00-summary.tex:44` says the twelve surface proposals are "none changing a theorem's meaning"
  and `10-auditability.tex:54-55` says "None changes the meaning of a master theorem", but item 1
  of the same list (`10-auditability.tex:59-63`) "Changes the statement of the knowledge-soundness
  theorem, for the better: it then says something". Reword to "none weakens a theorem; the first
  gives the knowledge-soundness theorem content".
- The six `gen/index-*.tex` files are input by nothing (the chapter files input the fragments
  directly); they hold generator notes and are harmless, but a reader of the sources may take
  them for the inclusion order.
- `08-faithfulness.tex:67-77` ("The review's verdict on the GKR round error") is the only
  orchestrator paragraph after a fragment in chapter 8; with the heading fix of 4.3 it will sit at
  the end of 8.4 as intended.

