# read-report: adversarial read of the assembled report

Object: `tex/report.pdf` (527 pages, commit `b6db3be`) built from `tex/main.tex`; the
orchestrator's chapters (00, 01, 02, 05, 07, 09, 10, 11, 13, e, and the wrappers 03, 04, 06, 08,
12, a, b, c, d, f), the fragments under `tex/sections/gen/`, read against the dossiers, the
register (`dossiers/register.md`), the hostile re-derivation (`verify-majors.md`), the four
citation checks (`verify-gt-*.md`), the probe re-run (`probes-rerun.md`), `NOTES.md` and
`BRIEF.md`. Read as the intended audience would (cryptographers and zkVM engineers who may not
read Lean; formal-verification experts who may not know zkVMs). Nothing was edited, no Lean or
build was run; `pdftotext` was used on the PDF for the summary and the table of contents.

Line numbers below are those of the `.tex` files at `b6db3be`.

## Summary

**Verdict: not fit to hand to the owner as it stands; fit after a few hours of editing.** No
technical finding of the report is wrong or overstated beyond the two weakenings the report
itself records, and the chapters are consistent with the dossiers on every number I could
check (the pool of 113 claims, the public-input equation, the pins, what is built, the GKR
error, the register's 138/115/58, the surface numbers, the build jobs). What blocks delivery is
of another kind: (1) twenty-eight `[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: …]`
markers remain in the reader's copy (chapter 12 and appendix D), every one of which the report
now knows how to fill; (2) the report's own tables label checks and transcript steps with the
very code families whose collisions it indicts (`R1`–`R5` beside the register's `R1`–`R140`;
`G1`, `G2`, `P1`–`P4`, `C1`, `S`, `T1`–`T12`); (3) one corrected fact is still stated
uncorrected in an orchestrator's chapter (the order of WHIR's introductory polynomials, chapter
5) and the two weakened findings and one corrected number stand in their strong form in the
register and the obligations tree with no note; (4) the report's own account of its method
overstates in five places (all majors "re-derived"; "every probe re-run"; "about 1,400
citations; a dozen wrong … no finding weakened"; "twelve dossiers"; "twelve proposals, none
changing a theorem's meaning"). The vocabulary rule is met in the orchestrator's chapters (one
bare code in 191 lines of chapter 9) and mostly in the fragments. For the audience, a dozen
cryptographic terms (`eq`, sumcheck, zerocheck, lincheck, R1CS, list decoding, grinding, …) are
used in chapters 2 and 5 and defined nowhere.

Counts: **must fix 8; should fix 14; editorial 14.**

The three things to change first: fill or reword the twenty-eight markers (each is assigned a
finding below); rename the table label families and add one paragraph to the register on what
was weakened or corrected after it was assembled; correct the method claims of chapter 1 and the
summary (re-derivation, citations, probes, dossiers, proposals, matters to report) and chapter
5's WHIR ordering.

## Must fix before delivery

### M1. Twenty-eight orchestrator markers remain in the reader's copy

`gen/findings-docs.tex`, `gen/docs-texts.tex` and `gen/docs-proposal.tex` (chapter 12 §5–§6 and
appendix D) still carry the text `[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: …]` in
bold. Appendix D's wrapper (`d-tracker-drafts.tex:6-8`) says such places "are marked in bold"
and that appendix A lists the changes, but the marker's wording is an instruction to the
orchestrator and, for the fourteen hole rows, the cell is otherwise empty. Each marker and what
the report now knows to fill it:

| Marker | Fill from |
|---|---|
| `findings-docs.tex:36` (the alternative for the program condition) | R27; the report's choice is the hypothesis `WellFormedBytecode` on both base theorems (ch 07 table row; ch 11 rec 8); the alternative (`verify` decides it) stays as the [decision] row of appendix A |
| `findings-docs.tex:67` (schedules, errors, relations per phase; the opening against §8.5) | the transcript tables of ch 08 (`transcript-*.tex`); the errors of ch 05; R18 (the opening is "λ, then one weighted query"; §8.5 settled) |
| `findings-docs.tex:110` (which ledger rows still hold at ArkLib `7653a901`) | ch 03 §lib-pins and R34: no relevant admission lifted; all rows stand; the ring-switching row is wrong for another reason (R59) |
| `findings-docs.tex:237` (whether Layer 11 builds on VCVio's Merkle trees) | R77: the library exists at `f9dc47d9`; the fit with leanVM's trees is unverified; say the decision is deferred |
| `docs-texts.tex:226` (hole table: generic components, statement types, opening schedule, Merkle, program hypothesis) | R36 (Layers 4–5 as `Component.Def`), R2 (`BusOut` in `BusVerify`'s shape), R14/R16 (the spine's Flock slot; `FlockRegion`), R18, R77 (unverified), R27 |
| `docs-texts.tex:257` (whether the sketches are restated in the same pull request) | R36; keep as a conditional note, reworded for the reader |
| `docs-texts.tex:367` (axioms at `144c5aa`; the ArkLib admission; numerals) | probes-rerun 7.4 (`AxiomsLeanerVM` byte-identical at `144c5aa`); verify-majors §6 and R34 (still admitted at `7653a901`, the port stays); R127 (the test comment at `tests/…/Field.lean:25-26, 37-38`) |
| `docs-texts.tex:392` (upstream watch and ledger rows the upgrade settled) | R84 (pins), R125 (CompPoly #331: retirement condition met), R73 (Clean balance unchanged at `42fe4b26`), BRIEF §8 (Clean `42fe4b26` is Clean PR #474 over its `main`); whether Clean #446 is in it: unverified, say so |
| `docs-texts.tex:482` (holes added, split, renamed, removed) | R18 (the opening hole loses its sumcheck), R60 (split the Flock hole), R12 (the deployed public-input phase), R137 with the exact assignment already written at `changes.tex:561-568` |
| `docs-texts.tex:524` (statement types; base-theorem hypotheses) | R2, R14, R18; R27, R28, R29 |
| `docs-texts.tex:571` (issue 23: Clean #446 in the new pin; eager `Fintype` retired) | R125 (retired); Clean #446: unverified |
| `docs-texts.tex:612` (do pull requests 39 and 43 fit the fixed statement types) | R2 (#39's fingerprint polynomial fits `BusOut` with forms per side and table) and R18 (#43's power batching is the opening's `λ` batching, kept); or mark as a [decision] |
| `docs-proposal.tex:313-330` (fourteen hole rows, "one sentence" each) | sumcheck G1/G2: R53, R36; GKR G5/G6: R7, R9, R10; bus P1/P2: R2, R43, R47, R50, R51; table P3/P4: R2, R11, R53; opening P7/P8: R18, R19; WHIR K1: R18, R19, R24; Merkle K2: R63, R66, R77; compiled verifier K3: R21, R6, R61, R25, R138; base theorems K4: R27, R28, R29 |
| `docs-proposal.tex:381` (rows for findings against the sources) | R57, R105–R109, R111, R112, R116–R118, R133 |

Fix: fill each cell from the finding named, or replace the marker by "[to be completed from
finding R…]" so that no instruction to the orchestrator reaches the reader.

### M2. The report's own labels collide with the codes it indexes and with its register

The check-by-check tables (chapter 13) and the transcript tables (chapter 8) label their rows
with letter–number codes: `checks-bus.tex` B1–B17; `checks-opening.tex` R1–R5, G1–G2, M1–M7,
W1–W8; `transcript-bus.tex` S0–S6, C1–C2, U0–U7; `transcript-table-pub.tex` T0–T12, P0–P4. They
are then cited bare from prose: `checks-opening.tex:275-277` ("M1 to M7, W2 to W5 … G1 …
(R2), full consumption (R4), grinding (G1, G2)"), `obligations.tex:163` ("check G1 for the
nonce, W3"), `:226` ("check B12"), `findings-bus.tex:173, 323-324`,
`disagreements-opening.tex:55`, `findings-table-pub.tex:25`. Collisions: `R1`–`R5` with the
register's `R1`–`R5` (appendix F, cited throughout); `G1`, `G2` with the blueprint's holes G1,
G2 (the sumcheck; `docs-proposal.tex:313-314` "formerly G1"); `P1`–`P4` with holes P1–P4 (the
bus and table phases); `C1` with hole C1 (five meanings already, R85); `S` with hole S (the
spine); `T1`–`T8` with the target theorems T1–T8 (`boundary-chain.tex:49-51`). Chapter 12
recommends names over codes and one index; the report reproduces the defect it reports.

Fix: prefix every family with its table (for example "bus check 12", "opening format check
4", "table-sumcheck step 3"), or rename the colliding families (R → Fmt, G → Grind, T/P steps
→ words) and say in chapter 1 §vocabulary that the report's own R-numbers are its register
index and that table labels are local to their table.

### M3. Chapter 5 states the WHIR ordering the citation check corrected

`05-phases.tex:220-223`: "Four details of the deployed schedule are not in the specification's
Protocol B.6: the per-claim introductory polynomials before each level's batching challenge,
…". `verify-gt-opening.md` rows I44 and B20: only the out-of-domain claim's introductory
polynomial precedes `λ_i`; the query batch's follows `λ_i` and depends on it (`whir.rs:1373`
then `1405-1406`; `py:1044` then `1057`). The fragment `findings-opening.tex:303-306` carries the
correction; chapter 5 does not, and chapter 8's wrapper (`:8-11`) promises that corrections are
marked in place.

Fix: "the introductory polynomial of the out-of-domain claim before each level's batching
challenge and that of the query batch after it".

### M4. Chapter 1 claims every major finding was re-derived

`01-scope-method.tex:135-136`: "Findings of severity major and above were re-derived by a
second, independent sub-agent before they entered this report." `verify-majors.md` attacked
eleven findings (its table); the opening's eight majors (R18–R26), the composition over the
sizes (R6), the framework (R34), the documentation majors (R36, R37) and the obligations' two
(R137, R138) were not re-derived; chapter 8 §2 says so ("eleven of the major findings, those
not concerning the opening").

Fix: "Eleven of the major findings, those on the spine, the bus, the table sumcheck, the public
input, Flock, the adaptor and the status, were re-derived …; the opening's were checked citation
by citation and by a second reading of the transcript (§8.2, §8.6)."

### M5. The summary says no proposal changes a theorem's meaning; chapter 10 says two do

`00-summary.tex:44-45`: "twelve proposals, none changing a theorem's meaning". `10-auditability.tex:59-63`
item 1: "Changes the statement of the knowledge-soundness theorem, for the better: it then
says something"; item 2: "Changes `Seam.bus` and the two phases around it"; the chapter's own
intro (`:54-56`) says "None changes the meaning of a master theorem; the first two are also
faithfulness repairs", which contradicts item 1.

Fix: "twelve proposals, of which the first two change statements (they are faithfulness
repairs) and the other ten change no statement's meaning".

### M6. "Three matters are to be reported to leanVM" against the appendix's eight

`00-summary.tex:80-83` names three. Appendix A's intro (`gen/changes.tex:22-25`) lists eight
rows "to be reported to leanVM or recorded in `docs/leanvm-target.md`" (R105, R107–R109, R112,
R116–R118), and the register adds R12 (the §8.2 ambiguity), R111 (the Flock prover), R57 (the
Flock constants), R106, R133. Chapter 11 rec 5 reports the Flock prover, rec 4 the §8.2
ambiguity; nowhere is the list given whole.

Fix: give the list once (a short table in chapter 11 or appendix A) and have the summary say
"a dozen matters, listed in …".

### M7. The summary's account of the method overstates in four numbers

`00-summary.tex:13-20`:
- "Twelve dossiers": the register processed thirteen (`register.md:9`, obligations included),
  and the 138 findings quoted in the same sentence include the obligations' four rows.
- "about 1,400 citations; a dozen wrong theorem or line numbers, no finding weakened": the four
  checks report 301 + 314 rows (≈400 references) + ≈381 + 277 rows = 1,273 rows (≈1,360
  references); not OK: 13 wrong lines, 3 misquotations (abbreviations), 33 claims not supported
  as cited (theorem numbers, overstatements, and for the opening an ordering, the Merkle-leaf
  model and an L_0 range), 4 could not be checked. No finding was reversed; several were
  corrected in wording.
- "forty-odd Lean and Python probes, re-run at the new pins": appendix B documents about fifty
  probes (fifty-seven headings, some not probes); `probes-rerun.md` re-ran 22 distinct probes (27 runs, five of them controls), and two
  could not be run because they were never written. Chapter e says twice (`:42-43`, `:68-69`)
  "every probe was re-run at the new pins": false; the probes of gt-bus (Python), boundary
  (`KnownColumn`, `PolyBridge`: re-run by that dossier itself), gt-opening
  (`InnerProductOracle`, `FiatShamirChain`: at both pins per its dossier), `Transport`,
  `DefInstance`, `Shapes`, `P1Axioms`, `P3cExtractor`, `P6Surface`, `ExtractorsExpectedFailure`,
  `CleanBalance`, `NumeralHazard` were not in the re-run.

Fix: "thirteen dossiers"; "about 1,300 citations; thirteen wrong line numbers, three abbreviated
quotations and thirty-three claims corrected as cited, no finding reversed"; "twenty-two of the
review's probes re-run at the new pins, all agreeing"; chapter e: "the probes whose numerals or
notation the upgrade touched, and the controls, were re-run".

### M8. The register and the obligations tree keep the strong form of what was weakened or corrected

Appendix F reproduces `register.md` as assembled before `verify-majors.md` and
`verify-gt-opening.md`: `gen/register.tex:55, 162` R7 "the wrong degree, the wrong error and no
definition" (the error is loose, not wrong: verify-majors §5; the summary and ch 08 say so);
`:111, 302` R35 "exists nowhere and is assigned to no layer" (overstated: verify-majors §10);
`:243` R23 "L_0 ≤ 110 to 396 at level 0" (110 to 648 over the 56 sizes: verify-gt-opening G10,
F19, F23; `analysis-opening.tex:597-600` has the correction); R28's proposed change "RO H for
the compression" (see S1). `gen/obligations.tex:358` node 2.5.6.3: "exists nowhere, assigned to
no layer". Neither `f-register.tex` nor `register.tex`'s intro mentions the re-derivation
(`grep verify-majors` finds nothing).

Fix: one paragraph in the register's intro: "The register was assembled before the
re-derivation of §8.2 and the opening's citation check; rows R7, R23, R28 and R35 are to be read
with the corrections recorded there", and a footnote at node 2.5.6.3.

## Should fix

### S1. The random oracle "standing for the compression" does not model the Merkle leaves

`11-options.tex:65-67` (rec 8): "An adversary with a query budget against a random oracle
standing for the compression". `verify-gt-opening.md` E9: nodes are one 64-byte BLAKE2s-256
(one compression); leaves are BLAKE2s-256 of 512 or 384 bytes (six to eight chained
compressions), so a random oracle for the single compression does not model the leaf hash;
`analysis-opening.tex:95` carries this ("the one compression does not hash the leaves").
Fix: "against a random oracle for the hash: the one compression for the chain, the grinding and
the Merkle nodes, and the iterated construction (or a second oracle) for the leaves".

### S2. Chapter e's account of which model ran which task is wrong for two dossiers

`e-brief-review.tex:51-55`: "the code audits, the boundary, the libraries' adequacy … ran on
the review's own model; … the literature survey ran on Opus". `NOTES.md:87-91, 203` record
`code-layer1` and `lib-others` as started fresh on Opus after the restart. Fix the sentence.

### S3. "The rule 'no sub-agents' was added" is not in the record

`e-brief-review.tex:74-75`. `BRIEF.md` §2 (line 55) permits sub-agents bound by the same rules;
`NOTES.md` records no forked helpers, no stops and no such rule. Cite where it was added
(the resume messages, if so) or drop the bullet.

### S4. "Fourteen load-bearing declarations not listed" is the spine's count alone

`07-tcb.tex:123-124`. Fourteen is `code-spine.md:1119`'s count for the spine; R91 merges three
dossiers: 198 of 333 public declarations unlisted (docs-debt), with load-bearing ones also in
Layer 1 (`idxColumnEval`, `bytecodeColumnEval`, `evalMle_padHigh`, `Blocks.*`) and the
public-input phase (`check`, `pooled`). Fix: "fourteen in the spine alone, more in Layer 1 and
the public-input phase (R91)".

### S5. The late public-input mutations are misdescribed in chapter 9, and chapter 13's probe citation needs a word

`09-nonvacuity.tex:186-191`: "The mutation probes … that were written after the toolchain
moved (the deployed check with the prover's values pooled, the wrong point, the wrong check …,
the extra check)". Per `probes-rerun.md` 1.8 and `code-pubinput.md` C.12–C.13, mutations 4b and
6 were never written (paper only); 7a and 8 were written and run at the new pins only, where
`not_complete` is proved and, contrary to C.10/C.11's prediction, `rbr` does not compile.
`13-drift.tex:104-105` cites `Probe7a` for "a wrong check breaks completeness for every prover":
supported by `not_complete`; say so, and record that the predicted `rbr` did not compile.

### S6. Chapter 2's Flock schedule omits the first challenges

`02-protocol-map.tex:97-104` and the figure node (`:134-135`): "64 values, one challenge, 8 + k
rounds …". `gt-flock-ring.md:126, 143`: `k_batch + 1` sampled equality coordinates are drawn
before any Flock message, and the lincheck opens with its own challenge `α_lc`; the stream is
`162 + 2·k_batch` scalars. Fix: "(k + 1 equality coordinates; 64 values; one challenge; 8 + k
rounds of two coefficients; two values; a lincheck challenge; 8 rounds; 64 values)".

### S7. Cryptographic terms used in the orchestrator's chapters and defined nowhere

The wrapper of chapter 3 promises to introduce "each object before anything is built on it",
but its `define` environments are Lean objects only. Used without a definition anywhere in the
report: the equality polynomial `eq(r, ·)` (`02:28, 02:59, 05:32`; only a code comment in
`lib-comppoly.tex:19` mentions the "Lagrange (equality) basis"); the sumcheck as a protocol
(`02:65`; chapter 3 defines ArkLib's `SumcheckDomain`, not the protocol); zerocheck (`05:47`);
lincheck (`05:173`); the univariate skip (`02:100`, half explained at `05:171-172`); R1CS
(`05:167`); list decoding, the Johnson bound and mutual correlated agreement (`05:246, 05:261`,
`07:46-48`); grinding as proof of work (`05:217`; `13:127` gives the gloss late); the
straight-line extractor (`11:66`); the novel polynomial basis (`02:110`). Fix: a half-page of
terms after §2.1 (one sentence each), or a glossary appendix, and a pointer from chapter 3's
wrapper.

### S8. Write-up items of the brief served thinly

(1a) The Layer 1 catalogue has no "depends on" field (`catalogue-layer1.tex`: none; the spine
has 90, the public-input phase 30). (2b) "Where does an auditor need to start" is answered only
by chapter 10 item 12 (read the existential theorem first); no reading order per component.
(3b) The acceptance tests are not checked systematically: tests 5, 6, 7, 10, 13, 14, 15, 17,
18, 20, 23, 24–28 appear in scattered places (`conformance.tex` E.3 and F.2, the findings), with
no table of all thirty saying whether each names a witness that exists and rejects what it
says; docs-debt checked only that the thirty references point at the intended test. (3c) The
public-input phase has no surface numbers (`10:35`). (2c) The summary gives no one-line result
of the trusted-base accounting (chapter 7's "none of leanerVM's theorems depends on an admitted
theorem today; the planned chain does, on four, and on one heuristic"). Fix: add the field, a
reading-order paragraph in chapter 7 or 10, an acceptance-test table (thirty rows) in chapter 9,
the phase's numbers, and one sentence in the summary.

### S9. "Corrections marked in place" holds for the fragments, not for the chapters

`08-faithfulness.tex:8-11`. Twelve fragments carry "the citation check corrected …"; chapter 5
(M3) and the register (M8) do not. Fix with M3 and M8, and reword to "marked in place in the
tables and the findings".

### S10. "The pins moved to what the review had examined as upstream" is true of ArkLib only

`00-summary.tex:10-11`. Chapter 2 §4 (`:224-226`) says it precisely (ArkLib's new pin
`7653a901` is what several dossiers examined as upstream); CompPoly's, Clean's and VCVio's new
pins were read only after the merge. Fix: "ArkLib's pin moved to the revision the review had
examined as upstream".

### S11. Chapter 2 names an anonymous open pull request

`02-protocol-map.tex:194`: Layer 4 "not built (an open pull request holds the honest round
algebra)". It is pull request #42 (docs-debt §G: "#42, the honest round polynomials of a
sumcheck, based on `main`"). Name it or drop the parenthesis; the map otherwise names no
in-flight work.

### S12. "The review proves it in two lines" is a paper argument

`05-phases.tex:250-251` (every codeword near a K-valued word is K-valued). `gt-opening-compile.md:87`:
"a two-line argument"; no Lean probe. Fix: "which the review argues in two lines on paper".

### S13. Bare codes in the fragments' prose

Outside the code inventories: `gen/changes.tex:561-568` ("K3 gains the Merkle compilation …;
K1 …; L1 …; I1 …; I2 …; P5 …; G1 …; S the bound on `piopError`" — hole codes as subjects);
`gen/findings-libraries.tex:82-93` ("ledger row A2", "(A3)", "rows A2 and A3", "A5", without
the rows' names); `gen/lib-clean.tex:401` ("finding C8"); the table labels of M2 cited from
prose. Fix: name each ("the compiled-verifier hole (K3) gains …"; "the ledger's row on the
knowledge-soundness composition (A2)").

### S14. Chapter 13 and chapter 7 describe the public-input divergence as a check Lean makes and Rust does not

`13-drift.tex:65-67`: "one check that Lean makes and the deployed verifiers do not (the
per-limb public-input check)"; `07-tcb.tex:115-116`: "one check on which they already differ".
Both verifiers check the public input; Lean's check is stricter (per limb) than the deployed
one (combined), and the deployed accepts strictly more (R12). Fix: "one check Lean makes more
strictly than the deployed verifiers".

## Editorial

- E1. Title page: "Review session of 29 September 2026"; the upgrade, the re-runs and the
  assembly are of 30 September. "29–30 September 2026".
- E2. The table of contents runs ten pages (689 entries at `tocdepth` 2, `preamble.tex:111`)
  between the two-page summary and Part I. Set `tocdepth` 1 for the appendices, or for the
  generated fragments' subsections.
- E3. `02-protocol-map.tex:179`: "It then specifies each phase (Layers 4 to 10)": Layers 4 and 5
  are generic components. "each generic component and phase".
- E4. `07-tcb.tex:52`: "names the first and the second and the third".
- E5. `e-brief-review.tex:61`: "an hour into the first wave"; `NOTES.md:85` says about 45
  minutes. Also `:63` "The three that had written their dossiers incrementally lost nothing" is
  right (gt-table-pub, gt-bus, gt-flock-ring).
- E6. `10-auditability.tex:92-93`: "the earlier review found that no phase can use it
  [`BlockClaims`] over an abstract instance": not in `code-layer1.md` (R81 says only "no
  consumer"); cite `docs/reviews/protocol-layer1.md` or drop the clause.
- E7. `09-nonvacuity.tex:128-129`: "the three of them run (probes `P1Axioms`, `Extractors`)":
  `P1Axioms` checks `Lean.isNoncomputable`; the evaluation is lib-arklib's `Extractors` probe
  (`lib-arklib.md:2559-2567`, three `#eval`s). "compile and evaluate (…)".
- E8. `09-nonvacuity.tex:121`: "the blueprint's `2^40/|E|` is the right order": the review's
  sum under the window is `2^-159.7 = 2^32.3/|E|` (`05:258-259`); at the caps alone the
  `(α, β)` term is already `2^40/|E|` (verify-majors §9). "an upper bound that holds under the
  stacking window and is reached at the caps alone".
- E9. `09-nonvacuity.tex:168`: "item H1 of that review" is the one bare code in the
  orchestrator's chapters; "(item H1 of that review)" after "its own compression".
- E10. `05-phases.tex:182`: "takes no inverse" is the wording the check corrected to "no inverse
  of a challenge-dependent value" (ch 08's table says so); "takes no inverse there".
- E11. `f-register.tex:8`: `\label{sec:reg}` is emitted only in the else-branch; the live label
  is `gen/register.tex:5`. Move the label to the wrapper so the reference does not depend on the
  fragment.
- E12. The report introduces its own code family (R1–R140, plus the table labels of M2) while
  recommending names over codes; say in §1.3 that R-numbers are the report's index, given only
  in parentheses after a name, and that table labels are local.
- E13. `00-summary.tex:28-29`: "one combiner too few" and the GKR sentence are right; the
  parenthesis is long enough to be split into a sentence.
- E14. `01-scope-method.tex` table: "Mathlib, Lean v4.33.1" is the old pin; add the new one or
  point to §2.4, since the sentence above the table says every revision a statement can be about
  is listed.

## Checked and found right (negative results)

- The orchestrator's chapters against the register and the dossiers: every number I checked
  matches. The pool: 5 + 104 + 3 = 112 point claims plus one weighted (ch 02, ch 05, fig:phases:
  113). The public-input equation `c₀ + y c₁ = (1 + r) w₀ + r w₁` (ch 02, ch 05, verify-majors
  §4). The table sumcheck's numbers (τ_max rounds over the six opcode tables, 104 values, three
  coefficients, `(B + 2)/|E|`, `3/|E|`; N1–N4). The bus (α ∈ E⁴, β; radix 4; twelve children; two
  combination challenges; one combiner more than layers; five boundary evaluations; gt-bus). The
  Flock and ring-switching errors (`(4 k_batch + 163)/|E|`, `2^32/|E|`; R58). The surface
  numbers 70/217/382, 76/248/432, 100/354/612 and Layer 1's 143/20/41, 17 (61 lines), 8 (22
  lines) against `surface.tex` and `code-layer1.md:13, 50, 445, 989, 998`. The register's
  138/1/37/63/37, 115, 58 (ch 00, `register.tex:7`). The build jobs 3280 and 3452 (`logs/`). The
  VCVio shallow clone (`probes/lib-others/upstream/VCVio-main`). Chapter 7's "the right four"
  against the blueprint's list at `:1419-1421`.
- The two weakened findings are stated in their weakened form in the summary (item 5), chapter
  5 (`:69-72`), chapter 8 §2 and §4 (the orchestrator's GKR verdict paragraph), chapter 9 §4 and
  chapter 11 rec 6; nowhere in an orchestrator's chapter is "assigned to no layer" or "the
  wrong error" used. (The strong forms survive only in the register and the tree, M8.)
- Chapter 8 §2's table matches `verify-majors.md`'s summary table row by row, including the
  three points the re-derivation added (no tension between R2 and R3; "no inverse of a
  challenge-dependent value"; the `Ensemble.toM3` phrase stale against decision 8).
- Consistency: the pins (old in ch 01's table, new in ch 02 §4, both as BRIEF §8); what is built
  (ch 02's table, fig:chain, ch 07, ch 09) agrees; the GKR error is "loose" everywhere; the
  count of findings is 138 everywhere (no "134" or "111 negative" left); no "[fragment pending]"
  fallback is live (all switches on, all fragments present); `sec:reg` and every `\cref` target
  I looked for exist (NOTES: no undefined references).
- The vocabulary rule in the orchestrator's chapters: one bare code (E9). Register rows are
  always given as `(R…)` after a name. The code inventories (appendix C, chapter 12 §4, the
  hole table's "formerly" column) are exempt by the task's terms.
- Chapter e's facts that are in the record: the usage limit (eleven of twelve stopped), the
  upgrade, the leanVM checkout's move, the branch, the two builds, the model split for the
  tasks other than the two of S2.
- Structure against the brief's six write-up items: (1) chapters 1–4 with fig:chain and
  fig:phases; (1a) chapter 4; (2a) chapter 5; (2b, 2c) chapter 7 with chapter 10; (3a) chapter 8;
  (3b) chapter 9; (3c) chapter 10; (3d) chapter 1 §4, chapter 8 §2, appendices B and F; (4)
  chapter 11; (5) chapter 12 with appendices C and D; (6) chapter 13 (6a the four check tables,
  6b the five paragraphs of §13.1, 6c §13.4). The summary answers the owner's question and the
  three criteria. What is thin is listed in S8.
- The audience: no Lean snippet in the orchestrator's chapters is shown without its meaning
  (`piopError P` is `P.toDef.err`, `SatisfiedBy.word0_eq`, `pooled`/`pooledFrom` are each
  glossed); the library objects the chapters use are introduced in chapter 3's fragments
  (oracle reduction, knowledge state function, extractor, round-by-round knowledge soundness,
  `OracleComp`, the fields). The gap is the cryptographic vocabulary (S7), not the Lean.

## Fit to hand over?

Not as it stands: a reader would meet twenty-eight instructions addressed to the orchestrator,
a label scheme that collides with the codes the report indexes, one uncorrected fact in chapter
5 and three in the register, and a method statement that claims more re-derivation and re-running
than was done. None of this touches a technical conclusion; all of it is editing, of the order
of a few hours. After M1–M8 the report is fit to hand over, with S1–S14 improving it.

The three things I would change first: (1) fill or reword the twenty-eight markers from the
findings named in M1; (2) rename the table label families (M2) and add the register's note on
what was weakened or corrected after it was assembled (M8); (3) correct chapter 1's
re-derivation claim (M4), the summary's numbers and counts (M5–M7) and chapter 5's WHIR ordering
(M3).


## Appendix: raw working notes (in reading order, before consolidation)

## Working notes (raw, in reading order; consolidated into the prioritised list at the end)

### After chapters 00, 01, 02, 05, 07, 09 and register rows R1–R140

- 00: "Twelve dossiers" vs register "all thirteen dossiers processed" (obligations.md is the
  thirteenth and contributes R137–R140 to the 138 count quoted in the same paragraph). CHECK.
- 00: "about 1,400 citations" — verify-gt-table-pub 301, verify-gt-bus 314 rows (NOTES says ~400),
  verify-gt-flock-ring ~381, verify-gt-opening 277 rows: sum 1273 (or 1359). CHECK the four files.
- 00: "forty-odd Lean and Python probes, re-run at the new pins" — CHECK probes-rerun.md count.
- 00 item 5: "its 'check on the cofactor' is right" — CHECK against verify-majors' wording.
- 00: "Auditability … 100 declarations and 354 lines … about 80 and 290" — CHECK ch 10 / code-spine.
- 02: Flock schedule omits the k_batch+1 initial challenges ("64 values, one challenge, 8+k rounds").
- 02: tab:map-where Layer 4 "an open pull request holds the honest round algebra" — CHECK source.
- 05 bus: "the specification's Theorem 5.1" for the fingerprint — R92/G14 says the blueprint's
  "Lemma 5.1" should be Lemma 5.2. CHECK which number the tex has.
- 05 opening: "the review proves it in two lines" (K-valued list members) — paper or Lean? CHECK.
- 05 numbers: "L_0 … a few hundred at μ=15" — register R23 says 110–396; verify-gt-opening says
  110–648. Register and check disagree; chapter vague enough but CHECK.
- 07: "Four structures … and one of the adaptor" (five listed) then "are the right four". CHECK.
- 07: "fourteen load-bearing declarations not listed" — R91 names ~14 names; CHECK the source count.
- 07: "closes on propext, Classical.choice, Quot.sound … at both pins" — CHECK probes-rerun.
- 09: "the blueprint's 2^40/|E| is the right order" — CHECK blueprint text (R23 says 2^-150).
- 09: "the three of them run (probes P1Axioms, Extractors)" — CHECK code-spine.

### After verify-majors, probes-rerun, the four verify-* heads, the marker and code greps

- MARKERS: 28 `[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR…]` remain: gen/findings-docs.tex
  :36, :67, :110, :237; gen/docs-texts.tex :226, :257, :367, :392, :482, :524, :571, :612 (+ the
  explanatory sentence at :7); gen/docs-proposal.tex :313, :314, :317-:322, :325-:330 (14 hole
  rows), :381. Appendix D's wrapper says such places are "marked in bold" and ch:changes lists
  the changes, but the marker text is an instruction to the orchestrator, not to the reader.
- CITATIONS: verify-gt-table-pub 301 (294 OK, 2 wrong line, 4 not supported, 1 could not check);
  verify-gt-bus 314 rows ≈ 400 refs (300 OK, 3 wrong line, 9 not supported, 2 could not check);
  verify-gt-flock-ring ≈ 381 (375 OK, 1 wrong line, 3 misquoted, 2 not supported);
  verify-gt-opening 277 rows (251 OK, 7 wrong line, 18 not supported, 1 could not check).
  Sum: 1,273 rows (≈1,360 refs). Not OK: 13 wrong lines, 3 misquoted, 33 not supported, 4 could
  not check. Summary's "about 1,400 citations; a dozen wrong theorem or line numbers, no finding
  weakened" undercounts the defects and slightly overcounts the total.
- PROBES RE-RUN: probes-rerun.md table has 27 runs (incl. 5 controls and 1 never-written row);
  not "every probe" (ch e says so twice; ch 00 says "forty-odd … re-run"). Not re-run per that
  table: gt-bus Python H.1/H.2 (re-run by verify-gt-bus), BusSeam.lean, KnownColumn/PolyBridge
  (re-run by boundary-adaptor itself as *New variants), InnerProductOracle & FiatShamirChain
  (gt-opening says both pins), Transport, DefInstance, Shapes, P1Axioms, P3cExtractor, P6Surface,
  ExtractorsExpectedFailure, CleanBalance, NumeralHazard, ProbeWordsLemma (re-run: yes, 1.4).
- probes-rerun differs from code-pubinput C.10/C.11: for mutations 7a and 8 `rbr` does NOT
  compile (sorryAx); only `not_complete` is proved. Ch 13 cites Probe7a for "a wrong check breaks
  completeness" — supported by not_complete. Ch 09 §nv-open says the four late mutations were
  "written after the toolchain moved" — 4b and 6 were never written.
- verify-majors: 11 attacked, 9 confirmed, 2 weakened (5: GKR error loose not wrong, wire/layer
  check/missing variant confirmed; 10: "assigned to no layer" overstated). Ch 00 item 5 and ch 08
  table state this correctly. BUT the register (dossiers/register.md, reproduced as appendix F)
  keeps R7's name "the wrong degree, the wrong error and no definition" and R35's "assigned to no
  layer" — CHECK whether gen/register.tex or f-register.tex notes the weakening.
- Bare codes in the orchestrator's chapters: only 09-nonvacuity.tex:168 "item H1 of that review".
- Build logs: main 3280 jobs exit 0; full 144c5aa 3452 jobs exit 0 — ch e's numbers are right.
- VCVio shallow clone exists at probes/lib-others/upstream/VCVio-main — ch e right.
- Ch 02 "Layer 4 … an open pull request holds the honest round algebra": docs-debt names PR #42
  ("the honest round algebra and the ArkLib bridge in #42 — claimed"). CHECK #42's state.
- Ch e "Models": NOTES records code-layer1 and lib-others as run fresh on Opus after the restart;
  ch e says "the code audits … the libraries' adequacy … ran on the review's own model". Wrong for
  those two.
- Ch e "the rule 'no sub-agents' was added": BRIEF.md §2 says sub-agents are allowed if bound by
  the same rules; NOTES.md records no such rule. Unsupported by the record as it stands.
- Ch 00 "twelve proposals, none changing a theorem's meaning" vs ch 10 item 1 "Changes the
  statement of the knowledge-soundness theorem" and item 2 "Changes Seam.bus and the two phases".
- Ch 07 "fourteen load-bearing declarations not listed": code-spine.md:1119 counts fourteen for
  the SPINE; R91 merges three dossiers (198 of 333 unlisted overall). Undercount as stated.
- Ch 09 "the blueprint's 2^40/|E| is the right order": blueprint :1130 has 2^40/|E| + flockError;
  gt-opening puts the sum at 2^-159.7 = 2^32.3/|E| under the window. "Right order" is loose by
  2^8 but the bound holds; verify-majors §9: at the caps alone the (α,β) term is already 2^40/|E|.
