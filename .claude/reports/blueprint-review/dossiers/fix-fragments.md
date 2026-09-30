# fix-fragments: the reviewer's fixes to the generated fragments (M1, M2, M6, S8, S13)

Task of the read-report's follow-up. Only files under `tex/sections/gen/` were edited or created;
no tracked file of the repository was touched, nothing was posted, no Lean was run. Compiles ran
from `tex/` with LuaLaTeX into a private output directory (the scratchpad), because another agent
was compiling `main.tex` into `tex/build/` at the same time and the two runs corrupted each
other's `main.aux` (first attempt, 11:27).

Status: complete (2026-09-30). The report compiles (LuaLaTeX, exit 0, two passes, no undefined
reference of the fragments touched; no new overfull box).

## Summary

| Task | What | Count |
| --- | --- | --- |
| M1 | orchestrator markers filled (and the sentence announcing them reworded) | 27 markers + 1 sentence, in `findings-docs` (4), `docs-texts` (8 + 1), `docs-proposal` (14 hole rows + 1, the latter a new 12-row index table) |
| M2 | table-row labels renamed `check N` / `step N` | 6 tables, 77 labels; 73 passages holding the references rewritten (75 occurrences; one of the 73 is a later rewording), in 14 fragments; 6 column widths |
| M6 | new `gen/report-upstream.tex` | 13 matters + what must not be reported (R38) |
| S8 | new `gen/acceptance-tests.tex` | 28 tests (landscape longtable) |
| S13 | bare codes put after their names | the reviewer's 3 places; the lint's 178 other violations and 71 dossier codes (all handled or judged allowed, listed below); 16 more found by a fresh scan (new register rows R141–R143, N116, and others) |
| addition (2) | dossier section codes in headings and finding titles | 78 titles (57 headings, 2 paragraphs, 19 finding titles) + 4 running-text mentions |

For the orchestrator (outside my files, or decisions):

1. Appendix D's wrapper (`tex/sections/d-tracker-drafts.tex:7-8`) still says the places that must
   change again are "marked in bold"; they are now paragraphs ending with their register rows.
2. **The register's R116 cites wrong lines at the pin**: `whir.rs:1210, 2231`,
   `whir_config.rs:915, 1017` hold other code at `a386121f`; the stale comment is at
   `crates/pcs/src/whir.rs:1364-1365` and `:1771-1772`, the assertion at `:2485`,
   `QUERY_GRINDING_BITS = 17` at `whir_config.rs:60` (used `:922`, asserted `:1027`).
   `report-upstream.tex` cites the pinned lines and says so; `register.md`/`register.tex` still
   carry the old ones.
3. `gen/register.tex` was edited here (dossier locators, codes, row names of R142, R143, N116);
   `dossiers/register.md` was not. If the fragment is regenerated from `register.md`, these edits
   are lost; the edit list below has each one.
4. The orchestrator's guessed rows for S8 differ from the register's: test 14 is R79, test 23 R58,
   test 10 R54, test 24 R46 (the table uses the register's). The blueprint has 28 acceptance tests,
   not the thirty the read-report says.
5. Pre-existing, not mine: 27 "??" in the PDF where `\cref` points at a sub-subsection of an
   appendix (LaTeX warns "cref reference format for label type `subsubsubappendix' undefined").
6. Row labels in the M2 tables are written `check N`/`step N` in each table's first (`#`) column,
   widened to fit; `transcript-flock-ring`, `transcript-opening` and the GKR iteration table keep
   their plain numbers (they had no letter codes).

Nothing could not be done. Two items are left by judgement and named in the S13 section:
`findings-flock-ring.tex:370` ("its gate F5", the Flock roadmap's gate code inside a proposed ledger
row) and the formula `T4 = verify_knowledgeSound ∘ …` (`boundary-statements.tex:397`).


## M1. The orchestrator markers (done)

All 27 markers and the explanatory sentence that announced them (`docs-texts.tex:7`) are
replaced: 4 in `findings-docs.tex`, 8 in `docs-texts.tex`, 15 in `docs-proposal.tex` (the
fourteen hole rows and the rows for the findings against the sources). Each insertion is drawn
from the register rows the read-report's item M1 names (and the finding boxes they point to),
and ends with a parenthesis naming the rows, `(from \code{R…})`. Where a proposed Markdown
passage was the natural form, the lead sentence carries the rows and the Markdown follows in a
`srccode` block without them (the status paragraph after `docs-texts.tex:367`, the checklist
lines after `:482`). The rows for the findings against the sources (`docs-proposal.tex:381`)
became a second index table, `tab:docs-index-draft-sources`, in the format of
`tab:docs-index-draft`. `grep -rc 'TECHNICAL CHANGES' tex/sections/` finds nothing.

Stated as unverified where the register says so: whether Clean pull request 446 is inside the
new Clean pin `42fe4b26` (`docs-texts.tex`, the upstream-watch and issue-23 insertions); the fit
of VCVio's Merkle trees and their state at `a4232d08` (`findings-docs.tex`, the VCVio finding;
the hole table's note; the Merkle hole row). The axiom insertion says which declarations the
re-run covered (the master theorems, the two built phases, the composition, the extractors:
probes-rerun §7.4) and that Layer 1's theorems and the 3298-declaration audit were not re-run.

Row numbers the reviewer's map did not name but the text needed: `R7`, `R9` (the GKR schedule,
in the sketches insertion and the GKR rows), `R19`, `R24` (WHIR's level-0 batch, the
list-binding hole), `R33`, `R15` (the adaptor's hypotheses), `R50`, `R51` (the bus orders),
`R63` (the Merkle wire format), `R66` (the byte hasher).

Not in a fragment, for the orchestrator: appendix D's wrapper (`d-tracker-drafts.tex:7-8`) still
says the places that change again "are marked in bold"; they are now paragraphs ending with the
register rows (suggested: "Where a text must change again because of a technical finding of
this review, the change follows it with the register rows it comes from; \cref{ch:changes}
lists those changes.").

Edits (file and line at the time of the edit; before in full, after abbreviated):

- `gen/findings-docs.tex:36` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: the alternative, \texttt{verify} deciding the program condition on the public program and rejecting otherwise, removes the hypothesis from the soundness theorem; which one the blueprint takes is a technical decision.]}` | after: `The review recommends the hypothesis on both theorems, as drafted above: the condition is faithful to leanVM, whose verifiers do not check it and whose compiler emits well-formed programs (\texttt{docs/\allowbreak{}leanvm-\allowbreak{}targe …`
- `gen/findings-docs.tex:67` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: the message schedules, errors and internal relations of each phase, and the opening phase's schedule against specification §8.5.]}` | after: `\begin{sloppypar} The schedules, errors and internal relations the restated sections receive are those of the deployed verifiers as \cref{ch:faithfulness} transcribes them (the bus phase in \cref{tab:gen-bus-phase}, with the normalized laye …`
- `gen/findings-docs.tex:112` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: which ledger rows (admitted sumcheck round, admitted composition, round-by-round to plain, Fiat–Shamir and BCS, correlated agreement, ring-switching packing) still hold at ArkLib \texttt{7653a901}, from the library review.]}` | after: `At ArkLib \texttt{7653a901} every admission the ledger records still holds (\cref{tab:gen-lib-ark-admitted}): the sumcheck's single-round knowledge soundness (and, which the ledger omits, its perfect completeness); the composition of knowle …`
- `gen/findings-docs.tex:239` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: that decision, from the review of Layer 11 or the library review.]}` | after: `\begin{sloppypar} The review does not make that decision. The library exists at the old VCVio pin \texttt{f9dc47d9}; whether it fits leanVM's trees (untagged nodes hashed by one 64-byte BLAKE2s call, leaves hashed over several blocks, the p …`
- `gen/docs-texts.tex:7` | before: `Where a passage will have to change again because of technical findings of the review that this dossier does not know, it carries a line \texttt{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR:\allowbreak{} …]}.` | after: `Where a passage has to change again because of the review's technical findings, the change follows it in a short paragraph that ends with the register rows it comes from (\cref{sec:reg}).`
- `gen/docs-texts.tex:226` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: the names and shapes of the generic components of Layers 4 and 5 once they are restated as \texttt{Component.\allowbreak{}Def}s with their \texttt{Complete} and \texttt{Security} (today's sketch states \texttt{sumcheck}, \texttt{gkr} and \texttt{batchClaims} as bare \texttt{Oracle\allowbreak{}Reduction}s); the statement types of the bus, table sumcheck, Flock and opening phases; the opening phase's schedule, pending the question of specification §8.5 (``there is no separate reduction sumcheck''); whether Layer 11 reuses the Merkle trees of the VCVio pin (\cref{sec:docs-merkle}); the hypothesis on the program of the base theorems  …` | after: `With the review's technical findings, the generic rows of Layers 4 and 5 produce \texttt{Component.\allowbreak{}Def}s with their \texttt{Complete} and \texttt{Security} in the named form, the sumcheck's in both variants the verifiers run (t …`
- `gen/docs-texts.tex:257` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: today's sentence ``where a signature below says \texttt{(\allowbreak{}prog) (\allowbreak{}s)}, read \texttt{lean\allowbreak{}Isa\allowbreak{}Instance prog s}'' is dropped above because the sketches of Layers 4 to 7, 9 and 10 are to be restated on the spine's types (\cref{sec:docs-sketches}); if they are not restated in the same pull request, the sentence stays.]}` | after: `The review recommends restating the sketches of Layers 4 to 7, 9 and 10 on the spine's types (\cref{sec:docs-sketches}), after which no signature below takes \texttt{(\allowbreak{}prog) (\allowbreak{}s)} and today's sentence ``where a signa …`
- `gen/docs-texts.tex:366` | before: `\begin{sloppypar} \textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: at \texttt{b435631} the status recorded that \texttt{\#print axioms} on \texttt{piop\_\allowbreak{}rbr\allowbreak{}Knowledge\allowbreak{}Soundness} and on every Layer 1 theorem gives the kernel's three axioms (\texttt{protocol-\allowbreak{}status.\allowbreak{}md:\allowbreak{}17-\allowbreak{}18,\allowbreak{} 130-\allowbreak{}131}), and an axiom audit of 3298 declarations (\texttt{:\allowbreak{}59}); this dossier ran no Lean and cannot confirm either at \texttt{144c5aa}, where the local build is not yet redone (brief, section 8). Whether the knowledge-soundness composition that ArkLib admitted at \texttt{dca90385} …` | after: `\begin{sloppypar} Settled since the draft. The review's axiom probe, re-run at \texttt{144c5aa} with the new pins, gives Lean's three axioms and no \texttt{sorryAx} for the two master theorems, the existential form, both halves of the commi …`
- `gen/docs-texts.tex:400` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: which rows of the upstream watch (\texttt{:\allowbreak{}190-\allowbreak{}206}) and of the upstream ledger (\texttt{:\allowbreak{}171-\allowbreak{}184}) the upgrade settled or changed: ArkLib \texttt{main}'s typed executor and one-round bound, ``adopt when: the pin bump'' (\texttt{:\allowbreak{}201}), are now in the pin; Clean pull requests 466, 464 and 446 against the new Clean pin \texttt{42fe4b26}; ``a CompPoly containing \#331'' (\texttt{:\allowbreak{}162}).]}` | after: `The upgrade settled three rows and left the others standing. ArkLib's typed executor and one-round bound (\texttt{:\allowbreak{}201}, ``adopt when: the pin bump'') are in the pin, but the typed framework still has no knowledge soundness, no …`
- `gen/docs-texts.tex:490` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: holes the review adds, splits, renames or removes (for example if the opening phase has no sumcheck of its own, or if Layer 11 takes VCVio's Merkle trees), mirrored from the table of \cref{sec:docs-text-holes}; the list must stay one line per row of that table.]}` | after: `\begin{sloppypar} The review's findings change the checklist in three places, each mirrored by a row of the table of \cref{sec:docs-text-holes} and following the assignment of the obligations no hole owns (\cref{f:obl-unowned}): the one Flo …`
- `gen/docs-texts.tex:542` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: the statement types of the bus, table sumcheck, Flock and opening phases and the schedule of the opening phase, which the layer sections receive in place of the obsolete signatures of the comment; whether the adaptor's and the base theorems' hypotheses change.]}` | after: `\begin{sloppypar} The layer sections receive the statement types the review fixes: the bus phase from \texttt{Seam.\allowbreak{}commit} to \texttt{Seam.\allowbreak{}bus}, with a \texttt{BusOut I} in the shape of the Rust's \texttt{BusVerify …`
- `gen/docs-texts.tex:591` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: whether the new Clean pin \texttt{42fe4b26} (pull request 61) contains Clean pull request 446, and whether the eager-\texttt{Fintype} concern is retired by the new CompPoly pin, which would change ``Blocked on''.]}` | after: `The eager-\texttt{Fintype} clause of ``Blocked on'' is deleted: the new CompPoly pin \texttt{572f9973} contains CompPoly pull request 331, which retired it. Whether the new Clean pin \texttt{42fe4b26}, Clean pull request 474 merged over Cle …`
- `gen/docs-texts.tex:632` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: whether the statements of pull requests 39 and 43 fit the statement types the review fixes for the bus and opening phases, which decides whether their descriptions promise a consumer that exists.]}` | after: `\begin{sloppypar} Both fit, so both descriptions promise a consumer that exists. The fingerprint of pull request 39 enters the weights of the bus forms that the fixed \texttt{BusOut I} carries per side and sumcheck table, in the shape of th …`
- `gen/docs-proposal.tex:313` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: one sentence, after the review of Layer 4]}` | after: `the sumcheck over eq-weighted virtual polynomials as a \texttt{Component.\allowbreak{}Def}, in the plain variant and the normalized one of the GKR layers, the linear coefficient derived, not sent (from \code{R36}, \code{R53}, \code{R7})`
- `gen/docs-proposal.tex:314` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR]}` | after: `its round-by-round knowledge soundness at $d/\abs{\E}$ a round, in the named form, with the lemma that carries it to the wire message of three coefficients (from \code{R53}, \code{R36})`
- `gen/docs-proposal.tex:317` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR]}` | after: `the batched grand product of the three trees, over a context whose oracles are the leaf tables, radix 4 with one binary layer for an odd height, a combiner after the roots and after every layer, the last unused (from \code{R10}, \code{R7},  …`
- `gen/docs-proposal.tex:318` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR]}` | after: `its round-by-round knowledge soundness at $4/\abs{\E}$ a round of the normalized layer sumcheck and $1/\abs{\E}$ a combination challenge, the zerocheck clause riding along (from \code{R7}, \code{R9}, \code{R10})`
- `gen/docs-proposal.tex:319` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR]}` | after: `the challenges $(α, β)$, the two roots, the GKR and the five boundary evaluations, emitting a \texttt{BusOut I} in the shape of the Rust's \texttt{BusVerify}, the orders of the leaf stacks, roots, evaluations and claims fixed (from \code{R2 …`
- `gen/docs-proposal.tex:320` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR]}` | after: `one \texttt{busError}, the zerocheck a conjunct of the state function that costs nothing beyond the GKR's errors, under the two side conditions on the instance (from \code{R47}, \code{R43})`
- `gen/docs-proposal.tex:321` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR]}` | after: `one sumcheck of $τ_{\max}$ rounds over the six opcode tables' constraints and bus forms, three coefficients a round and 104 values at the end, from the bus seam's \texttt{BusOut} (from \code{R2}, \code{R11}, \code{R53})`
- `gen/docs-proposal.tex:322` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR]}` | after: `its round-by-round knowledge soundness at $(B + 2)/\abs{\E}$ on $ξ$ and $3/\abs{\E}$ a round, over the tables the instance marks as the sumcheck's (from \code{R11}, \code{R2})`
- `gen/docs-proposal.tex:325` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: pending the question of specification section 8.5]}` | after: `the batching challenge $λ$ and one weighted query of the stack, with no sumcheck of its own (from \code{R18})`
- `gen/docs-proposal.tex:326` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR]}` | after: `its knowledge soundness at $(J - 1)/\abs{\E}$ on $λ$, the query answered by the stack's inner-product oracle (from \code{R18}, \code{R19})`
- `gen/docs-proposal.tex:327` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR]}` | after: `WHIR realizing the one weighted query, its level-0 batching the opening's $λ$, \texttt{encode} over $\E$ at every level with the lemma that a $\K$-valued message has a $\K$-valued codeword (from \code{R19}, \code{R18}, \code{R24})`
- `gen/docs-proposal.tex:328` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: see \cref{sec:docs-merkle} on VCVio's Merkle trees]}` | after: `Merkle trees with the pruned wire paths, the byte hasher (BLAKE2s-256 of a 64-byte input, not the compression keyed by the chain state) and the parameter ladder; whether the trees are VCVio's is open (from \code{R63}, \code{R66}, \code{R77} …`
- `gen/docs-proposal.tex:329` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR]}` | after: `the chain, the proof object and \texttt{verify}, compiled by a leanerVM BCS transform (roots for oracle messages, authenticated rows for queries, grinding and the encoding checks) over the family of admissible sizes, from front phases that  …`
- `gen/docs-proposal.tex:330` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: see \cref{sec:docs-leanisa} on the program hypothesis]}` | after: `both with \texttt{Well\allowbreak{}Formed\allowbreak{}Bytecode prog}: soundness for a $Q$-query adversary against the random-oracle verifier, with a straight-line extractor, at \texttt{niError Q}; completeness from a witness with admissible …`
- `gen/docs-proposal.tex:381` | before: `\textbf{[TECHNICAL CHANGES TO BE INSERTED BY THE ORCHESTRATOR: rows for the findings against the sources that the blueprint cites, once the other agents' findings are merged into the register.]}` | after: `\begin{sloppypar} The index gains one row per finding of the review against leanVM's own sources, of the same kind as the status findings on the sources mapped above: each is recorded by name in \texttt{docs/\allowbreak{}leanvm-\allowbreak{ …`

## M2. The report's own table-row labels (done)

Renamed, numbered from 1 within each table (a table's rows that the source numbered from 0 move
up by one; the old code is kept nowhere):

| Table | Old labels | New labels |
| --- | --- | --- |
| `tab:gen-bus-checks` (`gen/checks-bus.tex`) | B1–B17 | check 1–check 17 |
| `tab:gen-opening-checks` (`gen/checks-opening.tex`) | S-rate, S-window, S-implied; R1–R5; G1, G2; M1–M7; W1–W8 | check 1–3; check 4–8; check 9, 10; check 11–17; check 18–25 |
| `tab:gen-bus-setup` (`gen/transcript-bus.tex`) | S0–S6; C1, C2 | step 1–7; step 8, 9 |
| `tab:gen-bus-phase` (`gen/transcript-bus.tex`) | U0–U7 | step 1–8 |
| `tab:gen-table-pub-transcript-table` (`gen/transcript-table-pub.tex`) | T0–T12 | step 1–13 |
| `tab:gen-table-pub-transcript-pub` (`gen/transcript-table-pub.tex`) | P0–P4 | step 1–5 |

The label sits in each table's first column (`#`), written `check N` / `step N`; that column was
widened (checks of the bus 0.03 → 0.055 of the line, the widest column narrowed by as much;
transcripts 0.04 → 0.06 or 0.065) so that the label fits on one line. The captions were already
phase-specific and are unchanged. `gen/transcript-flock-ring.tex`, `gen/transcript-opening.tex`
(and the GKR iteration table) already number their rows 1, 2, …; `gen/checks-flock-ring.tex` and
`gen/checks-table-pub.tex` name their rows; none of them needed a change.

Every reference was rewritten as "check N" or "step N", with `\cref` to the table whenever the
reference is outside the table's own fragment (or the table is not the one just named): in
`checks-bus`, `checks-opening` (including the closing-list paragraph the reviewer named,
`:273-279`), `transcript-bus`, `transcript-table-pub`, `checks-table-pub`,
`disagreements-table-pub`, `findings-table-pub` (its note on step numbers reworded),
`disagreements-bus`, `disagreements-opening`, `findings-bus` (`:173`, `:323-324`),
`findings-opening` (its note on check names reworded), `analysis-opening`,
`transcript-opening`, `obligations` (`:140-164`, `:225-226`, `:307`, `:313`). A final search for
every old label in these files finds only the architecture's coverage-diagram quotation "S4"
(`obligations.tex:613`, `:636`), which is not a table label. The orchestrator's chapters
(`tex/sections/*.tex`) cite none of these labels. The register's `R#` and appendix F's `N#`/`U#`
are untouched. The compile shows no new overfull box in the changed tables.

Edits:

- `gen/checks-bus.tex:23` | before: `p{0.03\linewidth}>{\raggedright\arraybackslash}p{0.12\linewidth}` | after: `p{0.055\linewidth}>{\raggedright\arraybackslash}p{0.12\linewidth}`
- `gen/checks-bus.tex:23` | before: `p{0.29\linewidth}@{}}` | after: `p{0.265\linewidth}@{}}`
- `gen/checks-bus.tex:35` | before: `B1 & …` | after: `check 1 & …`
- `gen/checks-bus.tex:42` | before: `B2 & …` | after: `check 2 & …`
- `gen/checks-bus.tex:49` | before: `B3 & …` | after: `check 3 & …`
- `gen/checks-bus.tex:59` | before: `B4 & …` | after: `check 4 & …`
- `gen/checks-bus.tex:65` | before: `B5 & …` | after: `check 5 & …`
- `gen/checks-bus.tex:73` | before: `B6 & …` | after: `check 6 & …`
- `gen/checks-bus.tex:90` | before: `B7 & …` | after: `check 7 & …`
- `gen/checks-bus.tex:99` | before: `B8 & …` | after: `check 8 & …`
- `gen/checks-bus.tex:105` | before: `B9 & …` | after: `check 9 & …`
- `gen/checks-bus.tex:112` | before: `B10 & …` | after: `check 10 & …`
- `gen/checks-bus.tex:118` | before: `B11 & …` | after: `check 11 & …`
- `gen/checks-bus.tex:126` | before: `B12 & …` | after: `check 12 & …`
- `gen/checks-bus.tex:134` | before: `B13 & …` | after: `check 13 & …`
- `gen/checks-bus.tex:142` | before: `B14 & …` | after: `check 14 & …`
- `gen/checks-bus.tex:151` | before: `B15 & …` | after: `check 15 & …`
- `gen/checks-bus.tex:159` | before: `B16 & …` | after: `check 16 & …`
- `gen/checks-bus.tex:165` | before: `B17 & …` | after: `check 17 & …`
- `gen/checks-bus.tex:64` (2 occurrences) | before: `(B6)` | after: `(check 6)`
- `gen/checks-bus.tex:83` | before: `Given the stacking window (B9)` | after: `Given the stacking window (check 9)`
- `gen/checks-bus.tex:124` | before: `the caps and the windows (B4 to B9)` | after: `the caps and the windows (checks 4 to 9)`
- `gen/checks-bus.tex:175` | before: `the decomposition (U6 and U7)` | after: `the decomposition (steps 7 and 8 of \cref{tab:gen-bus-phase})`
- `gen/checks-opening.tex:41` | before: `S-rate & …` | after: `check 1 & …`
- `gen/checks-opening.tex:53` | before: `S-window & …` | after: `check 2 & …`
- `gen/checks-opening.tex:63` | before: `S-implied & …` | after: `check 3 & …`
- `gen/checks-opening.tex:74` | before: `R1 & …` | after: `check 4 & …`
- `gen/checks-opening.tex:80` | before: `R2 & …` | after: `check 5 & …`
- `gen/checks-opening.tex:89` | before: `R3 & …` | after: `check 6 & …`
- `gen/checks-opening.tex:95` | before: `R4 & …` | after: `check 7 & …`
- `gen/checks-opening.tex:101` | before: `R5 & …` | after: `check 8 & …`
- `gen/checks-opening.tex:110` | before: `G1 & …` | after: `check 9 & …`
- `gen/checks-opening.tex:124` | before: `G2 & …` | after: `check 10 & …`
- `gen/checks-opening.tex:133` | before: `M1 & …` | after: `check 11 & …`
- `gen/checks-opening.tex:139` | before: `M2 & …` | after: `check 12 & …`
- `gen/checks-opening.tex:154` | before: `M3 & …` | after: `check 13 & …`
- `gen/checks-opening.tex:160` | before: `M4 & …` | after: `check 14 & …`
- `gen/checks-opening.tex:166` | before: `M5 & …` | after: `check 15 & …`
- `gen/checks-opening.tex:172` | before: `M6 & …` | after: `check 16 & …`
- `gen/checks-opening.tex:183` | before: `M7 & …` | after: `check 17 & …`
- `gen/checks-opening.tex:197` | before: `W1 & …` | after: `check 18 & …`
- `gen/checks-opening.tex:205` | before: `W2 & …` | after: `check 19 & …`
- `gen/checks-opening.tex:216` | before: `W3 & …` | after: `check 20 & …`
- `gen/checks-opening.tex:226` | before: `W4 & …` | after: `check 21 & …`
- `gen/checks-opening.tex:235` | before: `W5 & …` | after: `check 22 & …`
- `gen/checks-opening.tex:244` | before: `W6 & …` | after: `check 23 & …`
- `gen/checks-opening.tex:251` | before: `W7 & …` | after: `check 24 & …`
- `gen/checks-opening.tex:257` | before: `W8 & …` | after: `check 25 & …`
- `gen/checks-opening.tex:17` | before: `The setup and commitment checks are B1 to B10 and B17 of \cref{tab:gen-bus-checks}` | after: `The setup and commitment checks are checks 1 to 10 and 17 of \cref{tab:gen-bus-checks}`
- `gen/checks-opening.tex:41` | before: `(B8 of \cref{tab:gen-bus-checks})` | after: `(check 8 of \cref{tab:gen-bus-checks})`
- `gen/checks-opening.tex:53` | before: `(B9 of \cref{tab:gen-bus-checks})` | after: `(check 9 of \cref{tab:gen-bus-checks})`
- `gen/checks-opening.tex:67` | before: `(B4 to B6 of \cref{tab:gen-bus-checks})` | after: `(checks 4 to 6 of \cref{tab:gen-bus-checks})`
- `gen/checks-opening.tex:100` | before: `(B17 of \cref{tab:gen-bus-checks})` | after: `(check 17 of \cref{tab:gen-bus-checks})`
- `gen/checks-opening.tex:169` | before: `by fixed-length parsing and R4` | after: `by fixed-length parsing and check 7`
- `gen/checks-opening.tex:207` (2 occurrences) | before: `settled at W5` | after: `settled at check 22`
- `gen/checks-opening.tex:268` | before: `(S-rate and S-window; \cref{f:bus-admissible})` | after: `(checks 1 and 2; \cref{f:bus-admissible})`
- `gen/checks-opening.tex:273` | before: `the stacking window (S-rate, S-window); ``every sumcheck's rounds'' is not a check in either verifier (W1); ``the PCS opening'' stands for M1 to M7, W2 to W5 and, absent from Annex B altogether, G1.` | after: `the stacking window (checks 1 and 2); ``every sumcheck's rounds'' is not a check in either verifier (check 18); ``the PCS opening'' stands for checks 11 to 17 and 19 to 22 and, absent from Annex B altogether, check 9.`
- `gen/checks-opening.tex:276` | before: `the canonical encodings (B2, B3, B10 of \cref{tab:gen-bus-checks}; R2), full consumption (R4), grinding (G1, G2).` | after: `the canonical encodings (checks 2, 3 and 10 of \cref{tab:gen-bus-checks}; check 5 here), full consumption (check 7), grinding (checks 9 and 10).`
- `gen/checks-opening.tex:279` | before: `exercise M6 and the scalars` | after: `exercise check 16 and the scalars`
- `gen/transcript-bus.tex:45` | before: `p{0.04\linewidth}>{\raggedright\arraybackslash}p{0.28\linewidth}` | after: `p{0.06\linewidth}>{\raggedright\arraybackslash}p{0.26\linewidth}`
- `gen/transcript-bus.tex:106` | before: `p{0.04\linewidth}>{\raggedright\arraybackslash}p{0.30\linewidth}` | after: `p{0.06\linewidth}>{\raggedright\arraybackslash}p{0.28\linewidth}`
- `gen/transcript-bus.tex:57` | before: `S0 & …` | after: `step 1 & …`
- `gen/transcript-bus.tex:63` | before: `S1 & …` | after: `step 2 & …`
- `gen/transcript-bus.tex:68` | before: `S2 & …` | after: `step 3 & …`
- `gen/transcript-bus.tex:72` | before: `S3 & …` | after: `step 4 & …`
- `gen/transcript-bus.tex:76` | before: `S4 & …` | after: `step 5 & …`
- `gen/transcript-bus.tex:80` | before: `S5 & …` | after: `step 6 & …`
- `gen/transcript-bus.tex:84` | before: `S6 & …` | after: `step 7 & …`
- `gen/transcript-bus.tex:88` | before: `C1 & …` | after: `step 8 & …`
- `gen/transcript-bus.tex:93` | before: `C2 & …` | after: `step 9 & …`
- `gen/transcript-bus.tex:118` | before: `U0 & …` | after: `step 1 & …`
- `gen/transcript-bus.tex:122` | before: `U1 & …` | after: `step 2 & …`
- `gen/transcript-bus.tex:126` | before: `U2 & …` | after: `step 3 & …`
- `gen/transcript-bus.tex:130` | before: `U3 & …` | after: `step 4 & …`
- `gen/transcript-bus.tex:134` | before: `U4 & …` | after: `step 5 & …`
- `gen/transcript-bus.tex:138` | before: `U5 & …` | after: `step 6 & …`
- `gen/transcript-bus.tex:142` | before: `U6 & …` | after: `step 7 & …`
- `gen/transcript-bus.tex:150` | before: `U7 & …` | after: `step 8 & …`
- `gen/transcript-bus.tex:76` | before: `(the checks B4 to B9 of \cref{tab:gen-bus-checks})` | after: `(checks 4 to 9 of \cref{tab:gen-bus-checks})`
- `gen/transcript-bus.tex:159` | before: `After the last of these steps (U7)` | after: `After the last of these steps (step 8)`
- `gen/transcript-bus.tex:358` | before: `the boundary evaluations (U6) are 5 elements` | after: `the boundary evaluations (step 7 of \cref{tab:gen-bus-phase}) are 5 elements`
- `gen/transcript-bus.tex:161` | before: `evaluations (U6).` | after: `evaluations (step 7).`
- `gen/transcript-bus.tex:349` | before: `(the last computation of the phase, U7)` | after: `(the last computation of the phase, step 8 of \cref{tab:gen-bus-phase})`
- `gen/transcript-table-pub.tex:41` | before: `p{0.04\linewidth}>{\raggedright\arraybackslash}p{0.295\linewidth}` | after: `p{0.065\linewidth}>{\raggedright\arraybackslash}p{0.27\linewidth}`
- `gen/transcript-table-pub.tex:191` | before: `p{0.04\linewidth}>{\raggedright\arraybackslash}p{0.225\linewidth}` | after: `p{0.06\linewidth}>{\raggedright\arraybackslash}p{0.205\linewidth}`
- `gen/transcript-table-pub.tex:53` | before: `T0 & …` | after: `step 1 & …`
- `gen/transcript-table-pub.tex:59` | before: `T1 & …` | after: `step 2 & …`
- `gen/transcript-table-pub.tex:63` | before: `T2 & …` | after: `step 3 & …`
- `gen/transcript-table-pub.tex:72` | before: `T3 & …` | after: `step 4 & …`
- `gen/transcript-table-pub.tex:77` | before: `T4 & …` | after: `step 5 & …`
- `gen/transcript-table-pub.tex:81` | before: `T5 & …` | after: `step 6 & …`
- `gen/transcript-table-pub.tex:90` | before: `T6 & …` | after: `step 7 & …`
- `gen/transcript-table-pub.tex:95` | before: `T7 & …` | after: `step 8 & …`
- `gen/transcript-table-pub.tex:99` | before: `T8 & …` | after: `step 9 & …`
- `gen/transcript-table-pub.tex:105` | before: `T9 & …` | after: `step 10 & …`
- `gen/transcript-table-pub.tex:112` | before: `T10 & …` | after: `step 11 & …`
- `gen/transcript-table-pub.tex:118` | before: `T11 & …` | after: `step 12 & …`
- `gen/transcript-table-pub.tex:123` | before: `T12 & …` | after: `step 13 & …`
- `gen/transcript-table-pub.tex:203` | before: `P0 & …` | after: `step 1 & …`
- `gen/transcript-table-pub.tex:209` | before: `P1 & …` | after: `step 2 & …`
- `gen/transcript-table-pub.tex:213` | before: `P2 & …` | after: `step 3 & …`
- `gen/transcript-table-pub.tex:217` | before: `P3 & …` | after: `step 4 & …`
- `gen/transcript-table-pub.tex:223` | before: `P4 & …` | after: `step 5 & …`
- `gen/transcript-table-pub.tex:59` | before: `drawn after the boundary evaluations (T0)` | after: `drawn after the boundary evaluations (step 1)`
- `gen/transcript-table-pub.tex:141` | before: `2 (step P2) & 1 (step P1)` | after: `2 (step 3 of \cref{tab:gen-table-pub-transcript-pub}) & 1 (its step 2)`
- `gen/transcript-table-pub.tex:209` | before: `the 104 values of the final message (T9)` | after: `the 104 values of the final message (step 10 of \cref{tab:gen-table-pub-transcript-table})`
- `gen/transcript-table-pub.tex:252` | before: `the column claims (T11)` | after: `the column claims (step 12 of \cref{tab:gen-table-pub-transcript-table})`
- `gen/transcript-table-pub.tex:254` | before: `the pooled claims (P4)` | after: `the pooled claims (step 5 of \cref{tab:gen-table-pub-transcript-pub})`
- `gen/checks-table-pub.tex:78` | before: `\textbf{Final check} (T10)` | after: `\textbf{Final check} (step 11 of \cref{tab:gen-table-pub-transcript-table})`
- `gen/checks-table-pub.tex:84` | before: `located by the routing of the limbs, T12)` | after: `located by the routing of the limbs, step 13 of \cref{tab:gen-table-pub-transcript-table})`
- `gen/checks-table-pub.tex:105` | before: `(P0)` | after: `(step 1 of \cref{tab:gen-table-pub-transcript-pub})`
- `gen/checks-table-pub.tex:111` | before: `(P3)` | after: `(step 4 of \cref{tab:gen-table-pub-transcript-pub})`
- `gen/disagreements-table-pub.tex:33` | before: `The public-input check (P3)` | after: `The public-input check (step 4 of \cref{tab:gen-table-pub-transcript-pub})`
- `gen/disagreements-table-pub.tex:37` | before: `The round consistency equation (T6)` | after: `The round consistency equation (step 7 of \cref{tab:gen-table-pub-transcript-table})`
- `gen/disagreements-table-pub.tex:42` | before: `Which coefficient is omitted (T5)` | after: `Which coefficient is omitted (step 6 of \cref{tab:gen-table-pub-transcript-table})`
- `gen/findings-table-pub.tex:24` | before: `The step numbers (T0 to T12, P0 to P4) refer to` | after: `A step number (``step 5'') refers to that row of`
- `gen/findings-table-pub.tex:125` | before: `the number of rounds (T4) and the final message (T9)` | after: `the number of rounds (step 5 of \cref{tab:gen-table-pub-transcript-table}) and the final message (its step 10)`
- `gen/findings-table-pub.tex:183` | before: `the derivation of $c_1$ (T5, T6)` | after: `the derivation of $c_1$ (steps 6 and 7 of \cref{tab:gen-table-pub-transcript-table})`
- `gen/disagreements-bus.tex:46` | before: `(B2)` | after: `(check 2)`
- `gen/disagreements-bus.tex:46` | before: `(B7)` | after: `(check 7)`
- `gen/disagreements-bus.tex:47` | before: `(B8)` | after: `(check 8)`
- `gen/disagreements-bus.tex:47` | before: `(B9)` | after: `(check 9)`
- `gen/disagreements-bus.tex:47` | before: `(B10)` | after: `(check 10)`
- `gen/disagreements-bus.tex:48` | before: `(B16)` | after: `(check 16)`
- `gen/disagreements-bus.tex:48` | before: `(B17)` | after: `(check 17)`
- `gen/disagreements-bus.tex:61` | before: `the layout (B11)` | after: `the layout (check 11 of \cref{tab:gen-bus-checks})`
- `gen/disagreements-opening.tex:49` | before: `S-rate of` | after: `check 1 of`
- `gen/disagreements-opening.tex:54` | before: `check in either verifier (W1); ``the PCS opening'' stands for M1 to M7 and W2 to W5, and grinding (G1, G2) is absent from Annex B altogether. The canonical encodings (B2, B3, B10 of \cref{tab:gen-bus-checks}; R2), full consumption (R4) and grinding` | after: `check in either verifier (check 18 of \cref{tab:gen-opening-checks}); ``the PCS opening'' stands for its checks 11 to 17 and 19 to 22, and grinding (its checks 9 and 10) is absent from Annex B altogether. The canonical encodings (checks 2, 3 and 10 of \cref{tab:gen-bus-checks}; check 5 of \cref{tab: …`
- `gen/disagreements-opening.tex:68` | before: `Soundness-neutral (M2 of` | after: `Soundness-neutral (check 12 of`
- `gen/findings-bus.tex:173` | before: `B8 and B9 of \cref{tab:gen-bus-checks}` | after: `checks 8 and 9 of \cref{tab:gen-bus-checks}`
- `gen/findings-bus.tex:323` | before: `the announced sizes (B2)` | after: `the announced sizes (check 2)`
- `gen/findings-bus.tex:324` | before: `the root's halves (B10)` | after: `the root's halves (check 10)`
- `gen/findings-bus.tex:324` | before: `the stream (B17)` | after: `the stream (check 17)`
- `gen/findings-opening.tex:22` | before: `The checks named (M2, M6, \dots) are those of \cref{tab:gen-opening-checks}.` | after: `A check named by its number (check 12, check 16, \dots) is that row of \cref{tab:gen-opening-checks}.`
- `gen/findings-opening.tex:274` | before: `check M2` | after: `check 12`
- `gen/findings-opening.tex:387` | before: `row S-implied.)` | after: `check 3.)`
- `gen/analysis-opening.tex:266` | before: `checks M2 to M7 of` | after: `checks 12 to 17 of`
- `gen/transcript-opening.tex:784` | before: `check M2 of` | after: `check 12 of`
- `gen/transcript-opening.tex:857` | before: `check B15 of` | after: `check 15 of`
- `gen/obligations.tex:140` | before: `(checks M1 to M7)` | after: `(checks 11 to 17 of \cref{tab:gen-opening-checks})`
- `gen/obligations.tex:142` | before: `(check M6)` | after: `(check 16 of \cref{tab:gen-opening-checks})`
- `gen/obligations.tex:143` | before: `check M7)` | after: `check 17)`
- `gen/obligations.tex:143` | before: `D.4 (M7)` | after: `D.4 (check 17)`
- `gen/obligations.tex:160` | before: `check W2)` | after: `check 19 of \cref{tab:gen-opening-checks})`
- `gen/obligations.tex:160` | before: `D.5 (W2)` | after: `D.5 (check 19)`
- `gen/obligations.tex:161` | before: `(check W4)` | after: `(check 21 of \cref{tab:gen-opening-checks})`
- `gen/obligations.tex:161` | before: `D.5 (W4)` | after: `D.5 (check 21)`
- `gen/obligations.tex:163` | before: `(check G1 for the nonce, W3 for row consistency)` | after: `(check 9 of \cref{tab:gen-opening-checks} for the nonce, its check 20 for row consistency)`
- `gen/obligations.tex:164` | before: `The terminal check} (W5)` | after: `The terminal check} (check 22 of \cref{tab:gen-opening-checks})`
- `gen/obligations.tex:225` | before: `(check B13)` | after: `(check 13 of \cref{tab:gen-bus-checks})`
- `gen/obligations.tex:225` | before: `gt-bus B (B13)` | after: `gt-bus B (check 13)`
- `gen/obligations.tex:226` | before: `(check B12)` | after: `(check 12 of \cref{tab:gen-bus-checks})`
- `gen/obligations.tex:226` | before: `gt-bus B (B12)` | after: `gt-bus B (check 12)`
- `gen/obligations.tex:313` | before: `gt-bus B (B15)` | after: `gt-bus B (check 15 of \cref{tab:gen-bus-checks})`
- `gen/obligations.tex:307` | before: `gt-table-pub A.1 (T5, T6)` | after: `gt-table-pub A.1 (steps 6 and 7 of \cref{tab:gen-table-pub-transcript-table})`
- `gen/findings-table-pub.tex:24` | before: `A step number (``step 5'') refers to that row of \cref{tab:gen-table-pub-transcript-table,tab:gen-table-pub-transcript-pub}.` | after: `A step number (``step 5 of'' a table) is the row of that number in the table named, \cref{tab:gen-table-pub-transcript-table} or \cref{tab:gen-table-pub-transcript-pub}.`

## M6. One list of what to report to leanVM (done)

New fragment `tex/sections/gen/report-upstream.tex` (label `sec:gen-report-upstream`), input by
`11-options.tex` §"What to report to leanVM" (`sec:opt-upstream-report`), which already had the
`\InputIfFileExists`. Thirteen items, each with the matter, the pinned lines, whose defect it is
and what is asked, and the register row:

| # | Matter | Whose | Asked | Row |
| --- | --- | --- | --- | --- |
| 1 | the public-input check: per limb in §8.2, one combined equation in the Rust, the Python and the recursion guest | specification against all three verifiers | clarification (which is normative) | R12 |
| 2 | the Rust Flock prover fails at `r_eq = 1` | Rust prover | fix | R111 |
| 3 | seven disagreements in setup, commitment, bus (rate announced, roots' order, seed constant, unmentioned checks, last combiner, Python's unchecked bytecode slots, fingerprint bound 5·2^μ vs 4·2^μ) | specification (six), Python (one) | clarifications; for the Python a check or a sentence | R105 |
| 4 | the seed's `R1CS_DIGEST` cannot be recomputed at the pin | Rust (mirrored by Python, guest) | documented constant | R106 |
| 5 | no round-by-round analysis of the bus phase | specification | clarification | R107 |
| 6 | table-sumcheck batching error loose by one; recycled point; dropped coefficient | specification | fix + two clarifications | R108 |
| 7 | the Rust's accounting unions only the algebraic checks over the list | Rust parameter accounting | clarification or fix | R117 |
| 8 | Flock's circuit, layout, constants only in Rust and Python | specification | documented constants (Annex C) | R57 |
| 9 | witness-stack size: no floor, ceiling, tie rule | specification | clarification | R133 |
| 10 | stale comments on the round message | Rust comments | fix | R109 |
| 11 | stale comments on the counter and flags | Rust comments | fix | R112 |
| 12 | stale comment on level-0 grinding | Rust comment | fix | R116 |
| 13 | stale comment on the Merkle leaf size | Rust comment | fix | R118 |

Then the paragraph on what must not be reported: the status's Python-caps finding (F9), false
at the pin (R38), with `verifier.py:856-864`, `:1378`, `:252-254` and `cpu/mod.rs:164-165`.

Checked against the pinned sources for this fragment (`git -C …/leanVM show a386121f:<path>`):
`08-end-to-end-protocol.tex:29-33, 55, 68`; `cpu/mod.rs:121-124, 147-150, 568-570, 619-620,
750-756`; `verifier.py:629, 888-891, 1398-1401`; `aggregate.py:1680-1685`; `gkr.rs:272-276`;
`leaf.rs:108-118`; `05-arithmetization.tex:37, 155`; `03-proving-primitives.tex:67`;
`flock/src/hash.rs:259-275`; `flock/src/zerocheck.rs:114-119`; `constraints.rs:24-26,
257-267`; `tables.rs:904-907`; `whir_config.rs:537-540`; `whir.rs:392-396, 461-464`;
`witness.rs:95-98`; `b-polynomial-commitment-scheme.tex:139-141`; `04-committing-the-witness.tex:10`.

**A correction to the register (R116), for the orchestrator.** The register (from
`literature.md` §G.1, status "paper", not citation-checked) cites the stale grinding comment at
`crates/pcs/src/whir.rs:1210` and the assertion at `whir.rs:2231`, `whir_config.rs:915, 1017`. At
the pin `a386121f` those lines hold other code (`whir.rs:1210` is `fn ext_row_words`). The comment
is at `whir.rs:1364-1365` (prover: "Query-phase PoW grinding for L0 (0 bits in the production
profile; …") and `:1771-1772` (verifier: "no-op at 0 bits"); the assertion `all(|&b| b ==
QUERY_GRINDING_BITS)` is at `whir.rs:2485`; `QUERY_GRINDING_BITS = 17` at `whir_config.rs:60`, used
at `:922` and asserted at `:1027`. The fragment cites the pinned lines and says they differ from
the register's. The finding itself stands.

## S8. The acceptance tests, one table (done)

New fragment `tex/sections/gen/acceptance-tests.tex` (label `sec:gen-acceptance-tests`, table
`tab:gen-acceptance-tests`), input by `09-nonvacuity.tex` §"The blueprint's acceptance tests",
which already had the `\InputIfFileExists`. A landscape `longtable`, 28 rows (the blueprint at
`b435631` has 28 tests, `:1261-1359`; the read-report's "thirty" is wrong): number, title in the
blueprint's words, the witness it names, whether that witness exists on `main` at `b435631`, and
the verdict with its register rows (or, where no row bears on it, the dossier section that
examined it).

Sources: `code-spine.md` §D.1, §E.3 (24-28); `code-layer1.md` §F.2 (7, 13, 14, 15);
`code-pubinput.md` §D.2 (10); `gt-bus.md` §C (1-5, 12, 15, 17, 18, 21, 28); `gt-table-pub.md` §4
C.1 and §E.4 (6-10, 16); `gt-flock-ring.md` §8.4, §8.8 (20, 23); `gt-opening-compile.md` §C.1,
§C.3, §E.1, §E.3, §F.1 (8, 11, 21, 22, 23); `boundary-adaptor.md` §E.2 (19, 24).

Register rows the orchestrator's guesses named differently (the table uses the register's):
test 14 is `R79` (not R82, which is test 7); test 23 is `R58` (not R59, the ledger's
ring-switching row); test 10 is `R54` (not R49); test 24 is `R46` (not R70). Test 22 is the one
test no dossier examined as a test; its row says "not examined as a test" and adds the one fact
a dossier states (the four tags are the chain's, gt-opening-compile §C.1).

Witness exists on `main`: tests 10 (as `#guard`s on the pool), 13, 14 (a tautology), 15, 20, 24
(in part), 25, 26, 27, 28; not built: 1-4, 6, 8, 9, 11, 12, 16-19, 21-23; named wrongly: 5
(`leanIsaTables` exists nowhere), 7 (`sumCube_prodVars` is another lemma, `tableSummand_target`
not built).

## S13. Bare codes in the fragments' prose (done), with the coordinator's addition (1)

Scope: the reviewer's three places (`changes.tex:561-568`, `findings-libraries.tex:82-93`,
`lib-clean.tex:401`), then every row of `probes/lint-report/codes-verdict.tsv` marked `VIOLATION`
other than `Layer N`, `acceptance test N`, `decision N` and the register's `R#` (178 rows), and
every row marked `VIOLATION:dossier finding code` (71), then a fresh scan of all fragments
(verbatim blocks, `\code`/`\lean`/`\file`/`\bndc`/`\texttt`, labels and comments blanked) for
codes written or added since the lint ran (the orchestrator's new rows R141–R143 and N116, and my
own insertions). Rule applied: the name first, the code in parentheses after it.

What was done, by kind:

- **The obligations tree's two-letter dossier codes** (CS, TP, GB, FR, LT, DD, AK, LO, PI; 71 in
  the lint, all gone): each replaced by the register row that states the finding, as `\code{R#}`.
  The mapping (from `probes/register/staging.md`, where the codes were born, matched to the
  register's "Where" column): CS1 R5, CS2 R2, CS4 R46, CS5 R40, CS8 R102, CS9 R119; TP1 R2, TP2
  R11, TP3 R12, TP4 R53, TP5 R47, TP6 R36, TP7 R14, TP13 R101; GB1 R7, GB2 R9, GB3 R10, GB6 R47, GB7
  R50, GB8 R51, GB10 R43, GB11 R36; FR1 R14, FR2 R15, FR3 R16, FR4 R17, FR5 R39, FR6 R56, FR7 R57,
  FR9 R59, FR12 R111, FR13 R23, FR14 R106; LT1, LT2, LT3 R23, LT4 R48, LT6 R67, LT7 R114, LT8 R115,
  LT10 R22, LT11 R100, LT13 R25, LT14 R68; DD1 R27, DD15 R77, DD19 R120; AK1 R1, AK2 R4, AK5 R42, AK6
  R96; LO4 R76; PI1 R13, PI2 R12; and code-layer1's "L1-1", "L1-3" R35, R78. "register (GB1, GB2,
  GB11)", a numbering the report does not have, became "register rows R7, R9, R36".
- **Dossier locators "gt-bus G1" … "G17"** (33 in the lint, plus the same in `register.tex`'s
  "Where" column and three `gt-bus.md G7/G15` in `findings-code.tex`, `probes-code.tex`): written
  "gt-bus §G1", a section of the bus dossier (its findings are headed "### G1." under "## G.
  Findings"), so that they no longer read as the sumcheck holes.
- **Target theorems T1–T8 used bare**: named on use ("base proof extraction and completeness
  (T4)", "the base theorem (T4)", "constraint soundness (T1-S)", "witness-generator correctness
  (T2)", "end-to-end soundness (T7)", "recursion (T6)", …; names from `architecture.md:63-70` at
  `b435631`), in `obligations`, `changes`, `register`, `analysis-opening`, `findings-opening`,
  `findings-code`, `findings-boundary`, `probes-code`, `statements-spine`, `surface`.
- **Ledger rows A1–A9 used bare**: "the ledger row on the admitted sumcheck round (A1)", "… on
  the knowledge-soundness composition (A2)", "round-by-round to plain (A3)", "context lifting (A4)",
  "Fiat–Shamir and BCS security (A5)", "WHIR (A7)", "correlated agreement up to Johnson (A8)",
  "ring-switching packing (A9)" (names from the report's own ledger map `tab:docs-map-ledger` and
  the blueprint's ledger at `b435631:253-267`), in `findings-libraries` (the change box of the
  legacy-framework finding, the Fiat–Shamir finding), `findings-opening`, `obligations`,
  `register` (R38's change, R141, R143, N116).
- **Holes used as subjects**: `changes.tex:541-568` (rows G4/P6/P7–P8/K3 and the unowned-obligations
  row, now "the compiled verifier (K3) gains …; the WHIR opening (K1) …; tables and stacking (L1)
  …"), `:1241`, `boundary-chain.tex:225`, `obligations.tex:433`, `register.tex` (the
  unowned-obligations row; R142's title and proposed change), `analysis-opening.tex:331`.
- **Status and review codes used bare**: F3, F9, F13, F14, F18, S12, P3 (leanISA's), E6, C8, A4, A6
  of the earlier reviews, each now after its name.
- **Probe names**: "probe P1/P2/P3a/P3b" → the files `P1Axioms`, `P2Relation`, `P3aSeams`,
  `P3bCommit` (`register.tex` N30–N34, `probes-code.tex:13, 303`, `obligations.tex:80`); the
  sentence "All seven probes (P1 to P6, with P3 in three files)" now lists the eight files by
  name (the directory `probes/code-spine/` holds exactly these eight).
- `conformance.tex:173` "deployment on L1" → "on Ethereum's layer 1".

Left as they are, judged allowed (the lint's own §1.3 agrees for most): codes inside quotations of
the documents (`findings-bus.tex:214` "Finding F9 …", `findings-flock-ring.tex:365, 370`,
`docs-texts.tex:388, 607`, `docs-contradictions.tex`, `findings-docs.tex:119-123, 182, 256, 265`,
`findings-libraries.tex:253, 266`, `layer0-audit.tex:488`, `lib-comppoly.tex:275`,
`transcript-opening.tex:467`, `disagreements-opening.tex:121`, `obligations.tex:268, 632-633`);
codes already in parentheses right after the name (`boundary-chain.tex:49-51, 220, 383`,
`findings-boundary.tex:498`, `changes.tex:224`, the holes table of `obligations.tex:665-681`, its
headings "(Layer 4, holes G1 and G2)", `lib-comppoly.tex:583`); identifiers (`toM3`, `M3Holds`,
"the M3 instance" as the blueprint's heading, `docs-vocabulary.tex:41`); the formula
`\bndc{T4 = verify_knowledgeSound ∘ …}` (`boundary-statements.tex:397`, and quoted "as it stands"
at `findings-boundary.tex:464`); the code inventories (`docs-codes`, `code-index`, the mapping
tables of `docs-proposal`, whose "Target theorems T1 to T8" row is an inventory); a comment in
`index-gen.tex`, which nothing inputs. `findings-flock-ring.tex:370` ("New work of #3 (its gate
F5)") is inside a proposed ledger row and names #3's gate by its code; I did not know the gate's
name and left it.

Edits (S13; one line per edited line, a regex pass over a file is logged per line):

- `gen/obligations.tex:220` | before: `register (GB1, GB2, GB11)` | after: `register rows \code{R7}, \code{R9}, \code{R36}`
- `gen/obligations.tex:567` | before: `(literature LT2; gt-flock-ring FR13)` | after: `(literature and gt-flock-ring, \code{R23})`
- `gen/obligations.tex:439` | before: `(literature LT13)` | after: `(literature, \code{R25})`
- `gen/obligations.tex:638` | before: `(literature E.5, LT11)` | after: `(literature E.5, \code{R100})`
- `gen/obligations.tex:632` | before: `docs-debt DD19` | after: `docs-debt, \code{R120}`
- `gen/obligations.tex:679` | before: `(docs-debt DD15)` | after: `(docs-debt, \code{R77})`
- `gen/obligations.tex:734` | before: `gt-table-pub TP1, TP4; code-spine CS1` | after: `gt-table-pub, \code{R2} and \code{R53}; code-spine, \code{R5}`
- `gen/obligations.tex:228` | before: `gt-bus D.3, G6 (GB6, TP5)` | after: `gt-bus D.3, §G6 (\code{R47})`
- `gen/obligations.tex:157` | before: `(LT7, LT8)` | after: `(\code{R114}, \code{R115})`
- `gen/obligations.tex:271` | before: `(FR1, FR7)` | after: `(\code{R14}, \code{R57})`
- `gen/obligations.tex:272` | before: `(FR4, FR12)` | after: `(\code{R17}, \code{R111})`
- `gen/obligations.tex:175` | before: `(LT6), G.5 (LT14)` | after: `(\code{R67}), G.5 (\code{R68})`
- `gen/obligations.tex:569` | before: `(LT1: without it` | after: `(\code{R23}: without it`
- `gen/obligations.tex:576` | before: `random-oracle model, LT14)` | after: `random-oracle model, \code{R68})`
- `gen/obligations.tex:114` | before: `DD1` | after: `the register rows R27`
- `gen/obligations.tex:115` | before: `DD19` | after: `the register rows R120`
- `gen/obligations.tex:134` | before: `LT10` | after: `the register rows R22`
- `gen/obligations.tex:135` | before: `LT13` | after: `the register rows R25`
- `gen/obligations.tex:136` | before: `LT3` | after: `the register rows R23`
- `gen/obligations.tex:143` | before: `LT10` | after: `the register rows R22`
- `gen/obligations.tex:145` | before: `DD15` | after: `the register rows R77`
- `gen/obligations.tex:147` | before: `LT2` | after: `the register rows R23`
- `gen/obligations.tex:153` | before: `LT4` | after: `the register rows R48`
- `gen/obligations.tex:176` | before: `AK5` | after: `the register rows R42`
- `gen/obligations.tex:188` | before: `CS5` | after: `the register rows R40`
- `gen/obligations.tex:189` | before: `AK2` | after: `the register rows R4`
- `gen/obligations.tex:196` | before: `CS4` | after: `the register rows R46`
- `gen/obligations.tex:197` | before: `CS1` | after: `the register rows R5`
- `gen/obligations.tex:198` | before: `TP13` | after: `the register rows R101`
- `gen/obligations.tex:203` | before: `CS8` | after: `the register rows R102`
- `gen/obligations.tex:204` | before: `CS2 TP1` | after: `the register rows R2, R2`
- `gen/obligations.tex:208` | before: `CS9` | after: `the register rows R119`
- `gen/obligations.tex:209` | before: `AK1` | after: `the register rows R1`
- `gen/obligations.tex:229` | before: `GB3` | after: `the register rows R10`
- `gen/obligations.tex:231` | before: `GB7` | after: `the register rows R50`
- `gen/obligations.tex:232` | before: `GB10` | after: `the register rows R43`
- `gen/obligations.tex:233` | before: `GB8` | after: `the register rows R51`
- `gen/obligations.tex:240` | before: `TP2 TP4 TP6` | after: `the register rows R11, R53, R36`
- `gen/obligations.tex:245` | before: `TP1 CS2` | after: `the register rows R2, R2`
- `gen/obligations.tex:252` | before: `PI2 TP3` | after: `the register rows R12, R12`
- `gen/obligations.tex:254` | before: `PI1` | after: `the register rows R13`
- `gen/obligations.tex:271` | before: `TP7` | after: `the register rows R14`
- `gen/obligations.tex:272` | before: `AK2` | after: `the register rows R4`
- `gen/obligations.tex:273` | before: `FR5` | after: `the register rows R39`
- `gen/obligations.tex:278` | before: `FR6` | after: `the register rows R56`
- `gen/obligations.tex:279` | before: `FR9` | after: `the register rows R59`
- `gen/obligations.tex:280` | before: `FR3 CS8` | after: `the register rows R16, R102`
- `gen/obligations.tex:283` | before: `FR2` | after: `the register rows R15`
- `gen/obligations.tex:284` | before: `FR14` | after: `the register rows R106`
- `gen/obligations.tex:307` | before: `GB1` | after: `the register rows R7`
- `gen/obligations.tex:313` | before: `TP4` | after: `the register rows R53`
- `gen/obligations.tex:329` | before: `AK6` | after: `the register rows R96`
- `gen/obligations.tex:368` | before: `LO4` | after: `the register rows R76`
- `gen/obligations.tex:400` | before: `DD19` | after: `the register rows R120`
- `gen/obligations.tex:568` | before: `LT3` | after: `the register rows R23`
- `gen/obligations.tex:126` | before: `gt-bus B, G4, G9` | after: `gt-bus B, §G4, §G9`
- `gen/obligations.tex:197` | before: `gt-bus D.4, G4` | after: `gt-bus D.4, §G4`
- `gen/obligations.tex:204` | before: `gt-bus E.4, G10.` | after: `gt-bus E.4, §G10.`
- `gen/obligations.tex:220` | before: `gt-bus A.3, A.4, E.1, G1, G2, G8, G11` | after: `gt-bus A.3, A.4, E.1, §G1, §G2, §G8, §G11`
- `gen/obligations.tex:221` | before: `gt-bus E.2, G10.` | after: `gt-bus E.2, §G10.`
- `gen/obligations.tex:226` | before: `gt-bus B (check 12), G13` | after: `gt-bus B (check 12), §G13`
- `gen/obligations.tex:227` | before: `gt-bus D.3, D.4, G1, G2, G12.` | after: `gt-bus D.3, D.4, §G1, §G2, §G12.`
- `gen/obligations.tex:229` | before: `gt-bus G3 (` | after: `gt-bus §G3 (`
- `gen/obligations.tex:231` | before: `gt-bus G7 (` | after: `gt-bus §G7 (`
- `gen/obligations.tex:232` | before: `gt-bus G10 (` | after: `gt-bus §G10 (`
- `gen/obligations.tex:233` | before: `gt-bus G8 (` | after: `gt-bus §G8 (`
- `gen/obligations.tex:240` | before: `gt-bus G16.` | after: `gt-bus §G16.`
- `gen/obligations.tex:307` | before: `gt-bus G1 (` | after: `gt-bus §G1 (`
- `gen/obligations.tex:335` | before: `gt-bus A.4, D.4, G1, G2, G12.` | after: `gt-bus A.4, D.4, §G1, §G2, §G12.`
- `gen/obligations.tex:337` | before: `gt-bus G17). Its leaves: the sumcheck of 2.5.1 in its normalized variant` | after: `gt-bus §G17). Its leaves: the sumcheck of 2.5.1 in its normalized variant`
- `gen/obligations.tex:392` | before: `gt-bus G4.` | after: `gt-bus §G4.`
- `gen/obligations.tex:477` | before: `gt-bus G2` | after: `gt-bus §G2`
- `gen/obligations.tex:478` | before: `gt-bus G1, D.3` | after: `gt-bus §G1, D.3`
- `gen/obligations.tex:479` | before: `gt-bus G12` | after: `gt-bus §G12`
- `gen/obligations.tex:480` | before: `gt-bus G6` | after: `gt-bus §G6`
- `gen/obligations.tex:667` | before: `gt-bus G14)` | after: `gt-bus §G14)`
- `gen/obligations.tex:668` | before: `gt-bus G3)` | after: `gt-bus §G3)`
- `gen/obligations.tex:672` | before: `gt-bus G11)` | after: `gt-bus §G11)`
- `gen/obligations.tex:734` | before: `gt-bus G7, G10` | after: `gt-bus §G7, §G10`
- `gen/register.tex:55` | before: `gt-bus G1 (` | after: `gt-bus §G1 (`
- `gen/register.tex:59` | before: `gt-bus G2 (` | after: `gt-bus §G2 (`
- `gen/register.tex:61` | before: `gt-bus G3 (` | after: `gt-bus §G3 (`
- `gen/register.tex:63` | before: `gt-bus G16 (` | after: `gt-bus §G16 (`
- `gen/register.tex:107` | before: `gt-bus G4 (` | after: `gt-bus §G4 (`
- `gen/register.tex:113` | before: `gt-bus G11 (` | after: `gt-bus §G11 (`
- `gen/register.tex:117` | before: `gt-bus G5 (` | after: `gt-bus §G5 (`
- `gen/register.tex:171` | before: `gt-bus.md G1)` | after: `gt-bus.md §G1)`
- `gen/register.tex:181` | before: `gt-bus.md G2)` | after: `gt-bus.md §G2)`
- `gen/register.tex:186` | before: `gt-bus.md G3)` | after: `gt-bus.md §G3)`
- `gen/register.tex:301` | before: `gt-bus.md G4` | after: `gt-bus.md §G4`
- `gen/register.tex:326` | before: `gt-bus.md G5)` | after: `gt-bus.md §G5)`
- `gen/register.tex:383` | before: `gt-bus G10 (` | after: `gt-bus §G10 (`
- `gen/register.tex:391` | before: `gt-bus G6 (` | after: `gt-bus §G6 (`
- `gen/register.tex:397` | before: `gt-bus G7 (` | after: `gt-bus §G7 (`
- `gen/register.tex:399` | before: `gt-bus G8 (` | after: `gt-bus §G8 (`
- `gen/register.tex:401` | before: `gt-bus G12 (` | after: `gt-bus §G12 (`
- `gen/register.tex:419` | before: `gt-bus G9 (` | after: `gt-bus §G9 (`
- `gen/register.tex:481` | before: `gt-bus G14 (` | after: `gt-bus §G14 (`
- `gen/register.tex:487` | before: `gt-bus G13 (` | after: `gt-bus §G13 (`
- `gen/register.tex:513` | before: `gt-bus G15 (` | after: `gt-bus §G15 (`
- `gen/register.tex:517` | before: `gt-bus G17 (` | after: `gt-bus §G17 (`
- `gen/obligations.tex:45` | before: `(\bndc{docs/architecture.md}'s T4 and its obligation map;` | after: `(\bndc{docs/architecture.md}'s base proof extraction and completeness (T4) and its obligation map;`
- `gen/obligations.tex:95` | before: `\bndc{docs/architecture.md}'s T4 has the right decomposition` | after: `\bndc{docs/architecture.md}'s base proof extraction and completeness (T4) has the right decomposition`
- `gen/obligations.tex:95` | before: `drops \bndc{WellFormedBytecode} at T4, and lacks` | after: `drops \bndc{WellFormedBytecode} at that theorem, and lacks`
- `gen/obligations.tex:95` | before: `its completeness dual (T2 with the honest prover, resource conditions recorded)` | after: `its completeness dual (witness-generator correctness, T2, with the honest prover, resource conditions recorded)`
- `gen/obligations.tex:103` | before: `which are the proof-system half of target T4 (\code{arch:261-275})` | after: `which are the proof-system half of the target theorem base proof extraction and completeness (T4, \code{arch:261-275})`
- `gen/obligations.tex:111` | before: `(Layer 13, the proof-system half of T4)}` | after: `(Layer 13, the proof-system half of the base theorem, T4)}`
- `gen/obligations.tex:114` | before: `\emph{Feeds:} T4, T7 through T5 and T6 (recursion consumes the extracted witness).` | after: `\emph{Feeds:} base proof extraction and completeness (T4), and end-to-end soundness (T7) through recursive-verifier correctness (T5) and recursion (T6), which consumes the extracted witness.`
- `gen/obligations.tex:115` | before: `\emph{Feeds:} T4's completeness half, T8.` | after: `\emph{Feeds:} the completeness half of base proof extraction and completeness (T4), and end-to-end completeness (T8).`
- `gen/obligations.tex:115` | before: `needs a witness generator (T2, out of scope)` | after: `needs a witness generator (witness-generator correctness, T2, out of scope)`
- `gen/obligations.tex:398` | before: `\bndc{leanisa-blueprint.md:1156-1177}; T1-S).` | after: `\bndc{leanisa-blueprint.md:1156-1177}; the soundness half of arithmetization and ISA equivalence, T1-S).`
- `gen/obligations.tex:399` | before: `AssignmentRepresents w t}; T1-C).` | after: `AssignmentRepresents w t}; the completeness half of arithmetization and ISA equivalence, T1-C).`
- `gen/obligations.tex:400` | before: `\textbf{2.6.8 The witness generator} (T2, \bndc{witnessGen_correct},` | after: `\textbf{2.6.8 The witness generator} (witness-generator correctness, T2; \bndc{witnessGen_correct},`
- `gen/obligations.tex:400` | before: `T4's completeness composes T1-C instead.` | after: `the base theorem's completeness composes constraint completeness (T1-C) instead.`
- `gen/obligations.tex:425` | before: `& the guest owner (T3) &` | after: `& the guest owner (exact guest correctness, T3) &`
- `gen/obligations.tex:428` | before: `& O (T2, out of scope) &` | after: `& O (witness-generator correctness, T2, out of scope) &`
- `gen/obligations.tex:613` | before: `the target ladder's T4 (\code{arch:261-275})` | after: `the target ladder's base proof extraction and completeness (T4, \code{arch:261-275})`
- `gen/obligations.tex:629` | before: `extraction into the arithmetization's relation, then T1-S)` | after: `extraction into the arithmetization's relation, then constraint soundness, T1-S)`
- `gen/obligations.tex:630` | before: `\bndc{WellFormedBytecode} of T1-S in the composed statement (\bndc{arch:224-228} states it for T1 and drops it at T4)` | after: `\bndc{WellFormedBytecode} of constraint soundness (T1-S) in the composed statement (\bndc{arch:224-228} states it for arithmetization and ISA equivalence, T1, and drops it at the base theorem, T4)`
- `gen/obligations.tex:632` | before: `Layer 13 composes T1-C (an existence theorem) instead of T2 and` | after: `Layer 13 composes constraint completeness (T1-C, an existence theorem) instead of witness-generator correctness (T2) and`
- `gen/obligations.tex:637` | before: `(\bndc{arch:332-335}, for T6)` | after: `(\bndc{arch:332-335}, for recursion, T6)`
- `gen/obligations.tex:638` | before: `T1–T8 refine the six obligations` | after: `The eight target theorems (T1–T8) refine the six obligations`
- `gen/obligations.tex:681` | before: `T4 (K4) & 2.0 &` | after: `the base theorems (K4) & 2.0 &`
- `gen/obligations.tex:308` | before: `which the blueprint's ledger row A1 omits.` | after: `which the blueprint's ledger row on the admitted sumcheck round (A1) omits.`
- `gen/obligations.tex:629` | before: `T4 first proves ``\bndc{BaseVerifier.Accep` | after: `The base theorem (T4) first proves ``\bndc{BaseVerifier.Accep`
- `gen/register.tex:97` | before: `(and of \texttt{docs/\allowbreak{}architecture.\allowbreak{}md}'s T4, which it transcribes)` | after: `(and of the base theorem, T4, of \texttt{docs/\allowbreak{}architecture.\allowbreak{}md}, which it transcribes)`
- `gen/register.tex:246` | before: `rewrite ledger row A5: obligations` | after: `rewrite the ledger row on Fiat–Shamir and BCS security (A5): obligations`
- `gen/register.tex:326` | before: `delete F9 and \code{st:164}` | after: `delete the status's finding on the Python caps (F9) and \code{st:164}`
- `gen/register.tex:331` | before: `column (K3, K1, a new list-binding hole, L1, I1, I2, P5, G1, S), as §5.1 assigns` | after: `column (the compiled verifier, K3; the WHIR opening, K1; a new list-binding hole; tables and stacking, L1; Clean expressions as polynomials, I1; the adaptor, I2; the public-input phase, P5; the sumcheck, G1; the spine, S), as §5.1 assigns`
- `gen/register.tex:665` | before: `code-spine §0 item 1; probe P1 &` | after: `code-spine §0 item 1; probe \code{P1Axioms} &`
- `gen/register.tex:669` | before: `code-spine §D.1; probe P2 &` | after: `code-spine §D.1; probe \code{P2Relation} &`
- `gen/register.tex:671` | before: `code-spine §D.2; probe P3a &` | after: `code-spine §D.2; probe \code{P3aSeams} &`
- `gen/register.tex:673` | before: `code-spine §D.5, §D.6; probes P3b, P1 &` | after: `code-spine §D.5, §D.6; probes \code{P3bCommit}, \code{P1Axioms} &`
- `gen/register.tex:805` | before: `the pointwise composition of T4 typechecks` | after: `the pointwise composition of the base theorem (T4) typechecks`
- `gen/register.tex:1059` | before: `The check corrected G1's wording` | after: `The check corrected the wording of gt-bus §G1`
- `gen/register.tex:125` (2 occurrences) | before: `Holes G1 and G2 (the sumcheck) name upstream sources` | after: `The sumcheck's two holes (G1, G2) name upstream sources`
- `gen/register.tex:346` | before: `\fhead{Proposed change} G1: the typed \code{Native}` | after: `\fhead{Proposed change} for its definition and completeness (G1), the typed \code{Native}`
- `gen/register.tex:346` | before: `for the honest algebra; G2: nothing upstream,` | after: `for the honest algebra; for its knowledge soundness (G2), nothing upstream,`
- `gen/changes.tex:357` | before: `(the fixture's loader, T7's \lean{PublicInput.encode})` | after: `(the fixture's loader, end-to-end soundness's (T7) \lean{PublicInput.encode})`
- `gen/changes.tex:503` | before: `as what T4 composes, and keep` | after: `as what the base theorem (T4) composes, and keep`
- `gen/changes.tex:504` | before: `and that what T4 waits` | after: `and that what the base theorem waits`
- `gen/changes.tex:541` | before: `Table, rows G4, P6, P7--P8 (\code{:601}, \code{:609-610}) &` | after: `Table, the rows on the fingerprint (G4), the Flock phase (P6) and the opening phase (P7--P8) (\code{:601}, \code{:609-610}) &`
- `gen/changes.tex:546` | before: `Table, rows P6 and K3 (\code{:609}, \code{:614}) &` | after: `Table, the rows on the Flock phase (P6) and the compiled verifier (K3) (\code{:609}, \code{:614}) &`
- `gen/changes.tex:553` | before: `Table, row K3 (\code{:614}) &` | after: `Table, the row on the compiled verifier (K3) (\code{:614}) &`
- `gen/changes.tex:562` | before: `nearest hole's products: K3 gains the Merkle compilation, the chain lemma, the state-restoration step, the grinding model, the hash and program-hash terms, the family composition, the canonical-encoding checks; K1 the $\K$-valuedness lemma and \lean{encode} over $\E$; a new hole \enquote{list-bindin …` | after: `nearest hole's products: the compiled verifier (K3) gains the Merkle compilation, the chain lemma, the state-restoration step, the grinding model, the hash and program-hash terms, the family composition, the canonical-encoding checks; the WHIR opening (K1) the $\K$-valuedness lemma and \lean{encode} …`
- `gen/changes.tex:694` | before: `and say that neither T4 composition uses it. &` | after: `and say that neither composition of the base theorem (T4) uses it. &`
- `gen/changes.tex:1034` | before: `Layer 13: T4 and the fixtures (\code{:1242-1259})` | after: `Layer 13: the base theorems (T4) and the fixtures (\code{:1242-1259})`
- `gen/changes.tex:1224` | before: `(or T4 takes \lean{hfit} as its hypothesis)` | after: `(or the base theorem (T4) takes \lean{hfit} as its hypothesis)`
- `gen/changes.tex:1237` | before: `BLAKE2S value limbs)}: the protocol status's F3 is another finding. &` | after: `BLAKE2S value limbs)}: the protocol status's finding on the one bus root (F3) is another finding. &`
- `gen/changes.tex:1243` | before: `\enquote{list-binding compilation} between K1 and K3, and the obligations folded` | after: `\enquote{list-binding compilation} between the WHIR opening (K1) and the compiled verifier (K3), and the obligations folded`
- `gen/analysis-opening.tex:76` | before: `the target theorem T4 in \code{architecture.md:264-269}` | after: `the target theorem base proof extraction and completeness (T4) in \code{architecture.md:264-269}`
- `gen/boundary-chain.tex:225` | before: `owed by the phases (holes P1 to P8; the public-input phase, P5, built)` | after: `owed by the phases (their holes, P1 to P8; the public-input phase, P5, is built)`
- `gen/conformance.tex:173` | before: `the report's object is deployment on L1;` | after: `the report's object is deployment on Ethereum's layer 1;`
- `gen/disagreements-opening.tex:102` | before: `(the status file records it, its finding S12)` | after: `(the status file records it, as its finding on grinding per level, S12)`
- `gen/findings-boundary.tex:510` | before: `\bndc{PublicInput.encode} in T7)` | after: `\bndc{PublicInput.encode} in end-to-end soundness, T7)`
- `gen/findings-bus.tex:425` | before: `the seed (the status file's finding on the seed, F14);` | after: `the seed (which the status file records as its finding on the seed, F14);`
- `gen/findings-code.tex:139` | before: `which the review's A6 reads as a property of the toy` | after: `which the earlier review's item on the toy (A6) reads as a property of the toy`
- `gen/findings-code.tex:169` | before: `The status finding (F18) records the divergence` | after: `The status file's finding on the combined public-input check (F18) records the divergence`
- `gen/findings-libraries.tex:324` | before: `Recorded as leanISA status finding E6 at \code{b435631}.` | after: `Recorded in the leanISA status at \code{b435631}, as its finding on the eager instance (E6).`
- `gen/findings-libraries.tex:88` | before: `\begin{change}{the ledger's actions for rows A2 and A3 (\file{protocol-blueprint.md:260-261})}` | after: `\begin{change}{the ledger's actions on the knowledge-soundness composition (A2) and on round-by-round to plain (A3) (\file{protocol-blueprint.md:260-261})}`
- `gen/findings-libraries.tex:89` | before: `\asis A2: \enquote{the port is deleted` | after: `\asis Composition (A2): \enquote{the port is deleted`
- `gen/findings-libraries.tex:89` | before: `when the pin moves past \#615}. A3: \enquote{the plain corollary` | after: `when the pin moves past \#615}. Round-by-round to plain (A3): \enquote{the plain corollary`
- `gen/findings-libraries.tex:91` | before: `\asproposed A2: \enquote{kept until ArkLib` | after: `\asproposed Composition (A2): \enquote{kept until ArkLib`
- `gen/findings-libraries.tex:93` | before: `\lean{ToArkLib} candidate}. A3: \enquote{the plain corollary` | after: `\lean{ToArkLib} candidate}. Round-by-round to plain (A3): \enquote{the plain corollary`
- `gen/findings-libraries.tex:103` | before: `The blueprint's ledger row A5 (\file{:263}) plans` | after: `The blueprint's ledger row on Fiat--Shamir and BCS security (A5, \file{:263}) plans`
- `gen/findings-libraries.tex:122` | before: `\begin{change}{ledger row A5 (\file{protocol-blueprint.md:263}) and` | after: `\begin{change}{the ledger row on Fiat--Shamir and BCS security (A5, \file{protocol-blueprint.md:263}) and`
- `gen/findings-opening.tex:103` | before: `\file{docs/architecture.md}'s target theorem T4, which it transcribes)` | after: `\file{docs/architecture.md}'s target theorem, base proof extraction and completeness (T4), which it transcribes)`
- `gen/findings-opening.tex:107` | before: `\lean{verify_knowledgeSound}, and T4 in \code{architecture.md:264-269}}` | after: `\lean{verify_knowledgeSound}, and the base theorem (T4) in \code{architecture.md:264-269}}`
- `gen/findings-opening.tex:120` | before: `the same repair of T4.` | after: `the same repair of the base theorem (T4).`
- `gen/lib-clean.tex:400` | before: `the \enquote{Clean bridge is plain} convention (leanISA status finding C8) retires` | after: `the \enquote{Clean bridge is plain} convention (recorded in the leanISA status as its finding C8) retires`
- `gen/probes-code.tex:13` | before: `All seven probes (\texttt{P1} to \texttt{P6}, with \texttt{P3} in three files)` | after: `All seven probes (\texttt{P1Axioms}, \texttt{P2Relation}, \texttt{P3aSeams}, \texttt{P3bCommit}, \texttt{P3cExtractor}, \texttt{P4Junk}, \texttt{P5PassThrough}, \texttt{P6Surface}: six probes, the third in three files)`
- `gen/probes-code.tex:303` | before: `re-established by probe P1 for the declarations` | after: `re-established by probe \texttt{P1Axioms} for the declarations`
- `gen/probes-code.tex:2134` | before: `t}, and T4's \texttt{b\allowbreak{}a\allowbreak{}s` | after: `t}, and the base theorem's (T4) \texttt{b\allowbreak{}a\allowbreak{}s`
- `gen/probes-code.tex:2168` | before: `and through it T4's \texttt{b\allowbreak{}a\allowbreak{}s` | after: `and through it the base theorem's (T4) \texttt{b\allowbreak{}a\allowbreak{}s`
- `gen/statements-spine.tex:142` | before: `universes are independent, checked). T4 (\texttt{b` | after: `universes are independent, checked). The base theorem (T4, \texttt{b`
- `gen/statements-spine.tex:142` | before: `What T4 does still wait on is upstream` | after: `What the base theorem does still wait on is upstream`
- `gen/surface.tex:228` | before: `if the named extractor is what T4 must carry` | after: `if the named extractor is what the base theorem (T4) must carry`
- `gen/transcript-opening.tex:732` | before: `(\code{:165-174}; the status file's finding F13)` | after: `(\code{:165-174}; the status file's finding on the bound nonce, F13)`
- `gen/probes-code.tex:13` | before: `All seven probes (\texttt{P1Axioms}, \texttt{P2Relation}, \texttt{P3aSeams}, \texttt{P3bCommit}, \texttt{P3cExtractor}, \texttt{P4Junk}, \texttt{P5PassThrough}, \texttt{P6Surface}: six probes, the third in three files)` | after: `All the spine's probes (\texttt{P1Axioms}, \texttt{P2Relation}, \texttt{P3aSeams}, \texttt{P3bCommit}, \texttt{P3cExtractor}, \texttt{P4Junk}, \texttt{P5PassThrough}, \texttt{P6Surface}, eight files)`
- `gen/changes.tex:600` | before: `would enumerate the field (leanISA finding P3); since CompPoly` | after: `would enumerate the field (the leanISA status's finding on the eager \lean{Fintype}, P3); since CompPoly`
- `gen/changes.tex:1052` | before: `error of the blueprint (and of \file{architecture.md}'s T4) & \sev{major}` | after: `error of the blueprint (and of the base theorem, T4, of \file{architecture.md}) & \sev{major}`
- `gen/findings-libraries.tex:270` | before: `would enumerate the field (leanISA finding P3); since CompPoly` | after: `would enumerate the field (the leanISA status's finding on the eager \lean{Fintype}, P3); since CompPoly`
- `gen/findings-libraries.tex:162` | before: `perfect completeness is admitted too (ledger row A1).` | after: `perfect completeness is admitted too (the ledger row on the admitted sumcheck round, A1).`
- `gen/obligations.tex:80` | before: `(lib-arklib B.1; code-spine P1; probes-rerun 1.0 at the new pin)` | after: `(lib-arklib B.1; code-spine's probe \code{P1Axioms}; probes-rerun 1.0 at the new pin)`
- `gen/obligations.tex:193` | before: `at both pins (ledger A2), and \#615 is open` | after: `at both pins (the ledger row on the composition, A2), and \#615 is open`
- `gen/obligations.tex:229` | before: `lib-arklib B.3 (ledger A4).` | after: `lib-arklib B.3 (the ledger row on context lifting, A4).`
- `gen/obligations.tex:279` | before: `lib-arklib B.3 (ledger A9).` | after: `lib-arklib B.3 (the ledger row on ring-switching packing, A9).`
- `gen/obligations.tex:309` | before: `at both pins (ledger A1). \emph{See:} lib-arklib B.3, F.1.` | after: `at both pins (the ledger row on the admitted sumcheck round, A1). \emph{See:} lib-arklib B.3, F.1.`
- `gen/obligations.tex:308` | before: `\emph{See:} lib-arklib B.3 (row A1).` | after: `\emph{See:} lib-arklib B.3 (its row on the sumcheck round).`
- `gen/obligations.tex:358` | before: `\emph{See:} code-layer1 G.1 (L1-1); gt-flock-ring 8.2.` | after: `\emph{See:} code-layer1 G.1 (\code{R35}); gt-flock-ring 8.2.`
- `gen/obligations.tex:359` | before: `\emph{See:} code-layer1 G.3 (L1-3), B.2` | after: `\emph{See:} code-layer1 G.3 (\code{R78}), B.2`
- `gen/obligations.tex:433` | before: `& O (holes P1 to P8; the public-input phase built) &` | after: `& O (the phase holes, P1 to P8; the public-input phase built) &`
- `gen/register.tex:65` | before: `(decision 15; status finding F18)` | after: `(decision 15; the status's finding on the combined check, F18)`
- `gen/register.tex:127` (2 occurrences) | before: `Ledger A8 and the status's coding-theory row are stale` | after: `The ledger row on correlated agreement up to Johnson (A8) and the status's coding-theory row are stale`
- `gen/register.tex:339` | before: `ledger row A1 names this as the leaf` | after: `the ledger row on the admitted sumcheck round (A1) names this as the leaf`
- `gen/register.tex:341` | before: `\fhead{Proposed change} ledger A1: Layer 4 proves` | after: `\fhead{Proposed change} the ledger row on the admitted sumcheck round (A1): Layer 4 proves`
- `gen/register.tex:393` | before: `(for T4 as stated)` | after: `(for the base theorem, T4, as stated)`
- `gen/register.tex:837` | before: `Ledger rows A2, A4, A5 (the admits), A7 (WHIR absent upstream) and A9 (ring-switching leaves admitted) are confirmed` | after: `The ledger rows on the composition (A2), context lifting (A4) and Fiat--Shamir and BCS security (A5), the admitted ones, on WHIR (A7, absent upstream) and on ring-switching packing (A9, leaves admitted) are confirmed`
- `gen/analysis-opening.tex:87` | before: `\lean{constraintSoundness} (the target theorem T1) then gives` | after: `\lean{constraintSoundness} (the soundness half of arithmetization and ISA equivalence, T1) then gives`
- `gen/analysis-opening.tex:331` | before: `Theorem B.7 in Lean (the hole for it, K1);` | after: `Theorem B.7 in Lean (the WHIR opening's hole, K1);`
- `gen/findings-code.tex:134` | before: `Layer 13 consumes it. What T4 waits on is` | after: `Layer 13 consumes it. What the base theorem (T4) waits on is`
- `gen/findings-code.tex:281` | before: `(\texttt{gt-{}bus.\allowbreak{}md} G7).` | after: `(\texttt{gt-{}bus.\allowbreak{}md} §G7).`
- `gen/findings-code.tex:398` | before: `(B.6, \texttt{gt-{}bus.\allowbreak{}md} G15;` | after: `(B.6, \texttt{gt-{}bus.\allowbreak{}md} §G15;`
- `gen/findings-opening.tex:144` | before: `\lean{verify_knowledgeSound}, the ledger row (A5, \code{bp:263}) and` | after: `\lean{verify_knowledgeSound}, the ledger row on Fiat--Shamir and BCS security (A5, \code{bp:263}) and`
- `gen/findings-opening.tex:160` | before: `In the ledger row (A5, \code{bp:263}) and` | after: `In the ledger row on Fiat--Shamir and BCS security (A5, \code{bp:263}) and`
- `gen/probes-code.tex:3150` | before: `(\texttt{gt-{}bus.\allowbreak{}md} A.5, G7;` | after: `(\texttt{gt-{}bus.\allowbreak{}md} A.5, §G7;`
- `gen/findings-code.tex:211` | before: `(the earlier review's item A4, kept)` | after: `(the earlier review's item on the message type, A4, kept)`
- `gen/findings-code.tex:139` | before: `which the earlier review's item on the toy (A6) reads as` | after: `which the earlier review's item on the pass-through's missing knowledge half (A6) reads as`

## The coordinator's addition (2): dossier section codes in headings and finding titles (done)

78 titles rewritten so that the trailing dossier code reads as one: "… (C.7)" → "… (dossier
section C.7)": the 57 headings of `probes/lint-report/headings-dossier-codes.txt` (in
`statements-spine`, `conformance`, `surface`, `probes-code`), two `\paragraph` titles of
`conformance.tex` (B.1, B.2) the list omits, and the 19 finding titles of `findings-code.tex`
ending "(G.1)" … "(G.10)". Labels are unchanged. In the same spirit: the heading "Three facts
behind sections B and C.7" → "… behind dossier sections B and C.7"; "The counting script of
section E" → "… of dossier section E"; `probes-code.tex:302` "sections B and C" → "the dossier's
sections B and C"; `conformance.tex:50` "that section B counts as load-bearing" → "that the count
of the audit surface (`\cref{sec:gen-spine-B2}`) finds load-bearing"; the heading
"`Refinement` and what T4 needs" → "… what the base theorem (T4) needs".

Edits:

- `gen/conformance.tex:291` | before: `Elsewhere in the blueprint, touching Layer 1 (F.4)` | after: `Elsewhere in the blueprint, touching Layer 1 (dossier section F.4)`
- `gen/conformance.tex:282` | before: `The interface list (\texttt{:1386-{}1406}) (F.3)` | after: `The interface list (\texttt{:1386-{}1406}) (dossier section F.3)`
- `gen/conformance.tex:273` | before: `Acceptance tests 7, 13, 14, 15 (F.2)` | after: `Acceptance tests 7, 13, 14, 15 (dossier section F.2)`
- `gen/conformance.tex:240` | before: `The Layer 1 sketch (\texttt{p\allowbreak{}r\allowbreak{}o\allowbreak{}t\allowbreak{}o\allowbreak{}c\allowbreak{}o\allowbreak{}l\allowbreak{}-{}\allowbreak{}b\allowbreak{}l\allowbreak{}u\allowbreak{}e\ …` | after: `The Layer 1 sketch (\texttt{p\allowbreak{}r\allowbreak{}o\allowbreak{}t\allowbreak{}o\allowbreak{}c\allowbreak{}o\allowbreak{}l\allowbreak{}-{}\allowbreak{}b\allowbreak{}l\allowbreak{}u\allowbreak{}e\ …`
- `gen/conformance.tex:220` | before: `Statement checks (F)` | after: `Statement checks (dossier section F)`
- `gen/conformance.tex:181` | before: `The flag \texttt{PublicLine.sent} (E)` | after: `The flag \texttt{PublicLine.sent} (dossier section E)`
- `gen/conformance.tex:175` | before: `The honest prover's values (B.2)` | after: `The honest prover's values (dossier section B.2)`
- `gen/conformance.tex:144` | before: `Which verifier do the theorems describe (B.1)` | after: `Which verifier do the theorems describe (dossier section B.1)`
- `gen/conformance.tex:116` | before: `The Lean verifier against the specification, the Rust, the Python and the recursion guest (B)` | after: `The Lean verifier against the specification, the Rust, the Python and the recursion guest (dossier section B)`
- `gen/conformance.tex:91` | before: `Acceptance tests 24 to 28 against the code (E.3)` | after: `Acceptance tests 24 to 28 against the code (dossier section E.3)`
- `gen/conformance.tex:52` | before: `The blueprint's other statements of the same objects (E.2)` | after: `The blueprint's other statements of the same objects (dossier section E.2)`
- `gen/conformance.tex:13` | before: `The Lean sketch (\texttt{:442-{}554}) against the code, declaration by declaration (E.1)` | after: `The Lean sketch (\texttt{:442-{}554}) against the code, declaration by declaration (dossier section E.1)`
- `gen/findings-code.tex:402` | before: `The upgrade to \texttt{144c5aa} (G.10)` | after: `The upgrade to \texttt{144c5aa} (dossier section G.10)`
- `gen/findings-code.tex:397` | before: `Disagreements between leanVM's sources (G.10)` | after: `Disagreements between leanVM's sources (dossier section G.10)`
- `gen/findings-code.tex:392` | before: `\texttt{idxColumnEval} is efficient (G.10)` | after: `\texttt{idxColumnEval} is efficient (dossier section G.10)`
- `gen/findings-code.tex:387` | before: `Unused or duplicated declarations (G.10)` | after: `Unused or duplicated declarations (dossier section G.10)`
- `gen/findings-code.tex:382` | before: `\texttt{Layout.\allowbreak{}comap} accepts a non-injective renaming (G.10)` | after: `\texttt{Layout.\allowbreak{}comap} accepts a non-injective renaming (dossier section G.10)`
- `gen/findings-code.tex:367` | before: `Acceptance test 7 names the wrong lemma and a witness that does not exist (G.9)` | after: `Acceptance test 7 names the wrong lemma and a witness that does not exist (dossier section G.9)`
- `gen/findings-code.tex:355` | before: `\texttt{Protocol/\allowbreak{}Basic.\allowbreak{}lean} imports the arithmetization and is not a listed exception of the wall (G.8)` | after: `\texttt{Protocol/\allowbreak{}Basic.\allowbreak{}lean} imports the arithmetization and is not a listed exception of the wall (dossier section G.8)`
- `gen/findings-code.tex:343` | before: `\texttt{BlockClaims.\allowbreak{}lean} has no consumer (G.7)` | after: `\texttt{BlockClaims.\allowbreak{}lean} has no consumer (dossier section G.7)`
- `gen/findings-code.tex:331` | before: `The interface list omits load-bearing Layer 1 names and mislabels three (G.6)` | after: `The interface list omits load-bearing Layer 1 names and mislabels three (dossier section G.6)`
- `gen/findings-code.tex:316` | before: `Acceptance test 15 overclaims (G.5)` | after: `Acceptance test 15 overclaims (dossier section G.5)`
- `gen/findings-code.tex:296` | before: `Acceptance test 14 names a tautology as its witness; \texttt{bytecodeColumn\_\allowbreak{}slot} and its tests prove nothing about the layout (G.4)` | after: `Acceptance test 14 names a tautology as its witness; \texttt{bytecodeColumn\_\allowbreak{}slot} and its tests prove nothing about the layout (dossier section G.4)`
- `gen/findings-code.tex:278` | before: `The order of equal-size blocks is pinned by no statement, definition or test before the compiled verifier (G.3)` | after: `The order of equal-size blocks is pinned by no statement, definition or test before the compiled verifier (dossier section G.3)`
- `gen/findings-code.tex:262` | before: `\texttt{leanIsaInstance\_\allowbreak{}fits} cannot be stated as written, and is needed before the instance, not after (G.2)` | after: `\texttt{leanIsaInstance\_\allowbreak{}fits} cannot be stated as written, and is needed before the instance, not after (dossier section G.2)`
- `gen/findings-code.tex:237` | before: `The strided reader of the eighteen BLAKE2S limb columns exists nowhere and is assigned to no layer (G.1)` | after: `The strided reader of the eighteen BLAKE2S limb columns exists nowhere and is assigned to no layer (dossier section G.1)`
- `gen/findings-code.tex:210` | before: `The message type is wider than the transcript (G.5)` | after: `The message type is wider than the transcript (dossier section G.5)`
- `gen/findings-code.tex:200` | before: `\texttt{PublicLine.\allowbreak{}sent} is pinned by prose only (G.4)` | after: `\texttt{PublicLine.\allowbreak{}sent} is pinned by prose only (dossier section G.4)`
- `gen/findings-code.tex:185` | before: `The top limb is checked by the instance's third line and enforced by the adaptor's theorem, which is not built; the acceptance test names the wrong witness (G.3)` | after: `The top limb is checked by the instance's third line and enforced by the adaptor's theorem, which is not built; the acceptance test names the wrong witness (dossier section G.3)`
- `gen/findings-code.tex:168` | before: `The theorems are about a verifier none of the three executable verifiers runs, and the debt is assigned to a layer that cannot pay it (G.2)` | after: `The theorems are about a verifier none of the three executable verifiers runs, and the debt is assigned to a layer that cannot pay it (dossier section G.2)`
- `gen/findings-code.tex:149` | before: `The check on the public-input message is not load-bearing for any theorem of the phase (G.1)` | after: `The check on the public-input message is not load-bearing for any theorem of the phase (dossier section G.1)`
- `gen/probes-code.tex:3142` | before: `Not done, unverified, and contradictions with the brief (J)` | after: `Not done, unverified, and contradictions with the brief (dossier section J)`
- `gen/probes-code.tex:3083` | before: `The counting script of section E (\texttt{count2.\allowbreak{}py}, scratch, not a probe) (I.7)` | after: `The counting script of section E (\texttt{count2.\allowbreak{}py}, scratch, not a probe) (dossier section I.7)`
- `gen/probes-code.tex:3006` | before: `\texttt{StridedProbe.\allowbreak{}lean}, run with the old pin's Lean binary, not through Lake (I.6)` | after: `\texttt{StridedProbe.\allowbreak{}lean}, run with the old pin's Lean binary, not through Lake (dossier section I.6)`
- `gen/probes-code.tex:2937` | before: `\texttt{DuplicatesProbe.\allowbreak{}lean}, run with the old pin's Lean binary, not through Lake (I.5)` | after: `\texttt{DuplicatesProbe.\allowbreak{}lean}, run with the old pin's Lean binary, not through Lake (dossier section I.5)`
- `gen/probes-code.tex:2691` | before: `\texttt{ValuesProbe.\allowbreak{}lean} (I.4)` | after: `\texttt{ValuesProbe.\allowbreak{}lean} (dossier section I.4)`
- `gen/probes-code.tex:2509` | before: `\texttt{values.\allowbreak{}py} (I.3)` | after: `\texttt{values.\allowbreak{}py} (dossier section I.3)`
- `gen/probes-code.tex:2344` | before: `\texttt{OffsetsProbe.\allowbreak{}lean} (I.2)` | after: `\texttt{OffsetsProbe.\allowbreak{}lean} (dossier section I.2)`
- `gen/probes-code.tex:2225` | before: `\texttt{offsets.\allowbreak{}py} (I.1)` | after: `\texttt{offsets.\allowbreak{}py} (dossier section I.1)`
- `gen/probes-code.tex:2205` | before: `Layer 1's probes (I)` | after: `Layer 1's probes (dossier section I)`
- `gen/probes-code.tex:2199` | before: `In the deployed verifiers: the top limb rides no scalar and is pooled at \texttt{0} (D.3)` | after: `In the deployed verifiers: the top limb rides no scalar and is pooled at \texttt{0} (dossier section D.3)`
- `gen/probes-code.tex:2170` | before: `In the tests: acceptance test 10's witness exists today (D.2)` | after: `In the tests: acceptance test 10's witness exists today (dossier section D.2)`
- `gen/probes-code.tex:2104` | before: `In the phase and the spine: no (D.1)` | after: `In the phase and the spine: no (dossier section D.1)`
- `gen/probes-code.tex:2100` | before: `The public-input phase: the top limb, along the chain (D)` | after: `The public-input phase: the top limb, along the chain (dossier section D)`
- `gen/probes-code.tex:2047` | before: `Mutation 4b: the deployed verifier (the words' equation, the prover's values pooled). Sound at \texttt{1/\allowbreak{}|E|}, by a different argument; the key lemma run, the phase not written (C.13)` | after: `Mutation 4b: the deployed verifier (the words' equation, the prover's values pooled). Sound at \texttt{1/\allowbreak{}|E|}, by a different argument; the key lemma run, the phase not written (dossier s …`
- `gen/probes-code.tex:2039` | before: `Mutation 6: the claims pooled at a wrong point. Caught by completeness (and by knowledge soundness); argued on paper, not written (C.12)` | after: `Mutation 6: the claims pooled at a wrong point. Caught by completeness (and by knowledge soundness); argued on paper, not written (dossier section C.12)`
- `gen/probes-code.tex:2013` | before: `Mutation 8: an extra check leanVM does not make. Caught by completeness; written, not run (C.11)` | after: `Mutation 8: an extra check leanVM does not make. Caught by completeness; written, not run (dossier section C.11)`
- `gen/probes-code.tex:1964` | before: `Mutation 7: a wrong check (the cells swapped). Caught by completeness ONLY IF the honest prover is held fixed; probe 7a written, not run (C.10)` | after: `Mutation 7: a wrong check (the cells swapped). Caught by completeness ONLY IF the honest prover is held fixed; probe 7a written, not run (dossier section C.10)`
- `gen/probes-code.tex:1958` | before: `The probe environment was lost at 09:18 on 2026-09-30 (read this before trusting \enquote{not run}) (C.9)` | after: `The probe environment was lost at 09:18 on 2026-09-30 (read this before trusting \enquote{not run}) (dossier section C.9)`
- `gen/probes-code.tex:1925` | before: `Mutation 5: the claim of a line whose value is not sent is not pooled. CAUGHT by knowledge soundness (C.8)` | after: `Mutation 5: the claim of a line whose value is not sent is not pooled. CAUGHT by knowledge soundness (dossier section C.8)`
- `gen/probes-code.tex:1896` | before: `Mutation 3b: first value checked, the prover's values pooled. CAUGHT by knowledge soundness (C.7)` | after: `Mutation 3b: first value checked, the prover's values pooled. CAUGHT by knowledge soundness (dossier section C.7)`
- `gen/probes-code.tex:1811` | before: `Mutation 2: no check, the prover's values pooled. CAUGHT by knowledge soundness (C.6)` | after: `Mutation 2: no check, the prover's values pooled. CAUGHT by knowledge soundness (dossier section C.6)`
- `gen/probes-code.tex:1774` | before: `Mutations 3a and 4a: a weaker check, the lines' values pooled. NOT CAUGHT (C.5)` | after: `Mutations 3a and 4a: a weaker check, the lines' values pooled. NOT CAUGHT (dossier section C.5)`
- `gen/probes-code.tex:1681` | before: `The general form: any message, any check the message passes. NOT CAUGHT (C.4)` | after: `The general form: any message, any check the message passes. NOT CAUGHT (dossier section C.4)`
- `gen/probes-code.tex:1609` | before: `Mutation 1: the check removed, the lines' values pooled. NOT CAUGHT (C.3)` | after: `Mutation 1: the check removed, the lines' values pooled. NOT CAUGHT (dossier section C.3)`
- `gen/probes-code.tex:1561` | before: `Results so far (C.2)` | after: `Results so far (dossier section C.2)`
- `gen/probes-code.tex:1465` | before: `The two refutation lemmas (shared by the probes) (C.1)` | after: `The two refutation lemmas (shared by the probes) (dossier section C.1)`
- `gen/probes-code.tex:1382` | before: `Method (C.0)` | after: `Method (dossier section C.0)`
- `gen/probes-code.tex:1376` | before: `The public-input phase: mutation probes (C)` | after: `The public-input phase: mutation probes (dossier section C)`
- `gen/probes-code.tex:283` | before: `What was not verified, and what would verify it (G)` | after: `What was not verified, and what would verify it (dossier section G)`
- `gen/probes-code.tex:273` | before: `Three facts behind sections B and C.7 (D.7)` | after: `Three facts behind sections B and C.7 (dossier section D.7)`
- `gen/probes-code.tex:254` | before: `The commit phase's security (D.6)` | after: `The commit phase's security (dossier section D.6)`
- `gen/probes-code.tex:207` | before: `The extractor (D.5)` | after: `The extractor (dossier section D.5)`
- `gen/probes-code.tex:192` | before: `What a layout can do (D.4)` | after: `What a layout can do (dossier section D.4)`
- `gen/probes-code.tex:101` | before: `\texttt{Phases.\allowbreak{}Complete} and \texttt{Phases.\allowbreak{}Security} (D.3)` | after: `\texttt{Phases.\allowbreak{}Complete} and \texttt{Phases.\allowbreak{}Security} (dossier section D.3)`
- `gen/probes-code.tex:70` | before: `The seams, one by one (D.2)` | after: `The seams, one by one (dossier section D.2)`
- `gen/probes-code.tex:50` | before: `\texttt{M3Holds} on the toy instance (D.1)` | after: `\texttt{M3Holds} on the toy instance (dossier section D.1)`
- `gen/probes-code.tex:8` | before: `The spine: non-vacuity by probe (D)` | after: `The spine: non-vacuity by probe (dossier section D)`
- `gen/statements-spine.tex:129` | before: `\texttt{Refinement} and what T4 needs (C.7)` | after: `\texttt{Refinement} and what T4 needs (dossier section C.7)`
- `gen/statements-spine.tex:125` | before: `The quantification over \texttt{σ}, \texttt{init}, \texttt{impl} (C.6)` | after: `The quantification over \texttt{σ}, \texttt{init}, \texttt{impl} (dossier section C.6)`
- `gen/statements-spine.tex:121` | before: `\texttt{piopError} (C.5)` | after: `\texttt{piopError} (dossier section C.5)`
- `gen/statements-spine.tex:91` | before: `What the master theorems are, and what remains (C.4)` | after: `What the master theorems are, and what remains (dossier section C.4)`
- `gen/statements-spine.tex:71` | before: `The seams, as input and output relations (C.3)` | after: `The seams, as input and output relations (dossier section C.3)`
- `gen/statements-spine.tex:53` | before: `\texttt{Layout} (C.2)` | after: `\texttt{Layout} (dossier section C.2)`
- `gen/statements-spine.tex:8` | before: `\texttt{M3Holds}, clause by clause, against the pinned specification (C.1)` | after: `\texttt{M3Holds}, clause by clause, against the pinned specification (dossier section C.1)`
- `gen/surface.tex:223` | before: `Proposals to reduce it (B.3)` | after: `Proposals to reduce it (dossier section B.3)`
- `gen/surface.tex:49` | before: `The count (B.2)` | after: `The count (dossier section B.2)`
- `gen/surface.tex:37` | before: `Method (B.1)` | after: `Method (dossier section B.1)`
- `gen/probes-code.tex:273` | before: `Three facts behind sections B and C.7 (dossier section D.7)` | after: `Three facts behind dossier sections B and C.7 (dossier section D.7)`
- `gen/probes-code.tex:3083` | before: `The counting script of section E (` | after: `The counting script of dossier section E (`
- `gen/statements-spine.tex:129` | before: `\texttt{Refinement} and what T4 needs (dossier section C.7)` | after: `\texttt{Refinement} and what the base theorem (T4) needs (dossier section C.7)`
- `gen/conformance.tex:50` | before: `is false of the fourteen of these that section B counts as load-bearing` | after: `is false of the fourteen of these that the count of the audit surface (\cref{sec:gen-spine-B2}) finds load-bearing`
- `gen/probes-code.tex:302` | before: `and the numbers in sections B and C are from that run` | after: `and the numbers in the dossier's sections B and C are from that run`

