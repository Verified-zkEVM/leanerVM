# fix-fragments: the reviewer's fixes to the generated fragments (M1, M2, M6, S8, S13)

Task of the read-report's follow-up. Only files under `tex/sections/gen/` were edited or created;
no tracked file of the repository was touched, nothing was posted, no Lean was run. Compiles ran
from `tex/` with LuaLaTeX into a private output directory (the scratchpad), because another agent
was compiling `main.tex` into `tex/build/` at the same time and the two runs corrupted each
other's `main.aux` (first attempt, 11:27).

Status: in progress (M1, M2, M6, S8 done).

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

