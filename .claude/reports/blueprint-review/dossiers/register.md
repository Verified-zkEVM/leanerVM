# Register of the review's findings and negative results (task `register`)

Status: IN PROGRESS. Built from the dossiers under `.claude/reports/blueprint-review/dossiers/`;
the register is an index and a summary, never the only record: every row points to the dossier
section that states it in full. No Lean was run for this register.

Object of the review: leanerVM `main` at `b435631`; leanVM at the pin `a386121f`. Library
revisions as each dossier states them (old pins: ArkLib `dca90385`, CompPoly `3468b38c`, Clean
`93c9d1ef`, VCVio `f9dc47d9`; new pins after `144c5aa`: ArkLib `7653a901`, CompPoly `572f9973`,
Clean `42fe4b26`, VCVio `a4232d08`).

## Dossiers processed

(filled as each dossier is processed)

## Part 1. Register of findings

(filled after all dossiers are read)

## Part 2. Negative results

## Part 3. Not verified

## Part 4. Counts

---

# STAGING (working extraction, one block per dossier; replaced by Parts 1-4 when complete)

Row format: temp id | short name | severity | subject | where | classification | claim | evidence | change | status | merge/disagreement notes

## Staging: gt-table-pub.md (+ verify-gt-table-pub.md)

Citation check: 301 citations, 294 OK, 2 wrong line, 4 not supported (numbering only), 1 could not check (probes not re-runnable). Corrections: Corollary 3.7 -> 3.9 (`cor:idtest`, `03:67`); Fact 3.8 -> 3.10 (`fact:sumcheck`, `03:79`); "Theorem B.2" -> Theorem B.7 (`thm:rbr`, `b-...tex:139`); `leanisa-blueprint.md:611-612` -> `:612-613`. Probes SeamBusShape/SeamBusMember: sources identical, run recorded by the dossier (exit 0), not re-run by the check.

- TP1 | The bus seam admits statements the deployed table sumcheck cannot serve | major | seams | gt-table-pub.md §8 (first finding), §6 E.1 | error of the blueprint | `Seam.bus` takes any list of linear claims, terms of one table at unrelated points, terms on any table, a degree clause on the statement alone; completeness and rbr knowledge soundness of the deployed table-sumcheck verifier against it cannot be proved without guards leanVM lacks (error on xi unbounded over the seam). | `Spine/Seams.lean:130-134,175-181` at b435631; probes `SeamBusShape.lean`, `SeamBusMember.lean` (exit 0 per dossier) | `BusOut` in the shape of the Rust's `BusVerify` (`leaf.rs:849-860`): one point, forms per side and sumcheck table with degree in the type, three totals, column claims; smaller alternative: guard clauses in `Seam.bus` (gt-table-pub.md §8) | cited-checked; probe-run | DISAGREEMENT candidate with gt-bus.md E (bus phase can fill its slot)
- TP2 | The table sumcheck's tables are not distinguished from the instance's other tables | major | table sumcheck | gt-table-pub.md §8 (second finding), §4 C.1 item 4 | error of the blueprint (an omission) | Layer 3 makes the six shared columns tables of the instance; Layer 7's `τ_max` and final-message width range over all tables, giving at least 16 rounds and 110 values where leanVM has `τ_max` (as few as 3) and 104. | blueprint `:836-839`, `:987-989` at b435631 | add `I.SumcheckTable` (tables with a constraint, flush or count) and restrict the schedule to it; acceptance test on a taller constraint-free table | cited-checked; unverified (reading of the text: `leanIsaInstance` not built) |
- TP3 | The public-input phase proves a check no executable verifier runs; its debt is assigned to Layer 12, which cannot pay it | major | public input | gt-table-pub.md §8 (third finding), §7 | deliberate deviation (decision 15; status finding F18) | Specification §8.2 checks each limb; Rust, Python and the recursion guest check one combined equation `c0 + y·c1 = (1+r)·w0 + r·w1` and pool the scalars sent; the combined check is a different oracle verifier, so the compilation layer cannot supply its soundness. | `cpu/mod.rs:752-755`, `verifier.py:1400`, `aggregate.py:1683`; blueprint `:1060-1062` | add a second phase `publicInputPhaseWords` (combined check, pooled values = values sent, `Phase.Security` at `1/|E|`) and use it for leanISA and `verify` | cited-checked; paper (error `1/|E|`) | merge with code-pubinput
- TP4 | Sumcheck round message: four coefficients and a check in the oracle protocol, three and none on the wire | minor | table sumcheck | gt-table-pub.md §8 "The round message" | deliberate deviation (owes an unstated lemma) | Both verifiers derive `c1` from the running claim and never check the round; the blueprint's oracle protocol sends four coefficients and checks, so Fiat–Shamir absorbs different data and a transport lemma (or a challenge oracle on the encoded message) is owed and unstated. | `constraints.rs:261-291`, `transcript.rs:303-307`; blueprint `:315`, `:1218-1221` | make the wire message the oracle protocol's (three coefficients, no round check) or state the transport lemma in Layer 4 | cited-checked; paper |
- TP5 | The zerocheck escape is over-charged, and charged in three ways | minor | error | gt-table-pub.md §8 "The zerocheck escape", §5 D.1, D.3 | — (error accounting) | The recycled point costs `τ_max/|E|` once (nothing with a conjunctive state function), carried by the last GKR layer's challenges; blueprint row Seams says per coordinate per constraint, Layer 7 says per constraint charged to Layer 6, tracker repeats it. | blueprint `:333`, `:1000-1003`, `:1283` | one conjunct of the bus phase's state function; `busError` has no term for it | cited-checked; paper | merge with gt-bus (zerocheck escape)
- TP6 | Layer 7's sketch and the tracker's signature predate the spine; one theorem is a placeholder | minor | documentation | gt-table-pub.md §8 "Layer 7's sketch", §4 C.2 | error of the blueprint | Layer 7's `BusOut`/`TableOut`, the tracker's `tableSumcheck I (S)` with `tableSpec` and `tableSumcheck_relOut_implies_constraints` (no statement) do not match the spine's `Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)`. | blueprint `:986-995`, `:991-992` | rewrite on the spine's names; delete the placeholder | cited-checked | merge into "stale per-layer sketches"
- TP7 | Layer 9's sketch makes the eighteen limb claims an input of Flock | minor | Flock | gt-table-pub.md §8 "Layer 9's sketch", §6 E.2 | error of the blueprint | Flock's reduction in leanVM takes no claim; the limb claims are opened with the other column claims; the spine's Flock slot is right, the sketch is not. | blueprint `:1078-1081` | rewrite Layer 9's sketch on the spine's slot | cited-checked | merge with gt-flock-ring
- TP8 | The status's round-message finding says "four nodes"; the wire carries coefficients | minor | documentation | gt-table-pub.md §8 "Two status findings are wrong" (first bullet) | error of the status (and a stale Rust comment) | Status finding F6 says the cubic is sent at four nodes; the wire carries three coefficients `c0, c2, c3`. | `constraints.rs:191-194`; `transcript.rs:56-71`; stale comment `constraints.rs:24` | "a cubic, three of its four coefficients on the wire" | cited-checked |
- TP9 | The status's finding that the Python verifier omits the caps is wrong at the pin (F9) | minor | documentation | gt-table-pub.md §8 "Two status findings are wrong" (second bullet) | error of the status | The Python verifier checks `16 <= log_memory <= 32`, heights `<= 32`, `τ_BLAKE2S >= 3`, bytecode power of two. | `verifier.py:857-864`, called at `:1378`; `log2_strict` `:252-254` | retire F9 | cited-checked | merge (three dossiers)
- TP10 | The tracker's text for the public-input phase is stale | minor | documentation | gt-table-pub.md §8 "The tracker's text" | error of the tracker | Hole comment says "the prover sends nothing" and the scalars are Layer 12's encoding; merged phase has the prover send the values. | tracker hole comment (re-read by the check, lines 67, 80, 93-97) | redraft (draft only) | cited-checked |
- TP11 | The specification's batching error is loose by one; no error for the recycled point; which coefficient is dropped unsaid | note | table sumcheck | gt-table-pub.md §8 Notes; §5 D.1, D.2 | error of a source (specification) | Spec charges `(ν_side + B)/|E|` (`05:155`); its own Corollary 3.9 gives `(ν_side + B − 1)/|E|` (dossier said 3.7: corrected by the citation check); no rbr statement for these phases (only Theorem B.7 `thm:rbr`, for the opening; dossier said B.2: corrected by the citation check). | `05:155`, `03:67` | report to leanVM | cited-checked; paper |
- TP12 | Stale comments in the Rust on the round message | note | table sumcheck | gt-table-pub.md §8 Notes, §2 A.4; verify-gt-table-pub.md §4 item 3 | error of a source (Rust comments) | `constraints.rs:24` ("sent WHOLE, at four nodes"), `:265-266`; the check adds `:26` and `:257-260`. | `constraints.rs:24,26,257-260,265-266` vs `transcript.rs:63-71` | report to leanVM | cited-checked |
- TP13 | The spine's slot does not pin the protocol: a phase reading the whole oracle fills it | note | seams | gt-table-pub.md §8 Notes; §6 E.4 item 6 | — | Faithfulness is not in the slot's type. | reading of `Spine/Compose.lean:77-78` | — | paper | related to code-spine
- TP14 | Blueprint line numbers shift by four at HEAD; the upgrade changed more than the pins table | note | documentation | verify-gt-table-pub.md §4 item 1 | — | At `8d3ea7d` the blueprint has a new 4-line paragraph after line 51 and a rewritten row "Module system"; every citation >= 315 is +4 at HEAD; contradicts brief §8 ("pins table only"). | `git diff b435631 HEAD -- docs/roadmap/protocol-blueprint.md` | report cites b435631 | cited-checked |

Negative results (gt-table-pub):
- N: Table sumcheck transcript agrees across spec, Rust, Python (xi; `τ_max` rounds of three elements; 104-value final message; final check; derived target) | §0 item 1, §2 | reading; cited-checked
- N: Blueprint's table-sumcheck conventions match (variable order, joining round, padding `padHigh`/`evalMle_padHigh`, degree, powers of xi, derived target, claim-pool order, third public claim with value 0, limbs as strided claims) | §4 C.1 items 1,3,5,6,8-12,15 | reading; cited-checked | caveat: item 8 only for the six opcode tables (TP2)
- N: The errors `(B+2)/|E|` on xi and `3/|E|` per round are correct and tight | §0 item 3, §5 | paper
- N: Checked and agreeing across sources: moment of every challenge; power assignment; three sides and order (`leaf.rs:610-622`, `verifier.py:570-574`); order of the 104 values (`tables.rs:436-863` vs `verifier.py:823-834`); slot of each BLAKE2s limb (`hash_flock.rs:85-115` vs `verifier.py:847-850`); pool order | §2 A.4 | reading; cited-checked
- N: Perfect completeness without exceptional challenges (acceptance test 20) holds of both phases (only inverse is of the constant `g+g^2`) | §8 Notes | paper
- N: The Rust-only guard `zeta.len() < n` is unreachable (`μ_bus >= τ_max + 1`) | §2 A.4 | reading
- N (check): no quotation misquoted; load-bearing blocks verbatim | verify-gt-table-pub §1 | citation check

Not verified (gt-table-pub §10):
- U: Rust and Python verifiers behave as read | read, not run | run both on a dumped proof and on the mutations of B.1, B.2
- U: errors of D.2, D.3, E.3 | paper | Layer 4 sumcheck and the bus phase's Security with the conjunct of D.3
- U: finding on the sumcheck's tables | reading of Layer 3 | `leanIsaInstance` when built
- U: combined check has error `1/|E|` | paper, one instance tested | the second phase of §8
- U: leanISA's tables have the Rust's column order | not checked | compare `Arithmetization/Tables/*.lean` with `tables.rs:436-863`
- U: leanth's `ZerocheckClaim` pattern cited by row Seams | not read | —
- U (check): probes SeamBusShape/SeamBusMember still elaborate at the new pins | could not check | rebuild and re-run
