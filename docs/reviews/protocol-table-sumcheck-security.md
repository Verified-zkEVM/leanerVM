# Review: the table sumcheck phase's knowledge soundness

> An archive of the review of one commit, `bbc11f7` of the branch
> `feat/protocol-table-sumcheck-security` (draft pull request #87), against its base `0516908`
> (the head of pull request #85, `feat/protocol-table-sumcheck`, the phase's definition and
> completeness, reviewed in [protocol-table-sumcheck.md](protocol-table-sumcheck.md)): names,
> paths and line numbers are that commit's. What is accepted from it is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of the
> pull request that met it.

**Disposition**:

| Finding | Disposition | Commit |
| --- | --- | --- |
| 1. the docstring misdescribes the state function after the final values | met: the bus seam before `ξ`, then the running claim with the side condition, up to the last message | `5e539bc` |
| 2. the unit lemma duplicates the sumcheck test's and generalises the spine's `overE_one` | met: `natCast_div_card_eq_overE` in `Spine/Errors.lean`, both copies gone | `5e539bc` |
| 3. the pull request's classification and validation, and three hygiene nits | met: the body classifies the work and reports the gate; the unused `open`, the double destructuring and the repeated docstring gone; the review listed in `docs/README.md` | `5e539bc` and the documentation commit |

Reviewed with the `adversarial-review` skill in three passes: the statements against the
blueprint's Layer 7 and holes table, the conventions *Errors*, *Load-bearing checks*,
*Extractors*, *Holes*, *Seams* and *Generic code*, decision 20 and acceptance tests 24, 31 and
32, with ArkLib's `KnowledgeStateFunction` (`.lake/packages/Arklib/ArkLib/OracleReduction/
Security/RoundByRound.lean:165-192`) and the composed state `KnowledgeAppend.state`, all read
before the proofs; the expectation for the error formed from the specification at the pin
(`doc/leanvm/body/03-proving-primitives.tex`, the sumcheck fact and the identity-testing
corollary; `05-arithmetization.tex` §5.5, lines 125-155, in the pinned checkout at `a386121f`)
before the Lean; and hygiene. The two changed files were read in full, with the base's
`ToArkLib/Batch.lean`, `Sumcheck.lean`, `SumcheckRound.lean`, `SendChecked.lean`,
`SampleChallenge.lean`, `Component.lean`, `Refutation.lean`, `Spine/Seams.lean`,
`Spine/Errors.lean`, `Spine/Phase.lean`, `Spine/Compose.lean`, and the two previous handoffs.
Lean was run once: `lake env lean` on a scratch copy of the test file (whose `.olean` in the
worktree predated the committed source) with `#print axioms` of the eight new declarations and
one probe appended (the composed error is the slot's by `rw` and `rfl`, with no inequality
left); it compiled with no error in about 90 seconds. The repository scripts `audit-lean.sh`,
`check-imports.sh`, `check-layers.sh` and `check-docs.py` pass. Nothing was edited but this
file.

Target classification: the commit names the hole and the direction ("knowledge soundness"). The
pull request's body names the hole, Layer 7's second half, the three error terms with their
provenance, the kernel axioms (verified below) and the two refutations by name, which meets the
convention *Load-bearing checks*; it does not say that the work feeds T4 through the table
sumcheck slot in the soundness direction, that the phase is Category A (the Lean is the
standard, written from §5.5; the previous handoff's fidelity reading stands, since no definition
changed), nor that `I.d ≤ 2` is load-bearing for the error beside the bus phase's `1 ≤ I.d` (the
previous review asked the pull request to say so), and its validation section reads "In
progress" (finding 3).

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological, and the statement is the one the spine's slot
consumes: `tableSumcheckSecurity` (`TableSumcheck.lean:552-575`) has exactly the type of
`Phases.Security.table` (`Spine/Compose.lean:122`), on `(tableSumcheck I).toDef`, from
`Seam.bus I` to `Seam.table I`, at `tableError I`, and the error is reached by equality (probed):
`(B + 2)/|E|` on `ξ` from `batchSecurity` with the true values fixed before the challenge, `3/|E|`
per round from `roundsSecurity` under `tableSummand_degree`, zero on the final values from
`finalSecurity` through `finalClaims_holds_iff`. It is a plain `def`, inhabited on the toy and on
the two-table instance as plain `def`s, with the toy's extraction a `def` (acceptance test 24),
and the kernel axioms are the standard three. The hypothesis `I.d ≤ 2` is necessary and stated
right. The two checks of the verifier are refuted: the final check at the phase's own output map
and seam, with no state function at all, instantiated on the two-table instance; the round check
at the round's own relations, instantiated on the two-table instance's first round. The batch
step has no check to refute, since its target is derived. What is short is one sentence of the
declaration docstring that misstates the composed state function, a duplicated helper lemma,
and the pull request's body.

## Findings, most severe first

No finding is above low.

### Low

**1. The docstring misdescribes the state function after the final values.** *Docstring
accuracy.* `TableSumcheck.lean:549-551` says the state function is "the table seam after the
final values". It is not. The composition (`KnowledgeAppend.state`, `:182-196`) makes the state
on a prefix inside the last message "the checks before it passed, and the last message's own
state of the statement its verdict produced"; the last message is `Component.sendChecked`, whose
state function (`SendChecked.lean:167-176`) is `(stmt, w) ∈ relIn` at *every* stage, the empty
prefix and the full one alike. So after the final values the state is "the statement entering
the last message is in `rel Φ τ_max`": the running claim is the summand at the final point and
the side condition holds (`mem_rel_self`). The values sent appear nowhere in it. Concrete
difference: on a transcript whose final values are not the columns' extensions while the running
claim is right, the state is true and the verifier rejects; "the table seam", read of the output,
would be false. ArkLib's `toFun_full` is one-directional (acceptance implies the state), so the
proof is right and only the sentence is wrong. Fix: "…the sumcheck's running claim with the side
condition during the rounds and through the final values, which the final check pins to the
columns' extensions"; or cut the sentence, since the module docstring (`:57-61`) says what each
term charges without describing the state.

**2. The unit lemma is a private copy of one the sumcheck test already has, and the general
case of the spine's `overE_one`.** *Convention: Generic code; duplication.*
`natCast_div_card_eq_overE` (`TableSumcheck.lean:541-543`) is, name and statement, the sumcheck
test's `natCast_div_card_eq_overE` (`tests/LeanerVMTests/Protocol/Sumcheck.lean:363-364`), and
`overE_one` (`Spine/Errors.lean:88-91`) is its case `k = 1`. Every phase's security rewrites a
generic component's `k / Nat.card E` to the slot's `overE k` (the bus phase's open branch will
need it a third time). Fix: state it once in `Spine/Errors.lean` beside `overE_one` (or in place
of it, `overE_one` becoming `overE_eq … 1`), and have the production module and the test use it.

**3. The pull request's classification and validation, and three hygiene nits.**
- The body: say that the work feeds T4 through the table sumcheck slot in the soundness
  direction; that the phase is Category A, the fidelity reading of #85's review standing since no
  definition changed; that `I.d ≤ 2` is load-bearing for the error (the summand has degree
  `d + 1` in each variable, and a cubic message against a quartic true round polynomial escapes
  at four challenges, `4/|E| > 3/|E|`), beside the bus phase's `1 ≤ I.d`; and fill "Validation:
  In progress" with the commands run.
- `tests:421-422`: `open scoped NNReal in` on `final_unchecked_no_stateFunction` is unused (no
  error appears in its statement); `final_unchecked_twoTab` rightly has none.
- `TableSumcheck.lean:563-564`: `(trueValues_eq_claimed_iff I s (theStack o)).mp heq` is computed
  twice; an `obtain ⟨h1, h2⟩` reads better.
- `TableSumcheck.lean:545-551`: the declaration docstring is seven lines and repeats the module
  docstring's argument (`:57-61`); two lines naming the statement, the hypothesis and the
  extractor suffice once finding 1 is taken.
- `docs/README.md:84-89` lists each review; this file is to be listed.

### Observations

- **The round refutation is at the round's relations, not the phase's seams.**
  `round_unchecked_not_rbr` (`tests:479-509`) is `SumcheckRound.drawChallenge_unchecked_not_rbr`
  on the phase's family, at `relMid Φ 0 → rel Φ 1` of the two-table instance; the convention's
  letter says "at the phase's seams". The final check's refutation is at the seam
  (`tableOut`, `Seam.table`). A phase-level refutation of a mid-phase check is not available from
  the generic lemmas: `Verifier.not_rbr` (`Refutation.lean:126-143`) needs only prover messages
  after the challenge, and `not_rbr_zero` gets the false state for free only at round zero; the
  first round's challenge of the phase is followed by further challenges, so it would need a new
  argument (an earlier error below one leaves a challenge keeping the state false). The sumcheck's
  and the GKR's reviews accepted the component-level route; nothing new to do unless the
  blueprint's wording is tightened.
- **The specification's `nside + B` is the count of powers, not the degree.** §5.5 charges
  `nside + B = B + 3` on `ξ`; the batch is a polynomial of degree at most `B + 2` in `ξ`
  (`B + 3` powers, `ξ^0` to `ξ^{B+2}`), and the identity-testing corollary charges the degree, so
  `(B + 2)/|E|` is the right bound and the specification's is conservative by `1/|E|`. The spine
  records the choice (`Spine/Errors.lean:57-58`); the Lean is right.
- **The batch step has no check, by design.** Its verifier draws `ξ` and derives the target
  from the bus totals (`claimed`, `batchStep`); nothing is sent, so nothing is checked and nothing
  can be omitted. Its soundness rests on the derived claim alone: a statement off the bus seam has
  `trueValues ≠ claimed` (`trueValues_eq_claimed_iff`), and the batched claim meets the batched
  true values at `B + 2` challenges at most. A design that sent the target would need a check,
  and the convention *A check is load-bearing only if the verifier commits to it* would apply.
- **The extractor keeps the trivial witness**, as every phase's does; the knowledge is the
  oracle's, read off the commit message by `piopExtractedStack_eq`. Right for a front phase.

## Answers to the questions put to the review

- **The statement the slot needs.** Yes: `Phase.Security I (tableSumcheck I).toDef (Seam.bus I)
  (Seam.table I) (tableError I)`, the type of `Phases.Security.table` verbatim. Non-vacuous: both
  seams are inhabited by the honest runs (`completeToy`, `completeTwo`, and the test's run lands
  in the table seam); the hypotheses of `batchSecurity`, `roundsSecurity` and `finalSecurity` are
  discharged, not assumed, and each is the sharp fact (`sum_tableSummand`,
  `trueValues_eq_claimed_iff`, `tableSummand_degree`, `finalClaims_holds_iff`). A verifier that
  checks nothing cannot inhabit the statement, since the definition is fixed; the two refutations
  show that removing either check breaks it. `I.d ≤ 2` is necessary (finding 3's text) and is
  the hypothesis the leanISA instance meets at `d = 2`.
- **Computable.** `tableSumcheckSecurity`, `securityToy`, `securityTwo` and `extractionToy` are
  `def`s without `noncomputable` and the modules compile; no real number or `Fintype` instance is
  an argument (`Nat.card`, `[Finite E]` inside the generic parts), and `Security.mono` and
  `Security.append` are inlined. The test shows the extraction as a `def` (the convention's
  check); it does not run the extractor on a transcript, which no phase's test does.
- **Load-bearing checks.** Two checks, two refutations, both instantiated: the final check's
  at the phase's own output map and seam (`final_unchecked_no_stateFunction`, generic over `I`,
  from `Component.sendChecked_no_stateFunction` with `tableOut_mem_table`; `final_unchecked_twoTab`
  on the honest two-table data with the claim off by one, `side_twoTab` discharging the side
  condition); the round check's at the round's relations (`round_unchecked_not_rbr`, from the
  honest family's consistency, the claim off by one, the side condition at every challenge). The
  batch step has no check (observation above). The hypotheses of the generic test theorem
  (`hside`, `hs`) are met by the instance, not assumed.
- **Hygiene.** Finding 1 (the state function), finding 3 (nits). No line over 100 columns; no
  roadmap, hole, layer or letter-code citation in either file (grepped); the module docstring's
  new paragraph is accurate on every point checked (the degree in `ξ`, the true values fixed
  before `ξ`, `3/|E|` per round, nothing on the values); the proof of `tableSumcheckSecurity`
  reads as the three generic halves with their hypotheses, and its `mono` is an equality.

## Pass A: the statements

Read before the proofs, from the blueprint, §5.5 and ArkLib's definitions. Besides the answers:

- `batchSecurity`'s hypothesis takes `a := trueValues I s (theStack o)`, a function of the
  statement and the oracle alone, fixed before `w` and `ρ`, as the lemma's docstring requires for
  the count `k − 1`; with `W = Unit` the order is moot but the shape is right.
- The side condition is inside the sumcheck's input relation, so a statement failing it fails
  the output relation of the batch step at every `ρ`, and the bad set is empty; a statement
  meeting it and the two seam claims is in the bus seam. So the bad challenges are exactly the
  roots of the batched difference (`card_false_batch_le`).
- `finalSecurity`'s hypothesis reads the table seam at `tableOut` and returns the values and the
  side condition: the carried claims (`Or.inl`), the final claims (`Or.inr`, through
  `finalClaims_holds_iff`), the lines and the Flock predicate. Exactly what the seam says.
- Substitution test: with `finalCheck` replaced by `fun _ _ ↦ true` the composition's third
  hypothesis still holds but `finalSecurity` is no longer available (it is stated on `final V
  out` with its check), and `final_unchecked_no_stateFunction` says no proof exists; with the
  round check dropped, `drawChallenge_unchecked_not_rbr` says the same of the round.
- The composed state function, read from `KnowledgeAppend.state`: the bus seam before `ξ`;
  after `ξ`, the batched claim is the sum and the side condition; during the rounds, the running
  claim is the family's and the side condition, with the recorded polynomial honest between a
  message and its challenge; through the final values, the statement entering the last message
  is in `rel Φ τ_max` (finding 1).
- Both refutation theorems universally quantify the extractor, and the round's the state
  function too; their conclusions (`False`, `1 ≤ ε ⟨0, rfl⟩`) are the convention's.

## Pass B: fidelity at `a386121f`

The protocol is Category A; the Lean is the standard. The expectation was formed from the
specification first.

- **The sumcheck fact** (`03-proving-primitives.tex:79-85`): "a false claim survives with
  probability at most `dκ/|E|`", with `d = 3` and `κ = τ_max`: the Lean's `3/|E|` on each of
  `τ_max` challenges, summing to `τ_max · 3/|E|` (`sum_tableError`, `Spine/Errors.lean:174-179`).
- **The identity-testing corollary** (`:67-72`): two distinct polynomials of total degree at most
  `d` agree at a random point with probability at most `d/|E|`. Applied to the batch in `ξ`: degree
  `B + 2`, so `(B + 2)/|E|`.
- **§5.5** (`05-arithmetization.tex:145-155`): "the soundness error is `(3τ_max + nside + B)/|E|`:
  `3τ_max` for the rounds (Fact) and `nside + B` for the `ξ`-batching (Corollary)". The rounds'
  share is the Lean's; the batching's is one more than the degree the corollary charges
  (observation above): the Lean is tighter and the specification's figure is conservative.
- **The Rust.** No definition changed in this commit; the citations of the module docstring
  (`cpu/mod.rs:404-441, 726-743`, `constraints.rs:243-291`) are #85's and were read at the pin
  for its review. The deployed verifier's checks are the two modelled (`constraints.rs:288-290`
  the final `acc ≠ claim`, and the round check that the wire's decoding makes implicit, the
  oracle protocol checking each round). Checks modelled: two; refuted: two; deviations declared:
  none.

## Pass C: hygiene

`TableSumcheck.lean` keeps the module shape, a Mathlib-style section header for the new section,
docstrings on both new declarations, one private helper, no proof narration, no roadmap
reference, no new import, no line over 100 columns. The test's new section is clear, its names
say what they state, and its module docstring's two new bullets are accurate. The findings are
the docstring sentence (finding 1), the duplicated helper (finding 2) and the nits of finding 3.

## Kernel axioms

`TableSumcheck.tableSumcheckSecurity`, and the tests' `final_unchecked_no_stateFunction`,
`side_twoTab`, `final_unchecked_twoTab`, `round_unchecked_not_rbr`, `securityToy`, `securityTwo`,
`extractionToy`: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## What was checked and found sound

The statement against the slot's field; the error against the fact, the corollary, §5.5 and
`tableError`, and that the composition reaches it by equality; the three hypotheses handed to the
generic halves, each the sharp lemma; the non-vacuity of the seams and of the refutations'
hypotheses; the computability of the four securities and the extraction; the necessity of
`I.d ≤ 2`; the two refutations against the convention; the composed state function; the vocabulary
and the line widths; the aggregate imports and the scripts; the kernel axioms.

## What could not be checked

The status page's entry, not yet written. `lake test` and `./scripts/validate.sh`, not run on the
memory-limited machine; the test module was compiled once from a scratch copy with the axiom
prints, every `#guard` passing. Whether the bus phase's open branch carries a third copy of the
unit lemma (finding 2), not read.
