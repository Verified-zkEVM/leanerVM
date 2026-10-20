# Review: the sumchecks' knowledge soundness

> An archive of the review of one commit, `5078069` of the branch `feat/protocol-sumcheck-security`,
> against its base `85fa71b` (the head of draft pull request #75, `feat/protocol-sumcheck`, the
> sumchecks' definitions and completeness, reviewed in
> [protocol-sumcheck.md](protocol-sumcheck.md)): names, paths and line numbers are that commit's.
> No pull request was open for the branch at the time of the review. What is accepted from it is
> text of the [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification,
> or of the pull request that met it.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. the relations leave no room for what the table phase carries untouched, and the last message outputs the sumcheck's statement, so the table phase cannot reach its seam from what is supplied | met, by the local route for the first part and the first option for the second: on #75's branch (`27659fa`) the relations and the family's invariant carry a side condition on the context, which no challenge changes (so the soundness clause still has no bad challenge), and `final` takes its output map, with `finalComplete` for any output relation the true values land in; on this branch `finalSecurity` takes any output map and output relation from which the values and the side condition follow, and the status names what the table phase composes (`roundsSecurity`, `finalSecurity`, `rel_zero`, `mem_rel_self`); a test builds the table slot's shape with an output map to the phase's own statement, and another carries a side condition through completeness. The generic `Component.Security.conj` was not taken: its completeness counterpart needs a probability-one intersection lemma the components do not have, and the family's invariant serves the sumcheck at no cost |
| 2. injective nodes are an artifact of the proof's route, not a condition of the verifier's soundness | recorded in the status as owed: dropping it needs the round's security stated for prover polynomials apart from the family, and a family whose honest polynomial is chosen classically; that family is data the compiled security would build, so the securities would stop computing, against acceptance test 24. Kept until the upstream port |
| 3. the test's docstring claims a round refutation the file does not contain | met: `unchecked_round_not_rbr` instantiates `SumcheckRound.drawChallenge_unchecked_not_rbr` on the family of the plain sumcheck on `t₁ · t₂` |
| 4. documentation | met: the status's long lines wrapped; this review listed in `docs/README.md`; the status row's number and the pull request body's classification and refutations filled when the pull request opens |
| the observation on `normalizedSecurity` | no change needed: kept with `Sumcheck.normalized` until the `docs(protocol)` request #75 records is decided |
| the observation on the error's unit and the slot's whole error | no change needed: `ξ`'s term is the table phase's |

Reviewed with the `adversarial-review` skill in three passes: the statements against the
blueprint's Layer 4 and Layer 7, the holes table's Layer 4 rows, the conventions *Holes*,
*Extractors*, *Errors*, *Load-bearing checks*, *Sumcheck variants* and *Generic code*, acceptance
tests 24 and 32, decisions 10, 11, 20 and 23, and ArkLib's `Verifier.KnowledgeStateFunction` and
`Verifier.rbrKnowledgeSoundnessWorstCaseWith`
(`.lake/packages/Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean:165, 557`), read before
the proofs; the expectation for the error formed from the specification at the pin
(`doc/leanvm/body/03-proving-primitives.tex`, Fact 3; `05-arithmetization.tex` §5.5, both fetched
from GitHub at `a386121f`) before the Lean; and hygiene. The three changed files were read in
full, with the base's `SumcheckRound.lean`, `SendChecked.lean`, `SampleChallenge.lean`,
`Component.lean`, `Schedule.lean`, `Spine/Errors.lean`, `Spine/Seams.lean`, `Spine/Phase.lean`,
`Spine/Compose.lean` and the GKR's `GrandProductSecurity.lean`, and the previous handoff. Lean was
run three times, serially: `lake build LeanerVMTests.Protocol.Sumcheck` (181 s; the test module's
`.olean` predated the committed source), then `lake env lean` on two scratch files printing the
kernel axioms of the nine new definitions and the signatures of three, and checking the three
facts reported under finding 2 and the answers (the vacuous soundness clause, the round
verifier's and the relations' independence of the nodes). The repository scripts `audit-lean.sh`,
`check-imports.sh`, `check-layers.sh` and `check-docs.py` pass. Nothing was edited but this file.

Target classification: the commit message names the hole and the direction ("round-by-round
knowledge soundness ... at `d / |F|` per round"). The pull request, once open, is to say that the
work feeds T4 through the table sumcheck phase (Layer 7) in the soundness direction, that with the
witness a subsingleton it is round-by-round soundness of the language `relIn` and the extractor
plumbing is trivial (as the GKR's description says of its own), that the protocol is Category A,
and which refutation covers which check (the round's is the base's
`SumcheckRound.drawChallenge_unchecked_not_rbr`, the final's is #75's
`final_unchecked_no_stateFunction`).

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological. `weightedSecurity` (`Sumcheck.lean:499-506`) is
the rounds' security (`roundsSecurity`, `:479-486`, the base's `SumcheckRound.roundsSecurity` on
the family of #75, whose invariant is `True`) followed by the last message's at error zero
(`finalSecurity`, `:488-497`), composed by `Security.append`; the per-round error is the
specification's `d/|E|` (Fact 3), the state function is "the running claim is the true one" (and,
between a round's message and its challenge, "the recorded polynomial is the honest one"), false
exactly at a false claim, and the extractor keeps the trivial witness, which is right for a
component whose knowledge is the committed oracle's. The five securities are plain definitions,
their kernel axioms the standard three, and the tests inhabit them over `E` as `def`s that
compile, with `tableRoundsSecurity` (`tests:386-393`) landing exactly on the table slot's
per-round term `roundsError E 3 (overE 3) I.τmax` for the toy. The per-round bound is tight (a
strategy below reaches it) and its two hypotheses that bear on the verifier, the degree in each
variable and the subsingleton witness, are necessary (two strategies below break the bound
without them); the third, injective nodes, is not (finding 2). What is short is the interface to
Layer 7: the relations have no place for the conjuncts the table phase carries untouched, and
the last message's output is the sumcheck's own statement (finding 1). The rest is a test
docstring and documentation.

## Findings, most severe first

### Medium

**1. The relations leave no room for what the table phase carries untouched, and the last
message outputs the sumcheck's statement, so the table phase cannot reach its seam from what
is supplied.** *Interface; Layer 7's needs.* The table phase's security is demanded at
`Seam.bus → Seam.table` (`Spine/Compose.lean:122`). `Seam.table` (`Spine/Seams.lean:176-178`) is
"every column claim holds, the input's carried forward (`tableClaims = busClaims + tableColumns`)
and the new ones, and `PublicLinesHold` and `aux`"; `Seam.bus` (`:167-174`) has those conjuncts
too. The blueprint says so (Layer 7, `protocol-blueprint.md:934-935`: "the output carries the
input's column claims forward (dropping them would forget a false boundary claim)"). A
round-by-round state function must carry those conjuncts through every challenge of the slot,
and the sumcheck's cannot: `family` fixes `inv := fun _ _ _ ↦ True` (`Sumcheck.lean:165`),
`relIn V wt` is the claim alone (`:172-175`), `relOut V` the values alone (`:177-179`), and
`roundsSecurity`'s state function is composed from those (`SumcheckRound.rel`, `relMid`,
`:149-158`). No lemma on `Component.Security` conjoins a predicate of the untouched context
(`Component.lean` has `mono` and `append` only; the GKR's relations carry riders, not an
arbitrary predicate). Second, the slot `tableSpec I = draw ++ₚ roundsSpec ++ₚ say`
(`Spine/Errors.lean:151-154`) leaves no round for a pass-through after the last message, and
`final` outputs `Out X F n m` by `finalOut` (`:192-205`), not `I.Stmt × TableOut I`; so
`finalSecurity`, `weightedSecurity`, `plainSecurity` and `normalizedSecurity` are not what Layer 7
composes at `tableSpec`: it needs the rounds' security and a last message of its own. The
consequence: Layer 7 either writes its own family on `SumcheckRound` (as the GKR does), and the
hole's bold names have no consumer, or writes the state function by hand (as the public-input
phase did), and the generic security is unused.

Fix, in two parts, both small. (i) A generic lemma, an ArkLib candidate serving Layer 6 and 9 as
well: `Component.Security.conj S P₀ P' h : Security D (relIn ∩ P₀) (relOut ∩ P') ε`, for a
predicate `P₀` of the input statement and oracles and `P'` of the output's, with
`h : ∀ s tr, P' (S.guarded.out s tr) → P₀ s` (a front verdict hands the untouched part of the
statement and the oracles on, so `P'` reads what `P₀` read). The state function is the old one
conjoined with `P₀` of the input statement, which ArkLib's `toFun` receives at every stage;
`toFun_empty` and `toFun_next` are unchanged, `toFun_full` uses `h`, and the bad event is
contained in the old one, so the error is the same. The cheaper local alternative is a
challenge-free invariant in `family` (`inv := fun ctx _ _ ↦ P ctx`, added to `relIn` and
`relOut`), whose `Family.Sound` holds since `¬ P` leaves no challenge restoring `P`; it serves
this sumcheck only. (ii) Either `final` takes its output map as a parameter, `finalOut` the
default, with `finalSecurity` over any map and output relation given the one hypothesis the
present proof uses (`finalCheck` and the output relation give the values), or the status records
that Layer 7 builds its last message from `Component.sendChecked` with `finalCheck` and its own
map, `finalSecurity` (four lines: `sendCheckedSecurity`, `mem_rel_self`) the model. Either way
the pull request says which names Layer 7 consumes (`roundsSecurity`, `rel_zero`,
`mem_rel_self`, `finalCheck`), and the status's bullet says what is owed.

### Low

**2. Injective nodes are an artifact of the proof's route, not a condition of the verifier's
soundness.** *Hypotheses; decision 23.* `roundsSecurity` and the three above it take
`hnodes : Function.Injective nodes` (`Sumcheck.lean:481, 503, 510, 517`) because they go through
`(family_honest V wt nodes hV hnodes).toConsistent` (`:485`), the completeness proof's honest
polynomial `roundPoly` (`:149-156`), which interpolates at the nodes. The verifier never reads
the nodes: probed, `(SumcheckRound.round P j wt).red.verifier = (SumcheckRound.round P' j wt).red.verifier`
is `rfl` for any two honest-polynomial families `P`, `P'`, and the relations between the rounds
read the family's claim and invariant only, so
`SumcheckRound.rel (family V wt nodes) j = SumcheckRound.rel (family V wt nodes') j` for any two
choices of nodes (probed, by `ext` and unfolding). The statement is therefore true for every
`nodes`, injective or not, and the hypothesis is one the honest prover needs, imported into the
security half against the letter of decision 23 ("knowledge soundness does not presuppose
completeness"). The other two hypotheses are necessary (see *Answers*). To remove it: let the
base's `sendPolySecurity`, `roundSecurity` and `roundsSecurity` (`SumcheckRound.lean:299, 371,
429`) take the prover's polynomials `P` apart from the family `Φ`, stating the security of
`round P j Φ.weight` (the proofs are unchanged, since nothing in them reads `P`); then prove
`Sumcheck.roundsSecurity` with the family whose honest polynomial is the degree-`d` polynomial
`exists_claim_poly` (`:346-358`) supplies, chosen classically. That family enters the state
function and the proofs only, never the extractor (`keepExtractor`) or the definition, so the
security still computes; its `Consistent` is `claim_split` and the polynomial's evaluation,
some twenty lines. Worth it when the module goes upstream, where a consumer's honest prover may
compute the round polynomial otherwise than by interpolation; not blocking here, since Layer 7
proves `nodes_injective` once for completeness and passes it twice.

**3. The test's docstring claims a round refutation the file does not contain.** *Convention:
load-bearing checks.* `tests/LeanerVMTests/Protocol/Sumcheck.lean:37-40` says "without its check,
a round of the family has no knowledge error below one"; the new section (`:336-394`) has no
such statement, and the file's only refutation is the final check's (`:316-326`, #75's). The
base's `SumcheckRound.drawChallenge_unchecked_not_rbr` is generic, for any consistent family
whose invariant every challenge restores; this family's instance is the GKR test's shape
(`tests/LeanerVMTests/Protocol/GrandProductSecurity.lean:76-87`): `family V wtOne nodes`,
consistent by `(family_honest V wtOne nodes V_degree nodes_injective).toConsistent`, the
invariant `fun _ ↦ trivial`, from a running claim off by one. Add it, or cut the sentence; the
convention wants the refutation listed in the pull request either way.

**4. Documentation.**
- `protocol-status.md:50` (135 columns), `:196` (105), `:269` (143) exceed the page's width,
  all three written by this commit.
- `protocol-status.md:29`: "the pull request stacked on #75"; fill the number when it opens.
- The status's new sub-bullet (`:243-249`) is accurate on every point checked (the rounds' then
  the last message's, the vacuous soundness clause, the hypotheses, `Nat.card`, the test at
  `overE 3`); it is short of findings 1 and 2.
- `docs/README.md:30-70` lists each review; this file is to be listed.
- The pull request's body: the classification above, and the refutations by name.

### Observations

- **`normalizedSecurity` has no consumer, as #75's finding 2 recorded.** The GKR's layers run
  `SumcheckRound.roundsSecurity` on their own family (`GrandProductSecurity.lean:27-29`), not
  `Sumcheck.normalized`; the table sumcheck is plain. The definition is a two-line specialization
  of `weightedSecurity` at `eqWeights pt` (`Sumcheck.lean:515-520`), non-vacuous (`securityNormalized`,
  `tests:350-355`, over `E`), and adds nothing to the surface a consumer reads; it is built
  because the hole names it in bold, and goes with `Sumcheck.normalized` when the `docs(protocol)`
  request the status records is decided. Nothing new to do.
- **The error's unit and the slot's whole error.** The securities are at
  `(d : ℝ≥0) / (Nat.card F : ℝ≥0)` and the slot at `overE 3 = 3 / Fintype.card E`
  (`Spine/Errors.lean:74-75, 164-167`); the two are equal by `Nat.card_eq_fintype_card`, which
  `natCast_div_card_eq_overE` (`tests:340-342`) states and `Security.mono` applies as an equality.
  The test assembles the slot's middle term only; the batching challenge's `drawError E (overE (B + 2))`
  and its state function ("some constraint extension at `ζ` is nonzero, or some form disagrees
  with its total") are Layer 7's, and the count it needs, `card_filter_powerSum_eq_le`, is in the
  base. The last message's `sayError (Vector E I.tableColumns)` is the slot's last term.
- **`roundsSecurity` is a cast** (`rel_zero nodes V wt ▸ …`, `:484`): a consumer that needs its
  state function or extractor by unfolding meets an `Eq.mpr` on the structure. The file's
  compositions cast the same way (`stateFunctionOfEq`, `guardedAppend`), and the extractor is
  `keepExtractor` on a subsingleton, so nothing is lost today.

## Answers to the questions put to the review

- **The error, and what Layer 7 still needs.** The blueprint's slot charges `3` over `|E|` per
  round of degree three (`tableError`, `Spine/Errors.lean:164-167`:
  `roundsError E 3 (overE 3) I.τmax`); `weightedSecurity` at `d = 3` is at
  `roundsError F 3 (3 / Nat.card F) n`, the same function of the challenge index once
  `Nat.card E = Fintype.card E` is rewritten, which the test does; `tableRoundsSecurity` lands on
  the slot's term for `I = Toy.toy` (`τmax = 1`, one round) at the rounds' schedule
  `roundsSpec E 3 I.τmax`. So the rounds are raised to the slot's error at the slot's schedule;
  the whole slot's error is not assembled, which is right, since `ξ`'s term is the table phase's.
  Missing for Layer 7: finding 1, both parts. The relations otherwise match the seam's objects:
  `relIn V unitWeights` is `T = Σ_x summand(x)` through `weightedCubeSum_one`
  (`ToCompPoly/WeightedCube.lean:94-100`), and `relOut V` is one claim per table at the point in
  coordinate order, which is a column claim at the low coordinates once the copying lift's
  extension is related to the table's (Layer 7's, with `Padding.lean`).
- **The hypotheses.** `hV` (degree at most `d` in each variable) is necessary: let the summand
  have degree `d + 1` in the round's variable, so the true round function `g` has degree `d + 1`;
  from a false claim `T` the prover sends `q := g − c·∏_{i ≤ d} (X − a_i)`, `c` the leading
  coefficient of `g`, of degree at most `d`, with the `a_i` distinct and chosen so that
  `q(0) + q(1) = T`; the verifier accepts, and the next claim is true at the `d + 1` points
  `a_i`. The state before is false (`toFun_empty`), the state after the
  final message is true wherever the honest values are accepted (`toFun_full`), and a prover's
  message cannot turn it true (`toFun_next`), so whatever the extractor and the state function,
  the flip happens at the challenge with probability `(d + 1)/|F| > d/|F|`. `Subsingleton W`
  (`SumcheckRound.lean:303`) is necessary: with the tables read off a free witness (say `W := F`
  and a constant table `w`), every challenge `x` has a witness making the next claim true, so the
  bad set is all of `F` and the error one; the hypothesis is why the sumcheck is stated for a
  component whose knowledge is the oracle's, and the phases have `W = Unit` (`Spine/Phase.lean:49-54`).
  `hnodes` is not necessary (finding 2).
- **`normalizedSecurity`.** Meaningful as a theorem, idle as an interface; the observation above.
- **The state function.** With `inv := True`, `Family.Sound` (`SumcheckRound.lean:176-180`) is
  `¬ True → …`, discharged by `absurd trivial` (`Sumcheck.lean:485`; probed as an `example`), and
  `card_badChallenge_le` (`SumcheckRound.lean:305-360`) never enters its third case. The bound
  then rests on `Family.Consistent` alone: `check` (the honest polynomial sums to the honest
  claim over the domain) and `next` (it evaluates to the next honest claim). That is correct and
  complete: a recorded polynomial that passes the check at a false claim is not the honest one,
  since the honest one sums to the true claim; two distinct polynomials of degree at most `d`
  agree at `d` points at most; and if the recorded polynomial is the honest one and passes, the
  claim was true and no challenge is bad. The invariant exists for families that carry a side
  fact (the GKR's riders), which this one does not. The state function is "the running claim is
  the true running claim", which is false on every false claim and true on every true one, and
  between a message and its challenge adds "the recorded polynomial is the honest one". The
  bound is tight within the hypotheses: over `E` with `d = 3`, from a false claim `T` the prover
  sends the honest polynomial plus `(T + T₀)·X³ + b`, which sums to `T` over `{0, 1}` and agrees
  with the honest one where `X³ = b/(T + T₀)`, three points when `b/(T + T₀)` is a cube
  (`gcd(3, 2^192 − 1) = 3`): escape probability exactly `3/|E|`. No statement within the
  hypotheses breaks the bound; the two outside it are above.

## Pass A: the statements

Read before the proofs, from the blueprint and ArkLib's definitions. Besides the answers:

- `Component.Security` (`Component.lean:149-158`) is `rbrKnowledgeSoundnessWorstCaseWith` for the
  named extractor and state function, at an error that is a parameter (decision 10, 20): no
  security here declares its own, and the test raises to the slot's (test 32).
- Non-vacuous: `securityPlain`, `securityNormalized` (degree two, two variables, `t₁ · t₂`) and
  `tableRoundsSecurity` (degree three over the toy's stack, `Vtoy_degree` through
  `DegreeLEAt.evalMle`, `nodes4_injective` from `y ∉ {0, 1}` and `y + 1 ∉ {0, 1, y}`) are
  inhabitants with every hypothesis discharged.
- Computes (test 24, convention *Extractors*): the three test securities and `extractionPlain`
  are `def`s without `noncomputable` and the module compiles; no security takes a real number or
  a `Fintype` instance (`[Finite F]`, `Nat.card`), and `Security.mono` and `Security.append` are
  inlined.
- Substitution test: with `finalCheck` replaced by `fun _ _ ↦ true`, `finalSecurity`'s proof loses
  `hc` and fails, and `final_unchecked_no_stateFunction` says no proof exists; with the round
  check dropped, `card_badChallenge_le` loses `hc` and `drawChallenge_unchecked_not_rbr` says no
  proof exists. The relations specify, the checks follow.
- `finalSecurity`'s hypothesis to `sendCheckedSecurity` is exactly what the final check and the
  output relation give: `formula(point, values) = claim` and `values = tables(point)` make the
  claim the summand at the point, `mem_rel_self` in reverse (`:493-497`). Its signature carries
  no unused instance (probed: no `Finite F`, `SampleableType F` or `Subsingleton W`).
- `weightedSecurity`'s `hV` quantifies over every context, witness and oracle included, as the
  degree of a formula in the tables' extensions does.

## Pass B: fidelity at `a386121f`

The protocol is Category A; the Lean is the standard. The expectation was formed from the
specification first.

- **Fact 3** (`03-proving-primitives.tex:79-85`): per round `h_j(0) + h_j(1) = claim`, degree at
  most `d`, the next claim `h_j(c_j)`, and "a false claim survives with probability at most
  `dκ/|E|`". The Lean: `d/|F|` on each of `n` challenges, `0` on each message, summing to
  `n · d/|F|` (`sum_roundsError`, `Schedule.lean:178-187`). The same object.
- **§5.5** (`05-arithmetization.tex:145-155`): "the soundness error is `(3τmax + nside + B)/|E|`:
  `3τmax` for the rounds (Fact 3) and `nside + B` for the `ξ`-batching". The rounds' share is the
  Lean's at `d = 3`, `n = τmax`; the batching's is the slot's `B + 2` on `ξ` (one less than the
  specification's count of powers, the spine's recorded choice, `Spine/Errors.lean:57-59`), not
  this commit's. The final check "`acc ≠ claim` rejects" is `finalCheck`, settled in #75.
- **The Rust.** The production module cites nothing of leanVM, as a generic module must; the
  deployed verifier's absence of a round check is the wire's business (`Sumcheck.transport`,
  #75). The test's one citation (`transcript.rs:289-309`) is unchanged by this commit.
- Checks modelled: two (the round's, the final's); refuted: two (the base's and #75's, the
  former not instantiated for this family in the tests, finding 3). Deviations declared: none.

## Pass C: hygiene

`Sumcheck.lean` stays generic (grepped for layer, decision, hole, acceptance, ledger, blueprint,
leanVM, GKR, Flock, WHIR, bus, slot: none); the five docstrings are one to three lines and name
what each definition says; the module docstring's new sentence (`:51-56`) carries the argument
in words and no proof narration; no import changed; no line over 100 columns in either Lean
file. The test's new section is clear and its names say what they state. The status page's
three long lines are finding 4.

## Kernel axioms

`Sumcheck.roundsSecurity`, `finalSecurity`, `weightedSecurity`, `plainSecurity`,
`normalizedSecurity`, and the tests' `securityPlain`, `securityNormalized`, `extractionPlain`,
`tableRoundsSecurity`: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## What was checked and found sound

The five statements against the blueprint's hole and the convention *Holes*; the error against
Fact 3, §5.5 and the slot; the state function and the vacuous soundness clause against the
textbook argument; the three hypotheses, two necessary by explicit strategies and one not; the
tightness of the bound; the inhabitants over `E` and that they compile; the kernel axioms; the
generic module's vocabulary; the aggregate imports; the scripts; the status's sub-bullet; the
verifier's independence of the nodes and the relations' independence of the nodes.

## What could not be checked

The pull request's description, not yet open. `lake test` and `./scripts/validate.sh`, not run on
the memory-limited machine; only the sumcheck test module was built. Whether the GKR's own
securities carry the same artifact as finding 2 (their honest polynomials' consistency is a
hypothesis of the same shape), not read for it.
