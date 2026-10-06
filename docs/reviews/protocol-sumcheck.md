# Review: the sumchecks' definitions and completeness, and the wire's transport

> An archive of the review of one commit, `ba66c9a` of the branch `feat/protocol-sumcheck`,
> against its base `7dbb95b` (`feat/protocol-gkr-security`, the GKR's knowledge soundness, itself
> stacked on pull request #62): names, paths and line numbers are that commit's. No pull request
> was open for the branch at the time of the review. What is accepted from it is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of the
> pull request that met it.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. the transport keeps the oracle protocol's message type; nobody owns the step from the wire's `d` scalars | met in `0ca8b85`, the first route: `TranscriptMap S pSpec' pSpec` maps transcripts of one schedule to another with the same directions, carrying the challenges across by a bijection (`chal`, `chal_bijective`); `Sumcheck.transport` is stated from `wireSpec F d`, `d` values then the challenge, with `decodeWire` injective (`encodeWire_decodeWire`) onto the messages that pass the check (`decodeWire_encodeWire`); the tests decode the Rust's wire for both dropped coefficients and degrees two and three; the status says Fiat–Shamir's absorption of the wire and the whole protocol's map are the compiled verifier's |
| 2. the normalized variant built here has no consumer in the protocol | met in part in `0ca8b85`: the status bullet records the blueprint change it implies (the GKR consumes `SumcheckRound.rounds` on `SumcheckRound.normalizedWeights`; `Sumcheck.normalized` kept only with a named consumer, or dropped) as a `docs(protocol)` request; `Sumcheck.normalized` and its security are kept until the blueprint decides, since the hole names them in bold |
| 3. no lemma gives a coordinate degree one, so Layer 7 cannot bound its summand with what is supplied | met in `0ca8b85`, beyond the finding: the uniform bound also added the padding's and the equality factor's degrees though they sit in different coordinates (four instead of three), so the bound is per coordinate (`DegreeLEAt`, with `coord_self`, `coord_ne`, `of_set_eq`, `sub`), `IndividualDegreeLE` its universal form; `tableShaped_degree` bounds a summand of the table sumcheck's shape at three |
| 4. the final check has no refutation | met in `0ca8b85`: `final_unchecked_no_stateFunction` beside `finalComplete`, generalized to any witness type, and a test that for every statement with its claim moved off the summand no knowledge state function exists |
| 5. public surface and hygiene | met in `0ca8b85`: the four helpers are private; docstrings on every rule; `Mathlib.Algebra.Polynomial.BigOperators` imported privately where used (the statements need `Degree.Defs` and `Eval.Defs`, imported publicly); the long lines wrapped; the citation `289-309`; the `erw` kept with a comment (the index type `Fin (2 ^ 1)` is `Fin 2` only after unfolding, and `rw` does not see it) |
| 6. documentation | met in `0ca8b85`: `CONTRIBUTING.md` carries the ledger and watch-list clause; this review is listed in `docs/README.md`; the status row's number and the pull request body's classification are filled when the pull request opens |
| the observation on the unconstrained `c_0` of a plain round in characteristic two | met in `0ca8b85`: guards on `coeffWeight` for both domains, and the module docstring says why each variant drops its coefficient |
| the observation on `TranscriptMap.ofMessage` and the whole protocol's map | no change needed: per round the statement holds the running claim; the whole protocol's map is the compiled verifier's (status) |
| the observation on `evalMle` of a lifted table | no change needed: CompPoly defines `eval₂Mle t φ z` as `evalMle (map φ t) z` (`CompPoly/Multilinear/Basic.lean:582`), so the bridge is `rfl` |

Reviewed with the `adversarial-review` skill in three passes: the statements against the
blueprint's Layer 4 and Layer 7, the conventions *Sumcheck variants*, *Sumcheck messages*,
*Generic code*, *Load-bearing checks*, *Holes*, *Extractors* and *Table sumcheck*, the holes
table's Layer 4 rows, acceptance tests 7, 8, 16 and 20, decisions 16, 26 and 33, and ArkLib's
`Verifier.rbrKnowledgeSoundnessWorstCaseWith` and `Verifier.KnowledgeStateFunction`
(`.lake/packages/Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean:165, 557`), read before
the proofs; the expectation for the table sumcheck formed from the specification at the pin
(`doc/leanvm/body/03-proving-primitives.tex`, Fact 3 and "Two savings on a round message";
`05-arithmetization.tex` §5.5, the formula `F` and "Rounds bind `X_{τmax−1}` first") before the
Rust (`crates/fiat_shamir/src/transcript.rs:289-309`, `crates/lean_vm/src/constraints.rs:243-291`,
`crates/lean_vm/src/cpu/mod.rs:726-743`, each fetched from GitHub at `a386121f`); and hygiene.
Every changed file was read in full, with the base's `SumcheckRound.lean`, `SendChecked.lean`,
`SampleChallenge.lean`, `Component.lean`, `Schedule.lean`, `Oracles.lean`, `Padding.lean`,
`ToCompPoly/Multilinear.lean` and `Spine/Errors.lean` (`tableSpec`). Lean was run three times,
serially: `lake env lean` on a scratch file printing the kernel axioms of the ten public results;
`lake env lean` on a scratch file with the probes reported below; and
`lake build LeanerVMTests.Protocol.Sumcheck`, which was not built in the worktree (157 s, every
`#guard` passes). The repository scripts `audit-lean.sh`, `check-imports.sh`, `check-layers.sh`
and `check-docs.py` pass. Nothing was edited but this file.

Target classification: the commit message names the hole and its direction ("definitions and
completeness"); the pull request, once open, is to say that the work feeds T4 through the table
sumcheck phase (Layer 7), in the completeness direction, that the sumcheck's knowledge soundness
is the next hole, that `Sumcheck.transport` is a soundness lemma, and that the protocol is
Category A (the Lean is the standard) while the wire decoding is Category B, pinned by the tests
against `transcript.rs:289-309`.

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological. The input relation says the claimed sum is
`weightedCubeSum` of the summand (`relIn`, `Sumcheck.lean:162-164`), the output relation that
every value sent is its table's `evalMle` at the final point (`relOut`, `:167-168`); both name
objects defined apart from the verifier, and the verifier's two checks are the deployed ones
(the round's, in the oracle protocol; the formula at the point and the values against the
running claim, `finalCheck`, `:182-183`, which is `constraints.rs:288-290`). Completeness is
inhabited over `E` as plain `def`s with the two hypotheses discharged (`tests:242-256`:
`V_degree` for a product of two tables, `nodes_injective` for `![0, 1, y]`), its kernel axioms
are the standard three, and `Verifier.rbrKnowledgeSoundnessWorstCaseWith_comap` transfers the
guarantee exactly: the comap'd state function is a `KnowledgeStateFunction` of the comap'd
verifier by construction, and the escape probability at each challenge is the original's at the
decoded prefix, so a degenerate map can neither trivialize the conclusion nor change the error.
The variable order is the specification's ("Rounds bind `X_{τmax−1}` first") and the test's guard
on the claim after one round would fail under the reversed order (verified: the two sums differ
on the test's tables). The decoding agrees with the Rust's `next_round_poly` for both dropped
coefficients and for degrees two and three. The design choices recorded in the status serve
Layer 7 and the GKR for the reasons given under *The design choices*, with one gap each in the
lemmas supplied (finding 3) and in what the transport covers (finding 1). The rest is surface,
hygiene and documentation.

## Findings, most severe first

### Medium

**1. The transport keeps the oracle protocol's message type; nobody owns the step from the
wire's `d` scalars.** *Interface; the hole's named deliverable.* The convention *Sumcheck
messages* (`protocol-blueprint.md:309`) and Layer 4 (`:820`) ask for a verifier "composed
with an injective decoding of wire messages onto the messages passing its round check". The wire
message of a round is `d` scalars (`transcript.rs:293-295` reads `n_coeffs − 1` of them); the
oracle protocol's is `Message F d`, `d + 1` scalars (`SumcheckRound.lean:83`). `Sumcheck.transport`
(`Sumcheck.lean:530-540`) composes the round's verifier with `roundDecoding` (`:519-523`), a
`TranscriptMap` of the round's *own* transcripts (`TranscriptMap.lean:45-53` is an endomap of
`pSpec.Transcript k`): the message type does not change, coefficient `k` is overwritten and
otherwise ignored (`decodeRound_set`, `:482-487`). Whoever states the compiled verifier over wire
messages, with Fiat–Shamir absorbing the encoded message (decision 26), still needs one of: a
transport across two schedules that differ in a message type, or a Fiat–Shamir statement that
absorbs an encoding of the message under which the decoded verifier is invariant (`decodeRound_set`
is that invariance). Neither is proved, and the status bullet (`protocol-status.md:222-225`)
records only that the whole protocol's map is Layer 12's and that injectivity is not needed. The
hole table says a hole is built when its bold names "match the section"; this one matches in
spirit and not in the type of the message. Two ways to meet it, the first cheap: (i) generalize
`TranscriptMap S pSpec` to `TranscriptMap S pSpec' pSpec` for two schedules of the same length
and directions whose challenge types agree, with `map_chal` carrying the challenge across the
equality; `Verifier.comap`, the two `comap`s and the theorem keep their proofs, and
`Sumcheck.transport` is then stated from the round's wire schedule `say (Vector F d) ++ₚ draw F`
with the decoding inserting the derived coefficient; or (ii) keep the endomap and write in the
status, under this bullet, that the retyping is owed by the compiled verifier, through which of
the two routes, and that `decodeRound_set` is the lemma it rests on. Either way the pull request
body says which.

### Low

**2. The normalized variant built here has no consumer in the protocol.** *Surface; a blueprint
ask.* `Sumcheck.normalized` (`Sumcheck.lean:220-223`) binds the highest variable first, as
`weighted` does. Its one named consumer, the GKR's layers (*Sumcheck variants*, decision 16),
binds the lowest first on `SumcheckRound.rounds` with `SumcheckRound.normalizedWeights`
(`SumcheckRound.lean:123-124`), and the status says so (`protocol-status.md:210-215`: "not what
it consumes"). The table sumcheck is plain. So the next hole's `Sumcheck.normalizedSecurity`
would be trusted surface no phase reads, unless WHIR's folding rounds (`protocol-blueprint.md:1128`
names "normalized sumcheck rounds") take it, which is undecided. The status records the fact but
not the consequence. Fix: add to the status bullet the blueprint change it implies (the holes
table's `Sumcheck.normalized` and the GKR row's *Needs*, the *Sumcheck variants* row and the
Interfaces list name the normalized sumcheck the GKR consumes, `SumcheckRound.normalizedWeights`
on `rounds`, or `Sumcheck.normalized` gains a consumer), and leave `normalizedSecurity` out of
the next pull request until one exists.

**3. No lemma gives a coordinate degree one, so Layer 7 cannot bound its summand with what is
supplied.** *Coverage of the helpers.* The table sumcheck's summand is
`Σ_t eq(ζ_{<τ_t}, z_{<τ_t}) · ∏_{k ≥ τ_t} z_k · (Σ_i ξ^{o_t+i} C_{t,i}(cols̃_t(z)) + …)`
(`05-arithmetization.tex` §5.5, `constraints.rs:271-274` accumulates the same weights), of
degree `1 + d` in each variable; the formula reads the point for the first two factors, as the
status's first bullet intends. `IndividualDegree.lean` supplies `const`, `add`, `mul`, `sum`,
`prod`, `pow`, `evalMle` and `mvPolynomial_eval` (`:47-119`) and nothing about `fun z ↦ z[k]`,
which both factors need. The only route today is to read `eq(ζ_{<τ_t}, ·) · ∏_{k ≥ τ_t} X_k` as
`evalMle (padHigh (lagrangeBasis ζ_{<τ_t}) _)` through `Padding.lean:54` and a lemma relating
`evalMle (lagrangeBasis r)` to `eq`, which does not exist locally either. Fix: add
`IndividualDegreeLE.coord (k) (hk : k < n) : IndividualDegreeLE (fun z : Vector R n ↦ z[k]) 1`
(the witness is `X` at `k` and `C z[k]` elsewhere), and a test that bounds a two-table summand of
the table sumcheck's shape at `3` with it.

**4. The final check has no refutation.** *Convention: load-bearing checks.* The round check's
omission is refuted by the base's `SumcheckRound.drawChallenge_unchecked_not_rbr`
(`SumcheckRound.lean:383-401`), for every extractor and state function. `finalCheck` has none: the
test shows it rejects wrong values (`tests:119`), not that without it the sumcheck is unsound.
By the round's precedent the refutation would travel with the security half, but it is six lines
here, since the base's `Component.sendChecked_no_stateFunction` (`SendChecked.lean`) is exactly
its shape and the message has no challenge, so "no knowledge soundness below error one" takes
the stronger form "no knowledge state function at all". The following compiles against the
branch (probed):

```lean
theorem final_unchecked_no_stateFunction … (V : Virtual F X O Unit n m) (wt) (nodes)
    (init) (impl) {W'} {E : Extractor.RoundByRound … (say (Vector F m)) W'}
    (K : (Component.sendCheckedVerifier O (Vector F m) (fun _ _ ↦ true) finalOut).toVerifier
      .KnowledgeStateFunction init impl (SumcheckRound.rel (family V wt nodes) n) (relOut V) E)
    (s : SumcheckRound.Stmt X F n) (o : ∀ i, O i)
    (hs : s.2.2 ≠ V.summand ((s.1, o), ()) s.2.1.reverse) : False :=
  Component.sendChecked_no_stateFunction O (Vector F m) (fun _ _ ↦ true) finalOut init impl K s o
    (fun _ h ↦ hs ((mem_rel_self V wt nodes _).mp h))
    (V.values ((s.1, o), ()) s.2.1.reverse) rfl () rfl
```

Add it to `Sumcheck.lean` beside `finalComplete`, and say in the pull request that the round's
refutation is the base's.

**5. Public surface and hygiene.** *Convention: Interfaces; CONTRIBUTING.*
- `Sumcheck.lean:319, 334, 352, 371, 455`: `claim_split`, `exists_claim_poly`,
  `evaluate_roundPoly`, `weightedSum_roundPoly` and `weightedSum_eq_sum` are steps toward
  `family_honest` and the decoding lemmas, consumed nowhere else and in no interface list; the
  first four can be private. `claim_zero`, `claim_self`, `rel_zero`, `mem_rel_self` and
  `family_honest` stay public for the security half.
- `IndividualDegree.lean:47-91`: seven public theorems (`mono`, `const`, `add`, `mul`, `sum`,
  `prod`, `pow`) without a docstring; one line each.
- `IndividualDegree.lean:13`: `public import Mathlib.Algebra.Polynomial.BigOperators` is used by
  no statement of the file; `Sumcheck.lean:342` is what needs it (`natDegree_sum_le_of_forall_le`)
  and should import it itself.
- Lines over 100 columns: `Sumcheck.lean:52` (110), `:126` (105), `:285` (103),
  `WeightedCube.lean:88` (101).
- `WeightedCube.lean:77`: `erw` where `rw` after unfolding the sum would do; harmless.
- `tests/LeanerVMTests/Protocol/Sumcheck.lean:24`: the citation says `transcript.rs:288-309`; the
  function starts at line 289 (the blueprint's `289-309`).

**6. Documentation.**
- `protocol-status.md:28`: the "On `main`" row names "the pull request stacked on #70"; fill the
  number when it opens, as #62's row does.
- The status bullet (`:193-229`) is accurate on every point checked (the formula reads the point;
  no heights; `IndividualDegreeLE`; one construction; `nodes`; rounds and final apart; the
  transport per round; decision 33 by default) and the new watch row's four ArkLib pull requests
  are what it says (titles fetched: native and Sumcheck soundness from local challenge bounds;
  restoration soundness with expected query bounds; stopped restoration security; single-salt
  Fiat–Shamir security and Sumcheck bounds). It is short of what findings 1 and 2 ask.
- `AGENTS.md:105-108` and `docs/dependencies.md:29-31` make the pin-bump rule update the
  blueprint's ledger and the status's watch list; `CONTRIBUTING.md:155-158` states the rule
  without that clause. One sentence aligns them. All three agree with *Generic code*
  (`protocol-blueprint.md:324`).
- `docs/README.md:30-66` lists each review; this file is to be listed.

### Observations

- **A plain round's `c_0` is unconstrained in characteristic two.** With unit weights the
  check's weight on coefficient `0` is `1 + 1 = 0` (`coeffWeight_pair_zero`, probed:
  `coeffWeight (domain unitWeights () 0) 0 = 0` over `E`), so `decodeRound … 0` returns a message
  that passes the check with `c_0 := 0` whatever `c_0` was, and the honest message does not
  survive. That is the reason the plain wire drops `c_1` and the normalized one `c_0`, which the
  specification leaves open ("Two savings", `03-proving-primitives.tex:110`;
  `leanvm-target.md:166-170` records it as unstated). A `#guard` on that weight in the test's
  wire section would pin it.
- **`TranscriptMap.ofMessage` decodes from the statement alone** (`TranscriptMap.lean:61-66`).
  Per round the running claim is in `Stmt X F j`, so it suffices; the whole protocol's map needs
  the running claim from the prefix, which the structure's `map k s tr` allows and `ofMessage`
  does not build. Consistent with the status's "the compiled verifier's to build".
- **A lifted table's extension.** `Virtual.tables` are over the sumcheck's field; the test lifts
  `K`-columns with `CMlPolynomialEval.map (algebraMap K E)` (`tests:198-199`). Neither CompPoly at
  the pin nor `ToCompPoly/` has `evalMle (map φ t) z = eval₂Mle t φ z`, which Layer 7 needs to
  meet the spine's column claims; a CompPoly candidate when it is written.
- `Sumcheck.transport` needs no `coeffWeight ≠ 0`: with a zero weight the decoded verifier rejects
  more, which is sound; completeness of the decoded verifier on the honest wire is
  `decodeRound_of_weightedSum` and is the compiled verifier's to assemble.

## Answers to the questions put to the review

- **`relIn`/`relOut`.** Right. `relIn V wt` is `T = Σ_x (∏_k w_k(x_k)) · summand(x)` with
  `summand` the formula at the point and the tables' `evalMle` (`:94-95, 110-112, 164`); `relOut V`
  is `values = tables' evalMle at the point` (`:168`), the point in coordinate order
  (`finalOut`, `:186-187`; `point_self`, `:285`). The formula's value is checked by the verifier,
  so the output relation rightly pins the tables' values only; the security half will chain
  `finalCheck` and `mem_rel_self` (`:398-402`) to the rounds' relation and `rel_zero` (`:389-394`)
  to `relIn`. `weightedComplete` is non-vacuous: `completePlain` and `completeNormalized`
  (`tests:251-256`) are `def`s over `E` from `V_degree` (`IndividualDegreeLE.evalMle` twice and
  `mul`) and `nodes_injective` (`y ≠ 0, 1` from `y_pow_three`).
- **The design deviations and Layer 7.** The formula reading the point and the absence of
  heights are what `constraints.rs:271-274` and §5.5's `F` need: the weights `w_t` are a function
  of `ζ` (in `BusOut`, hence in `X`), the point and the heights, evaluated by the verifier, and
  the tables of `τ_t` variables are lifted to `τmax` by the copying lift (the extension ignores
  the high coordinates) with the padding product in the formula, which is `F` as written. The
  degree as `IndividualDegreeLE` of the composed summand is the right hypothesis (the sketch's
  `formula_poly` says nothing about the point's factors), and `mvPolynomial_eval` bridges a
  constraint of total degree `d` in degree-one columns; what is missing is finding 3. One
  construction for both variants is sound: the running claim leaves out the bound coordinates'
  weights (`claim`, `:123-127`; `claim_split`, `:319-330`), which is the cofactor form of
  *Sumcheck variants* and of `SumcheckRound.normalizedWeights`. `nodes` is forced by
  characteristic two and only the honest prover reads it. Rounds and final apart are what the
  left-nested `tableSpec` needs; `tests:210-221` builds the slot's shape as a `Phase.FrontDef`.
  The transport per round on a generic theorem is sound and general; what it leaves is finding 1.
  For the GKR, nothing here is consumed (finding 2). Names: `Virtual`, `Sumcheck.plain`,
  `Sumcheck.normalized`, `plainComplete`, `normalizedComplete`, `Sumcheck.transport` are all
  declared; `Virtual` is `Sumcheck.Virtual`.
- **`rbrKnowledgeSoundnessWorstCaseWith_comap`.** Correctly stated. ArkLib's property is, per
  statement, challenge index `i` and prefix `tr`, a bound on the probability that some middle
  witness makes the state true after the challenge while it was false before on the extracted
  witness (`RoundByRound.lean:557-571`). The comap'd state function reads the original at the
  decoded prefix (`TranscriptMap.lean:121`), the comap'd extractor likewise (`:103-104`), and
  `map_chal` makes the decoded prefix extended by the challenge the decoding of the extended
  prefix (`:52-53`), so the event is the original's at `T.map i tr`, with the same uniform
  challenge (`:142-145`). The comap'd state function is a genuine `KnowledgeStateFunction` of the
  comap'd verifier (`toFun_empty` by the subsingleton empty transcript, `toFun_next` by `map_msg`,
  `toFun_full` because `V.comap T` runs `V` on the decoded transcript). A degenerate `T` cannot
  help a consumer: the challenges are kept by the structure, and the conclusion is the standard
  property of the verifier `V.comap T`, which is the verifier the consumer runs.
  `Sumcheck.transport` is the convention's statement up to finding 1. The test matches
  `next_round_poly` at the pin for both cases: `fixed = 1` when `eq` is `None` and
  `c_1 = claim + Σ_{i ≥ 2} c_i` (`transcript.rs:291, 299`; `tests:159-160, 187-188`, degrees
  two and three); `fixed = 0` when `eq = Some r` and `c_0 = claim + r · Σ_{i ≥ 1} c_i`
  (`:301`; `tests:163-164`). The Lean's general formula
  `(claim − Σ_{i ≠ k} c_i · w_i) / w_k` (`:477-479`) specializes to the Rust's in characteristic
  two with the two deployed domains (`coeffWeight_pair_zero`, `coeffWeight_pair_succ`), and the
  Rust's formula is only right there, which the Lean does not assume.
- **Highest first.** Correct: `point` places challenge `c_0` at coordinate `n − 1` (`:118-119`),
  `domain` weighs coordinate `n − 1 − j` at round `j` (`:131-134`), and the final point is the
  challenges reversed (`:187`, `point_self`). The specification says it (§5.5: "Rounds bind
  `X_{τmax−1}` first") and the Rust does it (`constraints.rs:264-269`: `m = n − 1 − j`,
  `chi[m] = rk`). The test's `tests:89` pins it against explicit points; probed on the test's
  tables, the sum with coordinate `0` bound to `r0` differs from `s1.2.2`, so the guard fails
  under the reversed order.
- **The documents.** Accurate and consistent with *Generic code*; finding 6 lists the four small
  items.

## The design choices

Six choices are recorded in the status bullet. All are taken rightly, for these reasons.

- *The formula reads the point; no heights.* The one thing the verifier evaluates itself in the
  table sumcheck is the weights `w_t(ζ, r)` of `constraints.rs:273-280`, a function of the point;
  a generic sumcheck that took heights would bake leanVM's padding into `To*` code against
  *Generic code*. Cost: finding 3.
- *Degree as a hypothesis on the composed summand.* The round polynomial's degree is that of the
  summand in the round's variable, point factors included; the sketch's bound on the formula's
  degree in the values could not give `exists_claim_poly` (`:334-346`).
- *One weighted construction.* `weightedCubeSum_succ` (`WeightedCube.lean:72-83`) is the one
  identity both variants need; the normalized check and the cofactor claim fall out of
  `claim_split`. The GKR does not take it (finding 2), and the table sumcheck does.
- *`nodes` as a parameter.* The honest prover interpolates a black-box function of the point, so
  nodes are unavoidable; the verifier does not read them, so the `Def`'s verifier and the
  compiled verifier are independent of the choice.
- *Rounds and final apart.* `tableSpec I` is `(draw ++ₚ rounds) ++ₚ say` (`Spine/Errors.lean:153-154`),
  so `weighted`'s `rounds ++ₚ say` is not a subterm of it; the test composes
  `(sampleChallenge.append rounds).append final` at `tableSpec Toy.toy` by definitional equality.
- *Transport per round, generic comap.* The generic theorem is the right object for ArkLib; the
  per-round instance is what the base's `Security` of a round delivers. Cost: finding 1.

## Pass A: the statements

Read before the proofs, from the blueprint, the specification's Fact 3 and §5.5, and ArkLib's
definitions. Besides the answers above:

- `Virtual` (`Sumcheck.lean:79-83`) reads the tables off the whole context, witness included,
  as decision 17 has the GKR do; for the table sumcheck the witness is `Unit` and the tables are
  read off the committed oracle, which a relation may do.
- `CoordWeights`, `unitWeights`, `eqWeights` (`:100-107`): `eqWeights` gives `(1 − p_k, p_k)`,
  which `weightedCubeSum_eq` (`WeightedCube.lean:100-105`) identifies with CompPoly's
  `lagrangeBasis`, the blueprint's `eq`. In characteristic two `1 − p = 1 + p`, as *Sumcheck
  variants* writes it.
- `claim` past `n` is `0`, `domain` past `n` is `[]`, `roundPoly` past `n` is the zero
  polynomial (`:125-127, 132-134, 141-145`): never reached by `rounds`, which stops at `n`.
- `family` has `inv := True` (`:154`), so the security half's `Family.Sound` will be vacuous and
  the rounds' error the base's `d / |F|`, the blueprint's `d/|F|` and `d_c/|F|`.
- `weightedComplete`'s hypotheses are needed and not over-strong: `IndividualDegreeLE` for every
  context is what any polynomial summand satisfies, and injective nodes are necessary for
  `evaluate_roundPoly` (`:352-368`, through `Lagrange.eq_interpolate_of_eval_eq`).
- `IndividualDegreeLE` (`IndividualDegree.lean:39-41`) is the existence, for each point and
  coordinate, of a polynomial of degree at most `d` agreeing with the restriction: the notion a
  sumcheck needs of a function, weaker than a polynomial's individual degree over a finite field
  and sufficient (`exists_claim_poly` sums `2^{n−j−1}` such witnesses).
- `transport` (`:530-540`) takes any `Security` of a round at any relations and error; its
  hypothesis is inhabited by the base's `roundSecurity` for a consistent and sound family, which
  `family_honest.toConsistent` and the trivial invariant give. Every extractor in it computes:
  `Extractor.RoundByRound.comap` is function composition, and no `Security` is declared here.
- Substitution test: replacing `finalCheck` by a different check of the same shape would leave
  `relOut` unchanged and `finalComplete` (`:415-420`) unprovable, since it rests on
  `mem_rel_self`; replacing the round check likewise breaks `family_honest.check`. The relations
  specify, the checks follow.

## Pass B: fidelity at `a386121f`

Run from the specification, then the Rust, before the Lean's checks. The protocol is Category A;
the wire decoding Category B.

- **The specification.** Fact 3 (`03-proving-primitives.tex:79-85`) is the textbook round:
  `h_j(0) + h_j(1) = claim`, `claim := h_j(c_j)`, degree at most `d` in each variable. "Two
  savings" (`:110`) drops one coefficient and, for a zerocheck, sends the cofactor one degree
  lower. §5.5 (`05-arithmetization.tex:145-155`) gives `F` with `eq(ζ_{<τ_j}, X_{<τ_j})`, the
  constraints and bus forms batched by powers of `ξ`, the padding `∏_{k ≥ τ_j} X_k`, individual
  degree `d + 1 = 3`, highest variable first, one claim per column at `χ_{<τ_j}`. The Lean's
  `weighted` with `unitWeights`, a formula carrying `eq`, the padding and the powers, degree `3`
  and the values as the last message is that sumcheck; the formula is Layer 7's.
- **`transcript.rs:289-309`, `next_round_poly`.** Four behaviours: the fixed index (`:291`), the
  reads skipping it (`:293-295`), the derivation (`:297-302`), the absorption of the transmitted
  coefficients only (`:303-307`). The first three are modelled by `decodeRound` with `k` a
  parameter and pinned by the test for both fixed indices and for four coefficients
  (`tests:158-168, 184-188`); the fourth is decision 26's and Layer 12's, not modelled here
  (finding 1 asks the status to say so). The function also asserts `n_coeffs ≥ 2` (`:290`),
  irrelevant to `d ≥ 1`.
- **`constraints.rs:243-291`, `verify`.** Checks and steps: `zeta.len() < n` rejects (`:251-253`,
  a parse check for the compiled verifier); per round, four coefficients read with `c_1` derived
  and no round check (`:267`), a challenge at `chi[m]`, `m = n − 1 − j` (`:264, 268-269`), the
  next claim `poly_eval(h, rk)` (`:270`), the weights (`:271-274`); finally `n_cols` values per
  table (`:280`), `acc = Σ_t weights[t] · eval_t` (`:282`), `acc ≠ claim` rejects (`:288-290`). The
  Lean: `n` rounds of `SumcheckRound.round` at degree `3` (the slot's `roundsSpec E 3 I.τmax`),
  each with the oracle protocol's check (removed on the wire by decision 26), the next claim by
  `evaluate`, the challenge appended; one message of all values (`say (Vector F m)`), the formula
  at the point and the values against the claim. Two deployed checks, two modelled; the weights
  and the `ξ` powers are the formula's.
- **`cpu/mod.rs:726-743`.** `ξ` is drawn (`:726`), the target `Σ_s ξ^{B+s} · totals_s` is derived
  and never sent (`:735`), `constraints::verify` runs at `bus.point` (`:736-743`). The slot's
  shape `draw ++ₚ rounds ++ₚ say` and the test's `tableShape` (`tests:210-214`), whose first step
  maps `(s, ξ)` to the statement with the claim, is that shape; the claim it puts there is `0` in
  the test and the derived target in Layer 7.
- **Deviations declared.** None in the Lean's docstrings; the status's six are checked above.
  Characteristic two is not assumed anywhere in `To*/`; the test's values are in `E`.

## Pass C: hygiene

The four modules are generic as *Generic code* asks: no slot, pad value, point or protocol
vocabulary, no reference to the roadmap's bookkeeping (grepped for layer, decision, hole,
acceptance, ledger, target, blueprint, leanVM, GKR, Flock, WHIR, bus: none), each with a header
saying which library it is a candidate for, imports explicit and public only where exposed
definitions need them (one exception, finding 5). Docstrings are one to two lines; the module
docstrings carry the design and no proof narration. The test file's docstring cites the Rust
with the pin. The rest is finding 5.

## Kernel axioms

`weightedComplete`, `plainComplete`, `normalizedComplete`, `transport`,
`Verifier.rbrKnowledgeSoundnessWorstCaseWith_comap`, `decodeRound_of_weightedSum`,
`weightedSum_decodeRound`, `IndividualDegreeLE.mvPolynomial_eval`, `weightedCubeSum_eq` and
`weightedFront`: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## What was checked and found sound

The three relations and the two checks against the specification; completeness inhabited over
`E` for both variants; the comap theorem's transfer; the variable order against the
specification, the Rust and a probe; the decoding against the Rust for both dropped coefficients
and two degrees; the slot's shape at `tableSpec Toy.toy`; the honest round polynomials passing
the check, a changed coefficient, a wrong claim and wrong values rejected (`tests:79-119,
139-154`); the generic modules free of protocol vocabulary; the aggregate imports; the status
bullet's six claims; the watch row's four pull requests; the pin-bump rule in the three
documents against the convention.

## What could not be checked

The pull request's description, not yet open. Whether WHIR (Layer 11) or the Flock phase will
consume `Sumcheck.normalized`, which decides finding 2's second option. The whole `lake test`
and `./scripts/validate.sh`, not run on the memory-limited machine; only the new test module
was built.
