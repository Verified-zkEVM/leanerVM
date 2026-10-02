# Review: the grand-product GKR at the slot's schedule, definition and completeness

> An archive of the review of one commit, `156e981` of pull request #62 (branch
> `feat/protocol-gkr-v2`, against its base `09f58f0`, pull request #65 on top of `main`): names,
> paths and line numbers are that commit's. What is accepted from it is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of the
> pull request that met it. It replaces the review of `efca3af`, whose findings are listed at the
> end with what this commit does about each.

**Disposition** (met in the commit after `156e981` unless the row says otherwise):

| Finding | Disposition |
| --- | --- |
| 1. the slot's type is a `FrontDef`, `gkr` is a `Component.Def` | recorded in the status's GKR item with the two ways out and the one proposed (`Phases.bus` as a `Phase.Def` with an oracle-freeness witness); the Lean change is the bus phase's, with decision 31. A test now composes the bus phase's shape around `gkr 3 toy.μBus` as a `Phase.Def` at `busSpec toy`. |
| 2. the status promises the parts "become" Layer 4's without the conditions | the two conditions (the family form; `batch` as `sampleChallenge` at the batching map) and the three blueprint asks are in the status's GKR item. |
| 3. roadmap vocabulary in two generic modules | reworded. |
| 4. implementation-only imports marked `public` | plain `import` of `ToPoly.RingHom`; `ToPoly.Degree` was not needed and is gone. |
| 5. documentation left stale by this review and by the merge | `docs/README.md` describes this review; the status says "on the branch of #62". |
| 6. the bus phase's prefix instances | declared in `Spine/Errors.lean` beside the bus slot's, as the step's are beside `stepSpec`. |
| 7. a pitfall that narrates an earlier form | the history dropped. |
| the observation on `normalizedWeights` past the point | the domain past the point is empty. |
| the observation on `Gkr.odd` being partial where `oddSpec` is total | kept: a `Fin 2` index would cast `μ % 2` on both sides of the schedule. |

Reviewed with the `adversarial-review` skill in three passes: the statements against the
blueprint's Layer 5, its conventions *Pinned conventions*, *Generic code*, *Sumcheck messages*,
*GKR*, *Sumcheck variants* and *Holes*, decisions 16, 17, 18, 20, 23, 26 and the spine's slot
(`LeanerVM/Protocol/Spine/Errors.lean`: `busSpec`, `busError`), with the Lean the standard and the
Rust possibly wrong; fidelity to leanVM `a386121f` (`crates/lean_vm/src/gkr.rs:1-430`,
`crates/fiat_shamir/src/transcript.rs:289-309`, `crates/primitives/src/multilinear.rs:36-41,
243-247`), run from the Rust before reading the Lean's checks; and hygiene. Lean was probed with
`lake env lean` on a scratch file (axioms, instance identity, a bus-shaped composition at
`busSpec I`) and on both test files. Nothing was edited but this file.

Target classification: the pull request names T4 through the bus phase, completeness only; the
knowledge-soundness half is a separate hole. That is stated correctly in the description.

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological; the five relations name independent objects
(`Finset.prod` over the table, CompPoly's `evalMle`, `partialSum`), the kernel axioms of
`gkrComplete`, `gkr`, `SumcheckRound.roundComplete`, `Component.sendCheckedComplete`,
`Component.sampleChallengeComplete` and `evalMle_contractPow` are the standard three, and both
test files compile without a warning. The component is at the slot's *schedule*: `gkr nside μ
leaves : Component.Def … (gkrSpec F nside μ)` type-checks by definitional equality through the
prefix instances, the instance its type carries is `instOracleInterfaceGkr` by `rfl`, and a
bus-shaped composition `draw ++ₚ say ++ₚ gkrSpec E 3 I.μBus ++ₚ say` with this `gkr` in the slot
type-checks at `busSpec I` as a `Phase.Def` once two prefix instances are declared. It is not at
the slot's *type*: `Phases.bus` is a `Phase.FrontDef`, whose verifier is a `FrontVerifier`, and
`gkr`'s is an `OracleVerifier` that keeps the oracles; nothing composes `FrontDef`s and no brick
has a front form, so the bus phase cannot consume `gkr` as the spine stands (finding 1). The six
design choices of the refactor are the right ones for the knowledge-soundness half that will
stack on them, for the reasons given under *The design choices*. The schedule, both checks, the
next claim, the interpolation bit order, the point order, the combiner's powers and the errors
match the pinned Rust. Below the first finding: the status page's promise that the local round
and the combiner "become" Layer 4's components is unconditional where it should name two
conditions, and small hygiene items.

## Findings, most severe first

### Medium

**1. `gkr` fills the slot's schedule and error, not the slot's type.** *Fit to the spine;
interface.* The slot is `Phases.bus : Phase.FrontDef I I.Stmt (I.Stmt × BusOut I) (busSpec I)`
(`LeanerVM/Protocol/Spine/Compose.lean:80`), and a `FrontDef` is a prover with a
`verifier : FrontVerifier []ₒ StmtIn StmtOut pSpec` (`Spine/Phase.lean:71-76`), a computation over
the shared oracles and the messages alone (`ToArkLib/FrontVerifier.lean:72-74`). `gkr` is a
`Component.Def` (`ToArkLib/GrandProduct.lean:572-576`) whose verifier is ArkLib's
`OracleVerifier.append` of `sendCheckedVerifier`, `sampleVerifier` and `passThroughVerifier`, each
keeping the oracles through `keepOracles` (`SendChecked.lean:63-67`, `SampleChallenge.lean:58-60`).
There is no `FrontDef.append`, no `FrontVerifier.append`, no front form of the three bricks, and
`FrontVerifier.toOracleVerifier` (`FrontVerifier.lean:83-85`) does not commute with
`OracleVerifier.append` definitionally. The one front phase built so far writes its two-round
verifier by hand (`PublicInput.lean:225-228`); a thirteen-round GKR cannot be. Verified: the
composition
`((sampleChallenge … ).append (sendChecked …)).append (gkr 3 I.μBus leaves)).append (sendChecked …)`
type-checks at `Phase.Def I I.Stmt … (busSpec I)` (with the two prefix instances of finding 6),
and `Phase.FrontDef` is a different structure. Concrete consequence: Layer 6 cannot write
`Phases.bus` from this `gkr`; the status's "at the spine's slot shape" (`protocol-status.md:78`)
is true of the schedule and the error only. Two ways out, one of them the spine's open decision
31 (`protocol-blueprint.md:1556-1558`): (i) `Phases.bus` becomes a `Phase.Def` with a separate
oracle-freeness witness (`∃ F, verifier = F.toOracleVerifier`, or a `Front` predicate), proved
for the bricks by construction and for `Def.append` by one lemma; (ii) each brick gets a
`FrontVerifier` with its oracle verifier *defined* as the lift, a generic `Component.FrontDef`
with `append` and `toDef`, and a propositional `toDef_append` along which `Complete` and
`Security` transport (`Component.lean` already has `stateFunctionOfEq` and
`rbrKnowledgeSoundnessWorstCaseWith_of_eq` for the latter). Fix for this pull request: say in the
status's GKR item that the slot's verifier type is not met and which option is taken, and draft
the decision-31 line for the blueprint; the Lean change belongs to whichever option is chosen.

**2. The status promises the parts "become" Layer 4's components without the conditions.**
*Documentation.* `docs/roadmap/protocol-status.md:81-85`: "its sumcheck rounds … for
`Sumcheck.normalized`; its combiner, `Gkr.lambdaStep`, for `batch nside`. When those holes land,
the parts become them". Two conditions are missing. First, the blueprint's `Sumcheck.normalized`
takes a `Virtual F n m d`, a formula in `m` fixed tables (`protocol-blueprint.md:808-815`), and the
GKR's summand (`GrandProduct.lean:149-151`) is a formula in tables read from the step's context
(the trees' levels from the oracles, the combiner and the point from the statement); only a
family form (`SumcheckRound.Family`, `SumcheckRound.lean:120-128`) can take it. This was the
earlier review's finding 4, left to the blueprint, and the blueprint's Layer 4 is unchanged.
Second, `Gkr.lambdaStep` (`:282-284`) is `sampleChallenge` with the map
`s ↦ lambdaNext (inp s)`, which relabels the input through `inp` and builds the stage-0 statement;
`batch nside` can replace it only if `batch` takes the statement maps as arguments, because a
relabelling pass-through on either side would put a `!p[]` into the schedule and break the
definitional equality with `stepSpec`. The honest line is that `batch` is `sampleChallenge` at
the batching map and `batchSecurity` its escape-count instance. Fix: add both conditions to the
item, and carry the three blueprint asks of the pull request's description (the last combiner's
place, batching among the GKR's *Needs*, the family form) into the status, which is where what
the built work owes the blueprint is recorded.

### Low

**3. Roadmap vocabulary in two generic modules.** *Surface.* `GrandProduct.lean:46-47`: "the
one the spine's bus slot names" ("spine", "bus slot" are this repository's roadmap words);
`SumcheckRound.lean:55`: "as the deployed verifiers read them" (leanVM's). The *Generic code*
convention forbids protocol vocabulary in a `To*` module. Fix: "its schedule is
`gkrSpec F nside μ`, so that a protocol's slot at that schedule takes it", and "as a verifier
reading coefficients off a wire does".

**4. Implementation-only imports marked `public`.** *Hygiene.* `GrandProduct.lean:14-15`:
`public import CompPoly.Univariate.ToPoly.RingHom` and `… ToPoly.Degree`. `toPolyRingHom_apply`
is used only inside the proof of `degree_roundPolyRaw_le` (`:178-190`), no name of `Degree.lean`
appears in the file, and the statement's `CPolynomial.degree` comes from `Univariate/Basic`
through `SumcheckRound.lean`'s `public import CompPoly.Univariate.ToPoly.Impl`. `CONTRIBUTING.md`
asks for `public import` only when a downstream user needs the dependency transitively. Fix:
plain `import` for both, and check whether `Degree` is needed at all.

**5. Documentation left stale by this review and by the merge.** *Documentation.*
`docs/README.md:50-53` describes the archived review of `efca3af` (2026-09-30) and its findings;
once this file replaces it the bullet must describe this review (2026-10-02: the slot's verifier
type, the conditions on Layer 4's components). `protocol-status.md:30-31`: "The grand-product
GKR's definition and completeness are built" sits in the paragraph that describes `main`, five
lines after the row says "on merge" (`:25`); say "on this pull request's branch", or leave the
row to say it.

**6. The bus phase's prefix instances.** *Observation for Layer 6.* Built one append at a time,
the bus phase meets `draw ((Fin 4 → E) × E) ++ₚ say (E × E)` and
`… ++ₚ gkrSpec E 3 I.μBus`, for which instance search fails (a literal left schedule, as
`Schedule.lean:40-46` records); `Spine/Errors.lean:106-112` declares the instances of the whole
`busSpec I` only. The probe needed both before the composition of finding 1 type-checked. They
belong to `Spine/Errors.lean` beside `instOracleInterfaceBus`, as this pull request put the step's
prefixes beside `stepSpec` (`Schedule.lean:201-227`), or go away with the schedule bundle the
spine-revision review suggested.

**7. A pitfall that narrates an earlier form.** *Documentation.* `tests/README.md:64-66`: "in an
earlier form of the sumcheck round's message" is history; the pitfall (a `#guard` on a subtype
value built by hand with its proof never returns) stands without it. The other two new pitfalls
(`:61-63`, `:67-70`) are accurate and self-contained.

### Observations

- `SumcheckRound.normalizedWeights` past the point (`SumcheckRound.lean:117`) gives the weights
  `1, 0`, a check `h(0) = claim` that no round reaches (`j < m` throughout); it makes the
  definition total, and an upstream reader will ask why those weights. `[]` or unit weights would
  read as "no opinion".
- `Gkr.odd` (`GrandProduct.lean:522-526`) is partial where `oddSpec` (`Schedule.lean:303-305`) is
  total: every `r ≥ 1` is the binary layer for the schedule, only `r ≤ 1` for the component, with
  an `absurd` branch. A `Bool` or `Fin 2` index on both would remove the dead branch.
- `degree_roundPolyRaw_le` (`:173`) is public and used by the private `roundPoly_eval` only; it is
  a true fact worth keeping public for the transport lemma. Nothing else public should be private
  and nothing private should be public; every public declaration of the six modules has a
  docstring.
- Audit surface: 119 public declarations besides instances across the six modules (`SendChecked`
  8, `SampleChallenge` 7, `SumcheckRound` 27, `GrandProduct` 48, `ProductTree` 19, `PartialSum`
  7), 3 added to `Multilinear.lean`, 6 instances added to `Schedule.lean`; 15 private. Twelve of
  the public ones are the parts' `*Complete` pieces, which the composition is made of. No dead
  declaration: `evalMle_contractPow` is used by no proof, as before, and is the closed form the
  module documents and the integer test checks (`tests/…/ProductTree.lean:58-63`).

## The design choices

For each choice of the refactor, whether it is the right one for the knowledge-soundness half
whose design is: the state function of a `sampleChallenge` step is the input relation before and
"check ∧ output relation" after, with an escape-count hypothesis; the riders' state in the last
layer is progressive restriction.

- **Coefficient vectors as round messages** (`SumcheckRound.lean:76-99`). Right. The blueprint's
  *Sumcheck messages* row is "every coefficient, low degree first"; the type says the degree bound
  as a length, so a prover cannot send a sixth coefficient and the transport lemma's decoding is
  an injection of the four wire scalars into `Vector F 5` with `c_0` derived. ArkLib's
  `Sumcheck.Impl.Representation.Message` is the subtype `{p : CPolynomial R // p.degree ≤ deg}`
  (`Impl/Representation.lean:25`), a value with a proof, which stalled kernel evaluation in a
  `#guard` (`tests/README.md:64-66`) and is queried by evaluation in the typed framework, whereas
  here the message is read whole. The security half needs one lemma: two distinct vectors of
  length `d + 1` agree at most at `d` points, through `Polynomial` (`evaluate` is
  `Polynomial.eval` of `∑ q_i X^i`).
- **The round split with the check at the challenge** (`sendPoly` pure, `drawChallenge` checks;
  `SumcheckRound.lean:175-196`). Right, and the reason is the security half's shape. The escape
  bound at the challenge is "claim false, check passes, `q(c)` is the true next claim", which
  forces `q ≠ p` and so at most `d` challenges; the check must be a hypothesis of the *same*
  component's escape analysis. With the check at the message, the generic challenge brick would
  not see it, and the mid relation would have to encode "check → claim true" to keep the escape
  bounded. The cost is `MidStmt` recording the polynomial, which is also what the state function
  needs. For completeness `relMid` (`:149-151`) adds "the polynomial is the honest one"; the
  security half's mid state can be "claim true" alone, since a dishonest `q` with a true claim
  escapes at most `d` times too.
- **Generic bricks with a Boolean `check`** (`SendChecked.lean`, `SampleChallenge.lean`). Right.
  The Boolean check and the pure `out` are exactly `GuardedForm`'s two fields, so
  `sendCheckedGuarded` and `sampleGuarded` are immediate and the security half's hypotheses read
  "`s ∉ relIn → check s = true → #{c | f s c ∈ relOut} ≤ k`" (error `k/|C|`, by VCVio's uniform
  bound in `ToVCVio/UniformSample.lean`) and "`s ∉ relIn → check s m = true → out s m ∉ relOut`"
  (error `0`). `fun _ ↦ true` in five of seven uses costs nothing; a second brick without a check
  would mean a second proof.
- **`interpolate` on a prefix, `interpDone` folded into the last challenge**
  (`GrandProduct.lean:404-421`). Forced and workable. Forced by `draws C (k + 1) = draws C k ++ₚ
  draw C` (`Schedule.lean:112-114`, itself forced by `draws C k : ProtocolSpec k`) and by
  `stepSpec` ending in `draws C ρ` with no `!p[]` after it. Workable because `InterpStmt … i`
  (`:334-335`) carries the `i` challenges drawn, so the security half can state the progressive
  restriction of the descendants' values and of the riders at each prefix (the completeness-side
  `childRel i`, `:362-364`, ignores them, which is fine: it is not the state function). The
  alternative is a `drawsRounds` like `roundsRounds` and `draws C (k + 1) = draw C ++ₚ draws C k`,
  after which `interpolate` recurses as `rounds` does with a `(drawn, remaining, h)` index and
  `interpPrefix`, `interpPrefixComplete` go; `flockRoundsOf` and `stepRounds` would read
  `drawsRounds k` for `k`. Either is sound; the two repeated-round combinators nesting in opposite
  directions is the only cost of the present one.
- **The first step reads the roots through `inp`** (`:277-284, 459-467, 522-526`). Forced and
  generic. `oddSpec C nside 1 = stepSpec C nside 1 0` leaves no room for a relabelling pass-through
  at `!p[]`, and `sampleChallenge`'s `f` is where a relabelling folds; `inp = id` for every later
  step. Typing `gkr`'s input as `LayerStmt X F nside 0` instead would push the relabelling to the
  consumer and depart from Layer 5's signature.
- **The prefix instances in `Schedule.lean`** (`:201-227, 344-350`). Forced by ArkLib's instance
  search failing on literal-left appends; `Def.append` must synthesize the intermediate schedule's
  instances. They are the price of composing at a closed-form schedule, and the family grows with
  every composition shape (finding 6). The schedule bundle the spine-revision review suggested
  would remove the family.

Two facts the security half will lean on, checked here. `SumcheckRound.Family.inv` is per stage
(`Ctx → (j : ℕ) → Vector F j → Prop`), so the riders' progressive restriction fits it, and
`inv_push` holds of it (a restriction of an identically zero function is identically zero);
`Gkr.family` fixes `inv := RidersZero` (`:213`), which serves completeness only, since the final
state must be implied by `relOut`'s "vanishes at `lowPoint ζ τ`" and `RidersZero` is not. The
security half instantiates a second family on the same `roundPoly` and `weights`; no definition
depends on `claim` or `inv` (`SumcheckRound.lean:43-45`), so nothing in `gkr` changes. And
`gkrError` is the right target: per prefix the escape is one of the claim's (`2^ρ` roots per
round, `nside − 1` per combiner) or a rider's or a descendant value's (one root per coordinate),
so the worst case per challenge is the larger, which is what `stepError` charges.

## The recorded divergences, verified

| Divergence | Verdict |
| --- | --- |
| `gkr` at `gkrSpec F nside μ` with no error; `gkrComplete` extends `Guarded` | Met for the schedule and the error (the earlier review's first divergence is closed); not met for the slot's verifier type (finding 1). `gkr` is now computable, so an executable honest run of the composed reduction is possible in principle (not attempted, see below). |
| Rounds on a local `SumcheckRound` with coefficient messages | Justified and recorded (`protocol-status.md:81-83, 89-90`); the blueprint's `Sumcheck.normalized` cannot take it as written (finding 2). |
| Riders on the relations and `gkrComplete`, not on `gkr` | Justified and recorded (`:86-88`); `gkr` reads no rider. |
| A rider's variable count is `Fin (μ + 1)` | Justified and recorded (`:88-89`): `lowPoint ζ τ` needs `τ ≤ μ`. |
| The unused last combiner inside `gkr` and `gkrSpec` | As the blueprint's Layer 5 and *GKR* row put it; the module docstring now says what it is written from and why the combiner stays (`GrandProduct.lean:57-58`). The blueprint change is pending. |

## Pass A: the statements

- `Gkr.relIn` (`GrandProduct.lean:121-123`): every rider table zero, every root the product of
  its leaves. Inhabited by `root`, `roots16`, `roots8` and refuted by `root'`
  (`tests/…/GrandProduct.lean:132-133, 157, 251`). Sound.
- `Gkr.relOut` (`:133-135`): each value is `evalMle` of its leaves at `ζ`; each rider's extension
  vanishes at `lowPoint ζ τ`. Reached by the three hand runs (`:150, 240, 286`); the rider conjunct
  separates `t1` from `atRoot` (`:326-330`). A verifier interpolating in the other bit order or
  appending the point the other way fails it on the honest run. Sound.
- `Gkr.layerRel` (`:127-129`): the value is the extension of the level on `m` variables at the
  point; `layerTable` is total (ones past the leaves) but every step takes `m + ρ ≤ μ`
  (`layerStepComplete`, `layerSteps`, `oddComplete`). Sound.
- `SumcheckRound.rel` (`SumcheckRound.lean:144-145`): the invariant and "the running claim is the
  family's"; `relMid` (`:149-151`) adds "the polynomial is the honest one"; `Gkr.childRel`
  (`GrandProduct.lean:362-364`): the trees' values are the honest ones at the sumcheck's point.
  All three are exercised by the hand run (`tests:192, 215, 217, 219`). Sound.
- `gkrComplete` (`:581-586`). What it pins: the honest messages pass both checks as written (the
  normalized weights `1 − r_j, r_j` against coordinate `j` of the layer's point; the descendants'
  check with the powers in the combiner's order); the output's point order `(u, c)` and the
  interpolation's bit order; the layer count and the rounds per layer, through the schedule and
  `m + ρ ≤ μ`. What it does not pin: a weaker or absent check (a verifier that checks nothing is
  complete, which is the knowledge-soundness half's job and is said so); a larger degree bound; a
  consistent change of the combiner's powers in both `lambdaNext` and `combineCheck`; the error
  values, which are not in `Complete`. The last three are pinned by tests (`tests:88, 222`;
  `:194, 230-231`; `:93-96`). Substitution test: the proof would not survive unit weights, an
  equality factor in the final check or the other point order. Axioms: `propext,
  Classical.choice, Quot.sound` for all six results probed; no `sorryAx`.
- Evidence of the tests: the hand runs call the verifiers' decision functions
  (`SumcheckRound.check`, `next`, `Gkr.combineCheck`, `childNext`, `interpNext`, `interpDone`,
  `lambdaNext`); `sendCheckedVerifier_verify`, `sampleVerifier_verify` and the composition prove
  that those functions are the oracle verifiers' verdicts. The four rejections (`:298-305`) each
  fail the named check and nothing else.
- Gates: `audit-lean.sh`, `check-imports.sh`, `check-layers.sh`, `check-docs.py` pass; both test
  files compile with `lake env lean`, exit 0, no warnings.

## Pass B: fidelity to `gkr.rs` at `a386121f`

Enumerated from `verify_product_triple` (`:358-430`) and the prover it mirrors (`:258-355`,
helpers `:32-74, 100-233`), ticked against the Lean:

| Rust | Lean | Match |
| --- | --- | --- |
| `lambda = sample()` after the roots (`:369`); `claim = poly_eval(values, λ) = Σ_s λ^s value_s`, Horner constant first (`:376`; `multilinear.rs:243-247`) | `Gkr.lambdaStep`, `lambdaNext` (`GrandProduct.lean:272-284`); every `layerStep` begins with it | yes |
| binary layer at the root when `μ` is odd: two tails per tree, `claim == Σ λ^s left·right` (`:377-386`), one challenge, `interp(left, right, χ)`, `point = [χ]`, λ resampled (`:387-394`) | `Gkr.odd 1 = layerStep 1 0 rootStmt` (`:522-526`): combiner, no round, `sendChildren` with `combineCheck` over `Fin 2`, `interpolate` with one challenge, point `cast (#v[u_0] ++ #v[])` | yes |
| radix-4 layer: `round_count = μ − layer` rounds; round `j` against `point[j]`: `next_round_poly(5, claim, Some(r_j))` reads `c_1 … c_4` and derives `c_0 = claim + r_j (c_1 + … + c_4)` (`:397-401`; `transcript.rs:289-302`), which is `(1 − r_j) h(0) + r_j h(1) = claim`; `claim ← h(χ_j)` (`:402-404`) | `SumcheckRound.round` on `Gkr.weights = normalizedWeights (layer's point)` (`SumcheckRound.lean:116-117, 183-196`; `GrandProduct.lean:204-205`), `m` rounds at depth `m` (`:464`), `Message F 4` of five coefficients | yes (every coefficient sent, decision 26) |
| equality points consumed in order `point[0], point[1], …`; the prover folds the lowest row bit first with `eq_table(&point[1..])` shrunk each round (`:311-312, 398`; `:168-179`) | `partialSum` binds coordinate `j` at round `j`; `roundPolyRaw` weights by `lagrangeBasis ((pointOf ctx).drop (j + 1))` (`PartialSum.lean:49`; `GrandProduct.lean:162-168`) | yes |
| four tails per tree, `claim == Σ_s λ^s t0·t1·t2·t3`, no equality factor (`:406-412`) | `Gkr.combineCheck` (`:344-346`), from `partialSum_self` | yes |
| `low = sample(); high = sample()`; `value = interp(interp(t0, t1, low), interp(t2, t3, low), high)`, `interp(lo, hi, t) = lo + t(lo + hi)` (`:414-421`; `multilinear.rs:36-41`); the tails are the four values at `4x + c` (`children`, `:229-232`; `fold`, `:174-179`) | `interpolate` draws `u_0` then `u_1`; `interpDone` takes `evalMle [t0, t1, t2, t3] (u_0, u_1)`, bit 0 = `u_0` (`:400-421`); `childIndex ρ c x = c + 2^ρ x` (`ProductTree.lean:67`) | yes (the Rust's form is the characteristic-2 instance of `(1 − t) lo + t hi`) |
| `point = [low, high] ++ round_point` (`:424-425`) | `Vector.cast (u ++ c)` (`:401`); tests `[b, a, c0, c1]` and `[c, b, a]` (`tests:238, 285`) | yes |
| λ resampled after every layer, the last unused (`:423`) | `lastCombiner` (`:542-544`) at `drawError C 0` (`Schedule.lean:362-364`) | yes |
| `build_layers`: `next[2 row] = current[4 row] · current[4 row + 1]`, `next[2 row + 1] = current[4 row + 2] · current[4 row + 3]` (`:44-46`) | `contract` (`ProductTree.lean:48-51`) | yes |
| errors (blueprint Layer 5): `(nside − 1)/|E|` per combiner but the last, `0` on the last, `4/|E|` per radix-4 round, `2/|E|` per binary round, `1/|E|` per combination challenge | `gkrError`; `tests:93-96` by `rfl` | yes |
| `μ = 0`: one sampled λ, no layer (`:369, 374`) | `odd 0`, `layerSteps 0` pass-throughs, then `lastCombiner`: one challenge | yes |
| the tails' order on the wire (tree-major, `:406-409`) and five coefficients against four | the compiled verifier's decoding (Layer 12) | out of scope |

Counts: the Rust has two explicit checks (the binary and the radix-4 layer checks, `:384`,
`:411`) plus the implicit wire format (four coefficients read, `c_0` derived); the Lean has
`check` per round (the derived-`c_0` equation as a check, by decision 26) and `combineCheck` per
layer, plus the type-level bound `Vector F (2^ρ + 1)`. Challenges for `μ = 4`:
`1 + (0 + 2) + 1 + (2 + 2) + 1 = 9`; for `μ = 3`: 7; for `μ = 2`: 4 (`tests:71-73`); acceptance
test 17's `μ²/4 + μ + 1` holds. The `FirstTwoShared` root shape (`:360-368`) is the bus phase's.
No historical (Poseidon, KoalaBear, LogUp) material. The description's citations (`:258-430`,
`:369, 391, 423`, `:398-404`, `:410-412`, `:414-425`) point at the right lines.

## Pass C: hygiene

Findings 3, 4, 5, 7 and the observations. Otherwise clean: module shape (header, `module`,
imports, module docstring, `@[expose] public section`) as `Component.lean`; no Lean line over 100
columns in any changed file (the status page's two long lines, `:25` and `:120`, are table rows
like the file's others); docstrings on every public declaration of the six modules; the module
docstrings carry the design and the ArkLib #818 name map without narrating proofs; `LeanerVM.lean`
and `tests/LeanerVMTests.lean` register the five production modules and the two test modules
(the reorder of four `Semantics.*` test imports is an unrelated tidy-up); no letter codes.

## What was checked and found sound

The definitional fit at the slot's schedule (the instance identity by `rfl`, the bus-shaped
composition as a `Phase.Def` at `busSpec I`); the schedule, the two checks, the next-claim rule,
the descendants' check, the interpolation bit order, the point order, the λ-power convention and
the per-challenge errors against the pinned Rust and the blueprint's *GKR* and *Sumcheck
variants* rows; the five relations for semantic content and inhabitation; the kernel axioms of
the six results; both test files; the four repository scripts; the dependencies bullet against
ArkLib at the pin (`ProofSystem/Sumcheck/Impl/Representation.lean:25-28` is a degree-bounded
subtype evaluated by Horner, `Interaction/Protocol.lean:151-157` sums the domain with unit
weights, `Interaction/Legacy.lean` relates single-round relations and the honest execution only,
`Domain.lean` has per-coordinate domains and no weights); the recorded divergences; the eleven
findings of the earlier review (below).

## What could not be checked

- An executable run of the composed `gkr` on the toy: `gkr` is computable now, but running
  ArkLib's `OracleComp` reduction was not attempted; the hand runs through the parts' decision
  functions and the verdict lemmas cover the wiring. Worth a `#guard` if it is cheap.
- The Python verifier as a cross-check of the schedule (not consulted; the Rust, the blueprint
  and the Lean agree, and acceptance test 17's counts hold).
- The security half's fit: reasoned above from the design, not built.
- `lake build --wfail`, the full `./scripts/validate.sh` and the kernel axiom audit over the whole
  namespace (CI).

## The earlier review

The review of `efca3af`, finding by finding, and what `156e981` does about it:

1. The unused last combiner inside a generic module: still inside `gkr` and `gkrSpec`, as the
   blueprint has it; the docstring now says what the module is written from and why the combiner
   stays. The blueprint change is pending.
2. The combiner is `batch nside`, unrecorded: met in the status (`Gkr.lambdaStep` named as the
   stand-in); the holes table's *Needs* for the GKR's knowledge soundness still omits batching
   (`protocol-blueprint.md:579`), pending; see finding 2 on the condition.
3. The degree bound and the combiner's power order unguarded: met (`tests:88, 222`; `:194,
   230-231`; listed in the description's "Refutations of the checks").
4. Whether `Sumcheck.normalized` can take the GKR's rounds: open in the blueprint; the status
   promises the switch without the condition (finding 2).
5. `boolVec_cubeIndex` dead: met (removed).
6. `evalMle_contractPow` documentary: kept as documented, tested over the integers.
7. Proof helpers public, docstrings missing: met (fifteen private theorems across the six
   modules; every public declaration documented).
8. Roadmap vocabulary in `SumcheckRound.lean`: met there; a new instance in
   `GrandProduct.lean:46-47` (finding 3).
9. Lines over 100 columns: met in every Lean and test file.
10. Status header pre-empting the merge; restated errors: met for the header and the errors; the
    "are built" sentence remains (finding 5).
11. Description and test header: met ("Each step is its own combiner"; "four, eight and sixteen
    leaves").
