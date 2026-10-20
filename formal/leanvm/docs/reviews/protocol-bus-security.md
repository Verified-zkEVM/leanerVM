# Review: the bus phase's knowledge soundness

> An archive of the review of one commit on the branch `feat/protocol-bus-security`, `f2d44dc`,
> against its base `feat/protocol-bus` (#79, reviewed in `docs/reviews/protocol-bus.md` on that
> branch and not re-reviewed here except where the security half depends on it). Names, paths and
> line numbers are those of `f2d44dc`. What is accepted from it is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of the
> pull request that met it.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. the check `R_c ≠ 0` is refuted at the roots step only, and nothing records the phase-level refutation as owed | recorded as owed: the status page says what a phase-level refutation takes (the generic backward induction, and the honest prover accepted after every vector of challenges); the step-level refutation stays in the bus tests |
| 2. `|E|` is written `2^192` in a production count, against the *Errors* convention, and the departure is not named | met: the module docstring and the status page say why `|E|` is `2^192` there, and that the convention *Errors* is owed a rewording |
| 3. no test exercises the clause the challenge step's bound rests on | met: the unbalanced stack and its guards are in the security tests |
| 4. audit surface: `Bus.length_tuples` is public | met: `length_tuples` is private |
| 5. the status page is short of the new work | met: the pull request number, the narrative, the owed blueprint edit with `busSecurity`, the long line, the missing noun, findings 1 and 2 recorded |
| 6. the module docstring has no pinned citation and no authoring note; the work is not classified | met: Theorem 5.1, §6.2 and the deployed check cited with the pin, a note on how the module was written; the classification is in the pull request description |

Reviewed with the `adversarial-review` skill in three passes. Reading order: the blueprint first
(the conventions *Errors*, *Load-bearing checks*, *Holes*, *Seams*, *Extractors*, lines 311-329;
`What the spine fixes`, the `Phases.Security` sketch; Layer 5's riders paragraph and Layer 6,
lines 841-928, in particular the state-function paragraph at 915-922; decisions 3, 10, 11, 18, 20;
acceptance tests 1, 3, 6, 24, 32; the Interfaces list's rule at 1429), then specification §5.2
(Theorem 5.1, `th:product_check`, in `doc/leanvm/body/05-arithmetization.tex`) and §6.2 "The
count product" (`06-bus-interactions.tex`), read from the working tree of
`/home/scaraven/Documents/leanEthereum/leanVM`, which is past the pin (no `git` was run there;
#78's review checked Theorem 5.1's constant at the pin); then the consumers' and producers' Lean:
`Spine/Errors.lean` (`overE`, `busSpec`, `busError`), `Spine/Seams.lean` (`Seam.commit`,
`Seam.bus`), `Spine/Compose.lean` (`Phases.Security`), `Spine/Phase.lean`, `ToArkLib/Component.lean`
(`Security`, `Security.mono`, `Security.append`, both `@[macro_inline]`),
`ToArkLib/SampleChallenge.lean`, `ToArkLib/SendChecked.lean`'s security,
`ToArkLib/Refutation.lean`, the header, relations and `gkrSecurity` of
`ToArkLib/GrandProduct.lean` and `ToArkLib/GrandProductSecurity.lean`,
`Fingerprint.lean`'s `card_sideProduct_collision_le`, `Bus.lean` (the steps, `afterChallenge`,
the riders, the side products, `busPhase`, `busComplete`) and the bus tests; ArkLib's
`KnowledgeStateFunction` and `rbrKnowledgeSoundnessWorstCaseWith`
(`.lake/packages/Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean:165-191, 557-571`).
Then the new files in full: `LeanerVM/Protocol/BusSecurity.lean`,
`tests/LeanerVMTests/Protocol/BusSecurity.lean`, the status page diff and the aggregates.
`audit-lean.sh`, `check-imports.sh`, `check-layers.sh`, `check-docs.py` and
`check-repository.sh` pass on the worktree (checked out at `f2d44dc`, clean). Two Lean processes
were run, one at a time under the shared `flock`: the commit's test file (42 s, 3.2 GB peak, no
error and no warning) and a probe (below), twice. Nothing in the repository was edited.

Target classification: the commit message names the hole but not the target. The pull request's
description should say: artifact, the bus phase's security half (its extractor, which keeps the
trivial witness, its knowledge state function, and worst-case round-by-round knowledge soundness
at `busError I`, from `Seam.commit` to `Seam.bus`); the soundness direction, completeness being
#79's; ideal oracle model with the inner-product oracle, Category A (the relations and the state
function written from §5.2, §6.2 and the blueprint's Layer 6, nothing transcribed from the Rust);
contribution to T4 through `piop_rbrKnowledgeSoundness`, as the `bus` field of
`Phases.Security`, conditional on the other phases.

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological, and `busSecurity I h` fills the slot: its type is
`Phases.Security.bus`'s for any bundle whose bus is `busPhase I h` (probe 2), at `busError I`
with no extra term, and its kernel axioms are the three standard ones. The error charged to
`(α, β)` is justified exactly: from a stack outside `M3Holds`, a challenge reaches
`afterChallenge` only when the four clauses no challenge touches hold, in which case the bus is
unbalanced, the two multisets differ and have at most `2^{μ_bus}` tuples each (push by its
definition, pull by `Conditions.pull_fits`), so `card_sideProduct_collision_le` counts at most
`4·2^{μ_bus}·|E|⁴` bad challenges, and `challenge_error_eq` turns that over `|E|⁵` into
`overE (4·2^{μ_bus})` with equality. The roots and the values are sound at no error by the two
implications #79's review probed, now in the commit. The zerocheck adds nothing: the riders sit in
`Gkr.relIn`/`Gkr.relOut`, `gkrSecurity` is at `gkrError` whatever the riders, and a rider's escape
at a coordinate is dominated by the claim's at the same challenge (a false state turns true only
when each of its false conjuncts does, so the bad set is the larger of the two, not their union).
The side conditions bound the instance, not the stack or the prover, so per instance the
statement is as strong as the blueprint's `busSecurity I h₁ h₂`. It computes: no definition takes
a real number or a `Fintype` instance, the two `mono`s and three `append`s are `@[macro_inline]`,
and the probe confirms that `|E|` must be a numeral in the count for that (finding 2). Every
finding is Low: the refutation of the one check stops at the roots step (finding 1), and the rest
is a convention's wording, test coverage, audit surface and documentation.

## Findings, most severe first

### Low

**1. The check `R_c ≠ 0` is refuted at the roots step only, and nothing records the phase-level
refutation as owed.** *Load-bearing checks (`protocol-blueprint.md:321`); acceptance test 3.*
`roots_unchecked_no_stateFunction` (`tests/LeanerVMTests/Protocol/Bus.lean:248-266`) shows that
without the check the roots step has no knowledge state function from `Bus.afterChallenge` to
`Gkr.relIn`, whatever the extractor. The convention asks for a theorem that the verifier without
the check has no round-by-round knowledge soundness *at the phase's seams* below error 1: the
step-level result excludes the decomposition `busSecurity` composes through, not a knowledge-sound
phase at other intermediate relations. #79's review asked that the status page record the
phase-level refutation as owed by this pull request; the page says "a refutation at the phase's
seams is not attempted" (`docs/roadmap/protocol-status.md:258-265`), and this commit leaves it.

No mutation survives the build: removing or weakening the check breaks `rootsSecurity` (it reads
`r.2 ≠ 0`, `BusSecurity.lean:139`), and `afterChallenge` cannot lose its count clause without
breaking `card_afterChallenge_le` (a balanced stack with a zero count would make every challenge
bad). So this is the convention's letter, not a hole in the security.

A phase-level refutation is true and feasible. On `busToy`, `zeroCount` is outside
`Seam.commit`, and without the check the honest prover reaches `Seam.bus` at every challenge
vector (its products agree since the bus balances, its riders are zero, so the grand-product
argument's and the values' completeness apply). The generic half is a backward induction over the
rounds, compiled in the probe (`not_rbr_of_tree`, about thirty lines over
`Verifier.not_rbr_of_escape`): from a statement with no witness and a family of prefixes that
contains the empty one, is closed under every challenge and some message, and whose full
transcripts are accepted, some challenge has error at least one, whatever the extractor and the
state function. The instance half is the cost: the unchecked phase as a `Def`; its perfect
completeness from `M3Holds` without `CountsNonzero` (the four completeness halves, with
`afterChallenge` less its count clause); and either a generic lemma that the honest run of a
perfectly complete reduction with a guarded verifier answers every challenge prefix with an
accepted full transcript (the support of `Prover.run` covers every challenge vector), or honest
message functions for the phase's rounds; then `busError busToy i < 1` for every `i`.

Fix: add the generic lemma to `ToArkLib/Refutation.lean` and the phase-level test, or, if the
support lemma is out of this pull request's scope, rewrite the status sentence as an owed item
naming that cost (the generic half is cheap, the support lemma is what is missing) and list the
step-level refutation in the pull request's description as the convention asks.

**2. `|E|` is written `2^192` in a production count, against the *Errors* convention, and the
departure is not named.** *Errors (`protocol-blueprint.md:311`: "`|E|` is `Fintype.card E`,
rewritten to `2^192` only in the numeric test").* `challengeSecurity`
(`BusSecurity.lean:117-122`) passes the count `4 * 2 ^ I.μBus * (2 ^ 192) ^ 4` to
`Component.sampleChallengeSecurity`, converted by the private `natCard_E` (`:68-69`) inside
`card_afterChallenge_le` (`:74-101`) and `challenge_error_eq` (`:104-115`). It is necessary: the
probe's copy with `Nat.card E ^ 4` fails to compile ("depends on 'Nat.card', which is
'noncomputable'"), `Fintype.card E` would compile but enumerate `E` when evaluated, and passing
the error instead runs into the rule that a security takes no real number. It is harmless: the
error stays the slot's `overE`, on `Fintype.card E`, and `card_E` is a theorem. But the
convention's sentence is now false of the built work, and the status page
(`protocol-status.md:266-271`) states the choice without calling it a departure. Fix: name it in
the status page as a departure from *Errors*, and add to the owed `docs(protocol)` edit the
convention's new wording ("…and in a bad-challenge count that a computable security passes as a
natural number").

**3. No test exercises the clause the challenge step's bound rests on.** *Test quality;
`AGENTS.md` ("a mutation, counterexample, or negative test for the condition doing the real
work").* The new tests (`tests/LeanerVMTests/Protocol/BusSecurity.lean:18-33`) type the security
and its extraction; the condition doing the work here is the product clause of `afterChallenge`
with `card_afterChallenge_le`, and no test, here or in the bus tests, has a stack whose only
failing clause is `Balanced` (`honest` fails none, `zeroCount` fails the counts). Nothing
executable shows that an unbalanced stack meeting the other clauses is kept out of
`afterChallenge` at a challenge. The proof pins it (a trivial product clause makes the count bound
false), so this is coverage, not a defect. Fix: the probe's stack `unbalanced`
(`a = [1, 0]`, counts `x, x + 1`) with its four guards (constraints and counts hold, `Balanced`
fails, `M3Holds` fails, the push and pull products differ at the tests' `(α, β)`), all of which
pass; and one sentence in the test docstring pointing to `#guard M3Holds busToy () honest` and
`zeroCount` as what makes `Seam.commit` neither empty nor full.

**4. Audit surface: `Bus.length_tuples` is public.** *Interfaces (`protocol-blueprint.md:1429`:
a declaration not listed "is `private` where the module system allows").* `Bus.length_tuples`
(`BusSecurity.lean:61-65`) is used only by the private `card_afterChallenge_le` (`:87`, `:90`),
and a theorem's body is never exposed, so it can be private, as #79's review did for that
module's proof-only lemmas. The three step securities must stay public, since the exposed
`busSecurity` refers to them, as `busComplete` does to the completeness halves. Fix: make it
private.

**5. The status page is short of the new work.** *Documentation.*
`docs/roadmap/protocol-status.md`: (a) `:33`, the placeholder `PRC`; (b) `:35-37`, "of those, the
public-input phase is built": with #79 and this commit both halves of the bus phase are built (on
merge); (c) `:278-281`, the owed blueprint edit lists `busPhase I h` but not `busSecurity I h` at
`(busPhase I h).toDef` (the blueprint's `:900` has `busSecurity I h₁ h₂ : Phase.Security I
(busPhase I h₁ h₂) …`); (d) `:42`, a line already over 100 columns grows to 148; (e) `:60-61`,
"on the grand-product argument's and the collision bound" drops its noun; (f) the owed item of
finding 1 and the departure of finding 2. Fix accordingly when the pull request opens.

**6. The module docstring has no pinned citation and no authoring note; the work is not
classified.** *Self-sufficiency; `AGENTS.md`'s classification rule.* `BusSecurity.lean:14-44`
cites "Theorem 5.1" without its file and the pin, and the count check without §6.2; it does not
say how it was written (Category A, from §5.2, §6.2 and the blueprint's state function, nothing
from the Rust). The commit message names the hole but not T4. Fix: one sentence in the module
docstring (`doc/leanvm/body/05-arithmetization.tex`, Theorem 5.1, and
`06-bus-interactions.tex`, "The count product", at `a386121f84292f6fa663aaa3e570c15bc0240ea2`;
written from the specification), and the classification above in the pull request's description.

### Observations

- **The side conditions restrict the instance only.** `Bus.Conditions` is the phase's own
  hypothesis (`busPhase I h`), proof-irrelevant, about sizes; it excludes no stack and no prover,
  so knowledge soundness per instance is as strong as the blueprint's two-hypothesis signature.
  `pull_fits` is used here twice (the pull multiset's size, `prod_pullLeaves`), `count_fits`
  through `prod_countLeaves_ne_zero_iff`; both are necessary (#79's review). That
  `leanIsaInstance` meets them is the adaptor's, as recorded.
- **Non-vacuity.** `Seam.commit busToy` holds of `honest` and fails of `zeroCount` and of the
  probe's `unbalanced`; the spine's toy has a stack failing each clause (acceptance test 27).
  `Seam.bus` is inhabited by `busComplete`'s honest runs, which matters: with an empty output
  relation a state function false after round zero would make any phase sound at error 0.
- **Where the zerocheck is paid.** The riders are tracked only on the last layer's coordinates
  (`constTrack` before, `progTrack` there), which is right since every coordinate of `ζ` is drawn
  in the last step; the low point `ζ_{<τ_j}` of `Seam.bus` is the riders' `lowPoint ζ τ_j` by
  `lowPoint_point`. Acceptance test 6 is met by construction; Layer 6 asks no executable test
  for it, and the grand-product tests carry "a rider nonzero at the final point rejected except at
  the charged challenge".
- **One joint draw.** `(α, β)` is one challenge of `(Fin 4 → E) × E`, charged
  `4·2^{μ_bus}/|E|`; the deployed transcript squeezes five scalars. That is the spine's schedule;
  its cost under state restoration is Layer 12's.
- **The specification's sizes.** Theorem 5.1 pads both sides to the same `2^μ`; the Lean bounds
  each multiset by `2^{μ_bus}` separately, which is more general and gives the same constant.

## Pass A: the statements

Read against the blueprint's Layer 6 paragraph and the spine before the proofs.

- **`busSecurity`** (`BusSecurity.lean:166-174`): `Phase.Security I (busPhase I h).toDef
  (Seam.commit I) (Seam.bus I) (busError I)`, the `bus` field of `Phases.Security` for a bundle
  whose bus is `busPhase I h` (probe 2); composed as
  `((challenge ⟫ roots) ⟫ gkr.mono) ⟫ values`, the shape of `busComplete`, so the error is
  `errAppend` of the parts', definitionally `busError I`. Decisions 10, 11 and 20 and acceptance
  test 32 hold by type.
- **`challengeSecurity`** (`:117-122`): `sampleChallengeSecurity` at the count
  `4·2^{μ_bus}·(2^192)^4`, raised by `mono` with `challenge_error_eq` to
  `drawError _ (overE (4·2^{μ_bus}))`, the slot's error. The bad challenges are those that carry a
  stack outside `M3Holds` into `afterChallenge` (`card_badChallenge_le_of_unit`).
  `card_afterChallenge_le` (`:74-101`): if counts, constraints, lines or Flock fail, none (they do
  not depend on `(α, β)`); otherwise `¬ Balanced`, so the multisets differ
  (`Multiset.coe_eq_coe`), with sizes `leafCount 0 ≤ 2^{μ_bus}` (`length_tuples`, `blocks_total`,
  `push_fits`) and `leafCount 1 ≤ 2^{μ_bus}` (`pull_fits`), and the agreeing products are
  `sideProduct`s (`prod_pushLeaves`, `prod_pullLeaves`). Theorem 5.1's constant with the 4 of
  acceptance test 1. The blueprint's state after `(α, β)` (`:915-918`) is `afterChallenge` word
  for word.
- **`rootsSecurity`** (`:129-141`): `sendCheckedSecurity` with the reflection "check passes and
  the output is in `Gkr.relIn` ⇒ the input is in `afterChallenge`": the shared root equals both
  products, the count root is the count product and nonzero, so `CountsNonzero`
  (`prod_countLeaves_ne_zero_iff`); the riders give the rest (`ridersZero_iff`).
- **`valuesSecurity`** (`:148-162`): the reflection "`Seam.bus` of the output ⇒ `Gkr.relOut` of
  the input", for every message: the column claims force the values, `sum_forms_eq_total_iff`
  gives the leaf claims, the zerocheck conjunct and the lines give `riders_vanish_iff`.
- **The grand product**: `gkrSecurity 3 μ_bus (leaves I) (riders I)` at `gkrError E (1/Nat.card E)`,
  raised to the slot's `gkrError E (overE 1)` by `overE_one`, an equality.
- **Substitution test.** Replacing `afterChallenge`'s product clause by `True` breaks
  `card_afterChallenge_le`; dropping its count clause breaks it too (zero counts would make every
  challenge bad); weakening the roots' check breaks `rootsSecurity`. The statement is not a
  restatement of the verifier.
- **Coverage.** The soundness direction of the bus phase in full: the fingerprint (§5.2), the
  count product (§6.2), the grand product with its riders (§5.3, the zerocheck of §5.5 paid
  here), the decomposition and the forms (§5.4). The phase-level refutation of the check is
  finding 1.

## Pass B: fidelity

Nothing in this commit is transcribed: the relations, the state function and the errors are
Category A, and the definitions they read are #79's (reviewed against `leaf.rs` and `gkr.rs` at
the pin). Against the specification: the error on `(α, β)` is Theorem 5.1's `4·2^μ/|E|`, the
`μ` of §5.2 being the padded log-size of a side, the Lean's `μ_bus`; the count check is §6.2's
"the verifier checks it is nonzero", and the state after the roots asks exactly the two facts
§6.2 and §5.2 draw from the roots. The Rust was not consulted, as the Category A discipline asks;
nothing in the commit claims Rust correspondence. Pass B found nothing.

## Pass C: hygiene and policy

- **Comments.** Docstrings are one or two lines except `busSecurity`'s four, a major result; no
  roadmap, layer, hole or acceptance-test reference in either Lean file ("slot" is the spine's
  vocabulary, as in `Spine/Errors.lean`). No line over 100 columns in either Lean file. The module
  docstring carries the design (finding 6 for what it lacks).
- **Surface.** Public: `Bus.length_tuples` (finding 4), the three step securities (required by the
  exposed `busSecurity`), `busSecurity`. Private: `natCard_E`, `card_afterChallenge_le`,
  `challenge_error_eq`. `natCard_E` restates `card_E` for `Nat.card`; private is right while the
  bus is the only phase with a challenge in `E^5`.
- **Imports.** `public import` of `Bus` and `ToArkLib/GrandProductSecurity`, both needed by the
  exposed body. Aggregates: one entry each, in order (`check-imports.sh` passes).
- **Computability (acceptance test 24, *Extractors*).** The test file's `security`, `extraction`
  and `toySecurity` are plain `def`s and compile; no definition of the commit takes a real
  number or a `Fintype` instance (`[Finite C]` is a proposition); both `mono`s and the
  `append`s are `@[macro_inline]`.
- **Tests: what they catch.** The test file compiles the security at the slot's error on two
  instances; everything else is caught by the proofs (a weaker check, a smaller error, a trivial
  product or count clause). Surviving: nothing in the code; the unbalanced-stack coverage is
  finding 3.
- **Status page.** Finding 5.

## Probe

Run with `flock /tmp/claude-1000/leanerVM-lean.lock lake env lean` from the worktree, whose files
are the commit's.

```lean
import LeanerVM.Protocol.BusSecurity
import LeanerVM.Protocol.Spine.Compose
import LeanerVMTests.Protocol.Bus

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Bus LeanerVMTests.Protocol.Bus
  CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

-- 1. Each: [propext, Classical.choice, Quot.sound].
#print axioms LeanerVM.Protocol.busSecurity
#print axioms LeanerVM.Protocol.Bus.challengeSecurity
#print axioms LeanerVM.Protocol.Bus.rootsSecurity
#print axioms LeanerVM.Protocol.Bus.valuesSecurity
#print axioms LeanerVM.Protocol.Bus.length_tuples

-- 2. The slot. Compiles.
example (I : M3Instance) (h : Bus.Conditions I) (P : Phases I) (hP : P.bus = busPhase I h) :
    Phase.Security I P.bus.toDef (Seam.commit I) (Seam.bus I) (busError I) :=
  hP ▸ busSecurity I h

-- 3. Why `2 ^ 192`. Fails: "failed to compile definition, consider marking it as
-- 'noncomputable' because it depends on 'Nat.card', which is 'noncomputable'".
def challengeSecurityNatCard {I : M3Instance} (h : Conditions I) :
    Component.Security (challengeStep I) (Seam.commit I) (afterChallenge I)
      (drawError _ (((4 * 2 ^ I.μBus * Nat.card E ^ 4 : ℕ) : ℝ≥0) /
        (Nat.card ((Fin 4 → E) × E) : ℝ≥0))) :=
  Component.sampleChallengeSecurity _ _ _ _ (4 * 2 ^ I.μBus * Nat.card E ^ 4) fun s o _ ↦
    Component.card_badChallenge_le_of_unit _ _ _ _ s o fun _ ↦ by sorry

-- 4. An unbalanced stack meeting the other clauses (finding 3). All four guards pass.
def unbalanced : Column 2 := ⟨#v[1, 0, K.ofBits 2, K.ofBits 3]⟩

#guard busToy.ConstraintsVanish unbalanced ∧ busToy.CountsNonzero unbalanced
#guard ¬ busToy.Balanced unbalanced
#guard ¬ M3Holds busToy () unbalanced
#guard (∏ x : Fin (2 ^ busToy.μBus), (pushLeaves busToy α β unbalanced)[x]) ≠
  ∏ x : Fin (2 ^ busToy.μBus), (pullLeaves busToy α β unbalanced)[x]

-- 5. The generic half of a phase-level refutation (finding 1). Compiles.
theorem not_rbr_of_tree {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
    {V : Verifier oSpec StmtIn StmtOut pSpec} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {relIn : Set (StmtIn × WitIn)}
    {relOut : Set (StmtOut × WitOut)} {WitMid : Fin (n + 1) → Type}
    {Ex : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    {kSF : V.KnowledgeStateFunction init impl relIn relOut Ex} {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut WitMid Ex kSF ε)
    (hε : ∀ i, ε i < 1) (s : StmtIn) (hin : ∀ w, (s, w) ∉ relIn)
    (Reach : (m : Fin (n + 1)) → Transcript m pSpec → Prop) (h0 : Reach 0 default)
    (hchal : ∀ j : Fin n, pSpec.dir j = .V_to_P → ∀ tr, Reach j.castSucc tr →
      ∀ c, Reach j.succ (tr.concat c))
    (hmsg : ∀ j : Fin n, pSpec.dir j = .P_to_V → ∀ tr, Reach j.castSucc tr →
      ∃ msg, Reach j.succ (tr.concat msg))
    (hacc : ∀ full : pSpec.FullTranscript, Reach (Fin.last n) full → ∃ witOut,
      0 < Pr{let stmtOut ← OptionT.mk do
        (simulateQ impl (V.run s full)).run' (← init)}[(stmtOut, witOut) ∈ relOut]) :
    False := by
  have key : ∀ m : Fin (n + 1), ∀ tr, Reach m tr → ∃ w, kSF.toFun m s tr w := by
    intro m
    induction m using Fin.reverseInduction with
    | last =>
      intro tr hr
      obtain ⟨witOut, hpos⟩ := hacc tr hr
      exact ⟨_, kSF.toFun_full s tr witOut hpos⟩
    | cast j ih =>
      intro tr hr
      cases hdir : pSpec.dir j with
      | P_to_V =>
        obtain ⟨msg, hm⟩ := hmsg j hdir tr hr
        obtain ⟨w, hw⟩ := ih _ hm
        exact ⟨_, kSF.toFun_next j hdir s tr msg w hw⟩
      | V_to_P =>
        by_contra hbad
        have := Verifier.not_rbr_of_escape h ⟨j, hdir⟩ s tr (not_exists.mp hbad)
          fun c ↦ ih _ (hchal j hdir tr hr c)
        exact absurd (hε ⟨j, hdir⟩) (not_lt.mpr this)
  obtain ⟨w, hw⟩ := key 0 default h0
  exact hin _ ((kSF.toFun_empty s w).mpr hw)
```

Results: every printed result has the kernel's three axioms and no `sorryAx`; the slot example,
the four guards and `not_rbr_of_tree` compile; `challengeSecurityNatCard` is rejected by the
compiler as quoted, which is the evidence for finding 2's "necessary".
