# Review: the grand-product GKR's knowledge soundness

> An archive of the review of one commit, `070fb8a` of the branch `feat/protocol-gkr-security`,
> against its base `771e20c` (the head of pull request #62, branch `feat/protocol-gkr`): names,
> paths and line numbers are that commit's. What is accepted from it is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of the
> pull request that met it.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. every `Security` of the argument is `noncomputable`, and no computable extraction is written | met. Removing `noncomputable` was not enough, for three reasons, each a value the compiler keeps. `Security.mono` and `Security.append` took the errors as implicit arguments, so every caller depended on `NNReal`'s division: both are now `@[macro_inline]`, inlined before compilation, where the errors sit only in types and proofs. The definitions took a `Fintype F` instance, and `Fintype E` is noncomputable: they take `[Finite F]`, a proposition, and count bad challenges with `Nat.card` of a subtype (`sampleChallengeSecurity`'s hypothesis, `Family.Sound`, `RiderTrack`'s escape fields), the proofs building `Fintype.ofFinite F` and turning the count into a `Finset` one by `natCard_subtype_eq_card_filter`. The parts took the unit `u` as an argument, which a slot would pass as `overE 1`, a division: no security takes a real number now, each is stated at its exact error (`N / Nat.card F`), and `gkrSecurity` is at `gkrError F (1 / |F|) nside μ`, which the slot's `overE 1` takes through `Security.mono`. The test builds `gkrSecurity 3 4` at the slot's error and its extraction as `def`s at `E` (`security34`, `extraction34`); `Phases.Security.toDef` lost its `noncomputable` too. |
| 2. the round-check refutation is for one state function and one extractor | met: `Component.sampleChallenge_not_rbr` and `SumcheckRound.drawChallenge_unchecked_not_rbr` take any extractor and state function, through `Verifier.not_rbr_zero` and `Verifier.GuardedForm.probEvent_pos_of_check`, as the reviewer sketched; the test instantiates the strong form. |
| 3. protocol vocabulary and generic lemmas misplaced in `GrandProductSecurity.lean` | met: "slot" is gone from `gkrSecurity`'s docstring; `diffTable`, `evalMle_diffTable` and `diffTable_restrictedZero_empty_iff` are in `ToCompPoly/Restriction.lean` over any commutative ring; `card_filter_powerSum_eq_le` is beside `card_filter_evaluate_eq_le` in `SumcheckRound.lean`; `card_filter_const_le` is private (now `card_const_le`, a `Nat.card` count). |
| 4. public proof helpers without docstrings | met: the ten one-use helpers are private (`ridersZeroOn_empty_iff`, `roundsPartial_zero`, `roundsPartial_push`, `interpPartial_zero`, `interpPartial_push`, `interpPartial_full`, `combPartial_zero`, `combPartial_push`, `combPartial_full`, `card_filter_const_le`, now `card_const_le`); `familyT_consistent`, `familyT_sound`, `Partial.point_empty` and the moved lemmas have docstrings. |
| 5. lines over 100 columns | met for this pull request's lines; `GrandProduct.lean:532` is #62's. |
| 6. documentation left stale, unstaged, or short of one sentence | met: (a) and (b) in the status page; (c) the bullet in `docs/README.md`; (d) the pitfall is committed, and corrected: a bisection showed that the hang was a closed statement over `E` in a definitional comparison (the round's refutation hit the recursion limit, the descendants' one a kernel timeout), not a named one, so the refutations now take a variable statement; (e) the description says the base is #62's branch; (f) the soundness sentence is in the module docstring, `gkrSecurity`'s docstring and the description. |

Reviewed with the `adversarial-review` skill in three passes, under the author's constraint that
no Lean process be started: the statements against the blueprint's Layer 5, Layer 6, decisions
16–18, 20, 23, 26 and 31, the conventions *Errors*, *Holes*, *Extractors*, *Load-bearing checks*
and *Generic code*, acceptance tests 20, 24, 31 and 32, and ArkLib's
`Verifier.rbrKnowledgeSoundnessWorstCaseWith`, `Verifier.KnowledgeStateFunction` and
`Extractor.RoundByRound` (`.lake/packages/Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean:77,
165, 557`), read before the proofs; fidelity to leanVM `a386121f`, the pinned `gkr.rs` read with
`git show a386121f:crates/lean_vm/src/gkr.rs` from the object store of the sibling checkout
`/home/scaraven/Documents/leanEthereum/leanVM` (whose working tree is at `7f80c64`, not the pin),
after the statements; and hygiene. The four repository scripts (`audit-lean.sh`,
`check-imports.sh`, `check-layers.sh`, `check-docs.py`) and `check-repository.sh` were run (they
spawn no Lean) and pass. Every changed Lean file was read in full, with `Component.lean`,
`Schedule.lean`, `Refutation.lean`, `GuardedVerdict.lean`, `PassThrough.lean`,
`KnowledgeAppend.lean`, `ProductTree.lean`, `PartialSum.lean`, both test files and the pull
request's description. Nothing was edited but this file.

Target classification: the description names T4 through the bus phase's knowledge soundness,
the soundness direction, with the completeness half in #62. That is right; one sentence is
missing (finding 6): with the witness `Unit` throughout, `Component.Security` here is
round-by-round *soundness* of the language `Gkr.relIn`, and the extractor plumbing is trivial.

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological. `gkrSecurity` is at the slot's error exactly:
`busError` (`Spine/Errors.lean:133-135`) is `gkrError E (overE 1) 3 I.μBus`, and the test
inhabits `gkrSecurity 3 4 sixteen noRiders (overE 1) overE_one` at that term. Per challenge the
proved escape counts are the blueprint's Layer 5 table (combiner `nside − 1`, radix-`2^ρ` round
`2^ρ`, combination challenge `1`, message none, last combiner `0`), each a `Finset.card` bound
turned into a probability once by VCVio's `prEvent_uniformSample_le_div_iff` in the direction that
matters, and `Security.mono` is used only where the proved bound is at most the charged error. The
composed knowledge state is pinned at both ends by ArkLib's contract (`toFun_empty` is an
equivalence with `Gkr.relIn`; `toFun_full` is forced by acceptance into `Gkr.relOut`), so a state
true after round zero would put escape probability one on the first challenge, which the errors
below one forbid; the state in between is the one the blueprint describes, the layer relations
with the riders zero, and at the last layer the riders and the descendants' values zero on the
coordinates of the final point drawn so far (`RestrictedZero` on a `Partial` point), with the
one-escape lemma `card_filter_restrictedZero_update_le` correct and applied at the right
coordinates (sumcheck challenge `j` of a layer at `ρ + j`, combination challenge `i` at `i`).
Both checks are load-bearing in the proofs (`card_badChallenge_le` needs the round check to
conclude the claim is the family's when the polynomial is honest; `combineCheck_sound` needs the
descendants' check to rewrite the final claim) and both refutations say what the description says;
the round's is stated for one state function where the blueprint's convention asks for every
extractor (finding 2). The one defect of substance is a convention: every `Security` of the
argument is `noncomputable`, against the *Extractors* convention and acceptance test 24, which the
public-input phase meets with a plain `def` (finding 1).

The observations are kept as they are, except two: `card_badChallenge_le` is stated at
`Φ.weight` and takes no `hwt`, and `nat_div_card_le_mul` is gone, since no security takes a
unit any more (finding 1). The refutation tests keep the completeness half's relations, which
coincide with the security half's when there are no riders.

## Findings, most severe first

### Medium

**1. Every `Security` of the argument is `noncomputable`, and no computable extraction is
written.** *Convention; interface for Layer 6.* `Component.sampleChallengeSecurity`
(`ToArkLib/SampleChallenge.lean:215`) is `noncomputable def`, and so, by inheritance, are
`drawChallengeSecurity`, `roundSecurity`, `roundsSecurity` (`SumcheckRound.lean:339, 347, 400`),
`lambdaSecurity`, `childrenSecurity`, `interpPrefixSecurity`, `interpolateSecurity`,
`layerStepSecurity`, `layerStepsSecurity`, `oddSecurity`, `lastSecurity` and `gkrSecurity`
(`GrandProductSecurity.lean:378, 425, 463, 504, 535, 578, 639, 669, 692`). The blueprint's
*Extractors* convention (`protocol-blueprint.md:329`) and acceptance test 24 (`:1369-1372`) ask for
"a computable extractor checked by a `def` without `noncomputable` at each `Security`"; decision
11 is the same rule. The public-input phase meets it: `publicInputSecurity`
(`LeanerVM/Protocol/PublicInput.lean:556`) is a plain `def` at the real error `pubError`, and
`Component.Security.append` (`Component.lean:273`) is a plain `def`, so the chain's
noncomputability enters at `sampleChallengeSecurity`, whose fields are all computable data
(`sampleGuarded`, `keepExtractor`, `sampleStateFunction`, whose `toFun` decides `m.val = 0` by
`Nat.decEq`) and a proof; the real-valued error is a parameter of the type, which the compiler
does not see. Concrete consequence: `busSecurity`, built from `gkrSecurity`, will be
`noncomputable`, `Phases.Security.extraction` (`Spine/Compose.lean:141-144`) applied to it cannot
be evaluated, and test 24 cannot be run for the GKR. Fix: remove `noncomputable` from
`sampleChallengeSecurity` and the twelve definitions after it if Lean accepts (probe below;
unverified here); if Lean names a genuinely noncomputable ingredient, write a computable
`gkrExtraction : Component.Extraction (gkr …) (Gkr.relIn …) (Gkr.relOut …)` from the parts'
extractions, definitionally `gkrSecurity.toExtraction`, as `Phases.Security.extraction` does for
the protocol, and say so in the status.

### Low

**2. The round-check refutation is for one state function and one extractor.** *Convention.*
`SumcheckRound.drawChallenge_unchecked_not_rbr` (`SumcheckRound.lean:359-372`) and
`Component.sampleChallenge_not_rbr` (`SampleChallenge.lean:231-238`) take their hypothesis `h` at
`Component.keepExtractor` and `Component.sampleStateFunction`. The *Load-bearing checks*
convention (`protocol-blueprint.md:321`) asks that "the verifier without it … has no
round-by-round knowledge soundness at the phase's seams below error 1, whatever the extractor";
the descendants' refutation `Component.sendChecked_no_stateFunction` (`SendChecked.lean:192-206`)
has that form (any `E`, any `K`), the round's does not, and the description's "for its state
function" is the weaker claim. The strong form is available at no cost: `Verifier.not_rbr_zero`
(`Refutation.lean:147-160`) quantifies over the state function and the extractor, and for the
one-challenge schedule `draw F` its `hacc` is supplied by
`Verifier.GuardedForm.probEvent_pos_of_check` on the unchecked verifier's guarded form
(`Component.sampleGuarded O F (fun _ ↦ true) _`, whose check is `true` and whose verdict is
`next … ∈ rel Φ (j + 1)` by `H.next`); the `acceptAll` example (`Refutation.lean:337-353`) is the
pattern. Concrete gap: a reader may ask whether another state function rescues the unchecked
verifier; the convention wants the theorem to answer. Fix: restate both over
`{WitMid} {E} {kSF}` through `Verifier.not_rbr_zero` and keep the test instantiations (probe
below).

**3. Protocol vocabulary and generic lemmas misplaced in `GrandProductSecurity.lean`.**
*Surface; the To-folder criterion.* `:687`: "at the slot's error `gkrError`" ("slot" is this
repository's roadmap word; the completeness half's review removed the same word from
`GrandProduct.lean`). `diffTable`, `evalMle_diffTable` and `diffTable_restrictedZero_empty_iff`
(`:192-216`) are facts about tables whose objects are CompPoly's; they belong in
`ToCompPoly/Restriction.lean` beside `RestrictedZero`. `card_filter_powerSum_eq_le` (`:324-342`)
is the power-batching escape count, generic over any field and any `n`, which the description says
`batchSecurity` will consume; it sits in the `Gkr` namespace and belongs beside
`card_filter_evaluate_eq_le` (`SumcheckRound.lean:183`) or in the batching module when it lands.
`card_filter_const_le` (`:250-254`) is a `Finset` fact. Fix: move them, and write "at the error
`gkrError`, so that a protocol's slot at that error takes it".

**4. Public proof helpers without docstrings.** *Hygiene.* `CONTRIBUTING.md` asks for a docstring
on every public declaration; `GrandProductSecurity.lean` has 43 public declarations and no
private one, `Restriction.lean` 11 and none. Without a docstring: `ridersZeroOn_empty_iff`
(`:75`), `roundsPartial_zero` (`:111`), `roundsPartial_push` (`:117`), `interpPartial_zero`
(`:133`), `interpPartial_push` (`:140`), `interpPartial_full` (`:156`), `combPartial_zero`
(`:164`), `combPartial_push` (`:170`), `combPartial_full` (`:186`), `evalMle_diffTable` (`:198`),
`diffTable_restrictedZero_empty_iff` (`:205`), `familyT_consistent` (`:311`), `familyT_sound`
(`:316`); `Partial.point_empty` (`Restriction.lean:54`). All but the last two are used by one
proof each in the same file. Fix: `private` for the one-use helpers, a one-line docstring for
the rest.

**5. Lines over 100 columns.** *Hygiene.* `GrandProductSecurity.lean:359` (103), `:696` (101),
`SumcheckRound.lean:417` (101). (`GrandProduct.lean:532` is 103 columns too, but is #62's line.)

**6. Documentation left stale, unstaged, or short of one sentence.** *Documentation.*
(a) `docs/roadmap/protocol-status.md:133-134`: "its knowledge soundness is to be stated at
`gkrError F u nside μ`" is now stated, two sentences before the paragraph says so. (b) `:181-184`,
"What can start now … the GKR's knowledge soundness on its local round": built on the stacked
branch; say so or leave the section to describe `main` explicitly. (c) `docs/README.md:50-55`
lists the reviews; this file needs its bullet. (d) `tests/README.md:79-83`, the pitfall on a named
test statement over `E`, is unstaged (`git status`: ` M tests/README.md`) while the description
cites it; stage it. (e) The description's "Stacked on #62 (the definition and completeness, on
`main`)": #62 is *on merge* in the status table (`protocol-status.md:27`). (f) Neither the
description nor the module docstring (`GrandProductSecurity.lean:18-19`) says that with the
witness `Unit` the theorem is round-by-round soundness of `Gkr.relIn` and the extractor is
trivial; the blueprint says it of the spine (`protocol-blueprint.md:556`, "a soundness statement
only"). One sentence in each.

### Observations

- The two refutation tests (`tests/…/GrandProductSecurity.lean:53-107`) instantiate the
  completeness half's relations, `family 3 4 sixteen noRiders 2 2` and
  `childRel 3 4 sixteen noRiders 2 2 0`, not the security half's `familyT (constTrack …)` and
  `childRelT`. With no riders the two coincide propositionally (`inv` is `RidersZero` of the empty
  list), so the same verifier is refuted; "at the phase's seams" would read better with the
  security half's relations.
- `Family.Sound` (`SumcheckRound.lean:177-179`) bounds the invariant's escape by the polynomial
  degree `d`; `familyT_sound` absorbs the riders' `1` by `Nat.one_le_two_pow`. A library would
  take the bound as a parameter; for the GKR this is fine.
- `Component.keepExtractor` (`Component.lean:170-174`) generalises `passThroughExtractor`
  (`PassThrough.lean:103-107`), which is it at `!p[]` up to `Fin.elim0`; one could go.
- `nat_div_card_le_mul` (`Component.lean:73-77`) is NNReal arithmetic and reads better beside the
  errors in `Schedule.lean`; harmless where it is.
- `card_badChallenge_le` takes `(hwt : wt = Φ.weight)` and is called with `rfl`
  (`SumcheckRound.lean:291, 343`); stating it at `Φ.weight` removes the argument.
- `Component.lean:24` ("fill a slot") pre-dates this pull request.

## Pass A: the statements

Read before the proofs, from the blueprint and ArkLib's definitions. What
`rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut WitMid E kSF ε` says: for every
statement, every challenge index `i` and every transcript prefix up to `i`, the probability over
the uniform challenge that some witness makes `kSF` true after the challenge while `kSF` was false
before it on the extracted witness is at most `ε i`. A `KnowledgeStateFunction` is pinned at
round zero by an equivalence with `relIn` and at the full transcript by acceptance into `relOut`
(the direction "accepted with positive probability ⇒ state true"); a prover message cannot make
it true (`toFun_next`). With `WitIn = WitOut = Unit` the witness quantifiers are trivial and the
contract is round-by-round soundness of the language `relIn`.

- **`gkrSecurity nside μ leaves riders u hu`** (`GrandProductSecurity.lean:692-697`):
  `Component.Security (gkr nside μ leaves) (Gkr.relIn …) (Gkr.relOut …) (gkrError F u nside μ)`.
  Direction right: `relIn` is the roots-are-products-and-riders-zero language the state must reach,
  `relOut` the evaluation claims at `ζ` with the riders vanishing at `lowPoint ζ τ`. The error is
  the slot's term by definition (`gkrError = errAppend (errAppend oddError stepsError)
  (drawError 0)`, `Schedule.lean:362-364`), with `u` the unit; `hu : 1 / |F| ≤ u` is the one
  hypothesis and excludes `u = 0`, at which the theorem is false. At the test's `overE 1` every
  bound is tight (`nat_div_card_le_mul` is an equality there). Non-vacuous: inhabited at
  `gkr 3 4`, `gkr 1 2` with a nonzero rider, `gkr 3 3` (`tests:36-48`).
- **The composed state**, by `KnowledgeAppend.state` (`KnowledgeAppend.lean:182-196`): the first
  component's state up to the seam, then "every earlier check passed and the current component's
  state on the verdict". Per component: `sampleStateFunction` (`SampleChallenge.lean:145-154`) is
  `relIn` before, `check ∧ f s c ∈ relOut` after; `sendCheckedStateFunction`
  (`SendChecked.lean:167-176`) is `relIn` before and after, with `toFun_full` discharged by the
  hypothesis "check and output relation imply the input relation"; `passThroughStateFunction` is
  `relIn` with the reflection hypothesis. The chain of relations is `relIn → stepsIn` (the layer
  relation, or `relOut` read at the layer with no step left) `→ relOut → relOut`, every seam
  definitional (`stepsIn_zero_iff`, `relIn_iff_stepsIn_zero`, `relIn_iff_layerRel_zero` where a
  cast separates them). Inside a step: `layerRel m → rel (familyT T) 0 → … → rel (familyT T) m →
  childRelT T 0 → … → childRelT T ρ → stepOutT T`.
- **Non-triviality.** `toFun_empty` of the composite is the first component's, an equivalence
  with `Gkr.relIn`; `toFun_full` is forced by acceptance into `Gkr.relOut`. A state true after
  round zero for a statement outside `relIn` would make the first challenge's escape certain, so
  the theorem at errors below one cannot hold of it; the real content is the four escape counts
  and the three reflection facts, each checked below.
- **The combiner**, `card_filter_lambdaNext_le` (`:351-374`): from `s ∉ layerRel m`, the
  challenges `l` with `lambdaNext s l ∈ rel (familyT T) 0` number at most `nside − 1`: none if a
  rider is nonzero (`T.inv_zero`), else the roots of `Σ l^t (a_t − b_t)`, nonzero of degree
  `< nside` (`card_filter_powerSum_eq_le` through `card_filter_evaluate_eq_le`). The family's
  first claim is `Σ l^t Ṽ_t(r)` by `partialSum_summand_zero` (needs `m + ρ ≤ μ`). `nside = 0` is
  handled.
- **The rounds**, `card_badChallenge_le` (`SumcheckRound.lean:289-336`): from
  `((s, q), o) ∉ relMid Φ j` with the check passed, the challenges landing in `rel Φ (j + 1)`
  number at most `d`: if the invariant fails, `Φ.Sound`; if `q` is the honest polynomial, the
  check gives `s.2.2 = Φ.claim`, so the statement was in `relMid` and nothing is bad; otherwise
  `q ≠ honest` and a bad challenge is an agreement point, at most `d` of them
  (`card_filter_evaluate_eq_le`, two coefficient vectors of length `d + 1`; the degree bound is the
  message's type). Removing the check kills the second case: the honest polynomial at a wrong
  claim is accepted at every challenge, which `drawChallenge_unchecked_not_rbr` states. The
  dishonest-polynomial-true-claim case is counted as an escape from `¬relMid` and bounded by `d`
  too, which is the design the completeness review predicted. `roundsSecurity` recurses on
  `(i, j)` with `j < m` throughout, so `normalizedWeights` past the point is never read.
- **The descendants**, `combineCheck_sound` (`:403-422`): values that pass `combineCheck` and are
  the honest ones (`childRelT T 0`, `combPartial #v[] = Partial.empty`, so `diffTable` zero means
  equality) make the final claim `Σ λ^t ∏_c Ṽ'_t(c, χ)`, the summand at `χ`, which is
  `partialSum … m χ` by `partialSum_self`. Removing the check leaves `s.2.2` unconstrained, which
  `sendChecked_no_stateFunction` states for any state function and extractor.
- **The combination challenges**, `card_filter_interpNext_le` (`:440-460`): from
  `s ∉ childRelT T i`, either the riders' predicate is broken (`T.invU_escape`, at most one value)
  or some tree's `diffTable` is not zero on `combPartial u` (`card_filter_restrictedZero_update_le`
  at coordinate `i`, at most one value). After `ρ` challenges `childRelT T ρ` is `stepOutT T`
  through `interpDone` (`interpDone_mem_stepOutT_iff`, by `restrictedZero_of_all`,
  `evalMle_diffTable`, `evalMle_cast_append`), so the new value is the level below at the new
  point `(u, χ)`.
- **The one-escape lemma**, `card_filter_restrictedZero_update_le` (`Restriction.lean:104-135`):
  `RestrictedZero t σ` is "the extension restricted to the fixed coordinates is the zero
  multilinear polynomial in the free ones" (every cube completion). If it fails and two distinct
  values `c₁ ≠ c₂` of coordinate `k` make it hold, then for every completion `b` the affine
  function `A(b) + c (B(b) − A(b))` (`evalMle_set`) vanishes at two points, so `A(b) = B(b) = 0`
  and the restriction was zero: contradiction, in any domain. Beyond the table's variables
  (`k ≥ n`) the update is invisible and the filter is empty. Coordinates: `roundsPartial_push`
  fixes `ρ + j` for the `j`-th sumcheck challenge, `interpPartial_push` and `combPartial_push` fix
  `i` for the `i`-th combination challenge; `interpPartial_full` reads back `(u ++ χ)[k]`, which
  is `interpDone`'s point and `lowPoint`'s source. Checked by the four `#guard`s
  (`tests:118-125`).
- **The riders.** Inside the argument `constTrack` keeps "zero tables" (no escape; the predicate
  is constant). At the last layer, chosen by the `k = 1` branch of `layerStepsSecurity` and the
  `(1, 0)` branch of `oddSecurity`, `progTrack` tracks `RidersZeroOn` on the partial point, which
  at the end is `relOut`'s "vanishes at `lowPoint ζ τ`" (`progTrack.out_iff`). A rider on `τ ≤ ρ`
  variables sees no sumcheck challenge (coordinates `≥ ρ` are beyond it) and escapes at a
  combination challenge only; one on `τ > ρ` escapes at a sumcheck challenge or a combination
  challenge; in each case one value, dominated by the claim's `2^ρ` or `1` by the case split (the
  bound is a maximum, not a sum), so `gkrError` carries no term for them, as decision 18 and the
  *Seams* convention say.
- **The probabilistic lemma**, `sample_rbr` (`SampleChallenge.lean:184-210`): the event is
  `∃ w, (s, w) ∉ relIn ∧ check s ∧ (f s c, w) ∈ relOut`; with the check passed it is contained in
  `badChallenge s o c`, whose count is `≤ N` by `hN` (stated on statements that pass the check,
  the right shape), and `prEvent_uniformSample_le_div_iff` is used in the direction count ⇒
  probability; the coercions rewrite `((N / |C| : ℝ≥0) : ℝ≥0∞)` to `N / |C|` in `ℝ≥0∞`
  (`ENNReal.coe_div` needs `|C| ≠ 0`, from `Fintype.card_ne_zero`). With the check failed the
  event is empty. `card_filter_badChallenge_le_of_unit` reduces `badChallenge` to language
  membership for the trivial witness.
- **The refutations** say what the description says. `drawChallenge_unchecked_not_rbr`: escape
  probability one for `sampleStateFunction` from `((s, honest poly), o)` with `s.2.2 ≠ claim`, the
  invariant holding after every challenge; `sendChecked_no_stateFunction`: for any `K` and `E`,
  from `(s, o)` with no witness in `relIn`, a message passing the check whose output is in
  `relOut` gives `False`, by `toFun_full` then `toFun_next` then `toFun_empty`. The tests
  instantiate them non-vacuously: the wrong claim is `trueClaim + 1 ≠ trueClaim`
  (`one_ne_zero (add_eq_left.mp h)`, the characteristic-two step), the riders are the empty list,
  the honest polynomial and descendants are the completeness tests' (`q0`, `ch` shapes). The
  hypothesis `h` of the first is satisfiable (at `ε = 1` every verifier is round-by-round sound),
  so its conclusion `1 ≤ ε` is informative. Both refute the right component (the step's verifier
  with the check replaced by `true`), on the completeness half's relations (observation above).
- **Substitution test.** The proof would not survive the check at the message instead of the
  challenge (`card_badChallenge_le` would lose `hc`), unit weights (`Φ.Consistent.check` fails
  for the normalized family), the other combiner power order (`combineCheck_sound` rewrites with
  the same powers on both sides), or the other point order (`interpDone_mem_stepOutT_iff` through
  `evalMle_cast_append`).
- `Security.mono` hides nothing: four uses, each from the proved count to the charged error.
- Gates: `audit-lean.sh`, `check-imports.sh`, `check-layers.sh`, `check-docs.py`,
  `check-repository.sh` pass. `lake build`, `lake test` and `#print axioms` were not run (CI).

## Pass B: fidelity to `gkr.rs` at `a386121f`

Category A: nothing in this diff transcribes the Rust; the errors are the blueprint's Layer 5
table and the relations are the mathematics'. What the security half relies on in the deployed
verifier, read from the pinned file: the binary layer's check `claim != poly_eval(&products,
lambda)` (`:384`) and the radix-four layer's (`:411`), modelled by `Gkr.combineCheck` and consumed
by `combineCheck_sound`; the round check, which the deployed verifier makes implicit by deriving
`c_0` from the running claim in `next_round_poly(5, claim, Some(r))` (`:399-401`,
`transcript.rs:289-302`), modelled by `SumcheckRound.check` under decision 26 and consumed by
`card_badChallenge_le`; the challenge order `low, high` after the tails (`:414-415`) and the point
`[low, high] ++ round_point` (`:424-425`), which fix the coordinate order the one-escape lemma is
applied at; the combiner resampled after every layer with the last unused (`:423`), charged `0`.
None of these changed between #62 and this commit, and the completeness review's enumeration
stands. Historical material (Poseidon, KoalaBear, LogUp): none.

The six design readings of the completeness review, checked against what this half does:

| Reading | Honoured by |
| --- | --- |
| coefficient vectors as round messages | `card_filter_evaluate_eq_le`: two vectors of length `d + 1` agree at `≤ d` points; the degree bound is the type |
| the round split with the check at the challenge | `card_badChallenge_le` takes `hc` from `sampleChallengeSecurity`'s `hN`; `relMid` records the polynomial |
| generic bricks with a Boolean check | the hypotheses read "`s ∉ relIn → check s → #{c ∣ f s c ∈ relOut} ≤ N`" and "`check s m → out s m ∈ relOut → s ∈ relIn`" |
| `interpolate` on a prefix, `interpDone` in the last challenge | `interpPrefixSecurity` on `childRelT T i`, the last challenge through `interpDone_mem_stepOutT_iff` |
| the first step reads the roots through `inp` | `lambdaSecurity` takes `hinp` as an equivalence; `oddSecurity` passes `relIn_iff_layerRel_zero` |
| the prefix instances | unchanged |

And the two facts it was to lean on: `Family.inv` is per stage, which `RiderTrack.inv` uses with
`(j, χ)`; `gkrError` is the right target, by the case splits above.

Recorded divergences of this half, verified: the round's knowledge soundness is proved on the
local `SumcheckRound.roundsSecurity`, not consumed from Layer 4's `Sumcheck.normalizedSecurity`
as the holes table's *Needs* has it (`protocol-status.md:153-156` records it, with the condition
that Layer 4's family form may take it over); the riders' state is the blueprint's; the
descendants' values are tracked the same way (`:156-159`); the combiner's bound is the
power-batching escape count, which the description names among #62's blueprint asks.

## Pass C: hygiene

Findings 3, 4, 5, 6 and the observations. Otherwise clean: module shape (header, `module`,
imports, module docstring, `@[expose] public section`) in both new modules; `public import` where
a statement needs it (`Restriction` is read by the exposed `RidersZeroOn`; `Refutation` by
`sampleChallenge_not_rbr`), plain `import Mathlib.Tactic.LinearCombination`; `LeanerVM.lean` and
`tests/LeanerVMTests.lean` register the two modules and the test once each, alphabetically;
module docstrings carry the design without narrating proofs; the four `tests/README.md` pitfalls
added by this branch are accurate and self-contained; no letter codes; `Family.Honest` now
`extends Family.Consistent` (`SumcheckRound.lean:170`) and `GrandProduct.lean` adapts; the three
`GrandProduct.lean` lemmas made public have docstrings.

## Kernel axioms

Not printed: no Lean process was started. Lexically, `audit-lean.sh` passes, and none of the
upstream files the new proofs reach contains `sorry`: VCVio's `NativeMeasure.lean`
(`prEvent_uniformSample_le_div_iff`, `prEvent_uniformSample_eq_one_iff`), ArkLib's
`RoundByRound.lean`, `CoordinateWiseSpecialSoundness/Guarded.lean` (`guarded_accepting_of_mem`,
`GuardedForm`) and `Append/StateFunction.lean`. The new Mathlib facts
(`Polynomial.card_le_degree_of_subset_roots`, `natDegree_sum_le_of_forall_le`) are theorems. The
VCVio bound is in the public-input phase's closure, printed clean at #60; the composition is the
#615 port, printed clean at #58. The description's claim, `propext`, `Classical.choice`,
`Quot.sound` for `gkrSecurity`, is consistent with that and is the first probe below.

## Probes for the author to run on CI

1. Axioms (unverified here):

   ```lean
   import LeanerVM.Protocol.ToArkLib.GrandProductSecurity
   #print axioms LeanerVM.Protocol.gkrSecurity
   #print axioms LeanerVM.Protocol.SumcheckRound.roundsSecurity
   #print axioms LeanerVM.Protocol.Component.sampleChallengeSecurity
   #print axioms LeanerVM.Protocol.card_filter_restrictedZero_update_le
   #print axioms LeanerVM.Protocol.SumcheckRound.drawChallenge_unchecked_not_rbr
   #print axioms LeanerVM.Protocol.Component.sendChecked_no_stateFunction
   ```

2. Finding 1 (unverified): delete `noncomputable` from `Component.sampleChallengeSecurity`
   (`SampleChallenge.lean:215`) and rebuild the module. If it compiles, delete it from the twelve
   definitions after it and add to the test
   `def gkrExtraction := (gkrSecurity 3 4 sixteen noRiders (overE 1) overE_one).toExtraction`
   without `noncomputable`, which is test 24's check. If Lean names an ingredient, write
   `gkrExtraction` from the parts' extractions as `Phases.Security.extraction` does, and check
   `example : (gkrSecurity …).toExtraction = gkrExtraction … := rfl`.

3. Finding 2 (unverified), the strong form of the round's refutation, in `SumcheckRound.lean`:

   ```lean
   theorem drawChallenge_unchecked_not_rbr (Φ : Family F X O W d) {m : ℕ} (H : Φ.Consistent m)
       (hj : j < m) {WitMid : Fin 2 → Type}
       {E : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (MidStmt X F j d × ∀ i, O i)
         W W (draw F) WitMid}
       {kSF : (Component.sampleVerifier O F (fun _ ↦ true)
         (fun p : MidStmt X F j d ↦ fun c ↦ next j p.1 (evaluate d p.2 c) c)).toVerifier
           .KnowledgeStateFunction init impl (relMid Φ j) (rel Φ (j + 1)) E}
       {ε : (draw F).ChallengeIdx → ℝ≥0}
       (h : Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl (relMid Φ j) (rel Φ (j + 1))
         _ WitMid E kSF ε)
       (s : Stmt X F j) (o : ∀ i, O i) (w : W) (hclaim : s.2.2 ≠ Φ.claim ((s.1, o), w) j s.2.1)
       (hinv : ∀ x, Φ.inv ((s.1, o), w) (j + 1) (s.2.1.push x)) : 1 ≤ ε ⟨0, rfl⟩ :=
     Verifier.not_rbr_zero h ⟨0, rfl⟩ rfl (fun i hi ↦ absurd hi (by omega))
       ((s, Φ.poly ((s.1, o), w) j s.2.1), o)
       (fun w' hmid ↦ by rw [Subsingleton.elim w' w] at hmid; exact hclaim hmid.1.2)
       default fun c ↦
         ⟨Transcript.concat c default, funext fun i ↦ by fin_cases i; rfl, w,
           Verifier.GuardedForm.probEvent_pos_of_check (Component.sampleGuarded O F _ _) init impl
             _ _ _ rfl ⟨hinv c, H.next ((s.1, o), w) j s.2.1 c hj⟩⟩
   ```

   (the `Subsingleton W` instance is in scope; the `funext` step may need
   `Fin.take` unfolding as in the `acceptAll` example). `sampleChallenge_not_rbr` gets the same
   shape with `hesc`.

## What was checked and found sound

The statement of `gkrSecurity` and its error term against `busError` and the blueprint's table;
the composed state function at every seam, in both directions where a seam is an equivalence;
the four escape counts and the two reflection facts; the one-escape lemma and the coordinate
order of the three partial points; the probabilistic lemma's event, direction and coercions; both
refutations, their instantiations and the component they refute; the role of `u`, `hu` and
`Security.mono`; the Rust checks the half relies on, at the pin; the six design readings; the
recorded divergences; the five repository scripts; aggregate registration; imports; docstrings on
every public definition and the main theorems.

## What could not be checked

- A build, `lake test`, and `#print axioms` (probe 1): the author's constraint.
- Whether `noncomputable` is needed anywhere in the chain (probe 2).
- The classical `Finset.filter` instance identity between `sample_rbr` and VCVio's lemma, which
  the author's pitfall (`tests/README.md:71-75`) says was met by keeping the instances in scope the
  same; the statements are instance-independent.
- An executable run of the composed `gkr` verifier on a dishonest transcript (the refutations are
  symbolic, as the description says).
