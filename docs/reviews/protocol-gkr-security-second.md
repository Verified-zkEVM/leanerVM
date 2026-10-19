# Review: the grand-product GKR's knowledge soundness, second pass

> An archive of an independent review of one commit, `7dbb95b` of the branch
> `feat/protocol-gkr-security` (draft pull request #70), against its base `771e20c` (the head of
> pull request #62, branch `feat/protocol-gkr`): names, paths and line numbers are that commit's.
> The first review, [protocol-gkr-security.md](protocol-gkr-security.md) of `070fb8a`, was read
> only after the three passes below were complete; the last section says where the two agree.
> What is accepted from this review is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of the
> pull request that met it.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. nine proof lemmas of `GrandProductSecurity.lean` are public, and three of `Restriction.lean` | met: the nine are `private`, their uses inside the exposed definitions written `by exact`; `Partial.point_update`, `point_update_of_le` and `point_set_self` are `private`. |
| 2. `Phases.Security.extraction` now duplicates `toDef.toExtraction` | met: it is `S.toDef.toExtraction`; `piopExtractor_readsFirst` unfolds `Phases.Security.toDef` and `Component.Security.append`. |
| 3. `passThroughExtractor` duplicates the new `keepExtractor` | met: deleted; the pass-through's state function, theorem and security use `keepExtractor _ W !p[]`. |
| 4. `RiderTrack` takes a `[Finite F]` no field uses | kept on purpose, and said: the docstring states that the field is finite because a `Nat.card` count of an infinite set is `0`; `Family.Sound` takes the same guard. |
| 5. the unit conversion `1 / Nat.card E = overE 1` lives only in a test | met: `overE_one` in `Spine/Errors.lean` beside `overE_add`; the test uses it. |
| 6. the rider test inhabits a security with an empty input relation; the children refutation names the completeness relation | met: (a) a security instance at `zeroRider`, the `rider` one kept and described as the empty-input case, and three `#guard`s on `RidersZeroOn` at the last layer of `gkr 1 2` (before any combination challenge, at the root `1`, at `a`), with the two `Decidable` instances they need; the completeness test of `GrandProduct.lean` had the same empty input relation and now uses `zeroRider`. (b) The test's docstring says why the refutations' relations are the security's. |
| 7. three partial-point builders and nine lemmas where one generic builder would do | met: `Partial.ofVector` and `Partial.or` in `Restriction.lean`, with `ofVector_zero`, `ofVector_push`, `empty_or`, `update_or`; `roundsPartial`, `combPartial` and `interpPartial` are abbreviations of them, and of the eight lemmas one remains (`interpPartial_full`, private). |
| 8. repeated proof shapes: the `Nat.cast_one` raise, the pass-through-with-iff, six `omit` headers | (b) and (c) met: `Component.passThroughSecurityOfIff` in `PassThrough.lean` replaces the five pass-throughs; the partial points come before the instance `variable` line, so their `omit` headers are gone. (a) not taken: a `private def` cannot be named in the exposed definitions that would call it, and a public one would add to the surface finding 1 reduces, to save two four-line raises. |
| 9. `GrandProduct.lean:532` is 103 columns | met. |

Reviewed with the `adversarial-review` skill in three passes, with the Lean work limited to one
probe (`lake env lean` on a scratch file outside the repository, importing
`GrandProductSecurity` and `Spine.Compose`): the statements against the blueprint's Layer 5 and
Layer 6, the conventions *Errors*, *Holes*, *Extractors*, *Load-bearing checks*, *Generic code*
and *Seams*, decisions 16–20, 23, 24, 26 and 31, acceptance tests 20, 24, 26, 31 and 32, the
holes table's row for this hole, and ArkLib's `Extractor.RoundByRound`,
`Verifier.KnowledgeStateFunction` and `Verifier.rbrKnowledgeSoundnessWorstCaseWith`
(`.lake/packages/Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean:77, 165, 557`), all
read before the Lean; then every source file in scope in full (`GrandProductSecurity.lean`,
`Restriction.lean`, `SampleChallenge.lean`, `SendChecked.lean`, `SumcheckRound.lean`,
`Component.lean`, `Spine/Compose.lean`, and for context `GrandProduct.lean`, `Schedule.lean`,
`Spine/Errors.lean`, `Refutation.lean`, `PassThrough.lean`, `GuardedVerdict.lean`, both test
files, the status page, the diffs against `771e20c`); then hygiene. `audit-lean.sh`,
`check-imports.sh`, `check-layers.sh` and `check-docs.py` pass. Nothing was edited but this
file.

Target classification: the pull request names T4, through the bus phase's knowledge soundness,
the soundness direction, with the completeness half in #62, and says that with the witness
`Unit` the result is round-by-round soundness of the language `Gkr.relIn`. That is the right
classification and it is stated in the module docstring, the docstring of `gkrSecurity` and the
pull request.

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological, and no finding below changes a statement.
`gkrSecurity` (`GrandProductSecurity.lean:637-642`) is the security half of the component the
slot takes (`gkr nside μ leaves` at `gkrSpec`), between the blueprint's two relations
(`Gkr.relIn`: every rider table zero and every root the product of its leaves; `Gkr.relOut`:
every leaf claim true at `ζ` and every rider's extension zero at the low coordinates of `ζ`),
at the error `gkrError F (1 / Nat.card F) nside μ`, whose per-challenge values are the
blueprint's (`(nside − 1)/|F|` on each combiner, `0` on the last, `2^ρ/|F|` on a round of radix
`2^ρ`, `1/|F|` on a combination challenge; the test pins them at `gkr 3 4`,
`tests/LeanerVMTests/Protocol/GrandProduct.lean:99-102`). The composed knowledge state is the
running relation of the parts, pinned at round zero to `Gkr.relIn` and at the end to acceptance
into `Gkr.relOut` by ArkLib's contract, so it cannot be made trivially true or false. The riders
ride the state as decision 18 asks: zero tables inside the argument, and at the last layer zero
on the coordinates of the final point drawn so far (`progTrack` through `RestrictedZero` on a
`Partial` point), the one-escape lemma applied at the right coordinates and its escape dominated
by the claim's, so the riders add nothing to the error. The extractor keeps the trivial witness
and computes: `security34` and `extraction34` are plain `def`s at `E`
(`tests/LeanerVMTests/Protocol/GrandProductSecurity.lean:43-50`), and `Phases.Security.toDef`
computes too. Both checks are load-bearing by theorems that quantify over every extractor and
state function, instantiated on the sixteen-leaf trees. The kernel axioms of `gkrSecurity` are
`propext`, `Classical.choice`, `Quot.sound` (probed). What the branch still owes is small: a
public surface about a third larger than it needs to be, three duplicated notions, one
conversion lemma in the wrong place, one test that exhibits less than it claims, and some
repetition.

## The four criteria

**(a) Faithfulness to the blueprint: met.** The component, the two relations, the error per
challenge, the riders on the state function, the `With` form with a computable extractor, the
refutations whatever the extractor, the `To*` placement by the objects' owner (`Restriction` over
CompPoly's tables, the rest over ArkLib's reductions) with no protocol vocabulary, and a shape
the bus phase consumes by one `Component.Security.append` after one `Security.mono`. On the
error's form: stating `gkrSecurity` at `gkrError F (1 / Nat.card F) nside μ` is right. A generic
module cannot name `overE`, and `Nat.card` (Mathlib's cardinality of a type, a natural number
defined for every type, zero on infinite ones, needing no data to compute) under `[Finite F]` (a
proposition) is what keeps every security a plain `def`, where `Fintype E` (a *structure* holding
the list of elements) is noncomputable. The slot's `overE 1` is the same number written with
`Fintype.card E`; the bus phase will cross that gap with one `Security.mono`, which is a numeric
rewrite and not a bridge between relations (the *Seams* convention forbids the latter only). The
two deviations from the Layer 5 sketch (riders as arguments of the relations, not of `gkr`; the
round's knowledge soundness proved on the local `SumcheckRound.roundsSecurity` rather than
consumed from Layer 4's `Sumcheck.normalizedSecurity`, which the holes table lists as a need)
are recorded in the status page with the blueprint asks they raise.

**(b) Reduced audit surface: partly met.** This pull request adds 65 public declarations
(29 in `GrandProductSecurity.lean`, 14 in `Restriction.lean`, 10 in `SumcheckRound.lean`, 6 in
`SampleChallenge.lean`, 3 in `SendChecked.lean`, 3 in `Component.lean`). The surface an auditor
must *trust* is far smaller: `gkrSecurity`'s statement, `Component.Security`, `gkr`,
`Gkr.relIn`, `Gkr.relOut`, `gkrError`, and ArkLib's three definitions; the rest is proof. Nine
theorems in `GrandProductSecurity.lean` and three in `Restriction.lean` are used only inside the
file's own definitions and can be `private` (finding 1). Three notions are duplicated:
`Phases.Security.extraction` with `toDef.toExtraction` (finding 2), `passThroughExtractor` with
`keepExtractor` (finding 3), and the completeness relations `family`/`childRel` with the
security's `familyT`/`childRelT` (observation). One instance argument is unused (finding 4).
The two count forms (`Nat.card` in statements, `Finset.filter` in the Mathlib-facing lemmas, with
`natCard_subtype_eq_card_filter` between them) are a deliberate split, not a duplication: the
`Finset` form is what Mathlib's root bound speaks, the `Nat.card` form is what keeps the
securities computable.

**(c) Non-vacuousness: met, with one test gap.** Every hypothesis of every load-bearing
statement is discharged in the file (`hm : m + ρ ≤ μ` by `omega` at each call; `Subsingleton W`
at `Unit`; `Finite F` and `SampleableType F` at `E` by Layer 0). The relations are neither empty
nor full at the tests' trees (`#guard`s on `relIn` and `relOut` in both directions). No error is
`1` or more anywhere: the numerators are `0, 1, 2^ρ, nside − 1`. No `Nat.card` count is taken on
an infinite type: each sits under `[Finite F]` or `[Finite C]`, and the probabilistic step
(`sample_rbr`) rewrites it to `Fintype.card` before VCVio's uniform bound. The state function is
not trivial: `toFun_empty` is an equivalence with `Gkr.relIn` and `toFun_full` is forced by
acceptance into `Gkr.relOut`, so a state true from round zero would put escape probability one on
some challenge. The refutations are genuine: each takes an arbitrary extractor and state function
and derives `1 ≤ ε` (round check) or `False` (descendants' check, where no challenge exists to
carry an error). The gap: the only security instance with a nonzero rider has an *empty* input
relation, so it exercises the construction and not the tracking (finding 6).

**(d) Maintainability and readability: met, with repetition to remove.** The module docstring of
`GrandProductSecurity.lean` lets a reader follow the argument (the four parts and their escape
counts, the two trackers, how `layerStepsSecurity` chooses between them). Every public
declaration has a docstring; none cites the roadmap; the only line over 100 columns is #62's
(finding 9). The repetition is in three shapes (finding 8), and three partial-point builders
could be one (finding 7).

## Findings, most severe first

No finding is above *low*: none changes a statement, a relation or an error.

### Low

**1. Nine proof lemmas of `GrandProductSecurity.lean` are public, and three of
`Restriction.lean`.** *Audit surface.* These are Prop-valued and used only as proof arguments
inside the file's own definitions, the same role the file already gives its ten `private` lemmas
(`roundsPartial_push` inside `progTrack`, for one): `card_ridersZeroOn_update_le` (`:83`, used
by `progTrack`), `familyT_consistent` and `familyT_sound` (`:280`, `:287`, used by
`layerStepSecurity`), `card_lambdaNext_le` (`:299`, by `lambdaSecurity`), `combineCheck_sound`
(`:355`, by `childrenSecurity`), `card_interpNext_le` (`:391`, by `interpPrefixSecurity` and
`interpolateSecurity`), `interpDone_mem_stepOutT_iff` (`:441`, by `interpolateSecurity`),
`stepsIn_zero_iff` (`:515`, by `layerStepsSecurity`), `relIn_iff_stepsIn_zero` (`:549`, by
`oddSecurity`). In `Restriction.lean`, `Partial.point_update` (`:102`),
`Partial.point_update_of_le` (`:113`) and `Partial.point_set_self` (`:121`) serve only
`card_filter_restrictedZero_update_le`. *Fix:* mark the nine `private`; in `Restriction.lean`
mark at least `point_set_self` private (it restates `Vector.set_getElem_self`), and the other
two unless they are wanted as the partial point's API. The file's public count drops from 29 to
20, the trusted reading unchanged. The intermediate securities (`lambdaSecurity` …
`lastSecurity`) are data and stay public while the section is `@[expose]`; whether the
section needs exposure at all (no consumer unfolds `gkrSecurity`; `ReadsFirst` concerns the
commit phase only) is a question for every `ToArkLib` module, not this one, and is left as an
observation.

**2. `Phases.Security.extraction` now duplicates `toDef.toExtraction`.** *Audit surface.*
`Spine/Compose.lean:140-144` defines the protocol's extraction by hand as the six extractions
appended, with the docstring "It is what `Phases.Security.toDef` carries, and it computes"; that
was its reason to exist while `toDef` was `noncomputable`. This pull request makes `toDef`
compute (`:133-136`), and the probe confirms
`S.extraction = S.toDef.toExtraction` by `rfl`. Two definitions of the same object, one of which
a reader must now check against the other. *Fix:* either `def Phases.Security.extraction (S) :=
S.toDef.toExtraction` with the docstring "the extraction `toDef` carries, named so that
`piopExtractor` reads it", or delete it and set `piopExtractor P S := S.toDef.extractor`; in
both cases `piopExtractor_readsFirst` (`:183-192`) adds `Phases.Security.toDef` and
`Component.Security.append` to its `simp only` list (both are `@[macro_inline]` definitions,
which `simp` unfolds like any other). If the proof resists, the minimal change is to keep the
definition and add `theorem Phases.Security.extraction_eq (S) : S.extraction =
S.toDef.toExtraction := rfl` as the guard that the two agree.

**3. `passThroughExtractor` duplicates the new `keepExtractor`.** *Audit surface.*
`Component.keepExtractor S W pSpec` (`Component.lean:174-178`, added here) is the extractor that
returns its witness at every round; `Component.passThroughExtractor` (`PassThrough.lean:103-107`)
is the same at the empty schedule, with `extractMid := fun i ↦ Fin.elim0 i` where
`keepExtractor` writes `fun _ _ _ w ↦ w`, which typechecks at `!p[]` too. *Fix:* replace the
three uses in `PassThrough.lean` (`:117`, `:128`, `:138`) by
`keepExtractor (StmtIn × ∀ i, OStmt i) W !p[]` and delete `passThroughExtractor`;
`passThroughStateFunction.toFun_next := fun m ↦ Fin.elim0 m` does not read the extractor's
step, so nothing else moves.

**4. `RiderTrack` takes a `[Finite F]` no field uses.** *Unneeded instance.* The header
`structure RiderTrack [Finite F] (ρ m : ℕ)` (`GrandProductSecurity.lean:200`) adds an
instance argument (the probe prints it after `riders`), but every field is a predicate or a
`Nat.card` bound, and `Nat.card` needs no instance. `constTrack` and `progTrack` then take
`[inst_1 : Finite F]` from the `variable` line only to fill it. *Fix:* drop it from the header;
`progTrack` keeps `[Finite F]` through `card_ridersZeroOn_update_le`, which needs it (the
counting lemma is over a `Fintype` built from it), and `constTrack` needs none. If it is kept on
purpose, as a guard that the `≤ 1` counts are meaningful (on an infinite `F` every `Nat.card` is
`0` and the two escape fields hold of any predicate), say so in the docstring; as it stands a
reader cannot tell a guard from an oversight.

**5. The unit conversion `1 / Nat.card E = overE 1` lives only in a test.** *Convention.*
`one_div_card_eq_overE` (`tests/LeanerVMTests/Protocol/GrandProductSecurity.lean:38-40`) is the
one fact the bus phase needs to take `gkrSecurity` into `busError`
(`Spine/Errors.lean:133-135` charges `gkrError E (overE 1) 3 I.μBus`), and a test module is not
importable from production. *Fix:* add `theorem overE_one : overE 1 = (1 / Nat.card E : ℝ≥0)`
beside `overE_add` (`Spine/Errors.lean:77`), proved by `rw [overE, Nat.card_eq_fintype_card,
Nat.cast_one]`, and have the test use it. The alternative, defining `overE` with `Nat.card E`,
would make `gkrSecurity`'s error the slot's up to `Nat.cast_one` alone, but changes the
*Errors* convention (`|E|` is `Fintype.card E`) for no gain beyond one rewrite.

**6. The rider test inhabits a security with an empty input relation; the children
refutation names the completeness relation.** *Non-vacuity of the tests.* (a) The example
`Component.Security (gkr 1 2 four) (relIn 1 2 four rider) (relOut 1 2 four rider) …`
(`tests/…/GrandProductSecurity.lean:53-55`) is the only security with a nonzero rider; since
`rider` is the constant table `(1, 0)`, `RidersZero` fails for every statement and
`relIn 1 2 four rider` is empty, so the example shows that the construction typechecks with a
rider and nothing about what `progTrack` tracks. The mechanism is only exhibited on `relOut`
(`tests/…/GrandProduct.lean:356-360`). *Fix:* add `#guard`s on the progressive predicate at the
last layer, for instance `RidersZeroOn 2 rider () noO (interpPartial 2 #v[] #v[one])` true and
the same at `#v[a]` false (a `Decidable (RestrictedZero t σ)` instance follows from
`Fintype (Fin (2 ^ n))` and `DecidableEq E`, as `relOut`'s does), and a security instance at
`zeroRider`, whose input relation is inhabited. (b) `unchecked_children_no_stateFunction`
(`:98-113`) refutes the descendants' check between `rel Φ 2` and `childRel 3 4 sixteen noRiders
2 2 0` (`GrandProduct.lean:371`, the completeness relation), while the security uses
`childRelT … (constTrack …) 0` (`GrandProductSecurity.lean:345`); the two are equivalent at
stage `0` (`combPartial` of the empty vector is the empty partial point, and a difference zero
there is an equality), but a refutation should name the relation the security is stated at, or
its docstring should say why the other is the same. *Fix:* state it at `childRelT` (the
`sendChecked_no_stateFunction` hypothesis `hout` becomes `⟨fun r hr ↦ absurd hr List.not_mem_nil,
fun t ↦ (diffTable_restrictedZero_empty_iff _ _).mpr rfl⟩` after `combPartial_zero`), or add
the sentence.

**7. Three partial-point builders and nine lemmas where one generic builder would do.**
*Readability; generic code.* `roundsPartial ρ χ` (`:98`), `interpPartial ρ χ u` (`:103`) and
`combPartial u` (`:108`) are "a vector placed at an offset" and "two such placed side by side":
`roundsPartial ρ χ` is `χ` at offset `ρ`, `combPartial u` is `u` at offset `0`,
`interpPartial ρ χ u` is `u` at `0` over `χ` at `ρ`. Each carries a `_zero`, a `_push` and (two
of them) a `_full` lemma, nine private lemmas with six identical two-line `omit` headers
(`:111-192`). *Fix:* in `Restriction.lean`, `def Partial.ofVector (off : ℕ) {k : ℕ} (v : Vector
R k) : Partial R := fun i ↦ if h : off ≤ i ∧ i < off + k then some v[i - off] else none` and
`def Partial.or (σ τ : Partial R) : Partial R := fun i ↦ (σ i).or (τ i)`, with `ofVector_zero`,
`ofVector_push : ofVector off (v.push c) = Function.update (ofVector off v) (off + k) (some c)`,
`ofVector_get` and `or_update_left : (Function.update σ i (some c)).or τ = Function.update
(σ.or τ) i (some c)`; the three builders become one-line abbreviations or disappear, the nine
lemmas become four generic ones, and the test's four `#guard`s (`:124-131`) keep pinning the
coordinates. A simplification, not a defect; it can wait for the upstream move if the owner
prefers.

**8. Repeated proof shapes.** *Readability.* (a) The raise from `((1 : ℕ) : ℝ≥0) / Nat.card F`
to `1 / Nat.card F` by `.mono fun _ ↦ by show …; rw [Nat.cast_one]` appears twice (`:425-429`,
`:471-477`); a `private def oneChallengeSecurity` wrapping `sampleChallengeSecurity … 1` at the
`1 / Nat.card F` error removes both. (b) The pass-through security built from an `iff`,
`Component.passThroughSecurity O f (fun s o w h ↦ by cases w; exact (iff …).mpr h) (fun s o w h ↦
by cases w; exact (iff …).mp h)`, appears five times (`:422`, `:461-468`, `:529-536`,
`:587-594`, `:595-602`); a generic `Component.passThroughSecurity_of_iff (f) (h : ∀ s o,
((f s, o), ()) ∈ relOut ↔ ((s, o), ()) ∈ relIn)` in `PassThrough.lean`, for the `Unit`
witness, removes about twenty-five lines and is itself a candidate for the same upstream.
(c) The six `omit` headers of finding 7 vanish if the partial-point section is opened before
the `variable` line that introduces the instances (`:63-64`), since those definitions and
lemmas use `F` alone.

**9. `GrandProduct.lean:532` is 103 columns.** *Hygiene.* The line is #62's
(`layerStepsFront`'s second case); this branch is stacked on it and can fix it in a commit of
its own, as the skill asks of findings owned by another layer.

### Observations

- **`family` and `childRel` beside `familyT` and `childRelT`.** `Gkr.family`
  (`GrandProduct.lean:208`) is `familyT` at `constTrack` definitionally (both invariants reduce
  to `RidersZero`), and `childRel i` (`:371`) is `childRelT T i` restricted to exact agreement
  (equivalent at stage `0`, stronger after). Completeness is stated on the first pair and
  security on the second, so a reader meets two names for one stage. Merging them would move
  `RiderTrack` into the definition module, which this review does not ask for; a sentence in
  the docstrings of `familyT` and `childRelT` ("`family` is this at `constTrack`") would do.
- **`@[macro_inline]` is a rule, not a one-off.** `Security.mono` and `Security.append`
  (`Component.lean:162`, `:278`) are inlined before compilation so that the real-valued errors
  they take as implicit arguments never reach compiled code; the attribute tells Lean's
  compiler to substitute the definition's body at each call, which is why a caller that passes
  `busError I` no longer depends on it. Every future combinator that takes a `Security` (a
  relabelling by equal verifiers, say) must carry the same attribute, and a `let` or `have`
  binding a `Security` inside a `def` would reintroduce the problem. `tests/README.md` records
  the rule; one sentence in `Component.lean`'s module docstring naming it for new combinators
  would keep it from being learned twice.
- **`natCard_subtype_eq_card_filter`** (`Component.lean:77-79`) is a two-rewrite Mathlib fact
  in an ArkLib candidate; its objects are Mathlib's. Trivial to leave; if the `To*` folders ever
  gain a Mathlib one, it goes there.
- **The whole-file `@[expose] public section`** (every `ToArkLib` module) exposes bodies that
  no consumer unfolds, against CONTRIBUTING's "expose implementation details only when
  definitional unfolding is an intentional API promise". Not this pull request's to settle; it
  is what keeps the eight intermediate securities public (finding 1).
- **Explicit-argument weight.** `lambdaSecurity nside μ leaves riders ρ m inp T hm hinp` and
  its siblings carry up to ten explicit arguments, matching the definition module's style; a
  reader follows them, but the section variables could be made implicit where the type
  determines them (`ρ m` do not: they index the schedule).

## Pass A: the statements

What was checked, statement by statement, against the expectation formed from the blueprint
before the Lean was opened.

- **`gkrSecurity`** (`GrandProductSecurity.lean:637-642`): `Component.Security (gkr nside μ
  leaves) (Gkr.relIn …) (Gkr.relOut …) (gkrError F (1 / Nat.card F) nside μ)`. A
  `Component.Security` (`Component.lean:151-158`) is a guarded verifier, an intermediate-witness
  family, a round-by-round extractor, a knowledge state function for every oracle state, and
  ArkLib's `rbrKnowledgeSoundnessWorstCaseWith` at the given error. That ArkLib predicate
  (`RoundByRound.lean:557-571`) says: for every statement, every challenge round and every
  transcript prefix, the probability over the fresh challenge alone that the state function is
  false before it (for the witness the extractor hands back) and true after it is at most the
  error of that round; the worst-case form, from which ArkLib derives the prover-averaged one.
  With the witness `Unit` this is: the state flips from false to true with probability at most
  the error. The state function's contract (`:165-191`) pins it at both ends: at round zero it
  is the input relation (`toFun_empty`, an equivalence), and at the end it is true whenever the
  verifier can output a statement in the output relation (`toFun_full`); a prover message cannot
  make it true (`toFun_next`). So the composed state is non-trivial by construction.
- **The error** is `gkrError`'s (`Schedule.lean:362-364`) at the unit `1 / Nat.card F`: the
  binary layer's and the radix-four layers' `stepError` (combiner `(nside − 1) · u`, rounds
  `2^ρ · u`, combination challenges `u`) and `drawError F 0` on the last combiner. Checked
  against the blueprint's *GKR* row, Layer 5, and `Spine/Errors.lean:55-57`. The radix-two
  round error `2/|E|` is never charged because the binary layer sits at depth `0` and has no
  sumcheck round; the blueprint agrees.
- **The composition** (`:640-642`) mirrors `gkr`'s (`GrandProduct.lean:627-629`), so the
  schedule and the error line up by definition. The seams between parts are definitional: for
  `constTrack`, `stepOutT` unfolds to `layerRel (m + ρ)`; for `progTrack` it unfolds to
  `stepsIn 0 (m + ρ)`, whose rider conjunct is `relOut`'s read at the layer
  (`stepsIn_zero_iff`).
- **The combiner** (`card_lambdaNext_le`, `:299-327`): if some rider is not zero, the state
  after the combiner is false for every `λ` (the tracked invariant at stage `0` is `RidersZero`,
  independent of `λ`); otherwise some tree's value is wrong and the combination agrees with the
  honest one at the roots of a nonzero polynomial of degree `nside − 1`
  (`card_filter_powerSum_eq_le`, `SumcheckRound.lean:216-234`). Count `nside − 1`.
- **The rounds** (`SumcheckRound.card_badChallenge_le`, `:311-360`): by cases on the invariant.
  If it fails, the challenge restores it at `d` values at most (`Family.Sound`, met by the
  trackers' one-escape fields through `familyT_sound`, `1 ≤ 2^ρ`). If it holds, the running claim
  is wrong, so a recorded polynomial passing the check is not the honest one (the honest one sums
  to the honest claim: `Family.Consistent.check`), and two polynomials of degree `d` agree at
  `d` points at most (`card_filter_evaluate_eq_le`, `:184-212`). Count `2^ρ`; no sum of the two
  cases, so the riders' escape is dominated.
- **The descendants** (`combineCheck_sound`, `:355-374`): values that pass the check and are the
  honest ones make the final claim the summand at the point, so the state before the message
  follows from the state after it; error zero, as a message has no challenge
  (`sendCheckedSecurity`, `SendChecked.lean:180-186`, whose `rbr` is the empty challenge index).
- **The combination challenges** (`card_interpNext_le`, `:391-416`): the state after `i`
  challenges is the tracker's predicate and, per tree, the difference between the sent values
  and the honest ones zero on every completion of the challenges drawn so far. By cases on the
  predicate: if it holds, some tree disagrees and agrees on one more coordinate at one value at
  most; if it fails, it is restored at one value at most. Count `1`. The last challenge also
  interpolates (`interpolateSecurity`, `:469-477`), and its bad set embeds into the previous
  one's through `interpDone_mem_stepOutT_iff`.
- **The one-escape lemma** (`card_filter_restrictedZero_update_le`, `Restriction.lean:129-160`):
  a table's extension is affine in any one coordinate, so if it vanishes on every cube completion
  with that coordinate fixed at two distinct values it vanishes with it fixed at anything, the
  cube's own value included; fixing a coordinate beyond the table's variables changes nothing.
  Over an integral domain. Correct as read.
- **The coordinates.** `roundsPartial_push` fixes sumcheck challenge `j` at coordinate `ρ + j`,
  `interpPartial_push` fixes combination challenge `i` at coordinate `i`; `interpDone`
  (`GrandProduct.lean:409-410`) builds the new point as `u ++ c`, combination challenges first;
  `interpPartial_full` and `progTrack.out_iff` close the loop with `lowPoint`. The test's
  `#guard`s (`:124-131`) pin `[none, none, some a, some b, none, none]` and
  `[some c, some one, some a, some b, none, none]` at `ρ = 2`.
- **The last combiner** (`lastSecurity`, `:613-622`): relation unchanged, so no challenge is
  bad; count `0`, raised from `(0 : ℕ) / |F|` to `0`.
- **The probabilistic step** (`sample_rbr`, `SampleChallenge.lean:189-216`): the event is the
  bad-challenge set, bounded by VCVio's `SampleableType.prEvent_uniformSample_le_div_iff` (the
  canonical sampler of a `SampleableType` is uniform on the whole type, so the probability of a
  set is its size over the type's), in the direction that matters, after `Nat.card` is rewritten
  to `Fintype.card` on a `Fintype` built from `Finite`. One probabilistic fact in the whole
  argument.
- **The refutations.** `sampleChallenge_not_rbr` (`:235-249`) and
  `drawChallenge_unchecked_not_rbr` (`SumcheckRound.lean:383-401`): from the honest polynomial
  at a wrong claim, every challenge lands in the next relation and the statement has no witness
  in the one before, so `Verifier.not_rbr_zero` makes the escape certain, whatever the extractor
  and the state function. `sendChecked_no_stateFunction` (`SendChecked.lean:192-206`): a
  message passing the trivial check carries a witness-less statement into the output relation,
  so `toFun_full`, `toFun_next` and `toFun_empty` contradict. Both are instantiated on the
  sixteen-leaf trees at a symbolic statement whose claim is the family's plus one.
- **Substitution test.** Replace the round check by a plain-weights one (`q(0) + q(1)`): the
  honest family's `Consistent.check` fails and `card_badChallenge_le`'s honest branch no longer
  concludes the running claim is the family's. Replace `combineCheck` by a check on tree `0`
  alone: `combineCheck_sound` cannot rewrite the final claim. The specification does not survive
  a differently shaped check.

Nothing vacuous was found; every hypothesis is discharged at each call site.

## Pass B: fidelity

Category A: a generic security statement written from the mathematics, with no transcribed
constant, layout or constraint; there is no artifact to enumerate against `gkr.rs`, and the
pinned Rust was not consulted for this pass. What fidelity there is to check is the schedule's
shape and the error per challenge, both fixed by #62 and the spine (`gkrSpec`, `gkrError`):
the radix, the binary layer first for odd `μ`, a combiner after every layer with the last at
error `0`, two combination challenges per radix-four layer and one for the binary layer, as
the blueprint's *GKR* row and `Spine/Errors.lean:30-37, 55-57` state. This pull request attaches
the proof to that schedule without changing it, and the numeric tests of #62
(`tests/LeanerVMTests/Protocol/GrandProduct.lean:72-102`) keep pinning rounds, challenges,
directions, message types and errors. Count matched: four kinds of challenge, four errors.

## Pass C: hygiene

Module shape, imports (`public import` where a downstream user needs the dependency, plain
`import` for `Mathlib.Tactic.LinearCombination`), naming, section headers and `omit` discipline
follow CONTRIBUTING. Every public declaration has a one- or two-line docstring; the module
docstrings carry the design (the trackers, the split on `k`, the stage relations) and do not
narrate proofs; no comment cites the roadmap. The repository gates `audit-lean.sh`,
`check-imports.sh`, `check-layers.sh` and `check-docs.py` pass. `tests/README.md` gained the
three pitfalls this work met (the classical `Finset.filter` instance, the `0/1/k+2` split, the
closed statement over `E` in a definitional comparison), and `docs/README.md` lists the first
review. The status page describes the branch as built. Residual items are findings 7–9.

## Kernel axioms

`#print axioms LeanerVM.Protocol.gkrSecurity`: `propext`, `Classical.choice`, `Quot.sound`
(probed at `7dbb95b`). The pull request reports the same for the whole namespace through
`./scripts/validate.sh`.

## Where this review agrees with the first

Read after the passes. The two agree on the verdict (no theorem wrong, vacuous or tautological),
on the escape counts, on the coordinates, and on the refutations now holding for every
extractor and state function (its finding 2, met). Its finding 1 (computability) is met as its
disposition says, and this review's finding 2 is a consequence of meeting it: the hand-written
`Phases.Security.extraction` lost its reason to exist. Its findings 3–6 are met; this review's
findings 1, 4, 6, 7 and 8 were not raised there and are new. On the error's form the two agree
that `gkrError F (1 / Nat.card F) nside μ` is the right statement for a generic module and that
the slot takes it through one `Security.mono`; this review adds that the conversion lemma
belongs in production (finding 5).

## What could not be checked

- That `Phases.Security.toDef` compiles to code that runs: it is a `def` without
  `noncomputable`, which is the convention's witness (test 24); no `#eval` of an extractor on a
  transcript exists, and none was attempted here.
- The bus phase's consumption, which is not built: the shape was checked against
  `busShape` in the tests (`tests/LeanerVMTests/Protocol/GrandProduct.lean:114-131`), which
  places `gkr 3 toy.μBus` in the slot's schedule, and against `busError`'s term.
