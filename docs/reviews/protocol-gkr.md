# Review: the grand-product GKR, definition and completeness

> An archive of the review of one commit, `efca3af` of pull request #62: names, paths and line
> numbers are that commit's. What is accepted from it is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of the
> pull request that met it.

**Disposition** (met in `f2229a3` unless the row says otherwise):

| Finding | Disposition |
| --- | --- |
| 1. the unused last combiner inside a generic module | kept, as Layer 5 and the *GKR* convention put it in `gkr`; the module docstring says what it is written from and why the combiner stays. Moving it to the bus phase is a change to the blueprint, left to its maintainer. |
| 2. the combiner is Layer 4's `batch nside` | the status records `Gkr.lambdaStep` as a stand-in for batching by powers. The holes table's *Needs* for the GKR's knowledge soundness is the blueprint's, left to its maintainer. |
| 3. the degree bound and the combiner's power order unguarded | guarded: the schedule's message types by `rfl`, the powers `1, λ, λ²` of the combined claim and of the descendants' check by numeric guards. |
| 4. whether Layer 4's `Sumcheck.normalized` can take the GKR's rounds | a question for the blueprint (a family form of the normalized sumcheck), left to its maintainer. |
| 5. `boolVec_cubeIndex` unused | removed. |
| 6. `evalMle_contractPow` used by no proof | kept: the layer identity in closed form, tested over the integers. |
| 7. proof helpers public; missing docstrings | seven proof-only theorems private (two referenced from exposed definitions through tactic blocks); the `fixLow` helpers of `PartialSum.lean` private except `fixLow_push_set`, which the grand product uses; docstrings added. |
| 8. roadmap vocabulary in `SumcheckRound.lean` | reworded. |
| 9. lines over 100 columns | rewrapped. |
| 10. status header and restated errors | the header no longer pre-empts the merge; the errors are those Layer 5 gives. |
| 11. description and test header | reworded. |

Branch `feat/protocol-gkr`, head `efca3af`, against `origin/main` at `32dbe65`. Reviewed with the
`adversarial-review` skill in three passes: statements against the blueprint (the Lean is the
standard, the Rust may be wrong), fidelity to leanVM `a386121f` (`crates/lean_vm/src/gkr.rs:247-430`,
`crates/fiat_shamir/src/transcript.rs:280-310`, `crates/primitives/src/multilinear.rs:39-41, 245-247`,
`doc/leanvm/body/05-arithmetization.tex:61-95`), and hygiene. The pass on fidelity was run from the
Rust and the specification before reading the Lean's checks. Nothing was edited.

Target classification: the pull request names T4 through the bus phase, completeness only; the
knowledge-soundness half is a separate hole. That is stated correctly in the description.

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological, and nothing in the schedule, the checks, the
interpolation or the point order departs from the pinned Rust. The recorded divergences from the
blueprint (the spine's slot shape, the local round, riders on the relations, `Fin (μ + 1)`) are
all justified and honestly recorded. What the review found is at the medium level: two things
the generic module carries that the blueprint's own "Generic code" convention forbids or leaves
unsaid (the unused last combiner, and the combiner as an unrecorded stand-in for `batch`); two
verifier conventions that no theorem or test currently pins and that the description does not
list among the unguarded checks (the message degree bound, the order of the combiner's powers);
and a blueprint gap on whether Layer 4's `Sumcheck.normalized` will be able to take the GKR's
rounds at all. Below that, surface and documentation nits.

## Findings, most severe first

### Medium

**1. The unused last combiner is a leanVM transcript quirk inside a generic ArkLib candidate.**
*Fit to the blueprint; surface.*
`LeanerVM/Protocol/ToArkLib/GrandProduct.lean:629-632` (`Gkr.lastCombiner`), `:661-664` (`gkr`
appends it). The pinned convention *Generic code* says a `To*` module carries "no special case the
protocol chose" and the special case "is derived in a leanVM module, which cites the
specification". A combiner that is drawn after the last layer and read by nothing is exactly such
a case: it exists because both deployed leanVM verifiers draw it (`gkr.rs:423`, recorded as a
discrepancy in `docs/leanvm-target.md:124-126`), and no other consumer of a product-tree GKR wants
it. The blueprint's Layer 5 and the *GKR* convention row put it inside `gkr`, so this is
**(c) a defect of the blueprint**, faithfully transcribed by the Lean. Concrete cost: an upstream
reviewer of `gkr` cannot see why the component ends with a `sampleChallenge (fun s _ ↦ s) 0`, and
the only citation that would explain it is forbidden in the module. Fix: end the generic `gkr`
after `Gkr.body`; let the bus phase (Layer 6) append `Component.sampleChallenge O E (fun s _ ↦ s) 0`
with the citation `gkr.rs:423`, and change Layer 5 and the *GKR* row accordingly in a
`docs(protocol): …` pull request. The acceptance test 17 counts move with it, unchanged in total.
Related: the module docstring of `GrandProduct.lean` neither cites a source nor says "nothing here
transcribes a source" (as `ProductTree.lean:20` and `PartialSum.lean:27` do), although the shape
(radix four, radix two first when odd, the point order) is what the pull request says was checked
against `gkr.rs`. One line either way.

**2. The combiner is the blueprint's `batch nside`, and the status does not say so.**
*Fit to the blueprint; documentation.*
`GrandProduct.lean:267-278` (`Gkr.lambdaNext`, `Gkr.lambdaStep`) draws one challenge and forms
`Σ_s λ^s · value_s` at error `(nside − 1)/|F|`; that is Layer 4's "batching by powers"
(`batch (k)`, error `(k − 1)/|F|`, state function "some claim is false"). The status records
`SumcheckRound.round` as "a local stand-in for `Sumcheck.normalized`" but records nothing for the
combiner, and the holes table's *Needs* column for "grand-product GKR: knowledge soundness" lists
the sumcheck's knowledge soundness but not "batching by powers". Concrete consequence: the
knowledge-soundness pull request will prove the power-batching escape bound a second time inside
`gkrSecurity`, or `batchSecurity` will land unused by the GKR. This is **(b)** for the status
(one more sentence in the GKR's "owes" item: `Gkr.lambdaStep` becomes `batch nside` followed by a
pass-through when batching by powers lands) and **(c)** for the holes table's *Needs* column.

**3. Two verifier conventions are unguarded and unlisted.** *Non-vacuity; documentation.*
The description says the round check and the descendants' check are the checks whose refutations
come with the knowledge-soundness hole. Two more things a wrong verifier could change while
`gkrComplete` and every test still pass:

- *The message degree bound.* `GrandProduct.lean:194-198` (`Gkr.roundPoly : SumcheckRound.Message F (2 ^ ρ)`)
  and `SumcheckRound.lean:72-73`. Replacing `2 ^ ρ` by `2 ^ ρ + 1` (or removing the bound) keeps
  `degree_roundPolyRaw_le` usable, keeps completeness, keeps `#guard q0.val.natDegree ≤ 4`
  (`tests/LeanerVMTests/Protocol/GrandProduct.lean:204`), and leaves the error `2 ^ ρ/|F|` false.
  Only the knowledge bound would refuse it. This is the type-level counterpart of the Rust
  reading exactly four coefficients (`transcript.rs:297-302`) and should be named among the
  unguarded checks.
- *The order of the combiner's powers.* `lambdaNext` (`:270`) uses `l ^ t.val` and `combineCheck`
  (`:346-348`) uses `s.1.2 ^ t.val`; both are consistent with the Rust's `poly_eval`
  (`multilinear.rs:245-247`: `values[0] + λ·values[1] + λ²·values[2]`). Changing both to
  `λ^(t+1)`, or to `λ^(nside − 1 − t)`, or dropping `λ` altogether, keeps `lambdaNext_mem_rel`,
  `gkrComplete` and every `#guard` (the tests compare the combined claim only with
  `partialSum (summand …)`, `tests/…/GrandProduct.lean:186`, which changes with it). Nothing pins
  the convention before `verify_iff_compiled` (Layer 12). Fix now, cheaply: two numeric guards,
  `claim0 = vals 0 + lam * vals 1 + lam * lam * vals 2` and
  `s2.2.2 = ∏ c, (ch 0)[c] + lam * ∏ c, (ch 1)[c] + lam * lam * ∏ c, (ch 2)[c]`, and list the
  convention in the description's "Refutations of the checks".

The description is otherwise honest: the round check and the descendants' check can be removed
or weakened without breaking any theorem in this pull request, and it says so.

**4. The blueprint's `Sumcheck.normalized` may not be able to take the GKR's rounds.**
*Fit to the blueprint (c).*
Layer 4 gives `Sumcheck.normalized (d_c) : Component.Def …` over a `Virtual F n m d` (a formula in
`m` fixed tables). The GKR's summand (`Gkr.summand`, `GrandProduct.lean:145-147`) is a formula in
tables that depend on the step's context: the trees' levels read from the oracles, and the
combiner and the point read from the statement. `SumcheckRound.Family` (`SumcheckRound.lean:112-121`)
is the family form the GKR needs (`claim`, `poly`, `weight`, `inv` as functions of the context and
the challenges). The status promises that the rounds "become" `Sumcheck.normalized` when the
sumcheck hole lands; whether that is possible depends on a shape Layer 4 does not fix. The
blueprint should say that the normalized variant is stated in family form (or that `Virtual` is
indexed by the context), so the promise can be kept. This is a gap in the specification, not in
the Lean.

### Low

**5. Dead lemma.** *Surface.* `LeanerVM/Protocol/ToCompPoly/Multilinear.lean:396-403`
(`boolVec_cubeIndex`) is used by nothing under `LeanerVM/` or `tests/`. Remove it or use it.

**6. The layer identity is documentary, not load-bearing.** *Surface; observation.*
`ProductTree.lean:155-165` (`evalMle_contractPow`) is used by no proof: `gkrComplete` reaches the
identity through `layerTable_contractPow`, `contractPow_getElem`, `evalMle_childPoint_boolVec`
(`Gkr.summand_boolVec`, `GrandProduct.lean:284-291`) and `partialSum_zero` with `evalMle_ofFn_sum`.
The module docstring (`:25-26`) and the description present it as "the layer identity a
grand-product argument runs sumcheck on". Either route `summand_boolVec` through it or say it is
the closed form for reading, tested at `tests/…/ProductTree.lean:58-63`.

**7. Proof helpers in the exposed public section.** *Surface.* Candidates for `private` or for a
place outside `public section`: `Gkr.descendant` (`GrandProduct.lean:150`), `roundPolyRaw`
(`:158`), `degree_roundPolyRaw_le` (`:169`), `roundPoly_eval` (`:215`), `roundPoly_check` (`:248`),
`summand_boolVec` (`:284`), `lambdaNext_mem_rel` (`:296`), `childrenComplete_aux` (`:463`, a public
theorem named `_aux`), `rootStmt_mem` (`:620`), `layerRel_subset_relOut` (`:638`);
`PartialSum.lean`: `fixLow_zero` (`:55`), `drop_zero` (`:62`, a general `Vector` fact under
`LeanerVM.Protocol`; core `v4.34.1` has `Vector.drop_mk` but no `drop_zero`, so not a duplicate),
`fixLow_self` (`:80`), `fixLow_push_zero`/`_one`/`_set` (`:100, 118, 137`). Missing docstrings on
public declarations: `ProductTree.lean:53` (`contract_getElem`), `:72` (`childIndex_val`),
`PartialSum.lean:55, 62, 80`. The security half will need `SumcheckRound.check`, `guarded`,
`verifier_verify`, `Gkr.combineCheck`, `childrenGuarded`, `childrenVerifier_verify`, `childRel`;
those are rightly public.

**8. Roadmap vocabulary in a `ToArkLib` docstring.** *Documentation.*
`SumcheckRound.lean:44`: "or once the spine moves to that architecture". "The spine" is this
repository's roadmap name; in a module written for ArkLib's other consumers it means nothing.
Say "once this repository's oracle reductions move to that architecture", or drop the clause.

**9. Lines over 100 characters.** *Hygiene.* `ProductTree.lean:54` (103), `PartialSum.lean:156`
(101), `tests/LeanerVMTests/Protocol/GrandProduct.lean:251` (101); in the status file, the lines
this pull request wrote: `docs/roadmap/protocol-status.md:4` (154), `:78` (141), `:93` (120).

**10. Status page wording.** *Documentation.* `protocol-status.md:3-4`: "stands on `main` at
`32dbe65` … with the grand-product GKR's definition and completeness (#62)" reads as if #62 were
on `main`, two lines after "Open pull requests are not part of `main`"; the row `#62 | on merge |
on merge` (`:22`) is the honest placeholder, so the header should not pre-empt it. `:75-79`
restates the blueprint's error values ("the values it charges today: …") which Layer 5 already
gives; under "one home per fact" say "the values Layer 5 gives" and keep only what differs (nothing
does). No letter codes were introduced; names are in words.

**11. Description and test-header nits.** *Documentation.* The description's summary sentence
("a combiner, then one binary step when `μ` is odd and radix-four steps after, each a normalized
sumcheck …") reads as one combiner in total; every step begins with its own combiner
(`Gkr.layerStep`, `GrandProduct.lean:557-561`). The test header (`tests/…/GrandProduct.lean:8`)
says "trees of four and sixteen leaves" while `gkr 3 3` runs on eight (`:233-235`).

## The recorded divergences, verified

| Divergence | Verdict |
| --- | --- |
| Error inside `Component.Def`; no closed-form `gkrSpec`/`gkrError`; `Complete` rather than `Guarded` | **(a)** justified: the spine on `main` still has `err` in `Def` and `Complete` with `guarded`/`outputPure`; the status names the revision that changes it. Side effect worth naming: `gkr` is `noncomputable` only through `err : ℝ≥0`, so no test can run the composed reduction; once the spine's revision lands, an executable honest run of `gkr` should replace the hand run. |
| Rounds on a local `SumcheckRound` rather than `Sumcheck.normalized` | **(a)** recorded; but see finding 4 on whether the switch is possible as Layer 4 is written. The docstring's description of ArkLib's native round (`Sumcheck.Interaction.Native.Core.verifier`, in `Interaction/Protocol.lean:98-125`: sum over a unit-weight domain, compare, sample, evaluate at the challenge, carry) is accurate, and ArkLib's sumcheck tree at `7653a901` has neither weights nor an `OracleReduction` adaptor, as `docs/dependencies.md` says. |
| Riders on the relations and `gkrComplete`, not on `gkr` | **(a)** justified and better than the sketch: `gkr` reads no rider, so a rider argument on it would be data the reduction ignores. Recommend the blueprint adopt it (Layer 5 signature; decision 18). For completeness the rider conjunct is a corollary of "a zero table has a zero extension" (`layerRel_subset_relOut`); its content is the security half's state function. |
| A rider's variable count is `Fin (μ + 1)` | **(a)** justified: `lowPoint ζ τ` needs `τ ≤ μ`, and the bus phase's side condition (decision 30, `∀ j, constraints j ≠ [] → τ_j ≤ μ_bus`) supplies it. Recommend the blueprint write `τ ≤ μ` in Layer 5. |

## Pass A: the statements

- `Gkr.relIn` (`GrandProduct.lean:117-119`): every rider table zero, every root the product of its
  leaves. Names independent objects (`Finset.prod` over the table, `RidersZero`); inhabited by
  `roots16` (`tests/…/GrandProduct.lean:151`) and refuted by `root'` (`:127`). Sound.
- `Gkr.relOut` (`:129-131`): each value is `evalMle` of its leaves at `ζ`; each rider's extension
  vanishes at `lowPoint ζ τ`. Semantic (CompPoly's `evalMle`), not a restatement of any check:
  a verifier that swapped the point's halves, or interpolated the descendants in the other bit
  order, would fail it on the honest run (`:229`). The rider conjunct distinguishes low from high
  coordinates: `atRoot` has point `[1, a]` with `a = y ≠ 1` (`:311, 318`). Sound.
- `Gkr.layerRel` (`:123-125`): the value is the extension of the level on `m` variables at the
  point; `layerTable` is total (ones past the leaves) but every step takes `m + ρ ≤ μ`
  (`layerStepComplete`, `body`, `layerSteps`), so the padding branch is never reached. Sound.
- `gkrComplete` (`:669-675`): `Component.Complete (gkr …) relIn relOut`, composed by
  `Complete.append` through `SumcheckRound.rel family j`, `childRel`, `layerRel`. Substitution
  test: it could not survive a different check *form* the honest prover fails (unit weights, a
  plain final check with an equality factor, the other point order), but it survives a *weaker*
  or absent check, which is the security half's job and is said so. Axioms:
  `propext, Classical.choice, Quot.sound` for `gkrComplete`, `gkr`,
  `SumcheckRound.roundComplete`, `Component.sampleChallengeComplete`, `evalMle_contractPow`; no
  `sorryAx`.
- Evidence of the tests: the hand runs call the verifiers' own decision functions
  (`SumcheckRound.check`, `SumcheckRound.next`, `Gkr.combineCheck`, `childNext`, `interpNext`,
  `interpDone`, `lambdaNext`), and `SumcheckRound.verifier_verify` (`SumcheckRound.lean:275-288`),
  `Gkr.childrenVerifier_verify` (`GrandProduct.lean:412-432`) and
  `Component.sampleVerifier_toVerifier_run` (`SampleChallenge.lean:76-81`) prove those functions
  are the oracle verifiers' verdicts; `gkrComplete` proves the composition wires them as the hand
  run assumes. The four rejections (`tests/…/GrandProduct.lean:286-293`) each fail the named check
  and nothing else: `q0'` fails `check` at the honest claim, the honest `q0` fails `check` at
  `claim0 + 1`, tampered descendants fail `combineCheck` at the honest claim, honest descendants
  fail it at `s2.2.2 + 1`. Together with finding 3, this is the whole current guard.
- Both test files compile (`lake env lean`, exit 0, no warnings); `audit-lean.sh`,
  `check-imports.sh`, `check-layers.sh`, `check-docs.py` pass.

## Pass B: fidelity to `gkr.rs:247-430` at `a386121f`

Enumerated from `verify_product_triple` and ticked against the Lean:

| Rust | Lean | Match |
| --- | --- | --- |
| `lambda = sample()` after the roots; `claim = poly_eval(values, λ)` = `Σ_s λ^s value_s` (`:369-374`) | `Gkr.lambdaStep`, `lambdaNext` (`:269-278`) | yes |
| Odd `μ`: root-most binary layer, no rounds, two tails per tree, `claim == Σ λ^s left·right`, one challenge, `interp`, `point = [χ]`, resample λ (`:376-394`) | `body` odd branch: `layerStep 1 0` (`:601-602`) | yes |
| Radix-4 layer: `round_count = μ − layer` rounds, each `next_round_poly(5, claim, Some(point[j]))` i.e. `claim = (1 − r_j)·h(0) + r_j·h(1)` with `c_0` derived, `claim ← h(χ_j)` (`:398-404`; `transcript.rs:297-302`) | `SumcheckRound.round` on `normalizedWeights` (`SumcheckRound.lean:108-109, 257-269`), `Message F 4` | yes (the wire's dropped `c_0` is Layer 4's transport, convention *Sumcheck messages*) |
| Equality points consumed in order `point[0], point[1], …`; prover folds the lowest row bit first with `eq_table(point[1..])` shrunk each round (`:398`, `:174-200`) | `partialSum` binds coordinate `j` at round `j`; `roundPolyRaw` weights by `lagrangeBasis (r.drop (j+1))` (`PartialSum.lean:49`, `GrandProduct.lean:160`) | yes |
| Four tails per tree; `claim == Σ λ^s t0·t1·t2·t3`, no equality factor (`:405-412`) | `Gkr.combineCheck` (`:346-348`), `partialSum_self` | yes |
| `low = sample(); high = sample()`; `value = interp(interp(t0,t1,low), interp(t2,t3,low), high)` with `interp(lo,hi,t) = lo + t·(lo+hi)` (`:413-420`; `multilinear.rs:39-41`) | `interpolate` draws `u_0` then `u_1`; `interpDone` takes `evalMle [t0,t1,t2,t3] (u_0,u_1)`, bit 0 = `u_0` (`:506-522`) | yes (child `c = a + 2b`, `childIndex ρ c x = c + 2^ρ x`, `ProductTree.lean:65`) |
| `point = [low, high] ++ round_point` (`:422`) | `Vector.cast (u ++ c)` (`:513`); test `[b, a, c0, c1]` (`tests:227`) | yes |
| λ resampled after every layer, the last included and unused (`:423`) | `layerStep` begins with `lambdaStep`; `lastCombiner` at error 0 (`:630-632`) | yes (see finding 1 on where it should live) |
| Errors (blueprint Layer 5): `(nside−1)/|E|` per combiner but the last, `0` on the last, `4/|E|` per radix-4 round, `1/|E|` per combination challenge | `tests:87-95` by `rfl` | yes |
| `μ = 0`: one sampled λ, no layer (`:369, 375`) | `body` = pass-through, then `lastCombiner` | yes |

Counts: two explicit checks in the Rust (binary and radix-4 layer checks) plus the implicit
five-coefficient wire format; two explicit checks in the Lean (`check` per round, which the Rust
folds into deriving `c_0`, and `combineCheck`) plus the type-level bound `Message F (2^ρ)`.
Challenges for `μ = 4`: `1 + (0+2) + 1 + (2+2) + 1 = 9` (`tests:73-74`); for `μ = 3`: 7; messages
for `μ = 4`: 4. Acceptance test 17's `μ²/4 + μ + 1` holds. The `FirstTwoShared` root shape
(`:361-367`) is the bus phase's, correctly out of scope. No historical (Poseidon, KoalaBear,
LogUp) material. The description's citations (`:369, 391, 423`, `:398-404`, `:410-412`,
`:414-425`) point at the right lines.

## Pass C: hygiene

Findings 5, 7, 8, 9, 10, 11 above. Otherwise clean: module shape (header, `module`, narrow
`public import`s, module docstring, `@[expose] public section`) follows `Component.lean`; the
module docstrings carry design rationale and the ArkLib #818 name map without narrating proofs;
`Gkr.LayerCtx` accessor abbreviations keep the projection chains readable; the two `tests/README.md`
pitfalls are self-contained; `LeanerVM.lean` and `tests/LeanerVMTests.lean` register every new
module (the reorder of four `Semantics.*` test imports is an unrelated but harmless tidy-up).

## What was checked and found sound

The schedule, checks, next-claim rule, descendants' check, interpolation bit order, point order,
λ-power convention and per-challenge errors against the pinned Rust and the blueprint's *GKR* and
*Sumcheck variants* rows; the three relations for semantic content and inhabitation; the axiom
closure of the five public results; both test files compiling without warnings; the four
repository scripts; the docstring's account of ArkLib's native round and the dependencies bullet
against ArkLib `7653a901`; the four recorded divergences; the absence of letter codes and of
roadmap citations in new text (one exception, finding 8).

## What could not be checked

- A run of the composed `gkr` reduction on the toy: `gkr` is `noncomputable` through `err : ℝ≥0`.
- The Python verifier as a cross-check of the schedule (not consulted; the Rust and the blueprint
  agree with the Lean, and the counts in acceptance test 17 are the blueprint's).
- Whether Layer 4's `Sumcheck.normalized` and the `batch` of pull request #43 will accept
  `SumcheckRound.Family` and `Gkr.lambdaStep` as written (findings 2 and 4); neither is on `main`.
- The full `./scripts/validate.sh` and the kernel axiom audit over the whole namespace (CI).
