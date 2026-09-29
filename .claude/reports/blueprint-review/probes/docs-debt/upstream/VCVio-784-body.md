Adds the library lemmas that #767 and #768 were proving inline, simplifies the existing proofs that re-derived one of them, and brings over the controls from both PRs as tests of the new lemmas.

## Library

**State preservation on reachable queries** (`VCVio/OracleComp/QueryTracking/QueryBound/Simulation.lean`)
- `AllQueriesSatisfy.simulateQ_run_eq_map_run'`: if every query `oa` can make satisfies `P`, and `impl : QueryImpl spec (StateT σ m)` answers each `P`-query without changing its state, then `(simulateQ impl oa).run s = (·, s) <$> (simulateQ impl oa).run' s`.
- `AllQueriesSatisfy.simulateQ_run'_bind`: its `run'`-of-bind corollary.

The existing lemmas `simulateQ_run_preserves_inv_of_query` and `simulateQ_run_eq_of_snd_invariant` need the invariance hypothesis on every query index. These only need it on indices the computation can reach, which is the random-oracle case: hash queries do change the cache, and a zero-budget adversary never makes one.

**Random-oracle corollaries** (`VCVio/OracleComp/QueryTracking/RandomOracle/Simulation.lean`)
- `roSim.run_eq_map_run'_of_isQueryBoundP_zero` and `roSim.run'_bind_of_isQueryBoundP_zero`: simulating through `unifFwdImpl + ro` a computation with `IsQueryBoundP p 0` leaves the cache untouched, for any `p` that charges every `hashSpec` query (`hp : ∀ t, p (.inr t)`). They play the role of `roSim.run_liftM` for a computation given with a query bound rather than as a `liftComp`.
- The predicate is a parameter rather than fixed to `(· matches .inr _)`: each module elaborates its own matcher for that idiom, so a caller's `(· matches .inr _)` doesn't match one fixed in the lemma statement. Callers pass `hp := fun _ => rfl`.

**Preimage form of `evalDist_map`** (`VCVio/EvalDist/Defs/Measure/Core.lean`)
- `evalDist_map_apply (hf : Measurable f) (hs : MeasurableSet s) : 𝒟[f <$> mx] s = 𝒟[mx] (f ⁻¹' s)` and `evalDist_map_apply_of_discrete`.
- Neither is `@[simp]`: on a discrete source type the lemma would fire on every `𝒟[f <$> mx] s` in the library and change existing simp normal forms.
- Call sites that rewrote with `evalDist_map`/`evalDist_map_of_discrete` and then `Measure.map_apply` now use them: `Core.lean` (`evalDist_map_apply_univ`), `OptionT.lean`, `ProbabilityNotation.lean` (2), `MacFromPRF.lean`, `Fischlin/ExtractionGuarantee.lean`, `Constructions/Fork.lean`, and the examples `BR93`, `OneTimePad/Reactive/Security`, `PRFTagReader/NetworkUnlinkability`, `ReplayCheckpoint`, `ProgramLogic/RandomOracleRouting`.

## Tests

- `VCVioTest/RandomOracleControls.lean` (from #767, by @eliasjudin): the file-local `IsHashQuery` predicate is replaced by the `(· matches .inr _)` idiom. The induction in `zeroHashQuery_guess_probability` is replaced by `roSim.run'_bind_of_isQueryBoundP_zero`, and the helper `finishGuess_localCoin` is removed.
- `VCVioTest/ProductRelationControls.lean` (from #768, by @eliasjudin): proofs use `evalDist_map_apply_of_discrete`. Statements are unchanged.

Supersedes #767 and #768.

## Validation

`./scripts/validate.sh --lint --test --axioms` passes locally on Lean 4.34.0: build and warning budget, lint, tests, and the axiom sweep (no new axiom or sorry taint).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
