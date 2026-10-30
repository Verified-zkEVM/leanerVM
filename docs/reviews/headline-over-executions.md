# Review: the headline over leanISA executions (PR B)

Branch `feat/headline-execution` at `61b288c2`; diff `origin/group/10-adaptive..HEAD` minus
PR A (`docs/reviews/leanisa-clean-equivalence.md`). Pins: leanVM `a386121f`, Clean fork
`61c6e013`. Kernel axioms of `baseVerifier_extractsExecution{,_rom,_coins,_adaptive,_adaptive_coins}`,
`prove_eq_none`, `prove_complete_of_execution`: the standard three (probe). `check-imports`,
`check-layers`, `audit-lean` pass. Claims T4 (knowledge soundness of the deployed verifier, an
execution extracted) and the completeness half of the deployed pair; both are supported.

## Findings, most severe first

### 1. The grind disjunct of `prove_eq_none` is witness-free — CONFIRMED (probe)

`Protocol/Headline.lean:579-583`, `:596-604`. The conclusion's third case is
`∃ fs : FsState, Id.run (fs.grind blake2sBytes fuel queryGrindingBits) = none`, quantified over
*every* state, not the states of the prover's run. The probe shows
`Deployed.grind fuel (FsState.seed fillProg mulInput) 17 = none` at fuel 1, 16 and 256, so at
those fuels the disjunction holds for every witness, and the `prove = none →` conjunct of
`prove_complete_of_execution` says nothing. For any fuel far below `2^17` some state fails, so
this is the general case. The docstrings overclaim: "a grind finds no nonce … at some chain
state" (`:577`, `:593`), the module doc `:65-66`, the blueprint (`:41`, `:2155-2160`) and the
status (`:1484-1486`) read as if the failing state were one the run visits.

Fix, in order of strength: (a) reword to "at some state, not necessarily one of the run's";
(b) make `Prove.proveFrom_eq_none` return a state of the writer's run (its `Runs` relation already
threads `FsState`), so the case reads `∃ fs ∈ chain states of the run`; (c) the honest bound the
status already owes: for `honestAdversary` under `runRandom`, `Pr[proof = ⟨[], []⟩] ≤
grinds · (1 − 2^-17)^fuel`.

### 2. `Trace.Fits` does not pin the stack: completeness is empty for `t.κ ≥ 26` — CONFIRMED (reading)

`Semantics/PaddedTrace.lean:85-87` (`room : t.κ < maxLogMem`, i.e. `≤ 31`),
`Semantics/PaddedImage.lean:125-127` (`padTrace` has `κ = t.κ + 1`), `Protocol/LeanIsa.lean:34,184`
(four memory columns at height `2^logMem`), `:385` (`maxMu = 28`). The completeness witness's
stack total is at least `4 · 2^(t.κ+1) = 2^(t.κ+3)`, so `leanIsaμ ≥ 29 > maxMu` whenever
`t.κ ≥ 26`: `prove` returns `none` at every fuel and rate, and the headline's conclusion is met by
its first disjunct alone. The status says only "nothing shows that the stack … is within
`2^maxMu`"; the blueprint (`:2570-2572`) still says `hfit` "stands in" for admissible heights,
which it does not. The same holds for any execution whose filled tables exceed `2^28` cells in
total, within the per-table cap `2^32`.

Fix: expose the sizes. Let `constraintCompleteness` return `Sizes.ofWitness w = some s` with
`s.logMem = t.κ + 1` and `s.τ j` the filled heights (the `JUMP` height is the one `JumpFeasible`
picks), and add to `prove_complete_of_execution` the positive conjunct, provable now from
`Prove.proveWith_ne_none` and `admissible_iff_of_satisfiedBy`:

```text
∀ s, Sizes.ofWitness w = some s → leanIsaμ prog s ≤ maxMu → validRate ρ →
  (∀ fs, Id.run (fs.grind blake2sBytes fuel queryGrindingBits) ≠ none) →
  prove fuel prog input w ρ ≠ none
```

The strongest statement provable today is that conjunct plus the present ones. What an
unconditional "`prove` returns `some`" still needs: a resource hypothesis on `t` that bounds
`leanIsaμ` (a `Sizes`-level fit, replacing `room`), and for the grind either the run-state form
(1b) or the random-oracle bound (1c); no deterministic form at BLAKE2s can drop the grind clause,
since the probe exhibits a failing state at small fuel.

### 3. Hypotheses stronger than needed, stale decision text — CONFIRMED (reading), Low

`Headline.lean:333-341`, `:426-434`: the `_wellFormed` corollaries take `WellFormedBytecode`,
which since PR A carries `hasFillBlocks`; soundness uses `.sentinelSafe` only. The weakest honest
hypothesis is `∀ g ∈ support …, SentinelSafe g.prog`. Keep the corollaries if they are the form
callers want, but say that the fill blocks are unused. Blueprint decision 42 (`:2659`) says the
fill blocks are "a later field" (they are the field now); `:2073` says completeness from an
execution "would take it through `constraintCompleteness`" (it does).

### 4. Observations (no defect)

- `baseVerifier_extractsExecution_rom_adaptive` puts `SentinelSafe` in the event, correctly: the
  program with a sentinel `JUMP` (`exists_satisfiedBy_without_execution`, now `∃ κ w` at
  `minLogMem`, same conjuncts) has an accepted proof and no execution.
- `blakeMisbehaves_of_comparison` at a coin-free adversary is degenerate (one run, `δ < 1` forces
  it clean), as the audit of #156 noted; the coins forms are the quantitative ones. Unchanged here.

## Pass A: statements

Who picks κ: the adversary, through `proof.announced?`; `extract` (`RandomOracleGame.lean:142`)
and `setup?` (`Verify/Setup.lean:68`) make the same `Sizes.Admissible ∧ validRate` check before
any hash, the extracted witness lives at `s.logMem`, `traceOf` keeps it, and `ValidExecution`
requires `minLogMem ≤ κ ≤ maxLogMem` with the two public words. The verifier's acceptance pins κ
to the window the specification leaves to the prover; nothing to exploit. The extractor is a chain
of plain `def`s (`extract`, `witnessOf`, `traceOf`); no classical step. `IsTotalQueryBound` counts
the adversary's queries, the verifier's `13700 = 3 + 13697` are counted in the bound. The BLAKE2s
hypothesis is per adversary, as required.

Forced changes against the stack tip: κ threaded through `proveFrom`, `proveWith`, `prove`,
`honestAdversary`, `_ne_none`, `_eq_none`, `baseProver_complete*` with no conjunct changed
(`Prove.lean:146-167`, `Prove/Complete.lean:586-640`); `baseVerifier_extractsExecution` now reads
through `extractExecution`, which is `extractTrace (leanIsaTraceExtraction hsafe)` under `hsafe`
(`:219`), so the statement is the old one; `fill_wellFormed` is gone (false with the fill-block
field) and the adaptive `_wellFormed` test and the completeness instance use `ladder_wellFormed`,
`ladderJump_wellFormed` on real programs; `badTrace` is a one-step valid execution (`bad_valid`),
so the completeness test's hypotheses are discharged, not assumed. No test passes vacuously.
`admissible_iff_of_satisfiedBy` (`LeanIsa/Complete.lean:173`) is right: the caps give the window,
the row cap and the `BLAKE2S` floor (`caps.blake2s_height`); only the stack cap is extra.

## Pass B: fidelity (read before the Lean)

- DEREF reads: Rust `tables.rs:641-643` flushes `memory_k(FP·O1)`, `memory_coords(P·O2)`,
  `memory(FP·O3)`: pointer, target, local. `Tables/Deref.lean:204-209`, `Rows.lean:derefSends`,
  `Messages.lean:deref_sends_gen` match. The order places the reads' bus blocks; the specification's
  flush list differs, which balance does not see. Match.
- Separators: `tables.rs:89-92` `SEP_STATE = g^0`, `SEP_MEM = g^1`, `SEP_BYTECODE = g^2`; the
  direction is the tree, not a tuple coordinate. `channelSep` gives the same three values. At the
  stack tip `channelSep` already mapped `bc.push` and `bc.pull` both to `gpow 2`, so the
  one-separator `isBytecodeBlock` accepts exactly the blocks the two-separator one did; no check
  dropped, and `leanVmBus_eq_busStep` (the route knowledge soundness takes) is unchanged. Match.
- Known coordinates: Rust `leaf.rs:444-453` evaluates `Coord::Index` by `index_mle` and the eight
  entry columns by `mle_eval_par`, `bytecode_claim` (`:627-637`) over the push blocks; Lean's
  `Coord.known` carries `ext_eq` to the column's MLE, `settleFixedClaims` evaluates the share once,
  equal by `bytecodeShare_eq`. `read_public` (`cpu/mod.rs:157-176`) is `Sizes.Admissible` plus
  `validRate`, `MIN_MU..=MAX_MU` the `leanIsaμ ≤ maxMu` clause. Match.

## Pass C: hygiene

Module docs and docstrings are self-contained and name their sources. Besides findings 1-3 the
docs match the code: the blueprint's hole table lists the new theorems, the status's "on merge"
paragraph is accurate but for the two owed items above, which it should state as the concrete
range (`t.κ ≥ 26`) and the witness-free grind case rather than as "nothing shows".

## Disposition

Applied on 2026-10-29 in `d8327492`; the statements of `Prove.proveFrom_ne_none`,
`proveFrom_eq_none`, `proveWith_ne_none`, `proveWith_eq_none`, `prove_eq_none` and
`prove_complete_of_execution` changed, `prove_ne_none` is new.

| Finding | Disposition |
| --- | --- |
| 1. Witness-free grind disjunct | Fixed (`d8327492`), route (b): the grind case reads `∃ fs, ProveReaches fuel prog input w ρ fs ∧ grind fails at fs`, `Prove.RunReaches` the writer's chain state after the announcement and some first rounds of the compiled protocol's honest prover, from the statement's seed; proved through the generic `Prover.runWith_total_or` (`ToArkLib/RunTrace.lean`), the every-round lemmas generic in the property. The ne-none forms take the grind hypothesis on reached states only. Fix (c), the honest random-oracle grind bound, stays owed in the status. |
| 2. `Trace.Fits` does not pin the stack | Fixed (`d8327492`): `prove_complete_of_execution` gives `∃ s, Sizes.ofWitness w = some s` and, at every fuel and rate, `leanIsaμ prog s ≤ maxMu → validRate ρ → (no grind fails at a reached state) → prove ≠ none` (`prove_ne_none`); the blueprint no longer says `hfit` stands in for admissible heights; the status states the range `t.κ ≥ 26` and what an unconditional form needs (a fit at the level of `Sizes`, the honest grind bound). |
| 3. Hypotheses, stale text | Fixed (`d8327492`): the `_wellFormed` corollaries say they use only `.sentinelSafe`; decision 42 and the completeness sentence of the trace-extraction paragraph updated. |
| 4. Observations | Kept: no defect. |
| Tests | Fixed (`d8327492`): the completeness instance at `ladderJumpProg`/`badTrace` states the new conjunct; `proveWith_ne_none` is restated in the prover tests. No table is evaluated. |
| Dead `Prover.runWith_total` | Fixed (`d8327492`): deleted, subsumed by `runWith_total_or`. |
