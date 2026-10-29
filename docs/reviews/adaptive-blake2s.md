# Review: the adaptive headline at BLAKE2s and the bytecode hypothesis

> An archive of the review of the branch `stack/45-adaptive-blake2s` before its first commit,
> against its base `stack/44-arklib-append-upstream` (`06642a67`). The review was a specification
> review by a fresh agent, read-only, of the new statements: `WellFormedBytecode`, the adaptive
> game, the adaptive section of `Protocol/Headline.lean`, the sentinel counterexample and its
> fixture, the adaptive tests, and the documents. What is accepted from it is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification. Findings are
> numbered by severity.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. the documents claimed the execution form fails without the bytecode hypothesis; what is proved is that constraint soundness does, and that `verify` accepts every proof `prove` returns for a statement with no execution | met: the blueprint (Layer 13, acceptance test 41), the status page, `Headline.lean` and the test docstring now claim necessity for constraint soundness only, and say that the probabilistic form's failure needs an adversary meeting `BlakeMisbehavesAdaptive`, the owed "hypothesis met by an accepted adversary" |
| 2. "every bound here is selective" and "the headline and `misbehaves_rom` are selective" contradicted the adaptive section | met: only the random-oracle forms are said to be selective, in `Headline.lean`, the blueprint's overview and Layer 13 |
| 3. the counterexample, an existential, was worded as true of every program with a sentinel `JUMP` (false: `jumpSentinelProg` keeps `fillProg`'s execution); test 41 said every run halts | met: "some program" in `Headline.lean`, `WellFormedBytecode.lean`, `Sentinel.lean` and the leanISA status; test 41 says every run over a memory holding the public input faults or halts at `(g^31, g^5)` |
| 4. `extractExecution` and `extractTrace (leanIsaTraceExtraction h)` were two public names for one extractor, the adaptive form bypassing the trace interface | met: `extractExecution` is `extractTrace (leanIsaTraceExtraction h)` when the chosen program is sentinel-safe and `none` otherwise; the `rfl` lemma is gone; decision 42 records the amendment of decision 41 |
| 5. `baseVerifier_extractsExecution_wellFormed` lacked the `_adaptive` suffix, and will ask more than soundness once the fill blocks are a field | met: renamed `baseVerifier_extractsExecution_adaptive_wellFormed`; Layer 13 says the `_adaptive` form stays tight |
| 6. `WellFormedBytecode.lean` said the fill blocks "are a further field" | met: "will be a later field" |
| 7. "the BLAKE2s forms lose nothing to adaptivity" could be read as adaptive security at no cost | met: Layer 13 says the adaptive BLAKE2s theorems are the selective proof at the chosen statement and that adaptivity's cost sits in the hypothesis, which the random-oracle bound does not yet support |
| 8. hygiene: `mem_support_runBlake2s_of_adaptive` public and unlisted; a vague sentence in `AdaptiveGame.lean` | met: private; the sentence names `Core.core_of_mem_support` |
| the observations | the `SentinelSafe` docstring in `Semantics/Execution.lean` still points to the roadmap's structure, which is accurate and left as is (an edit would rebuild every layer); docstring lengths match their selective neighbours; the `#guard` on `traceOf` runs on the light witness, as its comment says |

Files read in full by the reviewer: the new and changed Lean files above,
`Protocol/RandomOracleGame.lean`, `Protocol/Replay.lean`, `Protocol/Core.lean`,
`Arithmetization/Soundness.lean`, `Semantics/Execution.lean`, and the changed blueprint, status
and bench sections. The reviewer ran no Lean; after the fixes, `./scripts/validate.sh` passes and
`#print axioms` of every new result gives `propext`, `Classical.choice` and `Quot.sound`.
