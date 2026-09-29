## Current scope (2026-09-26)

This remains an open **legacy `OracleReduction`** issue. The original report below is historical; its line numbers, missing-definition inventory, and measured downstream impact are not a current census.

- Legacy append and basic cast definitions now have implementations. Scoped pure/guarded completeness results also exist; #802 is closed.
- Generic legacy append soundness, knowledge soundness, and round-by-round security still contain admissions in `Composition/Sequential/Append/Security.lean`; derived wrappers inherit them.
- `LiftContext/Reduction.lean` and `Security/Implications.lean` still have proof gaps. The interface concern in the existing comment remains part of the legacy work; this refresh does not resolve it.
- Native Sumcheck (#1214), shared strategy execution (#1216), and native composition (#1218) are separate proved results. They do not repair the axiom dependencies of legacy protocol clients.

Use #1 for the current interaction framework and #1222–#1229 for the next composition work. Keep this issue open until its remaining legacy claims are proved with correct assumptions or its consumers migrate with verified correspondence. Do not assume an unrestricted stateful composition statement is provable merely because its components are secure from the same fresh initialization.

## Historical report

## Summary

`ArkLib/OracleReduction/Composition/Sequential/Append.lean`,
`ArkLib/OracleReduction/LiftContext/`, `ArkLib/OracleReduction/Cast.lean` and
`ArkLib/OracleReduction/Security/Implications.lean` are stubbed to the point where **every protocol
that composes rounds ends up with `sorryAx` in its top-level security theorems**, no matter how
complete the protocol's own proofs are.

This is currently the highest-leverage gap in the library: it is not one protocol's problem, it is
the shared substrate every protocol lands on.

## Two classes of stub, and the distinction matters

### (a) Sorry-*defined* objects — the severe class

Here the theorem's *subject* does not exist, so a downstream statement is not a weaker claim but a
vacuous one, and no amount of docstring disclosure can make it honest.

| object | location | extent |
| --- | --- | --- |
| `OracleVerifier.append` | `Composition/Sequential/Append.lean:148,158` | `verify` field is `sorry` |
| `OracleVerifier.liftContext` | `LiftContext/OracleReduction.lean:53,57,58` | **all three** fields (`verify`, `embed`, `hEq`) |
| `OracleVerifier.cast` | `Cast.lean:128` | `verify` field is `sorry` |

### (b) Sorry-*proved* theorems

| theorem | location |
| --- | --- |
| `OracleVerifier.append_toVerifier` | `Append.lean:191` |
| `Verifier.append_rbrKnowledgeSoundness` | `Append.lean:506` (body `:515`) |
| `Reduction.append_completeness` | `Append.lean:439` |
| `OracleReduction.append_completeness` | `Append.lean:473` |
| `OracleReduction.append_perfectCompleteness` | `Append.lean:486` |
| `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` | `Security/Implications.lean:102` |

Supporting machinery also stubbed and on the same paths: `Extractor.RoundByRound.append`
(`Append.lean:255–260`), `Verifier.StateFunction.append.toFun_next/toFun_full` (`:299–300`),
`ProtocolSpec.Transcript.fst/snd` (`SeqCompose.lean:122,125,133`),
`seqComposeChallengeEquiv.left_inv` (`:500`), `LiftContext/Reduction.lean` (10 sorries).

## Measured impact

**PR #383 (FRI-Binius).** A census over its 37 modules (`Lean.collectAxioms` on every non-internal
constant) gives **2,013 axiom-clean / 89 `sorryAx`-tainted**, with **no `sorryAx` originating in the
PR**. All 89 trace to the stubs above, and all twelve of its advertised top-level theorems are
tainted. Its per-step mathematics — the DP24 soundness core, all four step reductions, the query
phase — is clean.

**PR #503 (LogUp).** Independently the same shape: `LogUp/**` sorry-free, but
`#print axioms logup_{soundness,completeness}` returns `sorryAx` inherited from `append_*`, the
`Implications.lean` implications, and `liftContext_*`.

Two unrelated protocol formalizations blocked at the identical point is the argument for treating
this as substrate work rather than as something each protocol PR works around.

## A possible reason `append_rbrKnowledgeSoundness` has stayed a stub

Offered as a hypothesis, not a finding.

`Verifier.rbrKnowledgeSoundness` is the **averaged** notion: the transcript prefix is prover-sampled
and the probability ranges over prefix and challenge together. PR #668 adds
`rbrKnowledgeSoundnessWorstCase` — worst-case-per-prefix, which its docstring calls "the standard
literature shape" — and proves worst-case ⟹ averaged, noting the converse fails.

Composition is exactly where that gap would bite: appending makes the second protocol's prefix
distribution depend on the first protocol's execution. A worst-case-per-prefix bound survives that
reindexing uniformly; an averaged bound is tied to the distribution it was proved against.

If that is right, #668 may already carry the missing ingredients — both the worst-case notion and
the mixture master bounds in `Security/RbrGame.lean`
(`probEvent_simulateQ_addLift_getChallenge_bind_le` and its `Option`-valued and prefix-extended
variants). Worth trying `append_rbrKnowledgeSoundness` against the worst-case notion before
attacking it against the averaged one.

Note #668 also removes all three `Security/RoundByRound.lean` sorries, but neither it nor #505
touches `Append.lean`, `Implications.lean`, `LiftContext/` or `Cast.lean`.

## The question to settle first

**Does #433 replace this layer wholesale?** PR #383's author explicitly paused waiting for #433 and
then resumed without it. If #433 supersedes `Append.lean`, filling these stubs is wasted effort and
the right move is to prioritise #433 and have protocol PRs land with disclosed taint in the interim.
If #433 does not cover the composition operators, this layer needs owning independently.

That decision is worth making explicitly, because right now protocol PRs are accumulating against a
substrate nobody has claimed.

## Suggested ordering if we do own it

1. `OracleVerifier.append`'s `verify` — everything else in (a) and (b) for the append path is
   downstream of the object existing.
2. `Verifier.append_rbrKnowledgeSoundness`, attempted against #668's worst-case notion first.
3. `OracleReduction.append_{completeness,perfectCompleteness}`.
4. `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` — independent of the append path, and
   on its own it unblocks the scalar-KS statements that protocol PRs most want to cite.
5. `OracleVerifier.liftContext` and `OracleVerifier.cast`.

## Interim convention worth adopting regardless

Make a `#print axioms` disclosure standing practice for advertised top-level security theorems, so
"the files are sorry-free" is never mistaken for "the results are proved". Both #383 and #503 would
have been accurately described from the outset under such a convention.
