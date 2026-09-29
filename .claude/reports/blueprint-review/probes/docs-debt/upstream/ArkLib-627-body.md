Per CONTRIBUTING's blueprint-first process: a concrete design for filling the `BCSTransform` stub in `ArkLib/OracleReduction/BCS/Basic.lean`, for maintainer feedback before implementation PRs. We intend to build this in full and have validated the load-bearing elaboration against current `main`.

## The observation the design rests on

`OracleVerifier.verify` already runs in `OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))`, and the honest adapter `toVerifier` (Basic.lean) is `simulateQ (simOracle2 oSpec oStmt transcript.messages) (verify ...)` — the verifier's access to the prover's oracle messages is *already* mediated by a `QueryImpl`. So the BCS compilation is not protocol surgery; it is a **change of oracle implementation**:

> the compiled verifier is `toVerifier` with the message-side `simOracle0` (answer-from-data) replaced by an *opening-backed* `QueryImpl [pSpec.Message]ₒ (OracleComp oSpec)` that runs the commitment scheme's opening procedure and refuses (`OptionT` failure) on rejection.

(The in-source TODO under `OracleVerifier` gestures at exactly this.) We have elaborated the skeleton — `openingOracle`, `simOracleBCS` (= `simOracle2` with the message component opening-backed and the `[OStmtIn]ₒ` side pure-lifted), and `toVerifierViaOpenings` — against current main; it type-checks cleanly, including `simulateQ` through the `OptionT` verify computation.

## Staged plan (one reviewable PR each)

1. **Transform, type level + constructions**: `pSpec.bcsCompile` via the existing `renameMessage`; committing prover threading `(data, decommitment)` state; `toVerifierViaOpenings`. **Stage-1 restriction: direct (0-round or single-message) openings** — `Proof` over `!p[]` / the `NonInteractive` shape — which is what Merkle vector openings are. Interactive openings are stage 2, composed via the existing `append_completeness/soundness` and `seqCompose_*` lemmas.
2. **Completeness**: with perfectly correct schemes, the compiled reduction inherits the IOR's completeness. Proof spine: a pointwise `simulateQ`-congruence between the opening-backed and data-backed implementations, anchored by one named lemma (`openingImpl_answer_eq`: openings on honest commitments answer exactly `(Oₘ i).answer data q`). We may first land the deterministic transcript-level equality and lift it, naming each honestly.
3. **Binding bridge**: `binding_implies_committed_transcript_sound` — two accepting opening responses for the same commitment+query that differ construct a `BindingAdversary` win. Full ROM/state-restoration soundness inheritance is deliberately **out of scope** and will be fenced as a named open statement referencing `Security/StateRestoration.lean` — we would rather ship a proven core with an honest fence than a hollow endgame.
4. **Instantiation**: Merkle vector commitments from the inductive Merkle tree development (Verified-zkEVM/VCV-io#473 batch openings + #474 tweaked paths), recovering the classic BCS'16 shape for vector-query IOPs.
5. If useful along the way: the fallback completeness route through the existing `NonAdaptive` oracle-verifier class, and small reusable `simulateQ` congruence lemmas upstreamed to VCV-io.

## Questions for maintainers

1. Is the change-of-oracle-implementation framing acceptable as *the* definition of the transform, with the appended-opening-rounds presentation derived for the interactive-opening stage — or do you want the appended-rounds shape as primary?
2. Placement: extend `BCS/Basic.lean` in place (replacing the commented stub) vs. new sibling files per stage?
3. Any objection to the stage-1 direct-opening restriction being visible in the definition's hypotheses (an `IsDirectOpening` class on the scheme's opening `ProtocolSpec`)?
4. `numQueries` is currently `sorry` — we plan not to depend on it; flag if that's wrong.

We'll iterate here before opening PR 1.

*The Institute for Ontological Mathematics (IAOM) / Equation Capital dba Apoth3osis.*