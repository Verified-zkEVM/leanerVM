## Status and integration base

**Draft: forward-ported to current `main` on Lean 4.34.0.**

The original proof was developed on `14a4b351d` (Lean 4.32.2). This forward-port incorporates all **131 intervening commits** through `0b5b67c63` (Lean **4.34.0**), including the exact dependency pins from `main`. Production files use the module system, probability statements use native measure semantics, and obsolete compatibility files are removed. Forward-port history and validation records live here; the KB audit contains the present-tense paper-to-code correspondence.

### Upstream work reviewed during the forward-port

- #897, #903, #913, #967: modules, Lean 4.34, native measure probabilities, and VCVio repin. Reuse native event, uniform-sampling, and `OptionT` lemmas; remove obsolete compatibility files.
- #766, #865, #906: consolidated module-code MCA and same-set agreement witnesses. Reuse `ProximityGenerator/Basic` and the existing interleaved relative-distance lemma.
- #841, #918, #932: interleaved RS list decodability, interleaving MCA, and exact agreement transfer; useful for future batched FRI.
- #902: the MDS MCA bound is proved in its unique-decoding range, with full-dimension and size hypotheses. Its all-radii theorem still has an admitted branch, so it does not replace the certified powers-MCA bound.
- #825, #845: folding contexts and list-decoding preservation; #909, #910: Johnson counting and finite list bounds.
- #937, #938, #945: tensor-fold probability and anchored agreement/reconstruction, relevant to related protocols.
- #907: Hasse–Taylor, differential-polynomial, hidden-derivative rank, affine Hilbert/Bezout, and weighted-simplex infrastructure; possible future MCA/list-decoding ingredients, not premises of this proof.
- #885, #887: state-aware sequential composition. The general round-by-round-to-ordinary implication remains unfinished; this proof uses direct adaptive accumulation.
- #851, #880, #884, #886, #889, #891: typed interactions and ordered execution/state/outcomes. A future framework migration, not a change to the computable FRI specification proved here.

### Review follow-up

- Generalize probability-to-binding to separate `θ` and `δ`, with `δ ≤ θ` and the rate constraint on `δ`.
- State explicit proximity, unique agreement, arbitrary-subset interpolation, and erasure detection together; retain the distinction between algebraic extraction and a runtime bound.
- Rename the folding-to-MCA lemma conclusion-first, correct relation docstrings, and index the paper and audit.
- Move branch-specific history and validation logs from the persistent audit to this PR description.

## Summary

Prove end-to-end ordinary and round-by-round soundness of the **actual computable FRI IOP specification** in `Fri.Spec.reduction`, against arbitrary adaptive provers:

- `Fri.Spec.soundness` uses the specification's input/output relations.
- `Fri.Spec.rbrSoundness` supplies the existing round-by-round security interface.
- `Fri.Spec.soundness_proximity` gives the stronger bound on *any acceptance* for input words at relative distance at least `δ`, including equality at the boundary.
- `Fri.Spec.reduction_run` proves the exact correspondence between the composed executable verifier and the bounded acceptance event, including oracle history, the final polynomial's degree guard, and executable query checks.

The total error is the sum of ArkLib's existing powers-generator MCA errors plus `Real.toNNReal (1 - min θ δ) ^ l`. The tradeoff parameter `θ` is independent of the input radius `δ`. The adaptive bound is on the actual `Prover.run`, not only on a fixed safe algebraic trace.

## Proof organization and specification review

- Reuse ArkLib's Reed–Solomon codes, distances, folding, MCA definitions, and numerical powers-MCA bounds; do not import parallel foundations from the reference development.
- Connect block interpolation and local executable checks to word folding; prove agreement lifting, safe-trace query bounds, and binding/interpolation/erasure consequences.
- Add reusable persistent bad-event state functions, adaptive accumulation along `Prover.runToRound`, and the transcript-acceptance-to-soundness bridge. The general round-by-round-to-ordinary soundness implication remains unfinished on the updated base; the FRI proof does not depend on it.
- Fix honest-prover oracle-history retention: round `i` must preserve `i + 1` old words, including the input at round zero.
- Replace four placeholder stage relations with proximity relations and remove the resulting eight entries from the axiom-debt baseline.
- Correct the auxiliary batched-FRI simulator's folding factor from exponent `s` to `2 ^ s`; this does **not** certify the older batched-FRI security claims.
- Add a blueprint section, paper provenance, and `docs/kb/audits/fri-soundness.md` with a declaration-level proof map and scope audit.

## Sources and credit

Follow the **March 27, 2026 revision** of Garreta–Mohnblatt–Wagner, [A Simplified Round-by-round Soundness Proof of FRI](https://eprint.iacr.org/2025/1993).

The earlier [zksecurity/simple-rbr-fri](https://github.com/zksecurity/simple-rbr-fri) development (consulted at `5d99bc7bcabc7b640e063f4d75f17d8262e00a8a`) informed the strategy. Credit to **Yoichi Hirai, Pietro Monticone, and Harmonic's Aristotle**. The executable-protocol and adaptive-execution bridges here are proved in ArkLib rather than assumed from the reference model.

## Forward-port validation at `b31adeff6` (Lean 4.34.0)

- `lake build ArkLibTest.ProofSystem.Fri.Soundness` passes (3,817 jobs).
- Guarded kernel checks cover the end-to-end theorems, exact executable-verifier bridge, numerical MCA specialization, and adaptive accumulation/acceptance lemmas. They report only `propext`, `Classical.choice`, and `Quot.sound`: **no `sorryAx` or nonstandard axioms**.
- Documentation integrity and knowledge-base lint pass.
- The 63-page blueprint PDF and bibliography build with XeLaTeX/BibTeX. A full API-docs/site build is not certified.
- `ArkLibBlueprint` builds, and `checkdecls` passes for the existing declaration list and all new FRI references.
- Full `scripts/validate.sh --axioms` passes: 4,731-job library build, all acceptance clients and warning gates, source-policy and retirement fixtures, compiled toy-problem/Hachi runtime checks, imports, build-timing fixtures, documentation, and axiom regression checks.
- The axiom sweep covers 14,285 declarations across 638 modules: **zero nonstandard-axiom taint and no new admission debt**. The remaining 283 admission-tainted declarations are pre-existing work elsewhere; the new FRI theorems are admission-free. Retired probability API usage is zero.

Unrelated local edits and untracked work are excluded from this PR.

## Review-fix validation

- `lake build ArkLibTest.ProofSystem.Fri.Soundness` and full `./scripts/validate.sh --axioms` pass, including warning/style gates, runtime checks, and documentation/KB lint.
- Kernel checks cover the new separate-parameter corollary, generalized binding, and arbitrary-subset interpolation as well as the computable IOP soundness theorems. All use only `propext`, `Classical.choice`, and `Quot.sound`.
- Acceptance examples exercise `δ < θ` where the former rate constraint on `θ` fails, and the non-strict boundary `δ = 1 - ρ`, without assuming final-code membership separately.
- The revised blueprint PDF/bibliography builds, and blueprint declaration checks pass for the existing list and the new FRI references. Full API-docs/site generation is not certified locally.
- The full axiom gate reports no new admission debt and no nonstandard axioms. Paper SHA-256 matches the committed March 27, 2026 source metadata.

## Scope and follow-up

This proves information-theoretic ordinary and round-by-round soundness of the interactive oracle reduction, for the existing powers-of-two folding domains. It does **not** claim Fiat–Shamir security, concrete commitment security, end-to-end knowledge soundness, or efficient extraction.

Before marking ready:

- [x] Forward-port to current `main` and reconcile module/probability/security API changes.
- [x] Re-check newly landed reusable material so the forward-port does not retain duplicate helpers.
- [ ] Reconcile overlap with the existing FRI relation work in #476; this PR does not close that PR automatically.
- [x] Repeat the complete build, axiom, lint, and documentation checks on the integrated tree (full API-docs/site build not certified locally).

## Co-author

[Yoichi Hirai (@pirapira)](https://github.com/pirapira), for the source FRI soundness formalization.

Co-authored-by: Yoichi Hirai <yoichi@flamingoponderado.com>

