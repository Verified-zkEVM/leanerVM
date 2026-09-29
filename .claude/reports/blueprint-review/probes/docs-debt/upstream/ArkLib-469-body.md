## Summary

This PR formalizes the Section 5 definitions of the duplex-sponge Fiat-Shamir transformation. It expands the current  specifications. It provides the executable constructions, trace machinery, bad-event infrastructure, and hybrid experiment definitions needed by the later security proofs.

- Define reusable oracle-distribution sampling and the single-salt Fiat--Shamir construction.
- Formalize the Section 5 protocol, codec, and nondegeneracy interfaces.
- Define the trace data structures and implement lookahead, backtracking, and candidate extraction.
- Implement the prover and trace transformations used by the duplex-sponge-to-single-salt reduction.
- Define the Section 5 bad events and prove the structural exclusion results corresponding to Lemmas 5.10, 5.12, 5.14, and 5.16.
- Define the endpoint experiments and hybrid chain `Hyb_0` through `Hyb_4`.
- Add `θStar`, `ηStar`, the per-transition bound expressions, and the required query-bound interfaces.
- Expose the new modules through ArkLib and update the axiom baseline and repository map.

## Authors

- Chung Thai Nguyen
- Michele Orrù
- Yuxi Zheng

## Proof boundary

This PR intentionally provides the Section 5 definitions and supporting infrastructure without proving the probabilistic hybrid claims, Lemma 5.8, or Lemma 5.1. Abort Analysis lemmas, Claims 5.21–5.24 and the final Key Lemma proof remain deferred to a later proof-focused PR.

The single-salt Fiat--Shamir completeness theorem is stated here, while its proof is also left outside the scope of this PR.

## Follow-up PR

#848 is stacked directly on this PR. It adds the NARG and state-restoration security definitions, proves canonical Fiat--Shamir soundness and straightline knowledge soundness, and derives the DSFS results corresponding to Theorems 6.1 and 6.2.

## Verification

- Ran `./scripts/validate.sh --axioms --docs` successfully using Python 3.12.
- Built the library and API documentation successfully.
- Verified that the refactored commit sequence preserves the final implementation and authorship attribution.