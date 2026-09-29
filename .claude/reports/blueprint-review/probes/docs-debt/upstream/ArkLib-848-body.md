## Summary

This PR formalizes the security layer needed for the duplex-sponge Fiat--Shamir transformation and proves the paper's Theorems 6.1 and 6.2.

- Define adaptive, query-bounded NARG soundness and straightline knowledge soundness, including the corresponding state-restoration notions and coin-bearing experiments.
- Prove the canonical single-salt Fiat--Shamir soundness and straightline knowledge-soundness results (Theorems 3.18 and 3.19).
- Prove DSFS soundness (Theorem 6.1).
- Define the DSFS straightline extractor (Construction 6.3) and prove DSFS straightline knowledge soundness (Theorem 6.2).
- Document the definitions, reductions, and explicit Section 5/Section 6 proof boundary in the blueprint.

## Authors

- Chung Thai Nguyen
- Michele Orrù
- Yuxi Zheng

## Proof boundary

The Section 6 reductions take an explicit `KeyLemmaSecurityWitness`, which packages the Section 5 endpoint statistical-distance and query-bound guarantees. Consequently, the Section 6 theorem bodies and the canonical Fiat--Shamir security proofs are complete; proving that the concrete Section 5 transforms produce this witness remains the separate Key Lemma obligation.

## Stacked PR

This PR is intentionally based on `dsfs-section5` while #469 is open. Once #469 merges, this PR will be retargeted to `main` automatically due to Github Stack; its content is limited to the security definitions and Section 6 results built on that foundation.

## Verification

- Ran `lake build` successfully.
- Checked every new blueprint `\lean{...}` declaration against Lean.
- Built the printable blueprint with LuaLaTeX and resolved the CO25 citation.
