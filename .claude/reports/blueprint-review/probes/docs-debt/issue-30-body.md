Add two VCVio operational countermodels supporting Layer 10's composition obligations in [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12). This claims no positive shared-execution product adapter.

Targets in `VCVioTest.ProductRelationControls`: `digest`, `extract`, `digest_injective`, `extract_digest`, `sameBit`, `missing_refinement_control`, `Target`, `relation_refinement`, `invalidFirst`, `missing_component_soundness_control`.

Use current VCVio `bd227bb4` native sampled computations. The fixed identity extractor reads a perfectly binding digest. Each example drops exactly one of component soundness and refinement into the target relation. Motivated by the controls in leanth `23929f8c`, `Leanth/LeanVM/Aggregation.lean`; these VCVio models are newly written. No #18 or batching dependency.

Acceptance: nonempty target relations, actual sampled executions, exact event probabilities, one fixed extractor and injective binding; VCVio full lint/test/axiom validation and explicit checks of the new test module. The future positive adapter must separately preserve actual joint executions.

Landed through [VCVio #784](https://github.com/Verified-zkEVM/VCVio/pull/784), merge commit `c8b3a2b84a65bb02ca17bdc833a81747f6ed0ca6`, which supersedes #768. Both countermodel statements, the fixed extractor and perfect binding are retained. The positive shared-oracle product-extraction theorem remains separate, unfinished work.
