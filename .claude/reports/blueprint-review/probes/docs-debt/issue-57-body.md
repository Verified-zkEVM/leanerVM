Tracks #12. Hole **K4**: T4, blueprint Layer 13. Needs K3, I2, leanISA Layer 10.

**Produces** (`LeanerVM/Protocol/Soundness.lean`, plain): `baseVerifier_extractsExecution (fs bcs mca flock) (h : verify prog input proof = true) : except with probability niError, ∃ t, ValidExecution prog input t`, composed as `verify_knowledgeSound` ∘ `knowledgeSound_of_refinement` with `satisfiedBy_witnessOf` ∘ `constraintSoundness`; `baseProver_complete (hfill : HasFillBlocks prog) (h : ValidExecution prog input t) : verify prog input (prove prog input (witness of t)) = true`, composed as `constraintCompleteness` ∘ `m3Holds_stackOf` ∘ `piop_perfectCompleteness` ∘ the determinism of the Fiat–Shamir chain. Both are the T4 statements of `docs/architecture.md`, the first conditional exactly on the three ArkLib interfaces and the Flock phase.

**Consumes:** K3, I2, the spine's transport lemma, leanISA Layer 10 (`constraintSoundness`, `constraintCompleteness`, `HasFillBlocks`).

**Tests:** the differential fixture of K3 restated as an instance of `baseVerifier_extractsExecution`'s hypothesis; `piopError_le` at the caps by `norm_num` (acceptance test 23).

**Claim** by assigning yourself.
