Prove the perfect completeness of GKR. Inherits sorryies from Reduction.append_completeness, Reduction.liftContext_completeness and Prover.append_run (see #802  ) .

We follow Thaler's line reduction for two claim merging step, instead of the original GKR's paper two claim handling.

Soundness is not proven.

ArkLib/ProofSystem/GKR/SumcheckAux.lean proves that sum-check preserves its oracle statement across rounds. Nothing in it is GKR-specific — it belongs in Sumcheck/Spec/ and lives here only to keep the development self-contained.