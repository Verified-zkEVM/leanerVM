Add sampled Boolean countermodels separating component soundness from relation refinement, with a fixed extractor and perfect binding. These operational controls address the two missing-premise arguments in [leanth PR #16](https://github.com/Verified-zkEVM/leanth/pull/16), revision `23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`; a positive shared-oracle product adapter remains separate work.

Tracks [leanerVM intention](https://github.com/Verified-zkEVM/leanerVM/issues/30).

Local validation at `3d14fdb`: `./scripts/validate.sh --lint --test --axioms`, focused module lint, ordinary-import clients, and a 10-declaration axiom audit pass on Lean 4.34.0.
