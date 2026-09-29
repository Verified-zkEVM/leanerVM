Add lazy random-oracle controls for cache consistency, independent misses, and the exact zero-versus-one-query guessing gap, with free local coins and structural hash-query budgets. Adapted from [leanth PR #16](https://github.com/Verified-zkEVM/leanth/pull/16), revision `23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`; the original source notice is preserved.

Tracks [leanerVM intention](https://github.com/Verified-zkEVM/leanerVM/issues/29).

Local validation at `03cc4a9`: `./scripts/validate.sh --lint --test --axioms`, focused module lint, ordinary-import clients, and a 40-declaration axiom audit pass on Lean 4.34.0.
