Interpret Clean expressions as polynomials, with evaluation agreement and syntactic degree bounds. The finite-width interpretation requires in-range variables and agrees with `Environment.fromArray`.

Supports [leanerVM Layer 2, intention #28](https://github.com/Verified-zkEVM/leanerVM/issues/28). New bridge code motivated by [leanth PR #16 at 23929f8c](https://github.com/Verified-zkEVM/leanth/pull/16/commits/23929f8c922cd4461ab22dbfaa6520f3ad23a3b2).

Local validation at `2a2f873`: spacing check, `lake build --wfail`, `lake build CleanTests`, all four Rust CI commands and module/test axiom audits pass. Controls cover degree two, index bounds and width zero.
