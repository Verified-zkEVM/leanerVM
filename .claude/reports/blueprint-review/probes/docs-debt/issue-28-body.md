Tracks #12, Layer 2/C1; implementation [Clean #466](https://github.com/Verified-zkEVM/clean/pull/466).

Targets in Clean's `Expression` namespace: `degreeBound`, `WithinWidth`, `instDecidableWithinWidth`, `toMvPolynomial`, `eval_toMvPolynomial`, `totalDegree_toMvPolynomial_le`, `toBoundedPolynomial`, `totalDegree_toBoundedPolynomial_le`, `eval_toBoundedPolynomial`.

Consumer: the expression-algebra part of `Component.toM3`. This does not claim `Component.toM3`, lookup/flush interpretation or global table balance. It depends on Clean's expression and array environment APIs, independently of #18.

Category A bridge, motivated by [leanth PR #16 at 23929f8c](https://github.com/Verified-zkEVM/leanth/pull/16/commits/23929f8c922cd4461ab22dbfaa6520f3ad23a3b2); it preserves the actual `Environment.fromArray` behavior and requires in-range variables for the bounded interpretation.

Acceptance: Clean's spacing check, warning-strict build, `CleanTests` with snarkjs/wabt, all four Rust CI commands, and new-declaration/test axiom checks. Controls cover degree two, array evaluation, out-of-range indices and width zero. Remote CI currently requires maintainer approval; it has not passed.
