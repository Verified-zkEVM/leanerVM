Add VCVio regression controls supporting Layer 12's oracle/query-accounting boundary in [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12). This claims no Fiat-Shamir, BCS or signature-security theorem.

Targets in `VCVioTest.RandomOracleControls`: `HashSpec`, `MainSpec`, `IsHashQuery`, `runROM`, `IsHashQueryBound`, `QueryGapAdversary`, `oneQuery`, `oneQuery_not_zero`, `localCoin_zero_bound`, `localCoin_uniform`, `repeatHash`, `repeatHash_consistent`, `twoHashes`, `twoHashes_independent`, `repeatHashWithCoin`, `repeatHashWithCoin_consistent`, `finishGuess`, `zeroHashQuery_guess_probability`, `queryGap_zero_exact`, `queryGap_one_exact`, `queryGap_one_strictly_better`.

Use current VCVio `bd227bb4` cache, forwarding and predicate-query-bound APIs with native measures. Source: leanth `23929f8c`, `Leanth/XMSS/RandomOracle.lean:266-476`, preserving its notice. There is no #18 dependency.

Acceptance: all structurally zero-query adversaries, arbitrary free local randomness, exact half-versus-one success, checker queries outside the adversary budget, same-address cache consistency and distinct misses. Require VCVio full lint/test/axiom validation plus explicit checks of the test module. Existing SLH-DSA work #766 is a protocol consumer, not this general Boolean control.

Landed through [VCVio #784](https://github.com/Verified-zkEVM/VCVio/pull/784), merge commit `c8b3a2b84a65bb02ca17bdc833a81747f6ed0ca6`, which supersedes #767. The cache and exact zero-versus-one-query controls are retained; `IsHashQuery` is now the `(· matches .inr _)` predicate. This remains supporting control coverage, with no Fiat–Shamir, BCS or signature-security theorem.
