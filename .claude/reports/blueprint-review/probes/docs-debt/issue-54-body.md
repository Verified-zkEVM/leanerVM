Tracks #12 and #3 (F6). Hole **K1**: WHIR over binary Reed–Solomon codes in the novel polynomial basis, blueprint Layer 11's protocol half (ledger A7, A8). Generic; shared with the Flock roadmap.

**Produces** (`LeanerVM/Protocol/Generic/Whir.lean`, module; `LeanerVM/Protocol/Pcs.lean`): `novelBasis : Fin 64 → K` (`x^c`), `encode κ R : Column κ → (Fin (2^(κ+R)) → K)` (the additive NTT on the `K` basis, CompPoly's `AdditiveNTT` instantiated), `encode_column_weight` (Lemma B.7), `whirOpen params` as an `OracleReduction` from `Fin J → WeightedClaim μ` over codeword oracles, exactly Protocol B.1 (batch, `ℓ_i` sumcheck rounds, commit, one out-of-domain sample from level 1 on, `t_i` queries, the final plaintext level), `whirError`, `whirOpen_perfectCompleteness`, `whirOpen_rbrSoundness (mca : McaJohnson)` (round-by-round soundness for the list relation, joint by construction: acceptance test 11), and the assumed interface `McaJohnson` ([BCHKS25] Theorem 4.6; ArkLib's `rs_mcaError_le_in_johnson_range` is admitted).

**Consumes:** the spine's `WeightedClaim`, Layer 0, Layer 1; CompPoly `Fields/Binary/AdditiveNTT/*`.

**Tests:** `encode` against CompPoly's additive NTT at `κ = 3`; the honest `whirOpen` at toy parameters (`μ = 4`, rate 1/2) accepted; every pinned coding parameter with an achievability witness (the leanth catalog's lesson: a list-decoding pin can be false at the production rate).

**Upstream watch:** ArkLib #383 (Binary Basefold, ring switching, additive NTT; completeness and rbr knowledge soundness), ArkLib #992 (end-to-end soundness of a computable FRI IOP; a pattern for the soundness statement), ArkLib #4 (Merkle umbrella), ArkLib #907 slices (Reed–Solomon proximity and correlated agreement, landing daily on `main`).

**Claim** by assigning yourself; coordinate with #3.
