# LeanDA security in Lean 4

**Credit: the security framework and its proofs are Benedikt Wagner's**, from [b-wagn/fv-pq-da](https://github.com/b-wagn/fv-pq-da) at `4475179c`, explained in his post [Formally verified security for PQ-DAS (LeanDA)](https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746).

**[LeanDa.lean](LeanDa.lean) proves that LeanDA, the erasure code commitment of [`crates/lean_da`](https://github.com/leanEthereum/leanVM/tree/4af2cdddd7cd41b9df2cc7e123e314a91b0b4462/crates/lean_da) specified in `doc/leanvm` §sec:leanda, is complete, position binding and code binding, for every number of rows, assuming a knowledge-sound argument for its relation; position and code binding in the random-permutation model (`leanDa_positionBinding_rpm`, `leanDa_codeBinding_rpm_bound`, [below](#the-random-permutation-model)).** The proofs of the generic construction are Benedikt Wagner's, ported here as the library `PqDas`; this project instantiates them with LeanDA, proves the building blocks they assume, and moves them to the random-permutation model. His theorems, for any hash function `H` and with the membership challenges a random oracle ([Wagner's theorems](#wagners-theorems-the-step-before-the-random-permutation-model)), are the step of the proof before that model. The root module pins the axioms of every front-page theorem to `propext`, `Classical.choice` and `Quot.sound` with `#guard_msgs`. There is no `sorry` and no `native_decide`.

## The random-permutation model

[LeanDa/RpmSecurity.lean](LeanDa/RpmSecurity.lean) and [LeanDa/RpmScheme.lean](LeanDa/RpmScheme.lean) idealize Keccak-f[1600] as a uniformly random permutation `π` (`lean_rpm`): `H` is Keccak-256, the sponge over `π`, and the challenges are the deployed duplex over `π` (`membershipChallengesM`, which over pure functions is `membershipChallenges`: `membershipChallengesM_id`), its 25 lanes the state's 200 bytes, little endian (`laneBytes`, which is `kBytes`). The adversary queries Keccak-256, `π` and `π⁻¹`; the verifier hashes the opening's climb with Keccak-256 (`verifyCellM`, which over a pure function is `verifyCell`) and calls `π` directly in the challenges' duplex. Every duplexing writes lanes `0 … 15` and keeps lanes `16 … 24`, so it absorbs a block whose byte `135` is that of an earlier answer, a non-final block (`duplexP_membershipChallengesR`): the duplex discipline of the two-oracle transfer `keccak256_transfer2` (`q² / 2^508`). Budgets count permutation calls on every path of the game, verifications included (`permCalls2`: a hash of `n` bytes costs `⌊n / 136⌋ + 1`, a query of `π` or `π⁻¹` and a duplexing one).

| Theorem | Statement |
| --- | --- |
| `leanDa_positionBinding_rpm` | for every argument `ps` (any verifier, any relation) and every adversary of at most `Q` permutation calls, `Pr[position binding] ≤ Q² / 2^256 + Q² / 2^508` |
| `leanDa_codeBinding_rpm` | the code-binding probabilities in the RPM and in the two-oracle ROM (`H` a random oracle, the challenges the duplex over an independent random function `F`, against the simulated adversary `advS2 A`) differ by at most `Q² / 2^508` |
| `leanDa_codeBinding_rpm_bound` | for every argument `ps` (an oracle-free parameter, any relation), extractor `ext` and adversary of at most `Q` permutation calls, `(Pr[code binding] - (Q² / 2^508 + 2 (Q + 15)² / 2^576 + ε_ks + ε₁))² ≤ (Q + 2) (ε₂ + 14 / 2^192 + 2^-2688)`, the three `ε` Wagner's reduction terms averaged over a uniformly random `H` |

The end statements are `leanDa_positionBinding_rpm` and `leanDa_codeBinding_rpm_bound`, with completeness (`leanDa_perfectlyComplete`, no adversary); `leanDa_codeBinding_rpm` is a step of the proof of `leanDa_codeBinding_rpm_bound`.

**How the proofs reach this model.** Through the two-oracle random-oracle model (`H` a random oracle, the challenges' duplex over an independent random function `F`), by `lean_rpm`'s indifferentiability of the sponge with the duplex's direct permutation calls (`LeanRpm.keccak256_transfer2`, `Q² / 2^508`), and from there to Wagner's theorems ([below](#wagners-theorems-the-step-before-the-random-permutation-model)), which are steps of the proof.

Position binding is a concrete bound: after the transfer, a win gives two openings that verify for the hash function of the final random-oracle cache, so the climbs' inputs, all cached, contain a collision (`posBindingPost_win`, by `openingsCollision_spec`), which `Q` hash calls find with probability at most `Q² / 2^256` (`prob_hCollision_le`).

Code binding goes from the two-oracle ROM to Wagner's game in three steps.

* **The challenges are a random oracle of the roots, up to capacity collisions** (the duplex lemma, `LeanRpm.Duplex.duplex_le`, instantiated by `daDuplex` in [LeanDa/RpmDuplex.lean](LeanDa/RpmDuplex.lean)). The challenges' sponge over `F` is a duplex: the label's hash seeds the first state, absorbing the root writes its words over the rate, each sample permutes with the rate zeroed, and every step keeps lanes `16 … 24`, the 576-bit capacity. The adversary's direct calls of `F` are answered by a simulator from `H` and a random oracle `G` of the roots, programming a fresh call on a challenge path with `G`'s challenge and uniform other bytes. Unless two of the at most `Q + 15` states share a capacity (probability at most `2 (Q + 15)² / 2^576`), the challenges the verifier derives are `G`'s ([LeanDa/RpmCodeBinding.lean](LeanDa/RpmCodeBinding.lean), `codeBindingExpRpm_le_G`; the verifier's recomputations of the challenges hit the cache, `prob_codeBindingPost`).
* **`H` is sampled in advance on short strings.** Every string the verifier hashes has at most 2048 bytes (a cell's), so `H` is sampled as a uniform table `h` on those strings and lazily elsewhere. For each `h`, the simulated world is Wagner's code-binding game for LeanDA with the hash `Hh h` against the adversary `advH h` (the simulated adversary, `H` answered from `h` and lazily on long strings, at most `Q` challenge queries) ([LeanDa/RpmWagner.lean](LeanDa/RpmWagner.lean), `cbIdealG_evalDistEq`, `prT_gameW`).
* **Wagner's bound for each `h`, averaged.** `leanDa_codeBinding` holds for each `h`; averaging the squared bound over `h` (Cauchy–Schwarz, `sq_tsub_avg_le`) gives the same bound with each term replaced by its average over a uniformly random `H`.

What stays as in Wagner's model:

* **The collision terms are not birthday bounds.** `ε₁` and `ε₂` are the probabilities that Wagner's two reductions from `advH h` find a collision of `Hh h`, for a random table `h`. Bounding them by a birthday bound needs those reductions as algorithms that query `H`: they hash the extracted codeword's Merkle trees (hundreds of hashes per row, beyond the adversary's `Q`), and `ε₂`'s runs the adversary twice by forking, which would need a forking lemma relative to a further random oracle. Neither is done here.
* **The argument has no oracle.** The argument of knowledge `ps` is modeled oracle-free, for a relation that depends on `H`; in the RPM the relation depends on `π`, and the argument (leanVM's) queries `π` itself.

## Wagner's theorems, the step before the random-permutation model

Benedikt Wagner's theorems for the generic construction, instantiated with LeanDA. They hold for every hash function, with the membership challenges a random oracle from roots to `E^14` (his model), and the random-permutation theorems above are proved from them. For `r` rows, any hash `H` (the crate's is Keccak-256), an argument `ps` for `Relation r H` and its extractor `ext`:

| Theorem | Statement |
| --- | --- |
| `leanDa_perfectlyComplete` | if `ps` is perfectly complete, every honest opening of an honest commitment verifies |
| `leanDa_positionBinding` | `Pr[position binding] ≤ Pr[collision of H]` for the explicit reduction `merkleCollider r H (posBindingReduction ps A)` |
| `leanDa_codeBinding` | `(Pr[code binding] - (ε_ks + ε₁))² ≤ (Q + 2) (ε₂ + 14 / 2^192 + 2^-2688)` for an adversary making at most `Q` random-oracle queries |

In the code-binding bound `ε_ks` is the success of the reduction `ksReduction` against the knowledge soundness of `ps`, and `ε₁`, `ε₂` are the successes of two explicit reductions finding collisions of `H`. `14 / 2^192` is the membership test's soundness and `2^2688 = |E|^14` the number of its challenges.

They rest on what this project proves about LeanDA's building blocks ([LeanDa/Security.lean](LeanDa/Security.lean)):

* `checker_complete`, `checker_sound`: the membership test accepts every codeword for every challenge, and a fixed matrix that is not a codeword for at most a `14 / 2^192` fraction of the challenges `z ∈ E^14`. This is Proposition prop:rs-membership of `doc/leanvm` Annex D: the additive Reed-Solomon code at rate one half is its own dual on the crate's domain (`orthogonal_rsCode`, by Lemma lem:domain-sum and Corollary cor:rs-dual), the dual codeword is the encoding of the tensor `⊗_j (1, z_j)` in the novel basis (`dual_eq_sum`), and the inner product with a row that is not a codeword is a nonzero multilinear polynomial of total degree at most 14 in `z`, so Schwartz-Zippel applies (`card_acceptSet_le`).
* `merkleVC_perfectlyComplete`, `posBindingExp_le_hashCollisionExp`: honest cell openings verify, and two openings of one cell to different values give a collision of the hash, which `merkleCollider` computes. Both hold for every hash function, as do the theorems.

## Assumptions

* **An argument of knowledge** for `Relation r`, the statement that the cells commit to the root and pass the membership test on the challenges: perfect completeness for `leanDa_perfectlyComplete`, and straightline knowledge soundness through `ε_ks`. Wagner's model of the argument makes no oracle queries, and its extractor `ext` runs inside the two collision reductions, so `ε₁` and `ε₂` bound an attack on `H` only for an efficient `ext`. Discharging this assumption with leanVM, the aggregation guest proving the relation, is not done here: leanVM's verifier queries a random oracle, its Fiat-Shamir transcript would need to be domain separated from the challenge oracle below, and its knowledge soundness (`lean_vm`) is stated with an extractor whose running time is not part of the statement.
* **Collision resistance of the hash**, through the explicit reductions. The theorems hold for every hash function `H`, so they are reductions, not bounds; LeanDA's is Keccak-256 (Ethereum's), which `lean_vm` defines and checks against the Rust.
* **The random-permutation model** (the RPM theorems): Keccak-f[1600] behaves as a uniformly random permutation.
* **The random-oracle model for the challenges** (the ROM theorems). The crate derives `z` with a duplex sponge over Keccak-f[1600], seeded with the hash of the label `leanDA/rs-membership/v1`, that observes the root's four words as two scalars and samples `14` times (`membership_challenges`); Wagner's game models this as one random oracle from roots to `E^14`. The RPM theorems derive the challenges by the deployed duplex instead.

## The model and the Rust code

[LeanDa/Scheme.lean](LeanDa/Scheme.lean) is the scheme, citing the crate at leanVM's `main` branch, commit `4af2cdddd`. It is checked by reading both sides; it is not a mechanized refinement of the Rust.

* **The code.** A row's `2^14` payload symbols are the values of a polynomial of degree below `2^14` on the domain points `0 … 2^14 - 1` (the element of `K` whose bits are `b` is point `b`, the span of `e_c = x^c`), and its codeword is that polynomial's values on the `2^15` points. The crate computes these maps with the inverse and forward additive NTT; the model uses the maps themselves, so the NTT's correctness (Annex D, Proposition prop:ntt) is not mechanized here. The dual codeword is `∏_j (1 + z_j Ŵ_j(x))`, which `dual_eq_sum` shows is the encoding of the tensor that `dual_codeword` transforms; `dualCodeword_eq_dual` proves the transcribed `dual_codeword` computes it.
* **The matrix.** The row count `r` is a parameter; the crate accepts `1 ≤ r ≤ 1024` and the theorems hold for every `r ≥ 1`. The erasure code's positions are the `128 r` cells of the `r` rows, the cells sampling opens. The commitment pads the rows to `2^⌈log₂ r⌉` with zero codewords and hashes the padded matrix, as `commit_codewords` does.
* **Openings.** The crate keeps the column tree for answering samples but verifies none. An opening is modelled as the cell's path in the column tree, of the tree's height, with the row root; it verifies when the path climbs to a column root that hashed after the row root gives the commitment.
* **The deployed algorithms.** `Scheme.lean` also transcribes, computably on lists, the crate's commitment (`commitCodewords`, each tree built level by level), the challenges' duplex sponge (`Sponge`, `verifier/src/transcript.rs`, and `membershipChallenges`), the membership vector by the additive NTT (`membershipVector`, `verifier/src/da.rs`) and its digest, the hash of the hashes of its `128` columns of `2^8` entries (`vectorDigest`). The hash `H` and the sponge's permutation `P` are parameters; the crate's are Keccak-256 and Keccak-f[1600]. [LeanDa/Commitment.lean](LeanDa/Commitment.lean) proves the commitment is the model's: for every hash `H` and codewords of `2^15` symbols, `commitCodewords H rows = commitCells H (cellsOfRows rows)` (`commitCodewords_eq_commitCells`). `membershipVector_eq_dual` proves that `membershipVector` computes the model's `dual` at the challenges.

`lean_vm` imports `LeanDa/Scheme.lean` by path and states the aggregation node's DA claim with these definitions, on its own Keccak-256 and Keccak-f[1600] (`lean_vm/LeanVM/Spec/Da.lean`); its node vectors check `commitCodewords` and the membership vector's digest against the crate's. So `Scheme.lean` and `Field.lean` stay Lean modules, building on both projects.

## Build

```sh
cd lean_da
lake exe cache get
lake build
```

## Libraries

| Library | What it is |
| --- | --- |
| [PqDas](PqDas) | Wagner's framework and proofs: erasure codes, vector commitments, code checkers, arguments of knowledge, the scheme, and its completeness, position binding and code binding (the latter through a forking argument). Ported from [b-wagn/fv-pq-da](https://github.com/b-wagn/fv-pq-da/tree/4475179c19296acf3469d7d552a3186ad1feda74) at `4475179c` to the VCVio and Lean pinned here; [NOTICE](NOTICE) says what changed. Apache-2.0, see [LICENSE](LICENSE). |
| [LeanDa](LeanDa) | LeanDA: the fields, the scheme and its deployed algorithms, the self-duality of the code, the membership test's soundness, the Merkle commitment and the deployed one's agreement with it, the instantiation, and the random-permutation model (`RpmScheme`, `RpmSecurity`, and for code binding `RpmDuplex`, `RpmCodeBinding`, `RpmWagner`). |
