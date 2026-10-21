# The leanXMSS proof

Target: `LeanXmssSecurityStatement` (`LeanXmss/Statement.lean`), 127 bits of classical SUF-CMA security in the random-oracle model for the scheme of `LeanXmss/Scheme.lean` (`crates/signatures/src/lean_xmss`, `doc/lean_xmss`): for every `q ≥ 1` and every adversary whose experiment makes at most `q` hash calls (key generation, signing, the adversary's queries and the final verification, cache hits included), the forgery probability is at most `q / 2^127`. The adversary picks a leaf index per signing request and may not reuse one.

The proof combines three earlier ones: the byte layout, seed model, honest graph and scan tooling of `formal/lean_sphincs` (B), the layered descent and one-time witnesses of the 3-layer leanSPHINCS proof at `0cd0539ae` (C), and the stateful game and two-lane accounting of the single-layer XMSS proof `formal/xmss` at `35fae6781` (A).

## Units

A *unit* is `2^-128`. The bound is two units per hash call the adversary or the final verification makes, which is `q / 2^127` once the key-generation calls, charged to `q` but never bad, pay for the two seeds and the lower-order terms.

## Route

0. **Tagged seed.** The secret key is a 32-byte seed `S_0`, and key generation first computes `S = H("leanXMSS" || S_0)`, a 40-byte input that no other hash input matches. Its answer is uniform, so `S` is a uniform seed; the cached entry names `S_0`, and dropping it costs at most `2^-256` per later hash call, a guess of `S_0` (`XmssSecurity/Proof/Bridge/SchemeSeed`).

1. **Seed elimination.** Every derivation input contains the seed `S` at bytes 32 to 63: the parameter, the chain starts (two per hash, its halves) and the randomizer bases `R0(l, e, M)`. Their answers are sampled first and programmed; the adversary learns one only by querying an input that contains `S`, `2^-256` per query. Afterwards `P`, every chain start and every `R0` are independent and uniform (B: `Sphincs/SecuritySeedModel`, `Sphincs/SecuritySeedCoupling`, `Sphincs/SecuritySeedGuess`, `Sphincs/BridgeDet`; here `XmssSecurity/Proof/Seeded/*` and `XmssSecurity/Proof/Bridge/Seed`).

2. **Honest graph.** Every honest hash input has a *position*: `(chain, l, e, μ, i)`, `(leaf, l, e)`, `(node, l, λ, j)` and `(msg, l, e)`. An address and, for a chain step, the chain index in the payload's last 16 bytes determine the position (`LeanXmss/Bytes.lean`: `hashDomainFields_injective`, `tweakableInput_injective`; `XmssSecurity/Proof/HashAddress.lean`: `atHashAddress_unique`). A position has one honest input and one honest output; a chain step's input is hidden until the signer reveals a position at or below it.

3. **Bad events**, for a hash call `x` of the adversary or of the final verification, at position `π`:
   - **hit**: `x` differs from the honest input of `π` and its output is the honest output of `π` (node, leaf, chain step);
   - **guess**: `x` is the honest input of a chain step whose value is still hidden;
   - **digest collision**: `π = (msg, l, e)`, `x` differs from the signed digest input of key `(l, e)` and its output is the signed digest.

4. **Classification.** A win implies a bad event (C's descent, two layers). The verifier's top fold reaches the root: a node or leaf of the top layer with a non-honest input but the honest output is a hit. Otherwise the top chain ends are honest and the top codeword `x*` is compared with the signed one `x` of key `b`: if `x* ≠ x` some digit is lower (codewords are incomparable: equal digit sums), so a chain step with an honest output and a non-honest input is a hit, or the revealed value at that position is a hidden one, a guess; an unsigned key has every value hidden. If `x* = x`, the digests are equal (a codeword determines all 128 bits), so the digest inputs differ, a digest collision, or are equal, which makes the bottom root honest. The bottom layer is the same with the adversary's message; equal digest inputs there make the forgery the signer's answer (SUF), so the signature differs in a chain value or a path node, a hit or a guess.

5. **Probability.**
   - A hit or a guess at a query whose output or input target is uniform and independent of the adversary's view costs at most one unit each: two units per chain, leaf or node call (lane 1: guesses; lane 2: hits).
   - **Digest calls.** The signed digest of key `(l, e)` is the output of the first trial `R0 + c` that is a codeword, `R0` uniform and hidden. A call after signing is a hit at the signed digest, one unit. A call before signing pays its pending risk, one unit, as in A: the monitor charges a fresh trial that lands on a pending codeword output, skips a cached trial (it samples nothing) and installs a selected cached input's output as the signed digest with no hit. A later call that lands on that digest is then an ordinary hit.
   - **Partner (lane 2).** What the monitor leaves out is a selected cached input `y` whose output an earlier call `z ≠ y` at the same key also produced. For one key and a cache state, `W(y) = Σ_r reach(r → y)` is the mass of starts the scan walk carries to `y` (B's `Sphincs/LoopWalk`, here `XmssSecurity/Scan/LoopWalk`: a fresh trial lands with probability `p`). The selection law is `Pr[select y] = W(y) / 2^128`. So `Pr[partner] ≤ E[Φ] / 2^128`, with `Φ = Σ_{y partnered} W(y)` over all messages of the key. Three facts make `Ψ = 2^128 Φ - (V/p) H` a supermartingale over the fresh digest calls, where `V` counts the landed calls and `H = Σ_{y landed} W(y)`:
     - a probe leaves every `W` unchanged in the mean (`probe_eq`, with a point payoff);
     - a call partners itself with probability `|D|/2^128 ≤ V/2^128` and an existing `z` with probability `2^-128`, so `E[Δ 2^128 Φ] ≤ V W_new + H`;
     - `E[Δ (V/p) H] ≥ H + V W_new`.
     Stopped at each key's signing, and with `H ≤ C + V (1-p)/p` (`mass_le`; `C` counts the cached calls), this gives `E[Φ] 2^128 ≤ E[(V/p)(C + V(1-p)/p)] ≤ (2-p) Q^2 + Q/p` for `Q` digest calls (`E[V] ≤ p Q`, `E[V^2] ≤ p^2 Q^2 + p Q`). For `Q < 2^127` this is at most `Q 2^128`: one unit per digest call, the unit a digest call never spends on a guess. The constant `2 - p` is attained (islands of consecutive calls each ending at a landing), so the separated accounting has no room for a looser argument.
   - Total: `Pr[win] ≤ (2 (q - K) + lowerOrderSlack + 2) 2^-128 ≤ q 2^-127` for `q < 2^127` (trivial above), the `2` paying the guesses of `S_0` and `S` (each at most `q 2^-256 ≤ 2^-128`), with `K = 2 + 2^16 (29 + 174 + 1) + 2^16 - 1 = 13,434,881` the hash calls of key generation (the seed hash, the parameter and the top tree, `keygenQueries` in `XmssSecurity/Proof/Bridge/Real`) and `lowerOrderSlack = 2^20` (`XmssSecurity/Proof/RandomizedStatement`) the room for the final verification's calls and the lanes' lower-order terms (`final_arithmetic` in `XmssSecurity/Proof/Bridge/Security`).

## Attributed and multi-user security

`LeanXmss/MultiUserStatement.lean` states two more targets, proved from the same route.

**Attributed** (`Security.HasAttributedSecurity`, `LeanXmssAttributedSecurityStatement`). A hash call after key generation is *attributable* to the key when its input starts with the key's parameter `P`, as every input of the scheme's own hashes after key generation does. With `E` the expected number of attributable calls after key generation (`expectedAttributedQueries`), for `q < 2^127` and an adversary with budget `q`:

`forgeAdvantage ≤ (2 E + 2^10) / 2^128 + 4 q (E + 2^10) / 2^256 + 2 q / 2^256`.

The two lanes are re-run in expectation over the attributable count, and the count is carried through the bridge's hops: equalities in distribution keep it, erasures only drop calls, and a seed guess moves each tail `Pr[t < count]` by at most the guess (`Proof/FirstLaneExpectedBound`, `Proof/CappedExpected*`, `Proof/Seeded/CountTransport`, `Proof/Bridge/Attributed*`). The slack `2^10` covers the final verification's `384` calls, the `290` forgery probes and the seed guesses.

*The second-order term.* The form `Pr[hit] ≤ u E[stopped count]` with `u = 2^-128`, lane 1 without a second-order term, is false. An adversary that guesses one uniform hidden value at `F` distinct points hits with probability exactly `F u`. Counted up to its first hit, its count has mean `F - u F (F - 1) / 2`, so `u` times that mean falls short of `F u` by `u^2 F (F - 1) / 2`. The count stops at a hit, so it misses the guesses that would have come after it. What holds is `H ≤ u A + u F H` for the hit probability `H`, `A` the count's mean and `F = q + forgeryProbeCount` the fuel, hence `H ≤ u A + 4 (u F)(u A)` when `u F ≤ 3/4` (`le_add_four_mul_of_le_add_mul`). That is the term `4 q (E + 2^10) / 2^256`.

**Multi-user** (`MultiUser.HasMultiUserSecurity`, `LeanXmssMultiUserSecurityStatement`). `n` keys from independent seeds in one random oracle, each with its own signing oracle. The adversary names a key and wins when its forgery verifies under that key, the key never reused a leaf index, and the key never answered a request with that message and signature. The budget `q` counts every hash call: all key generations and signatures, the adversary's calls and the final verification. For every `n` and `q < 2^126`:

`forgeAdvantage ≤ q / 2^127 + n^2 / 2^127 + q^2 / 2^252`,

with no factor `n` on `q`. The proof (`Proof/MultiUser/*`):

1. **A win names a key** (`gameCore_le_sum`): the forgery probability is at most the sum over `j` of the multi-user game verified under key `j`.
2. **One reduction per key** (`reduction`). Against key `j`, it receives key `j`'s public key, generates the other keys itself through the oracle, signs their requests with their secret keys, passes key `j`'s requests to its own signing oracle, and outputs the forgery. Its signing log is the multi-user log filtered to key `j` (`run_reduction`).
3. **Key generations commute.** Two computations sharing the lazy random oracle and private sampling may run in either order: the joint law of their results and the final cache is the same (`romRun_bind_comm`). So moving key `j`'s generation first leaves the multi-user game's law unchanged (`romRun_sequenceFin_front`), and the reduction's single-key game is the multi-user game verified under key `j` (`forgeAdvantage_reduction`). Its budget is `q` plus one verification, `q + 384` (`hasHashQueryBound_reduction_of`).
4. **The attributable counts sum to `(1 + C) q`.** Kept as traces of hash inputs (`traceHashes`), the reduction against key `j` counts, over every trace of the run but key `j`'s own generation, the inputs starting with key `j`'s parameter (`expectedAttributedQueries_reduction`). An input starts with the parameters of at most `1 + C` keys, `C` the ordered pairs of distinct keys sharing a parameter (`card_attributed_le`). So over one run the keys' counts sum to at most `(1 + C)` times the run's length, at most `(1 + C) q`. Each key generation's own calls, at least `2^16` starting with its parameter (one leaf hash per top leaf, `own_count_le`), are subtracted. They pay for the slack `2^10` and the reduction's extra verification (`sum_expectedAttributedQueries_le`):

   `Σ_j E_j + 2^16 n ≤ q (1 + n^2 pairBound) + 384 n`.

5. **Coincidences.** Key generation from a cache of at most `L` inputs outputs a fixed parameter with probability at most `2^-128 + (2L + 1) / 2^256`. Either `S_0` names a cached seed-hash input, or `S` a cached parameter input, or the parameter is a fresh truncation (`probEvent_keygen_parameter_le`). Any two keys can be generated first, by commuting, from the empty cache, where the first caches at most its `K` calls. So two keys share a parameter with probability at most `pairBound ≤ 2^-127` (`probEvent_sequence_pair_le`), and `E[C] ≤ n^2 2^-127`.
6. **Arithmetic** (`multiUser_arithmetic`). The `n` attributed bounds at budget `q + 384` sum to `(Σ_j (2 E_j + 2^10)) / 2^128 + 4 (q + 384) Σ_j (E_j + 2^10) / 2^256 + 2 n (q + 384) / 2^256`. With step 4, `q ≥ n K` and `q < 2^126`, this is at most `q / 2^127 + n^2 / 2^127 + 12 q^2 / 2^256`.

*The pair term.* The pair term is `n^2 / 2^127`, not the `n^2 / 2^129` of `n(n-1)/2` pairs at `2^-128` each. The first-order term contributes `2 q E[C] / 2^128 ≤ n^2 / 2^128`. That bound counts ordered pairs: an input starting with a parameter shared by `m` keys counts at most `1 + m(m-1)` times. It also rounds `pairBound` up to `2^-127` and uses `q < 2^126`. The second-order term `4 q Σ_j E_j / 2^256`, with `Σ_j E_j ≤ q (1 + E[C])`, contributes as much again.

## Codewords

A digest is a codeword when its top 12 bits are zero and its first 58 base-4 digits sum to 106: `#codewords = [z^106](1 + z + z^2 + z^3)^58 ≈ 2^107.995`, `p = #codewords / 2^128 ≈ 2^-20.0045`. A codeword determines its digest (all 128 bits are digits). Two distinct codewords are incomparable.

## Modules

The proofs are complete: `XmssSecurity.leanXmss_has_127_bits_of_classical_security : LeanXmssSecurityStatement`, `XmssSecurity.leanXmss_has_attributed_security : LeanXmssAttributedSecurityStatement` and `XmssSecurity.leanXmss_has_multi_user_security : LeanXmssMultiUserSecurityStatement` (`XmssSecurity.lean`). The build fails unless the axioms of each are exactly `propext`, `Classical.choice` and `Quot.sound`.

| modules (`XmssSecurity/`) | content |
| --- | --- |
| `Scheme`, `Proof/IdealStatement`, `Proof/RandomizedStatement` | the model with precomputed keys (`Concrete.scheme`) and its after-key-generation budget |
| `Proof/Bridge/*` | the real game to the model: the seed hash programmed as uniform (`(q-1)/2^256`), derivations programmed as uniform tables, seed elimination (`(q-K)/2^256`), memoization, key distribution, the final arithmetic |
| `Proof/Interface` | `concreteScheme_afterKeygenSecurity`: `(2q + 2^20)/2^128` after key generation, from the two lanes |
| `Proof/OutcomeClassification`, `ConcreteForgery`, `*BadEvent`, `LossDecomposition`, `CappedExactFirstLane` | a win implies a bad event, bottom or top, split into the two lanes |
| `Proof/CappedGlobal*`, `Causal*`, `Chain*`, `ChainKey`, `CappedExactFirstLane*` | lane 1: guesses of hidden chain values of both layers (`ChainKey = LeafIndex ⊕ TopIndex`) and the encoding monitor, `(q + 2^19)/2^128` |
| `Proof/CachedSelectionBound`, `Scan/*` | lane 2, digest term: the partner bound of a cached selection (supermartingale and moment potential) |
| `Proof/CappedUnified*`, `Capped{Leaf,Merkle,Suffix}EventProbability`, `TopStructural` | lane 2, structural term: hits on outputs key generation fixed, bottom and top |
| `Proof/*Keygen*`, `*QueryBound`, `*QueryPresence`, `HonestKeygenRun`, `Top*` | what key generation queries and caches |
| `Proof/PrecomputedBoundedSign*`, `Capped*Trace`, `CappedConcreteExecution` | the signer and the game's traces |
| `Proof/FirstLaneExpectedBound`, `BoundedFirstLaneCountedCoupling`, `CappedExpected*`, `ExpectedTail`, `VerifyQueryBound` | the attributed model bound: lane 1 in expectation with its second-order term, lane 2 up to the expected attributable count |
| `Proof/Seeded/CountTransport`, `Proof/Bridge/Attributed*` | the attributed count through the bridge, and the attributed single-key theorem |
| `Proof/MultiUser/{Commute,Trace,Reduction}` | lazy-oracle commutation, hash traces, the reduction per key and its game |
| `Proof/MultiUser/{Count,Keygen,Coincidence,Budget,Expected}` | the reductions' counts and budgets, key generation's trace, coincident parameters, the sum of the counts |
| `Proof/MultiUser/Security` | the multi-user theorem and its arithmetic |
