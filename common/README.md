# common

Proofs the projects share (no end statement: those are in [`Statement/`](../Statement/README.md)):
the random-permutation model (RPM) and the indifferentiability of the sponge construction
(Keccak-256 as leanVM computes it) from a random oracle, after Bertoni, Daemen, Peeters and
Van Assche, *On the Indifferentiability of the Sponge Construction*, EUROCRYPT 2008. It moves
random-oracle-model (ROM) games to the RPM.

Build with `lake build` (the root module `Common.lean` checks that the main theorems use only
`propext`, `Classical.choice` and `Quot.sound`).

## Files

The definitions the end statements need (the permutation oracle `permutationOracleSpec`, the lazily sampled
permutation `lazyRandomPermutation`, `QueryCostAtMost`, the oracles of the model `RandomPermutationOracles` and a game's run `runWithRandomPermutation`,
Keccak-256 the sponge `keccak256With` over the permutation of the lane state `KeccakState`, the SUF-CMA
game in the random-permutation model) are in
[`Statement/RandomPermutation.lean`](../Statement/RandomPermutation.lean), namespace `Common`;
the files below keep their proofs and the definitions only the proofs use.

- `Common/Defs.lean`: the sponge the proofs are written in, over a state `(Dg × E) × C` (digest
  part, rest of the rate, capacity) with a padding and its decoder (`spongeWith`, `Padding`), the
  Keccak state as `200` bytes (`KState`, `32 + 104 + 64`) with Keccak-256's padding
  (`keccakPadding`), the real world `realGame`, the model on byte states (`KSpecB`,
  `permCallsB`, `runKB`) and the simulator's bookkeeping replayed from a transcript (`pathsOf`).
- `Common/Lanes.lean`: the statement's lane states and the proofs' byte states: the bijections
  (`stateEquiv`, `digestEquiv`: byte `8i + k` is byte `k` of lane `i`), Keccak-256 over a
  permutation of the lanes is `common`'s sponge over it read on bytes (`keccak256With_rpm`), the
  lazily sampled permutation is the same on either side (`lazyPerm_relabel`), and a game of the
  statement's model is the game with its permutation queries read on bytes (`relabel`), with the
  same distribution (`runK_relabel`) and the same permutation calls (`isWeightBound_relabel_iff`).
- `Common/Model.lean`: the permutation oracle (`permutationOracleSpec`: `π` and `π⁻¹`), the lazily sampled
  random permutation (`lazyRandomPermutation`) and its validity (a partial permutation, extendable to a
  permutation), the lazily sampled random function (`lazyFun`).
- `Common/Sponge.lean`: the sponge over an arbitrary `π : S → m S` (`spongeWith`), the laws the
  proofs need of its XOR and padding (`XorCancel`, `Padding.Lawful`; the statement uses only `^^^`,
  `pad` and `unpad`), Keccak-256's padding's laws (its six lemmas, the instance for
  `keccakPadding`), its Keccak-256 instance `keccak256With` (rate 136 bytes, capacity 512 bits,
  padding `0x01 ‖ 0* ‖ 0x80`, the first 32 bytes as digest), Keccak-f[1600] (`keccakF`) and test
  vectors.
- `Common/Indiff/`: indifferentiability. `Defs.lean` has the real world (`realGame`), the
  simulator (`simulator`) and the ideal world (`idealGame`); `Main.lean` has the theorem.
- `Common/Transfer.lean`: the ROM-to-RPM transfer, and `pathsOf`.
- `Common/Indiff2/`, `Common/Transfer2.lean`: the two-oracle model (hash `H` and direct
  permutation calls `F`, as in leanVM's Fiat–Shamir duplex).
- `Common/Keccak.lean`: the Keccak-256 instances.
- `Common/Lemmas.lean`: weight bounds through simulations, and the permutation calls of a
  Keccak-256 hash (`keccakPad_length`: `⌊n / 136⌋ + 1` for `n` bytes).
- `Common/Signature.lean`: the SUF-CMA game of a hash-based signature scheme in the ROM and in the
  RPM (on byte states, `rpmGameB`, and the statement's on lanes, `forgeryGame`, the one read on
  bytes: `rpmGame_relabel`), and the transfer of its bounds (`rpm_bound`, `rpm_bound_perm`; used
  by `lean_xmss` and `lean_sphincs`).
- `Common/Eager.lean`: eager sampling of a finite part of a random oracle as a uniform table.
- `Common/Rerun.lean`: a coin-free computation recomputed from a later cache returns the same
  result; weight bounds of prefixes and through simulations; coins through simulations.
- `Common/Duplex/`: the duplex lemma (`Defs.lean` the duplex and its simulator, `Lazy.lean` the
  simulator with lazily sampled challenges, `Table.lean`, `Inv.lean`, `Chal.lean`, `Budget.lean`
  against a table of challenges, `Main.lean` the lemma, `Vec.lean` the challenges as one random
  oracle of vectors and the order of random oracles).

## Results

**Indifferentiability** (`indifferentiability`). The simulator answers a forward query `π x` at
a fresh state `x` reached from the initial state by a sponge path that pads a message `m` with
`H m` completed by uniform bits, any other fresh query uniformly. A distinguisher whose hash and
permutation calls cost at most `q` (`queryCost`: a hash call costs its padded length in blocks,
a permutation call one) has advantage at most

    indiffBound |S| |C| q = q² / |S| + (q (2q + 1) + q (q + 1)) / |C|,

which for Keccak-256 is at most `q² / 2^509` (`keccak256_indifferentiable`).

**Transfer** (`transfer`, `keccak256_transfer`). For a game made of an honest part with `H`, an
RPM adversary `A` with `H`, `π`, `π⁻¹`, and an honest part with `H`, every event has
probabilities in the RPM and in the ROM against `advS A` (`A` with the simulator) within
`indiffBound`.

**Hash queries of a transcript** (`pathsOf`). From a transcript of permutation queries, the
messages whose whole sponge paths it contains, with digests: correct sponge hashes for any
consistent permutation (`pathsOf_sound`), and in the ROM exactly the simulator's random-oracle
queries for the adversary, with the oracle's answers (`pathsOf_ideal`, `pathsOf_ideal2`). So a
straight-line extractor reading the ROM adversary's hash queries runs in the RPM on the
adversary's own hash queries and `pathsOf` of its permutation transcript.

**Two oracles** (`transfer2`, `keccak256_transfer2`). In the two-oracle ROM, `H` is a random
oracle and `F` an independent random function on states; in the RPM, `H` is the sponge over `π`
and `F = π`. For a game made of an honest part with `H`, an RPM adversary with `H`, `π`, `π⁻¹`,
and an honest part with `H` and `F`, every event has probabilities in the RPM (`realGame2`) and
in the two-oracle ROM against `advS2 A` (the simulator `simulator2` answers a fresh non-final
forward query with `F`) within

    indiffBound2 |S| |C| q = indiffBound |S| |C| q + q² / |C|,

at most `q² / 2^508` for Keccak-256, provided the honest direct calls follow the duplex
discipline (`Duplex`): each call `F x` absorbs a non-final block into the initial state or into
the answer of an earlier direct call. For Keccak-256 a block is non-final when byte 135 has its
top bit clear (`keccakNF`); the last padded block never is (`not_keccakNF_of_pad`), and a
duplexing that overwrites lanes `0..16` and keeps the rest absorbs a non-final block
(`keccakNF_blockTo`).

The two-oracle statement needs both restrictions. The ideal `F` cannot answer like the
simulator at the end of a sponge path, where the simulator answers with `H`; and if the
adversary saw a direct call's full answer `y = F x` and then queried `π` at `y ⊕ B` for a final
block `B`, the RPM would tie the answer to `H` while the ROM simulator would not know `y`. Hence
the direct calls are made by the honest part after the adversary has finished.

**Signature games** (`SufCma.rpm_le_rom`, `SufCma.rpm_bound`). For a scheme hashing with
`H : List UInt8 → D` (`D ≃` the 32 Keccak-256 bytes; leanXMSS and leanSPHINCS read them as the
little-endian `BitVec 256`, `digestBitVec`), the ROM game (`romGame`, `romExperiment`: seed, key
generation, the adversary with `H` and a logging signing oracle, verification, every hash call
counted) and the RPM game (`forgeryGame`, `forgeryExperiment`: the same with `H` Keccak-256 over `π`, the
adversary also querying `π` and `π⁻¹`). The signer runs in the adversary's phase, so the transfer's
adversary is the RPM adversary with the signing oracle (its key from the honest phase before), and
the ROM adversary `romAdv A` is `A` with its permutation queries answered by the simulator (and
its hash answers read through the bijection), against the game's own signing oracle. If the RPM
game makes at most `Q` permutation calls on every path (`permutationCallCost`: a hash of `n` bytes costs
`⌊n / 136⌋ + 1`, a query of `π` or `π⁻¹` one) and at most `q` calls of `H`, `π`, `π⁻¹` (`oracleCalls`),
then `romAdv A`'s ROM experiment makes at most `q` hash calls on every outcome and
`Pr_RPM[A wins] ≤ Pr_ROM[romAdv A wins] + Q² / 2^509`; a ROM bound `q / 2^b` gives
`q / 2^b + Q² / 2^509`, and `Q / 2^b + Q² / 2^509` with the permutation budget alone
(`rpm_bound_perm`).

**The duplex lemma** (`Duplex.duplex_le`). A protocol derives `n` challenges of a root `r` by a
duplex over the random function `F` (`chalP`): `y₀ = F (init (H label))`, `y₁ = F (first r y₀)`,
`y_{k+1} = F (next y_k)`, the challenges the `out y_k`, where `first` and `next` keep the
capacity and `first` is injective in `r` (`DuplexSpec`). In the two-oracle ROM, a computation `B`
with at most `N_B` calls of `F`, followed by the challenges of a root it chose and a computation
`post` of them with coins and `H`, succeeds with probability at most that of the simulated world
plus `N (2N εc)`, `N = N_B + n + 1`, `εc` the largest probability of a capacity. In the simulated
world `B` runs against the simulator (`simImpl`: a fresh call `F x` with `x` the next state of a
challenge path is answered `build (G (r, j), w)` for fresh `w`, any other uniformly), and `post`
gets `G (r, ·)`, `G` a random oracle on `(root, index)`; with the challenges sampled lazily the
simulator is exactly `F` (`run'_simImpl_evalDistEq`), and against a table of challenges the
derived challenges are the table's unless a fresh answer's capacity repeats one seen
(`chal_ok`, `prob_bad_le`). `run'_romImpl_evalDistEq_vec` reads `G` as one random oracle of
vectors. The reverse bound, the simulated world at most the two-oracle one plus the same term,
follows for the negated `post` (`Duplex.duplex_ge`). LeanDA's membership challenges instantiate it
(`lean_da`, `LeanDa.daDuplex`: capacity 576 bits, `εc = 2^-576`).

## Not covered

The real permutation is Keccak-f[1600]; the results hold for a uniformly random permutation.
`keccakF` is transcribed and tested on vectors, not used in any proof.
