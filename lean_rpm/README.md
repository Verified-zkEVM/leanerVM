# lean_rpm

The random-permutation model (RPM) and the indifferentiability of the sponge construction
(Keccak-256 as leanVM computes it) from a random oracle, after Bertoni, Daemen, Peeters and
Van Assche, *On the Indifferentiability of the Sponge Construction*, EUROCRYPT 2008. It moves
random-oracle-model (ROM) games to the RPM.

Build with `lake build` (the root module `LeanRpm.lean` checks that the main theorems use only
`propext`, `Classical.choice` and `Quot.sound`).

## Files

- `LeanRpm/Model.lean`: the permutation oracle (`permSpec`: `π` and `π⁻¹`), the lazily sampled
  random permutation (`lazyPerm`) and its validity (a partial permutation, extendable to a
  permutation), the lazily sampled random function (`lazyFun`).
- `LeanRpm/Sponge.lean`: the sponge over an arbitrary `π : S → m S` (`spongeWith`), its
  Keccak-256 instance `keccak256With` (rate 136 bytes, capacity 512 bits, padding
  `0x01 ‖ 0* ‖ 0x80`, the first 32 bytes as digest), Keccak-f[1600] (`keccakF`) and test vectors.
- `LeanRpm/Indiff/`: indifferentiability. `Defs.lean` has the real world (`realGame`), the
  simulator (`simulator`) and the ideal world (`idealGame`); `Main.lean` has the theorem.
- `LeanRpm/Transfer.lean`: the ROM-to-RPM transfer, and `pathsOf`.
- `LeanRpm/Indiff2/`, `LeanRpm/Transfer2.lean`: the two-oracle model (hash `H` and direct
  permutation calls `F`, as in leanVM's Fiat–Shamir duplex).
- `LeanRpm/Keccak.lean`: the Keccak-256 instances.

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

## Not covered

The real permutation is Keccak-f[1600]; the results hold for a uniformly random permutation.
`keccakF` is transcribed and tested on vectors, not used in any proof.
