# leanerVM

Lean 4 proofs about [leanVM](https://github.com/leanEthereum/leanVM): its verifier, and the signature schemes and data-availability scheme its aggregation guest checks. The four projects are leanVM's `formal/` at the commit in [`leanvm-rev`](leanvm-rev) (branch `FV`), with their history.

| Path | What it proves |
| --- | --- |
| [`lean_vm/`](lean_vm/README.md) | leanVM's verifier at `main` (`4af2cdddd`, the `keccak-gkr` branch merged: Keccak-256 hashing, a Keccak-f[1600] duplex sponge for Fiat-Shamir, the `KECCAK` instruction proved by GKR over the rounds), knowledge sound with a fixed straight-line extractor (information-theoretic: its running time is not part of the statement), and complete, with Keccak-256 and Keccak-f[1600] as independent random oracles (`LeanVM.knowledgeSoundness_holds`, `LeanVM.completeness_holds`), and with both built from one random permutation (`LeanVM.knowledgeSoundnessRpm_holds`, `LeanVM.completenessRpm_holds`: the random-oracle errors plus `q² / 2^508` for `q` permutation calls; at most `2^-63` for `2^64` adversary queries). The aggregation guest's proofs of the previous (BLAKE2s) leanVM are not carried over: see [`lean_vm/README.md`](lean_vm/README.md) |
| [`lean_rpm/`](lean_rpm/README.md) | the random-permutation model (a uniform permutation π with π and π⁻¹ queries), the indifferentiability of the Keccak-256 sponge from a random oracle (q²/2^509), and the transfer of random-oracle bounds to the random-permutation model, for Keccak-256 alone and with direct permutation calls in leanVM's duplex (q²/2^508) |
| [`lean_xmss/`](lean_xmss/README.md) | leanXMSS's 127 bits of classical SUF-CMA security in the random-oracle model (`XmssSecurity.leanXmss_has_127_bits_of_classical_security`), and in the random-permutation model `Q / 2^127 + Q² / 2^509` for `Q` permutation calls (`XmssSecurity.leanXmss_rpm_security`) |
| [`lean_sphincs/`](lean_sphincs/README.md) | leanSPHINCS's 127 bits of classical SUF-CMA security in the random-oracle model, at every proved lifetime (`Sphincs.Lifetimes.requestedSecurity`), and in the random-permutation model `Q / 2^127 + Q² / 2^509` for `Q` permutation calls (`Sphincs.Lifetimes.requestedSecurityRpm`) |
| [`lean_da/`](lean_da/README.md) | LeanDA's completeness, position binding and code binding: Benedikt Wagner's framework and proofs ([b-wagn/fv-pq-da](https://github.com/b-wagn/fv-pq-da), [his post](https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746)), ported and instantiated with LeanDA; in the random-permutation model, position binding `Q² / 2^256 + Q² / 2^508` and code binding moved to the two-oracle random-oracle model |

Each is its own Lake project on the toolchain in [`lean-toolchain`](lean-toolchain); `lean_xmss`, `lean_sphincs` and `lean_da` require `lean_rpm` by path, and `lean_vm` requires those three by path, for their `Scheme` modules, and `lean_rpm`, for its statements in the random-permutation model.

## Building and checking

`lake build` here runs [`check-all.sh`](check-all.sh): for each project, in turn and in its own directory, what [`.github/workflows/lean.yml`](.github/workflows/lean.yml) runs: no proof escapes, the build, no deprecated API, the axiom footprints and `lake test`, then the checks against leanVM below, which need `cargo`. `./check-all.sh lean_vm` (or any of `lean_xmss lean_sphincs lean_da lean_vm leanvm`) runs some. A cold build is several CPU-hours.

## Against leanVM

[`leanvm-rev`](leanvm-rev) is the leanVM commit whose verifier, guest and prover `lean_vm` is about. [`leanvm-tree.sh`](leanvm-tree.sh) checks it out into `.leanvm/`, with its `formal/lean_vm` a link to `lean_vm/`. There the Rust verifier is fuzzed against the Lean one, and `lean_vm/scripts/guest-export` writes the aggregation guest's data and the node vectors from leanVM's sources (at this pin leanVM has no tests that write Lean data); CI runs both.

leanVM's own `formal/` goes on changing. Following it is deliberate: bump `leanvm-rev`, carry over the matching `formal/` changes, and let the checks above say what is stale. The generated data's headers and some prose still name leanVM's paths (`formal/lean_vm/…`, `crates/…`); those are citations into the leanVM tree.

## License

As leanVM: MIT ([`LICENSE-MIT`](LICENSE-MIT)) or Apache-2.0 ([`LICENSE-APACHE`](LICENSE-APACHE)). `lean_da/` carries its own [`LICENSE`](lean_da/LICENSE) and [`NOTICE`](lean_da/NOTICE).
