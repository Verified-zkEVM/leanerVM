# leanerVM

Lean 4 proofs about [leanVM](https://github.com/leanEthereum/leanVM) at the commit in
[`leanvm-rev`](leanvm-rev): its verifier is knowledge sound and complete (and stays so through the
proof's wire encoding, a compression layer whose pruned Merkle paths are
[scaraven](https://github.com/scaraven)'s idea), and the schemes its aggregation guest program checks
are secure (leanXMSS, leanSPHINCS; LeanDA's code binding given a knowledge-sound argument), in the
random-permutation model (Keccak-f[1600] modeled as a random permutation). An accepted proof of the guest program is explained by a witness or by a collision
of the deployed Keccak-256 (one recursion level; soundness across levels is not proved).

**What is proved** is in [`Statement/`](Statement/README.md): definitions and end statements only,
the one folder a reviewer reads. Everything else is proof.

## Check

```sh
./check-all.sh lean      # build and kernel-check every Lean project: no sorry, axioms Lean's three
./check-all.sh vectors   # compare with leanVM's Rust: guest data, verifier and prover (needs cargo)
```

A cold build takes several CPU-hours on a large machine.

## License

MIT or Apache-2.0, as leanVM. [`lean_da/`](lean_da/) is Benedikt Wagner's work
([b-wagn/fv-pq-da](https://github.com/b-wagn/fv-pq-da)), ported to LeanDA, under its own
[`LICENSE`](lean_da/LICENSE) and [`NOTICE`](lean_da/NOTICE).
