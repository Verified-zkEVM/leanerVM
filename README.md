# leanerVM

Lean 4 proofs about [leanVM](https://github.com/leanEthereum/leanVM) at the commit in
[`leanvm-rev`](leanvm-rev): its verifier is knowledge sound and complete, its aggregation guest
program proves what it claims, and the schemes it checks (leanXMSS, leanSPHINCS, LeanDA) are secure,
all in the random-permutation model (Keccak-f[1600] modeled as a random permutation).

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
