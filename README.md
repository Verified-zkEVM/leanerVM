# leanerVM

Lean 4 proofs about [leanVM](https://github.com/leanEthereum/leanVM): its verifier, its aggregation guest, and the signature schemes and data-availability scheme the guest checks. The four projects are leanVM's `formal/` at the commit in [`leanvm-rev`](leanvm-rev) (branch `FV`), with their history.

| Path | What it proves |
| --- | --- |
| [`lean_vm/`](lean_vm/README.md) | leanVM's verifier, sound and complete in the random-oracle model (`LeanVM.knowledgeSoundness_holds`, `LeanVM.completeness_holds`); for the aggregation guest's deployed bytecode, that a valid execution's memory decodes to a statement of its public input's digest and a witness holding it (signatures, DA matrices, child proofs: `guest_knowledge`), that an honest node within the limits and the size budget has a valid execution (`guest_complete`), and the recursion step (`children_sound`, `batch_rom`). How these compose into an aggregate's security, and what that needs, is in [`lean_vm/README.md`](lean_vm/README.md) |
| [`lean_xmss/`](lean_xmss/PROOF.md) | leanXMSS's 127 bits of classical SUF-CMA security in the random-oracle model (`XmssSecurity.leanXmss_has_127_bits_of_classical_security`) |
| [`lean_sphincs/`](lean_sphincs/README.md) | leanSPHINCS's 127 bits of classical SUF-CMA security in the random-oracle model, at every proved lifetime (`Sphincs.Lifetimes.requestedSecurity`) |
| [`lean_da/`](lean_da/README.md) | LeanDA's completeness and binding |

Each is its own Lake project on the toolchain in [`lean-toolchain`](lean-toolchain); `lean_vm` requires the other three by path, for their `Scheme` modules.

## Building and checking

`lake build` here runs [`check-all.sh`](check-all.sh): for each project, in turn and in its own directory, what [`.github/workflows/lean.yml`](.github/workflows/lean.yml) runs: no proof escapes, the build, no deprecated API, the axiom footprints, `lake test` and the compiled checks of `lean_vm`, then the checks against leanVM below, which need `cargo`. `./check-all.sh lean_vm` (or any of `lean_xmss lean_sphincs lean_da lean_vm leanvm`) runs some. A cold build is several CPU-hours.

## Against leanVM

[`leanvm-rev`](leanvm-rev) is the leanVM commit whose verifier, guest and prover `lean_vm` is about. [`leanvm-tree.sh`](leanvm-tree.sh) checks it out into `.leanvm/`, with its `formal/lean_vm` a link to `lean_vm/`. There, leanVM's tests that write the Lean data (`guest_bytecode_lean`, `guest_source_lean`, `node_spec_vectors`) fail when the copy here is stale, the Rust verifier is fuzzed against the Lean one, and the Rust aggregation against the guest's mirror; CI runs all three.

leanVM's own `formal/` goes on changing. Following it is deliberate: bump `leanvm-rev`, carry over the matching `formal/` changes, and let the checks above say what is stale. The generated data's headers and some prose still name leanVM's paths (`formal/lean_vm/…`, `crates/…`); those are citations into the leanVM tree.

## License

As leanVM: MIT ([`LICENSE-MIT`](LICENSE-MIT)) or Apache-2.0 ([`LICENSE-APACHE`](LICENSE-APACHE)). `lean_da/` carries its own [`LICENSE`](lean_da/LICENSE) and [`NOTICE`](lean_da/NOTICE).
