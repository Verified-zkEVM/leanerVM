# lean_vm

A Lean 4 proof that leanVM's verifier is knowledge sound and complete in the random-oracle model, for the verifier, the instruction set and the arithmetization of the leanVM commit in [`../leanvm-rev`](../leanvm-rev).

## What is proved

The statements are in [`LeanVM/Spec/`](LeanVM/Spec/README.md), which imports nothing else from this project (CI checks it): the rest is proof. Read in this order:

| File | What it is |
| --- | --- |
| [`Field.lean`](LeanVM/Spec/Field.lean) | the fields `K = GF(2^64)`, `E = GF(2^192)` and the generator `g` |
| [`Keccak.lean`](LeanVM/Spec/Keccak.lean) | Keccak: the permutation Keccak-f[1600] and Keccak-256 of bytes |
| [`Isa.lean`](LeanVM/Spec/Isa.lean) | leanISA: memory, the six instructions, programs, one step, `ValidExecution`, `Trace.count` |
| [`Verifier.lean`](LeanVM/Spec/Verifier.lean) | the verifier, `python-verifier/verifier.py` transcribed section by section, for any hash function and permutation |
| [`Extractor.lean`](LeanVM/Spec/Extractor.lean) | the knowledge extractor: from the proof and the oracle's answers to the adversary's queries, the committed word, its Johnson list and the execution a candidate's memory holds |
| [`Statement.lean`](LeanVM/Spec/Statement.lean) | `KnowledgeSoundness` and `Completeness` |
| [`Guest.lean`](LeanVM/Spec/Guest.lean) | what a proof of the aggregation guest would establish, its witness named: `GuestKnowledge`, `AggregateSound` (up to a Keccak-256 collision); stated, not proved at this pin (below) |
| [`Da.lean`](LeanVM/Spec/Da.lean), [`Node.lean`](LeanVM/Spec/Node.lean) | the DA claim, on LeanDA as [`lean_da`](../lean_da) defines it, and what a node of the aggregation guest establishes (`NodeRel`, `NodeSpec`): its statement's Keccak-256 digest, its deferred bytecode claim and the batching of its children's |

The proofs are `LeanVM.knowledgeSoundness_holds` ([`LeanVM/Protocol/LeanVMSound.lean`](LeanVM/Protocol/LeanVMSound.lean)) and `LeanVM.completeness_holds` ([`LeanVM/Protocol/LeanVM.lean`](LeanVM/Protocol/LeanVM.lean)).

The knowledge-soundness error is `soundnessError Q = (Q + 12008)(2^-128 + 7(Q + 12008)/2^256) + 12008/2^256` for an adversary of `Q` queries to Keccak-256 and Keccak-f[1600] together (`12008` bounds the verifier's queries, proved over every admissible shape and not tight: it charges every WHIR opening at the largest commitment height; the `7` counts the digests and sponge capacities a fresh answer may collide with or predict; the last term pays for a fresh Keccak-256 answer to one of the verifier's queries equal to a Merkle root the adversary announced without computing it, which the extractor, reading only the adversary's queries, would miss). It is at most `2^-63` for `Q ≤ 2^64` (`soundnessError_le`).

The completeness error at a fuel of `fuel` nonces per proof of work is `completenessError fuel = Q · (1 - 2^-17)^fuel`, `Q = 12012 + 48017 · (2^27 + 2·fuel + 2)` the queries of the honest prover and the verifier together; it is below `2^-128` at a fuel of `2^25` (`completenessError_le`).

[`LeanVM.lean`](LeanVM.lean) fails the build if the axioms of any of these theorems grow beyond `propext`, `Classical.choice` and `Quot.sound`.

**The model.** Keccak-256 (Merkle hashes, the IV, the bytecode and statement digests) and Keccak-f[1600] (the Fiat-Shamir duplex sponge: the seed `F(iv ‖ public input ‖ 0)`, then one permutation per challenge and per full rate of absorbed scalars) are two independent random oracles, `H` on byte strings and `F` a random *function* on states. The experiment runs the adversary, given both oracles, then the verifier with the same oracles; every hash and permutation the verifier and the honest prover compute goes through `H` and `F`, and none happens before or during the adversary's run except its own queries. Inside the executed program, the `KECCAK` instruction's Keccak-f[1600] is the deployed permutation, proved (it is the instruction's semantics, not an oracle call). `KnowledgeSoundness` is stated for one extractor, `LeanVM.extractor` ([`Spec/Extractor.lean`](LeanVM/Spec/Extractor.lean)), which is straight-line: from the proof and the Keccak-256 answers to the adversary's own queries alone (not the verifier's, not the permutation's; no rewinding) it reads the announced sizes and the stack's Merkle root off the proof as the verifier's first two steps do, reads the committed word off the adversary's answers by inverting the Merkle tree, and returns the halting run of the memory image of a stack in the word's Johnson list (its Reed–Solomon encoding agreeing with the word on at least level 0's Johnson threshold of columns) that is a valid execution, if one is. The choice within the list is classical: the extractor is a definition, not an efficient algorithm. The statement applies to programs whose last instruction is not a `JUMP` (`SentinelSafe`: for others the deployed verifier accepts invalid runs). A proof is the Python verifier's format (full Merkle paths); the Rust verifier's expansion of the pruned wire paths is not formalized. That the Lean verifier is the Rust and Python ones is test evidence: it accepts the Rust prover's proofs, gives the Rust verifier's verdict on mutated ones, and its helpers and Fiat-Shamir sponge agree with the Python's on the inputs of the tests.

`Completeness` covers every valid execution within the verifier's size cap: its committed size (`Trace.committedSize`, the cells the prover commits to, set by the memory, the bytecode and how many instructions of each opcode it executes, the `KECCAK` table at least `2^9` rows and `q_keccak` `2^6` cells per row) at most `2^28`.

## The proof, in phases

The verifier is the composition commit → bus (GKR grand products) → table sumcheck → public input → Keccak reduction (GKR over the rounds of Keccak-f[1600]) → ring switching → WHIR opening of the stack. Its soundness is a round-by-round doom certificate (`LeanVM/Protocol/Compile/`, `EndToEnd/Sound/Assemble.lean`) compiled to the random-oracle model (`Compile/Rom/`), with the leanISA instance (`Protocol/LeanIsa.lean`) carrying the arithmetization (`Arithmetization/`) into the protocol. Two points specific to `keccak-gkr`:

* **The `KECCAK` table's lanes.** Its fifty value lanes are not committed. The input lanes are columns of `q_keccak` (slots `0..24`), which also commits the state after the first twelve of the permutation's twenty-four rounds (slots `25..49`), and the output lanes are *derived*: lane `l` of the last twelve rounds applied to that middle state (`M3Instance.derived`, `LeanIsa.outColumn`). The instance's Keccak clause (`KeccakRegion.Holds`: the middle state is the first twelve rounds of the input) makes the output Keccak-f[1600] of the input (`column_outCol_of_aux`).
* **The Keccak clause through the table sumcheck.** The Keccak reduction checks the middle state only at one point, drawn earlier; so the clause is carried through the table sumcheck as a moving invariant (`Spine/KeccakZero.lean`, `TableSumcheck.inv`), binding the region's coordinates high first and escaping with at most one challenge per round, inside the round's `3/|E|`. The reduction's precondition is then the output claims against the committed middle state and the middle state's agreement at the table point (`Front/KeccakBridge.lean`, `Keccak/` for the GKR proofs).

## The aggregation guest

The previous leanVM (BLAKE2s, Flock) had a formalized aggregation guest (`LeanVM/Guest/`: its compiled bytecode, program logic, a symbolic executor and kernel-checked certificates, `guest_knowledge`, `guest_complete`, `aggregate_sound_outer`, `children_sound`, `batch_rom`). At `keccak-gkr` the guest (`crates/rec_aggregation/guests/lean_ethereum.py`) is a different program (it verifies the Keccak-GKR proof system, with ring switching and a duplex transcript), and its proofs are being re-ported; the statements they prove are kept in `Spec/Guest.lean` and `Spec/Node.lean`. `Protocol/Verifier/Deferred.lean` (the deferring verifier with a true bytecode claim is the deployed one, `verify_of_verifyDeferred`) and `DeferredShape.lean` (`verifyDeferred_shaped`), which the guest's recursion step uses, are ported.

What is there so far:

* **The data.** leanVM has no `LEANVM_WRITE_*` tests at this pin, so `scripts/guest-export` exports the guest from leanVM's own sources (it compiles `crates/rec_aggregation`'s sources as its own crate, with the exporters as a child module of `aggregation.rs`, reading `../.leanvm` and never writing it): the compiled guest (`LeanVM/Guest/Data/Bytecode*.lean`: `2^19` slots, 364,192 instructions in 900 functions, 45,830 of them `KECCAK`), its source AST after the deployed placeholders (`Data/Source.lean`; the exporter checks that it compiles to the same bytecode), the compiler's test programs (`tests/LeanVMTests/Guest/Programs.lean`), the Rust's figures for the guest (`tests/LeanVMTests/Guest/Manifest.lean`) and the node vectors (`tests/LeanVMTests/Spec/NodeVectors.lean`).
* **The bytecode as a `Program`** (`Guest/Code.lean`, `Guest/Bytecode.lean`): instructions in offset form (`OInstr`, `KECCAK` as `.keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd`, its cells at the offsets `keccakIns`, `keccakOuts`), `guest`, and the fetch lemma at every pc of its functions. That `guest` is the bytecode the Rust proves is checked compiled: its Fiat-Shamir IV, the Keccak-256 hash of its `2^23` bytecode words (`deployedSeed guest`), is the Rust's `fs_seed` (`lake exe node-vectors`).
* **The source AST** (`Guest/Source.lean`, with `[body for v in unroll(lo, hi)]`, `listComp`) and **the core IR** (`Guest/Core.lean`): one `Atom.keccak ins outs inOdd outOdd` per `KECCAK` instruction, its thirteen read and thirteen written cells, meaning `KeccakCells`.

The batching of a node's children, which depends on `Spec/` alone, is re-proved for `keccak-gkr` ([`LeanVM/Guest/Batch/`](LeanVM/Guest/Batch/)). The recursion step `LeanVM.Guest.Batch.children_sound`: for a witness of `NodeRel` under the deployed seed whose statement's deferred claim holds, every child's proof is accepted by the deployed verifier and the child's own deferred claim holds, or a challenge of the node's batching is bad (`BatchBad`: a lambda that the gaps and the earlier lambdas fix, or a sumcheck challenge that is a root of a nonzero quadratic its round fixes; `batch_sound`). That no challenge is bad is the batching's soundness with Keccak-256 and Keccak-f[1600] independent random oracles, `LeanVM.Guest.Batch.batch_rom`: the batching as a verifier program (`batchAny`, which is `Node.batch` with its deferred claim checked, `runProof_batchAny`) accepts a proof that begins with fewer than `M` children of the bytecode's shapes with a false claim with probability at most `Q · (2^-191 + 5Q/2^256)` for `Q` queries of the adversary and the program together (`batch_rom_explicit`), at most `Q · 2^-189` for `Q ≤ 2^64` (`batch_rom_bits`). The guest computes the batching with Keccak itself, so applying it is the Fiat-Shamir assumption for the batching.

## Layout

| Path | Contents |
| --- | --- |
| `LeanVM/Spec/` | the statements |
| `LeanVM/Parameters/`, `LeanVM/Semantics/` | constants and encodings; lemmas about the ISA, `KECCAK`'s cells |
| `LeanVM/Arithmetization/` | the tables, the bus and the constraints, sound and complete for valid executions |
| `LeanVM/Protocol/` | the proof system and its proofs; `Keccak/` the Keccak reduction; `To{ArkLib,Clean,CompPoly,VCVio}/` hold lemmas meant for those libraries |
| `tests/` | `#guard`s and `example`s, checked by `lake test`; `fixtures/verifier/` are proofs of the Rust prover |
| `LeanVM/Guest/` | the aggregation guest: its compiled bytecode (`Data/Bytecode*`, generated) as a `Program` (`Code`, `Bytecode`), its source AST (`Source`, the generated `Data/Source`), the core IR (`Core`) and compile-time words (`Word`) |
| `cli/` | `leanvm-verify`, the compiled verifier on a proof's files, and `node-vectors`, the costly checks of the Rust vectors |
| `scripts/` | the Rust-vs-Lean fuzz, its Rust verifier CLI, the fixture exporter, the WHIR parameter table generator, and `guest-export`, the exporter of the guest's data from leanVM's sources |

## Building and testing

```sh
lake exe cache get
python3 -I scripts/ci-build.py
lake test
lake exe node-vectors
```

`lake build` at the repository root runs all of it, with the Rust checks below, for the five projects (`../check-all.sh`).

The Rust checks run against leanVM at [`../leanvm-rev`](../leanvm-rev), which `../leanvm-tree.sh` checks out into `../.leanvm`, its `formal/lean_vm` a link to this directory. The Rust-vs-Lean differential, as CI runs it:

```sh
../leanvm-tree.sh
lake build leanvm-verify
cargo build --release --manifest-path scripts/rust-verifier-cli/Cargo.toml
python3 -I scripts/fuzz-verifier.py tests/fixtures/verifier --jobs 4
```

After a bump of `../leanvm-rev` to a protocol change, regenerate the fixtures with `scripts/export-verifier-fixtures-rust.sh tests/fixtures/verifier`.

The guest's data (the bytecode, the source, the test programs, the manifest and the node vectors) is regenerated, after a bump of `../leanvm-rev` or a change to the exporter, by one command; `--check`, which CI runs, fails when any of it is stale:

```sh
cargo build --release --manifest-path scripts/guest-export/Cargo.toml
scripts/guest-export/target/release/guest-export .           # write
scripts/guest-export/target/release/guest-export . --check   # CI
```

An independent check of the bytecode data against leanVM's own disassembly: `DBG_DISASM=/tmp/disasm.txt scripts/guest-export/target/release/guest-export . --check`, then `python3 -I scripts/guest-export/roundtrip.py . /tmp/disasm.txt` compares every slot and every function's range.

The guest-diff cases, real aggregations of the Rust (a one-signature leaf, a leaf of both schemes with a blob, one whose leanXMSS list is longer than a claim group, a node over them), each with its statement, seed, witness and installed hint streams, are written by the exporter's ignored tests; they are the input of the Lean mirror's differential check, `guest-diff`, once it is ported:

```sh
LEANVM_GUEST_DIFF=/tmp/guest-diff cargo test --release --manifest-path scripts/guest-export/Cargo.toml --lib guest_diff -- --ignored
```

## Credits

The formalization was started in `Verified-zkEVM/leanerVM`, by scaraven, aryaethn, Alexander Hicks, Elias Judin, Stefano Rocca and Aristotle (Harmonic). Modules derived from the earlier leanth formalization say so in their docstrings.
