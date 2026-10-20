# The specification

What the project proves, in the files a reviewer reads. They import nothing else from the project (CI checks it); the rest is proof.

Read in this order:

1. [`Field.lean`](Field.lean): the fields `K = GF(2^64)` and `E = GF(2^192)`, and the generator `g`.
2. [`Blake2s.lean`](Blake2s.lean): the BLAKE2s compression function and BLAKE2s-256 of bytes.
3. [`Isa.lean`](Isa.lean): leanISA (programs, memory, one step, valid executions, the instructions of each opcode an execution executes) and the encoding of an instruction.
4. [`Verifier.lean`](Verifier.lean): the verifier, transcribed from leanVM's Python verifier, with the WHIR and Flock constants it reads and the Fiat-Shamir transcript it runs on; and the deferring verifier an aggregate runs on its children, which takes the values of the fixed polynomials from claims instead of computing them. The prover announces each table's row count, the table's height being the least power of two holding them; the bus discounts the rows past the count (padding rows) through a public term (`paddingWeight`, `Table.padding`).
5. [`Statement.lean`](Statement.lean): the random-oracle experiment and the two statements, `KnowledgeSoundness` and `Completeness`.

The aggregation guest, proved for its deployed bytecode: `guest_knowledge` and `aggregate_sound_outer` ([`../Guest/EndKnow.lean`](../Guest/EndKnow.lean)) prove `GuestKnowledge` and `AggregateSound` of [`Guest.lean`](Guest.lean) for the decoder that reads the witness off the execution's memory; `guest_sound` and `guest_complete` ([`../Guest/EndFinal.lean`](../Guest/EndFinal.lean), [`../Guest/EndFinalComplete.lean`](../Guest/EndFinalComplete.lean)) prove `GuestSound` and `GuestCompleteWithin` ([`../Guest/End.lean`](../Guest/End.lean)), the latter within the deployed limits and budget, and [`../../LeanVM.lean`](../../LeanVM.lean) pins their axioms:

6. The two signature schemes, leanXMSS and leanSPHINCS, imported from the projects that prove their security: [`lean_xmss/LeanXmss/Scheme.lean`](../../../lean_xmss/LeanXmss/Scheme.lean) and [`lean_sphincs/Sphincs/Scheme.lean`](../../../lean_sphincs/Sphincs/Scheme.lean).
7. [`Da.lean`](Da.lean): the claim on a DA root, in terms of LeanDA as [`lean_da/LeanDa/Scheme.lean`](../../../lean_da/LeanDa/Scheme.lean) defines it (the deployed commitment, the membership vector and its digest), on this project's BLAKE2s.
8. [`Node.lean`](Node.lean): a node's statement and its digest, the batching of deferred claims, `NodeRel` and `NodeSpec` (what a node establishes, with a witness and with some witness) and the outer verifier.
9. [`Guest.lean`](Guest.lean): a decoder (a seed, a statement and a witness read off a memory), and what a proof of the guest establishes with it: `AggregateSound` (what the outer verifier's acceptance of a statement establishes, the headline), `GuestKnowledge` (every valid execution decodes to a statement of its input's digest and a witness holding it); the collision candidates of two statements' digests.

[`Fast/`](Fast/) needs no review: it holds `@[csimp]` theorems, each proved, that make the compiled field arithmetic, BLAKE2s, LeanDA's membership vector and the signature schemes' verifiers fast. They change no definition.

The proofs are `LeanVM.knowledgeSoundness_holds` and `LeanVM.completeness_holds` in [`LeanVM/Protocol/LeanVM.lean`](../Protocol/LeanVM.lean).
