# The specification

What the repository proves, in the files a reviewer reads. They import nothing else from the
repository (`scripts/check-layers.sh` enforces it); the rest of the repository is proof.

Read in this order:

1. [`Field.lean`](Field.lean): the fields `K = GF(2^64)` and `E = GF(2^192)`, and the generator `g`.
2. [`Blake2s.lean`](Blake2s.lean): the BLAKE2s compression function and BLAKE2s-256 of bytes.
3. [`Isa.lean`](Isa.lean): leanISA (programs, memory, one step, valid executions), the encoding of
   an instruction, and the fill blocks completeness assumes.
4. [`Verifier.lean`](Verifier.lean): the verifier, transcribed from leanVM's Python verifier, with
   the WHIR and Flock constants it reads and the Fiat–Shamir transcript it runs on; and the
   deferring verifier an aggregate runs on its children, which takes the values of the fixed
   polynomials from claims instead of computing them.
5. [`Statement.lean`](Statement.lean): the random-oracle experiment and the two statements,
   `KnowledgeSoundness` and `Completeness`.

The aggregation guest (in progress: stated, not yet proved):

6. The two signature schemes, leanXMSS and leanSPHINCS, imported from the leanVM projects that
   prove their security:
   [`formal/lean_xmss/LeanXmss/Scheme.lean`](../../../lean_xmss/LeanXmss/Scheme.lean) and
   [`formal/lean_sphincs/Sphincs/Scheme.lean`](../../../lean_sphincs/Sphincs/Scheme.lean).
7. [`Da.lean`](Da.lean): LeanDA's commitment and the claim on a DA root.
8. [`Node.lean`](Node.lean): a node's statement and its digest, the batching of deferred claims,
   `NodeSpec` (what a node establishes) and the outer verifier.

[`Fast/`](Fast/) needs no review: it holds `@[csimp]` theorems, each proved, that make the compiled
field arithmetic and BLAKE2s fast. They change no definition.

The proofs are `LeanVM.knowledgeSoundness_holds` and `LeanVM.completeness_holds` in
[`LeanerVM/Protocol/LeanVM.lean`](../Protocol/LeanVM.lean).
