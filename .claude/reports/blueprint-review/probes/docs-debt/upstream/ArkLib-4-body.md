FYI, I have created a duplicate of this issue at https://github.com/Verified-zkEVM/VCVio/issues/571, since I think it will be easier to track Merkle Tree development from there now that the code has been upstreamed. -BB

---

This issue tracks all development of Merkle trees. This is the basic vector commitment scheme that is required for all proof systems we care about (later development may bring in other schemes such as KZG, Bulletproofs, etc.)

We would like to prove completeness, extractability, and hiding for Merkle trees. These proofs (extractability and hiding) are non-trivial, and will require serious effort (from the core team or a serious outside contributor). The reference for this is in Chiesa & Yogev's recent zkSNARK textbook.

Relevant files in ZKLib:
- [Merkle Trees](https://github.com/quangvdao/ZKLib/blob/main/ZKLib/CommitmentScheme/MerkleTree.lean)
- [Basic Definitions of Commitment Schemes](https://github.com/quangvdao/ZKLib/blob/main/ZKLib/CommitmentScheme/Basic.lean)

Depends on progress in #2  to be able to state security properties for Merkle commitments.

Tasks:

- [x] Flesh out the definitions of Merkle trees, especially the opening phase.
  - [x] Single index opening
- [ ] Prove completeness of Merkle commitments.
  - [x] Single-index
  - [ ] Batch-index
- [ ] Initial development of the extractability proof.
  - [x] Extractor definition
  - [ ] Single-instance extractability
    - [x] Single-index
    - [ ] Batch-index
  - [ ] Multi-instance extractability 
- [ ] Initial development of the hiding proof.

References:
- Chapter 18 (Merkle commitment scheme) of [Building Cryptographic Proofs from Hash Functions](https://snargsbook.org/).
- Section 3 of the [original IOP paper](https://eprint.iacr.org/2016/116.pdf).

The textbook has more details but the paper might be an easier first read.