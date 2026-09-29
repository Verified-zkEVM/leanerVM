# G-notes: known bugs in deployed SNARK / zkVM verifiers (literature helper G)

Date: 2026-09-29. Written incrementally (one class at a time). Status legend per source:
OPENED = I fetched the page and read the relevant part; SEARCH-ONLY = seen in search results
(title/snippet) but not opened; UNVERIFIED = could not confirm, do not cite without checking.

Theorem shapes used in the "which theorem catches it" column (from the task):

- (a) rbr knowledge soundness of the ORACLE protocol (IOP), proved in Lean, abstract oracle model.
- (b) refinement: executable `verify : Proof -> Bool` accepts iff the FS + Merkle compilation of
  the oracle verifier accepts the decoded proof (Lean definitions only).
- (c) ASSUMED interface: rbr KS of IOP => KS of its FS compilation in the ROM.
- (d) differential testing of Lean `verify` against proofs of the deployed Rust prover, with
  mutations.
- (e) a check that Lean verifier and deployed Rust/Python verifier are the same function (no
  formal correspondence; separate code).

(Work in progress; classes appended below.)
