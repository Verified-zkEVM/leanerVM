Tracks #12. Hole **K3**: compilation, the transcript, the proof object and the executable verifier, blueprint Layer 12 (ledger A5).

**Produces** (`LeanerVM/Protocol/{Transcript,Proof,Verify}.lean`, plain): `FsState` with `seed`, `observe`, `sample`, `grind` (Category B, `fiat_shamir/src/lib.rs:18-174`: a Merkle–Damgård chain of `compress` on a 256-bit state, lane-3 tags 1/2/3/4, no labels (F1), seeded by `compress(iv, input)` with `iv` the BLAKE2s of `"leanvm" ‖ len ‖ R1CS_DIGEST ‖ bytecodeHash` (F14)); `Proof` (`transcript.rs:9-19`), `RoundPoly.decode` (one coefficient derived, `transcript.rs:289-309`, acceptance test 8); `leanVmIopp` (WHIR in place of the evaluation oracle); `verify : Program → PublicInput → Proof → Bool` (Category A, written from §8.5 before `cpu/mod.rs:711-779` is opened; total, never panics), `settleFixedClaims` (the seam for T5); `verify_iff_compiled` (unconditional: `verify` is the Fiat–Shamir compilation of the composed oracle verifier, `∃ s` over the announced sizes: test 21); the assumed interfaces `FiatShamirSecurity` and `BcsSecurity`; `verify_knowledgeSound (fs) (bcs) (mca) (flock)` with `niError`.

**Consumes:** the spine's six `ProtocolSpec`s and the phase `Def`s (their verifiers; not their `Security`), K1, K2, ArkLib `Reduction.fiatShamir`/`Verifier.fiatShamir` (definitions).

**Tests:** a proof dumped from the pinned Rust prover (`scripts/dump-proof.sh`, recorded with its program and public input) accepted by `verify` under `#guard`; six mutations rejected (a flipped stream scalar in each phase, a wrong Merkle sibling); `RoundPoly.decode` on the Rust encoding; `ToyProblem.Codegen`-style compilation probe.

**Upstream watch:** ArkLib #848 and #469 (duplex-sponge Fiat–Shamir: Theorems 6.1/6.2 and the single-salt straightline knowledge-soundness transfer, the shape for `FiatShamirSecurity`; leanVM's chain is Merkle–Damgård, not a duplex sponge, so the transfer theorem, not the sponge, is what applies), ArkLib #627 (BCS), VCVio #784 (merged; query-budget controls, #29).

**Claim** by assigning yourself.
