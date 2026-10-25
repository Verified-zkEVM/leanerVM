# Statement

What the repository proves, in the files a reviewer reads: definitions and end statements only,
one Lake package (`statement`) of ten files, `Statement/<Name>.lean` (Lean modules
`Statement.<Name>`), the generated guest bytecode in [`Data/`](Data/), and, for speed only,
proved `@[csimp]` lemmas in [`Fast/`](Fast/), which a reviewer need not read. It imports Mathlib, VCVio
and CompPoly and nothing else (CI checks it); every other project of the repository is proof and
imports it.

**The model.** Every end statement with an adversary is in the random-permutation model: one
uniformly random permutation `π` of the 1600-bit Keccak state, which every party queries forward
(`π x`) and inverse (`π⁻¹ y`), Keccak-256 the sponge over `π` and Keccak-f[1600] `π` itself. That
the deployed Keccak-f[1600], a fixed permutation, behaves as a random one is the assumption. The
random-oracle model and the sponge's indifferentiability, through which the proofs pass, are proof
steps and are not stated here (two definitions of the two-oracle random-oracle model are, because
LeanDA's code-binding bound names them: see `RandomPermutation.lean`).

**The sources.** The leanVM definitions are transcribed from leanVM at
`94ee12ff6b2a3d42ba8328e22d09443692e4800b` (branch `main`, [`../leanvm-rev`](../leanvm-rev)): each
cites its source (`verifier.py:N`, `*.rs:N`, `doc/leanvm` sections). LeanDA's security framework is
Benedikt Wagner's ([b-wagn/fv-pq-da](https://github.com/b-wagn/fv-pq-da), Apache-2.0, see
[`../lean_da/NOTICE`](../lean_da/NOTICE)).

## Reading order

1. [`RandomPermutation.lean`](RandomPermutation.lean): Keccak-f[1600] and Keccak-256 as leanVM
   computes them (`keccakF`, `KeccakHash.keccak256`); the random-permutation model (`permSpec`: `π`
   and `π⁻¹`; `lazyPerm`, the lazily sampled uniform permutation; the sponge over a permutation
   and Keccak-256's padding, `spongeWith`, `keccakPadding`); a cost bounded on every path
   (`IsWeightBound`); the Keccak-256 evaluations a transcript of permutation queries contains
   (`pathsOf`); the SUF-CMA game of a hash-based signature scheme in the random-permutation model
   (`SufCma.rpmGame`, `rpmExperiment`, `permCalls`); and, for LeanDA's code-binding bound, the
   two-oracle and duplex simulators.
2. [`LeanXmss.lean`](LeanXmss.lean): the leanXMSS scheme, its SUF-CMA game, and
   `LeanXmss.Rpm.LeanXmssRpmSecurityStatement`.
3. [`LeanSphincs.lean`](LeanSphincs.lean): the leanSPHINCS scheme, its SUF-CMA game with the
   deterministic signer, the proved lifetimes, and `Sphincs.Lifetimes.RequestedSecurityRpm`.
4. [`Field.lean`](Field.lean): `K = GF(2^64)` (CompPoly's `BF64`), `E = GF(2^192)`, the generator
   `g`; Keccak lanes, bytes and digests as field elements.
5. [`LeanDa.lean`](LeanDa.lean): LeanDA (fields, Reed–Solomon rows, the Merkle commitment, the
   membership test), Benedikt Wagner's framework for erasure code commitments and the reductions
   his bound names, LeanDA's games in the random-permutation model, and
   `LeanDa.PerfectlyCompleteStatement`, `LeanDa.PositionBindingRpm`, `LeanDa.CodeBindingRpm`.
6. [`LeanIsa.lean`](LeanIsa.lean): leanISA (memory, the six instructions, programs, one step,
   `run`, `ValidExecution`: a run from `(1, 1)` that halts in the final state
   `(g^(N_prog - 1), 1)`, the instruction counts `Trace.count`, the bytecode encoding), the
   machine under any `KECCAK` semantics (`ValidExecutionB`), and a program assembled from compiled
   functions (`CompiledFn`, `assemble`).
7. [`LeanVmVerifier.lean`](LeanVmVerifier.lean): the verifier, `python-verifier/verifier.py`
   transcribed section by section, for any hash function and permutation in any monad
   (`verifyWith`), with the WHIR constants it reads, the Keccak GKR reduction, the Fiat-Shamir
   duplex over Keccak-f[1600], the deferring verifier an aggregate runs on its children, and the
   sizes a stream announces (`announced`). Where
   the pin rewrote a step of the previous pin (`3375f7a13`) without changing what it computes, the
   transcription keeps the earlier form and its docstring gives both the pin's lines and why the
   two agree.
8. [`Extractor.lean`](Extractor.lean): the knowledge extractor, straight-line: from the proof and
   the adversary's Keccak-256 evaluations, the announced sizes and the stack's root, the committed
   word, its Johnson list (at most `2^18` stacks), and the halting run of a candidate's memory
   image that is a valid execution, if there is one.
9. [`LeanVm.lean`](LeanVm.lean): a statement (a program and a public input), the verifier on it
   (`verifier H F`, `verify`), its calls as oracle queries (`HashSpec`), the honest prover's type,
   the errors `soundnessError`, `completenessError`, the committed size; the random-permutation
   experiment (`rpmExperiment`, the adversary's `Transcript`), the extractor on the transcript
   (`extractorRpm`), **`LeanVM.KnowledgeSoundness`, `LeanVM.Completeness`,
   `LeanVM.KnowledgeSoundnessBits`**, and a digest as a public input (`publicInputOfDigest`).
10. [`LeanVmGuest.lean`](LeanVmGuest.lean): the aggregation guest's specification: DA claims, a
    node's statement, witness and relation (`NodeRel`, `NodeSpec`: leanXMSS and leanSPHINCS
    claims, DA claims, children verified by the deferring verifier, the batching of their
    deferred claims), the same with any hash and permutation (`NodeRelWith`), a decoder and what a
    proof of the guest establishes with it (`GuestKnowledge`, `AggregateSound`, `Explains`), the
    deployed guest (`LeanVM.Guest.guest`, from [`Data/`](Data/)), its deployed limits (`Limits`,
    `CapsAgree`, `NoZeroChallenge`, a node's `work`), and
    **`LeanVM.Guest.Budget.GuestCompleteRecursion`, `GuestCompleteLeaf`**.

[`Data/`](Data/) is the guest's compiled bytecode, generated from leanVM's sources by
`lean_vm/scripts/guest-export` (do not edit; `guest-export --check` fails when it is stale, as CI
runs it). It needs no review beyond that check.

[`Fast/`](Fast/) makes the compiled definitions fast and changes nothing they mean: `@[csimp]`
lemmas, each proved, that compile `GF(2^64)` products on machine words (`FieldWords`), the
degree-three extension's product unrolled (`CubicExt`), Keccak-f[1600] and Keccak-256 with their
lanes written out (`Keccak`), and the signature schemes' verifiers with a constant-depth lookup
(`Schemes`). A `@[csimp]` lemma acts where a definition is compiled, so they are here, imported by
`Field.lean`, `LeanDa.lean` and `LeanVmGuest.lean`, for the statement's own compiled definitions
(the verifier, the guest's specification, LeanDA) and every module after them. They need no review:
a `@[csimp]` lemma is an equation the kernel checks.

A few definitions carry proofs, which are here because the definitions need them:
`Common.keccakPadding` (a `Padding`, with the padding's laws: six lemmas in
`RandomPermutation.lean`) and `LeanDa.daDuplex` (a `Common.Duplex.DuplexSpec`, with the duplex's
laws: the lemmas before it in `LeanDa.lean`); and decidability instances.

## The end theorems

| Statement | Proved by | In |
| --- | --- | --- |
| `LeanVM.KnowledgeSoundness` | `LeanVM.knowledgeSoundness_holds` | [`lean_vm/LeanVM/Protocol/LeanVMRpm.lean`](../lean_vm/LeanVM/Protocol/LeanVMRpm.lean) |
| `LeanVM.Completeness` | `LeanVM.completeness_holds` | same |
| `LeanVM.KnowledgeSoundnessBits` | `LeanVM.knowledgeSoundness_bits` | same |
| `LeanVM.Node.GuestKnowledge guest decode` | `LeanVM.Guest.End.guest_knowledge` | [`lean_vm/LeanVM/Guest/EndFinal.lean`](../lean_vm/LeanVM/Guest/EndFinal.lean) |
| `LeanVM.Node.AggregateSound guest decode` | `LeanVM.Guest.End.aggregate_sound_outer` | [`lean_vm/LeanVM/Guest/EndRpm.lean`](../lean_vm/LeanVM/Guest/EndRpm.lean) |
| `LeanVM.Guest.Budget.GuestCompleteRecursion` | `LeanVM.Guest.Budget.guest_complete_recursion` | [`lean_vm/LeanVM/Guest/Budget/Covered.lean`](../lean_vm/LeanVM/Guest/Budget/Covered.lean) |
| `LeanVM.Guest.Budget.GuestCompleteLeaf` | `LeanVM.Guest.Budget.guest_complete_leaf` | same |
| `LeanXmss.Rpm.LeanXmssRpmSecurityStatement` | `XmssSecurity.leanXmss_rpm_security` | [`lean_xmss/XmssSecurity/Rpm.lean`](../lean_xmss/XmssSecurity/Rpm.lean) |
| `Sphincs.Lifetimes.RequestedSecurityRpm` | `Sphincs.Lifetimes.requestedSecurityRpm` | [`lean_sphincs/Sphincs/LifetimesRpm.lean`](../lean_sphincs/Sphincs/LifetimesRpm.lean) |
| `LeanDa.PerfectlyCompleteStatement` | `LeanDa.leanDa_perfectlyComplete` | [`lean_da/LeanDa.lean`](../lean_da/LeanDa.lean) |
| `LeanDa.PositionBindingRpm` | `LeanDa.leanDa_positionBinding_rpm` | [`lean_da/LeanDa/RpmSecurity.lean`](../lean_da/LeanDa/RpmSecurity.lean) |
| `LeanDa.CodeBindingRpm` | `LeanDa.leanDa_codeBinding_rpm_bound` | [`lean_da/LeanDa.lean`](../lean_da/LeanDa.lean) |

Each project's root module (`lean_vm/LeanVM.lean`, `lean_xmss/XmssSecurity.lean`,
`lean_sphincs/Sphincs.lean`, `lean_da/LeanDa.lean`) is its end file: it checks that each end
theorem proves its statement and pins its axioms to Lean's three (`propext`, `Classical.choice`,
`Quot.sound`). The guest's two soundness statements take the decoder as a parameter; the end
theorems name `LeanVM.Guest.End.decode` ([`EndFinal.lean`](../lean_vm/LeanVM/Guest/EndFinal.lean)),
which reads the witness off the execution's memory: the statements hold of any decoder that outputs
valid witnesses, and their content is in the decoder the theorems name.

## Building

`lake build` here builds the ten files, the data and `Fast/`; the other projects build it as a dependency.
The data's modules are heavy: `python3 -I ../lean_vm/scripts/ci-build.py ../Statement` builds a few
at a time, as CI does.
