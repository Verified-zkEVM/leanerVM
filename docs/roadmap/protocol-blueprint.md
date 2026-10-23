# Roadmap: the leanVM proof system on ArkLib

leanVM proves that a leanISA execution exists by committing the six M3 tables as one multilinear
polynomial, the *stack*, and running, in order, a grand-product argument for the bus (GKR), one
batched sumcheck for the tables' constraints, a two-cell public-input check, the Flock argument
for the BLAKE2S rows with ring switching, and one WHIR opening of the stack; Fiat–Shamir over
BLAKE2s makes it non-interactive. This roadmap builds that verifier in Lean 4 on ArkLib's
interactive oracle reductions and states the theorems that make it a proof system for the
constraint relation of the [leanISA roadmap](leanisa-blueprint.md):

```text
piop_perfectCompleteness (I : M3Instance) (P : Phases I) (C : P.Complete) :
  M3Holds I input q → the honest prover makes leanVmVerifier P accept with probability 1
piop_rbrKnowledgeSoundness (I : M3Instance) (P : Phases I) (S : P.Security) :
  leanVmVerifier P is round-by-round knowledge sound for M3Holds I, with the named extractor
  piopExtractor P S (it reads the stack q off the commitment), at the error piopError I
```

Both are composition theorems over an abstract M3 instance `I` and a bundle `P` of the five
phases after the commitment. They hold of every bundle that meets the spine's seams, and say
nothing of leanVM until the instance and the phases are leanVM's: the instance is trusted data,
checked by the adaptor's theorems and by fixtures, not by these two. The error `piopError I` is a
closed form of the instance's sizes that the spine fixes, so a phase meets its slot only by
earning its bound. They are stated in the *ideal oracle model*: the stack `q` is an oracle
answering inner products `⟨W, q⟩`, and the challenges are uniform.

The adaptor (Layer 3) is the one place the proof system meets leanISA: `witnessOf` reads an
`EnsembleWitness` off `q`, and `satisfiedBy_witnessOf` turns `M3Holds` of the leanISA instance
into `SatisfiedBy prog input (witnessOf q)`. Composed with `constraintSoundness` (leanISA Layer
10) it gives "an accepted proof has an execution", the proof-system half of target T4 of
[architecture.md](../architecture.md). The non-interactive verifier `verify`, the one Rust proofs
are checked against, is specified in full and proved to be the compilation of the oracle
verifier. The headline theorem (Layer 13) is its knowledge soundness, with a computable
extractor of the witness, and of the execution through leanISA's trace interface:

```text
baseVerifier_extractsWitness (hB : BlakeMisbehaves prog input A δ) :
  Pr over the run of A, its hash queries and the verifier's answered by BLAKE2s-256, that
      verify prog input proof = true  and  the stack extract reads off A's queries
      does not give SatisfiedBy prog input (witnessOf …)
    ≤ δ
```

Every step to it is a theorem: Flock's security (with the Flock roadmap's inhabitant, #3), WHIR's
correlated agreement (ArkLib's), the list-binding compilation, and `core` (Layer 12): an accepted
proof from whose queries the extractor reads no witness shows BLAKE2s misbehaving in the run's log,
by a collision, a fresh digest equal to one already in play, or a challenge of the proof's own chain
in a set of density at most `2^{−128}` fixed by its prefix. Its one assumption is `hB`, that this
happens with probability at most `δ` for the adversary at hand, a hypothesis in the statement and
never an axiom. `misbehaves_rom` shows that, for a statement fixed before the adversary runs, an
adversary making at most `Q` hash queries, a verifier making at most `V` and a uniformly random
function in place of BLAKE2s, it happens with probability at most `niError εquery V Q`, which
`niError_le` bounds by `(Q + V)/2^128` plus a hash term quadratic in `Q + V` over `2^256`.

Home: `LeanerVM/Protocol/Spine/` (the spine), `LeanerVM/Protocol/` (the phases over an abstract
instance, the adaptor, the compilation), the Clean bridge in `LeanerVM/Protocol/ToClean/`, the
transcribed constants in `LeanerVM/Parameters/`, following [architecture.md](../architecture.md).
Generic components live under `LeanerVM/Protocol/ToArkLib/` (and `ToClean/`, `ToCompPoly/`,
`ToVCVio/`), or `LeanerVM/Parameters/To<Library>/` when a lower layer must import them, until their
upstream pull request merges.

This document is the specification: what is wanted and what was decided. It records no state;
what is built is in [protocol-status.md](protocol-status.md), who is taking what in issue
[#12](https://github.com/Verified-zkEVM/leanerVM/issues/12) (see
[How work is tracked](#how-work-is-tracked)). The Lean signatures pin the shapes most likely to
drift; they are not exhaustive.

## For zkVM engineers

ArkLib formalizes a proof system as a chain of *reductions*. A reduction is a short interactive
protocol with a fixed message schedule (`ProtocolSpec`) that turns a claim "the statement `x` is
in relation `R₁` with some witness" into a claim about a relation `R₂`, typically smaller:
sumcheck turns "this sum equals `T`" into "this polynomial has value `v` at the random point
`r`"; a random linear combination turns ten claims into one. Some prover messages are *oracles*:
the verifier does not read them, it queries them. The stack is such an oracle, and its query is
a *weight*: the verifier names a table `W` over the hypercube, with an efficiently computable
extension, and learns `⟨W, q⟩ = Σ_w W(w)·q(w)`. An evaluation `q̃(r)` is the query at the equality
weight `eq(r, ·)`. This is the interface of the specification's commitment (Definition 3.13), and
WHIR realizes it.

Two properties are proved per reduction and composed. **Perfect completeness**: an honest prover
always passes. **Round-by-round knowledge soundness** ([CMS19] Definition 8.5): a *state
function* on partial transcripts, false while no witness the extractor could read off makes the
current claim true, which a cheating prover can turn true only when a fresh challenge lands
badly, with a bound per challenge. The *extractor* is straight-line: it reads the
witness off the transcript and the oracle messages, no rewinding. ArkLib lets an extractor be any
function, so a theorem that merely asserts some extractor exists is satisfied by one that picks a
witness by classical choice and carries no knowledge: every theorem here names its extractor and
its state function (the `With` form), and every extractor is a computable definition. The error
of each challenge is fixed by the spine as a closed form of the instance; summing them gives the
interactive error, and after Fiat–Shamir each per-challenge bound is what one random-oracle
query buys the adversary.

Four things are built. **The relation**: `M3Holds I input q`, a checklist on the committed stack:
every constraint polynomial of every table, of degree at most two in the row's columns, vanishes
on that table's rows read out of `q`; the pushed and pulled bus tuples read out of `q` are the same
multiset; every read count is nonzero; cells 0 and 1 of the memory limbs hold the public words;
Flock's R1CS holds of the committed BLAKE2s region. The caps on the announced sizes are not a
clause: the compiled verifier checks them before the protocol starts. It is stated over an
abstract instance `I` (the tables' log-heights and widths, constraint polynomials and their
degree bound, flush tuples, count columns, boundary blocks, public lines, stack layout, the Flock
region). **The adaptor**: the leanISA instance, and the maps `stackOf` (an `EnsembleWitness` to
its stack) and `witnessOf` (a stack to an `EnsembleWitness`, total and computable) with
`m3Holds_stackOf` and `satisfiedBy_witnessOf`. **The oracle protocol**: specification §8, phase
by phase, as ArkLib reductions over the one oracle `q`, composed sequentially; the spine fixes the
seams, the schedules' shapes and the errors, so that the phases are independent units of work.
**The compilation**: WHIR realizes the stack's oracle and replaces the opening's query, Merkle
trees realize WHIR's oracles, a BLAKE2s chain replaces the verifier's coins, and
`verify : Proof → Bool` is that compiled verifier, executable.

What is proved without hypotheses: everything about the oracle protocol, given ArkLib's framework
and the composition this roadmap proves itself, and two facts about `verify`. The first, `core`,
is deterministic and holds for every function answering the hash: if `verify` accepts and the
extractor reads no witness off the adversary's queries, the log of the run shows the hash
misbehaving. The second, `misbehaves_rom`, is the random-oracle model: with BLAKE2s replaced by a
uniformly random function, the hash misbehaves with probability at most `niError εquery V Q`, for a
statement fixed before the adversary runs and a verifier making at most `V` queries. They rest on
Flock's security (inhabited from the Flock roadmap, #3), on WHIR's correlated agreement in the
list-decoding regime (ArkLib proves it with Annex B's constant), on Merkle binding by replaying
the log, and on the charged invariant, which bounds what each fresh hash query can buy, each a
theorem. The compiled verifier's 128-bit level needs 17 bits of proof of work per WHIR level. No
published theorem covers Fiat–Shamir with proof of work for a multi-round protocol, so Layer 12
proves that step. What is not attempted: recursion (T5, T6), zero knowledge (leanVM has none),
security against quantum adversaries.

The random-oracle model here stands for one function: BLAKE2s-256 on byte strings. The Fiat–Shamir
chain, the Merkle nodes and the grinding call it on 64-byte inputs, and the Merkle leaves on 384- or
512-byte ones. The statement's seed (a 78-byte string) and the program hash are constants of the
statement, computed by BLAKE2s outside the oracle. So the statement is fixed before the adversary
runs, and the random-oracle bound is selective: for an adversary picking the public input after its
queries, every statement's first chain state would be in play from the start, and a hit on one of
them would not be unlikely. The headline theorem's one assumption, `BlakeMisbehaves`, is about
BLAKE2s on the adversary's run: except with probability `δ`, no two inputs share a digest, no fresh
digest equals a value already in play, and no challenge of the proof's own Fiat–Shamir chain lands
in the bad set of its prefix, a set of density at most `2^{−128}` that the prefix and the committed
words fix (a theorem, `bad_density`). These are collision resistance, unpredictability and
correlation intractability against a sparse relation, asked of one run. The adversary's BLAKE2s
calls must be its oracle queries: an adversary that hashes in its own code fails the hypothesis,
since the verifier's query on a Merkle node the adversary hashed itself is fresh and answered by the
proof's root, a hit with probability `1`. The theorem then says nothing about that adversary; the
hypothesis is false, not the theorem wrong. The adversary draws no coins, so under BLAKE2s its run
is one computation and the hypothesis is one bit about it; the headline's content is `core`: on any
run where the verifier accepts and the extractor fails, the hash misbehaves. Why the hypothesis must
be per adversary, and what it excludes (attacks that use the code of BLAKE2s, [KRS25], [Fen26]), is
in Layer 13. leanVM binds the statement and commits the trace before the first challenge, so the
known attacks do not apply, but no theorem here says so.

Why the relation is polynomial and not "a valid execution exists": sumcheck, GKR and WHIR
manipulate polynomials, and a knowledge extractor recovers column data, never an execution; a
protocol stated against `ValidExecution` would demand of the extractor what it cannot produce and
would couple every phase to the semantics. The extractor is `piopExtractor`, whose extracted stack
the adaptor turns into a witness by `witnessOf`.

How a missing check is caught. The master theorems hold of any instance, so a verifier that
omits a check *together with* an instance that omits the matching clause (two public lines for
three, a Flock predicate that is `True`, an aliasing layout) satisfies them. What catches it is
the adaptor's soundness theorem, whose conclusion `SatisfiedBy` does not weaken with the
instance, and, behind it, leanISA's `constraintSoundness`. Inside a phase, a check is
load-bearing only if the verifier commits to what it checked, and every check comes with a
theorem that refutes its omission (convention *Load-bearing checks*).

## Scope

### In scope

- ArkLib as a Lake dependency, with the field, sampling and oracle-interface instances that make
  `E = GF(2^192)` a challenge space and the stack an inner-product oracle;
- the spine: the abstract instance `M3Instance`, its relation `M3Holds`, the seams, the hole
  interfaces, the closed-form error, the composition with its two master theorems, the adaptor's
  transport lemma, and a toy instance every phase is tested on;
- hypercube tables over `K` and `E`, stacking with selectors, the strided reader, the index
  column, the bytecode multilinear, and their evaluation identities;
- the polynomial view of a Clean component: constraint and flush polynomials, the degree bound,
  and the bridge lemmas to Clean's row-wise meaning;
- the leanISA instance: announced sizes and admissibility, the stack and leaf layouts, the
  boundary blocks, the stack of an `EnsembleWitness`, and the extractor's witness read back;
- the two sumcheck variants leanVM runs, a batching component by the powers of one challenge,
  the fingerprint and product lemma, and the radix-4 grand-product GKR (generic; upstream);
- the bus phase (§5.2–§5.4, §6), the table sumcheck (§5.5), the public-input check (§8.2), the
  Flock phase's definition and completeness, and the opening (§8.5), as reductions with perfect
  completeness and round-by-round knowledge soundness at the spine's errors;
- WHIR over Reed–Solomon codes in the novel polynomial basis of `K`, Merkle trees over BLAKE2s,
  and leanVM's WHIR parameters (Annex B; generic parts upstream, shared with #3);
- the Fiat–Shamir chain with grinding, the `Proof` object and its decoding, the executable
  `verify`, its refinement theorem, the list-binding compilation through a list-decoder
  interface, Merkle binding by replaying the hash log, and the random-oracle theorems on the one
  hash oracle: a deterministic core and the bound on the hash's misbehaviour, proof of work
  included;
- the base theorems of T4, with a computable extractor and a hypothesis on the hash named in the
  statement; the honest prover and `verify` as a native executable that writes and checks test
  vectors; and executable fixtures: kernel-checked identities on small instances, a Rust-produced
  proof accepted by `verify`, a mutation rejected for every check.

### Out of scope

- the tables, channels, `SatisfiedBy` and `AssignmentRepresents`: leanISA Layers 5–10 (#4); this
  roadmap consumes `SatisfiedBy` and changes nothing in it beyond the requests in
  [Boundaries](#boundaries);
- the BLAKE2s Boolean circuit, Flock's zerocheck and lincheck, ring switching, and the Flock
  phase's knowledge soundness: the Flock roadmap (#3), consumed through `FlockSpec` and the Flock
  phase's slot (Layer 9);
- witness generation from an execution (T2): base completeness starts from a satisfying witness,
  and the test vectors take theirs from an untrusted, test-only generator whose output a
  decidable check of `SatisfiedBy` accepts (Layer 13);
- the recursion guest, deferred claims, the verifier in circuit (T5) and extraction across
  recursion (T6); `verify` is the native verifier, shaped so that the deferred variant is a
  one-function change;
- adaptive statement soundness in the random-oracle model, where the statement may depend on the
  oracle: the theorems here quantify over the statement outside the probability, as
  architecture.md's T7 schema does with its fixed expected statement;
- zero knowledge, and security against quantum adversaries (the classical bound does not transfer:
  the loss is quadratic in the query count);
- the proximity-gap theorem for Reed–Solomon codes up to the Johnson bound ([BCHKS25] Theorem
  4.6): ArkLib proves it with the printed constant, and it is consumed as the interface
  `McaJohnson`, inhabited from ArkLib's theorem (Layer 11);
- whether BLAKE2s misbehaves on a given adversary's run: the headline theorem's hypothesis, per
  adversary, never discharged (Layer 13);
- performance of the extractor: it is computable and runs on toy instances; an efficient list
  decoder is another inhabitant of its interface, not a requirement. The honest prover has a
  performance target (Layer 13), not a theorem;
- agreement of the Lean prover's proofs with the Rust prover's: future work (Layer 13).

## Dependencies and exact contracts

A prerequisite is a named declaration of a pinned library, an earlier layer here or in the
leanISA roadmap, or a cited section of a source. The pins are in `upstreams.json`, with the
history of each in [dependencies.md](../dependencies.md); leanVM is pinned at
[`a386121f`](https://github.com/leanEthereum/leanVM/commit/a386121f84292f6fa663aaa3e570c15bc0240ea2).
Library paths below are at the current pins.

**Prior work.** The earlier formalization of leanVM-a in the private repository `leanth` is
surveyed in [leanth-reuse.md](leanth-reuse.md), layer by layer; issues cite that page, never the
private tree, and derived material carries the credit it prescribes.

### The leanVM specification and implementation

Two kinds of source, with opposite disciplines ([CONTRIBUTING.md](../../CONTRIBUTING.md) sets the
rules). What the verifier accepts and why it is sound is **written from the specification**
first and then diffed against the Rust and Python verifiers. Transcript tags, absorption order,
encodings, layouts, parameters and constants are **transcribed from their source**, and are wrong
if they deviate. Every module docstring says which, names its source section or file and lines,
and the pin. Where the two sources disagree the oracle protocol models the checks of the deployed
verifier and takes its arguments from the specification (decision 22); the disagreements are
recorded, by name, in [leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin).

| Artifact | How | Source at the pin |
| --- | --- | --- |
| M3 model, grand product, GKR, leaf stacking, table sumcheck | from the specification | §5 (`doc/leanvm/body/05-arithmetization.tex`) |
| Lookup and count arguments, index column | from the specification | §6.2–§6.5 |
| Unrolled protocol, public input, opening | from the specification, checks as deployed | §8.2, §8.3, §8.5; `cpu/mod.rs:711-779` |
| Ring switching, WHIR, novel basis, additive NTT | protocol from the specification; parameters transcribed | Annex A, Annex B; `crates/pcs/src/whir.rs`, `whir_config.rs:38-86` |
| Flock: protocol and errors | from the specification, owned by #3 | Annex C |
| Flock: the BLAKE2s circuit, wire positions, limb slots, `φ_8`, the fixed coordinates, `R1CS_DIGEST` | transcribed (the specification lacks them) | `flock/src/hash.rs`, `lean_vm/src/hash_flock.rs:87-115`, `pcs/src/stack_open.rs:84-97`, `py:1092-1095` |
| Fiat–Shamir chain: tags, seeding, sampling, grinding | transcribed (§8.4 is `TODO`) | `crates/fiat_shamir/src/lib.rs:18-174`; `cpu/mod.rs:82-124` |
| Proof object, stream order, round-polynomial encoding | transcribed | `fiat_shamir/src/transcript.rs:9-19, 280-330`; `cpu/mod.rs:711-779` |
| Stack and leaf layouts, block order, selectors, strided limb slots | transcribed | `witness.rs:67-101`, `cpu/layout.rs:13-49, 400-445`, `leaf.rs:53-156`, `stack_open.rs:84-97` |
| Count blocks (the tables' count columns only) | transcribed | `cpu/layout.rs:412-414`; `leaf.rs:606-622` |
| Bytecode multilinear, sixteen slots | transcribed | §8.1; `leaf.rs:585-637` |
| Caps, the stacking window `μ ∈ [15, 28]`, the rate window `[1, 4]` | transcribed | `cpu/mod.rs:45-64, 130-178`; `lean_vm/src/pcs.rs:49-51` |
| GKR radix, combiners, normalized round, root sharing | transcribed | `gkr.rs:32-76, 247-430` |
| `ξ`-power assignment, derived target | transcribed | `cpu/mod.rs:404-441, 726-735` |
| WHIR fold factors, rates, queries, out-of-domain samples, grinding | transcribed | `whir_config.rs:38-86, 260-370`; `py:910` |
| Merkle hashing, pruned paths, digest encoding | transcribed | `fiat_shamir/src/merkle.rs:14-67`; `crates/pcs/src/merkle.rs` |
| BLAKE2s byte hasher | transcribed | `crates/primitives/src/hash.rs`; RFC 7693 §3.3 |
| Second verifier (cross-check only) | — | `python-verifier/verifier.py:1365-1414` |

### The leanISA roadmap

Consumed as named declarations of its
[interfaces](leanisa-blueprint.md#interfaces-supplied-to-later-work); nothing is restated here.

| Declaration | Contract used here |
| --- | --- |
| `K`, `E`, `y`, `ofK`, `E.limb`, `E.ofLimbs`, `g`, `gpow`, `orderOf_g` (Layer 0) | Challenges are `E`; columns are `K`; `gpow` is the index column. |
| `iv`, `sigma`, `compress` (Layer 1) | The RFC compression `F`, which the Fiat–Shamir step, the Merkle nodes, the grinding and the Flock circuit share. |
| `Program`, `PublicInput`, `word0`, `word1`, `minLogMem`, `maxLogMem`, `maxLogRows`, `maxLogBytecode`, `minLogRowsBlake2s` (Layer 2) | The typed statement and the caps; the top limb of a public word is zero by type. |
| `encodeSlots` (Layer 4) | The bytecode multilinear is `encodeSlots` laid out on `2^(k_bc + 4)` points. |
| `xorTable` … `blake2sTable`, `memTable`, `bytecodeTable`, `leanIsaVerifier` (Layers 6–8) | The opcode tables become tables of the instance; the memory, bytecode and verifier rows become boundary blocks. |
| `StatePull` … `BytecodePush`, `MemMsg`, `Regs`, `BytecodeMsg`, `channelSep`, `channelDir`, `busTuple` (Layer 5) | A channel names its domain separator and coordinate order on the 16-slot bus. |
| `SatisfiedBy`, `BalancedPair`, `CountsNonzero`, `Caps`, `imageOf`, `Blake2sRowsValid` (Layer 8) | The relation the adaptor targets; nothing above the adaptor mentions it (convention *The wall*). |
| `constraintSoundness`, `constraintCompleteness`, `WellFormedBytecode` (Layer 10) | Consumed by Layer 13: `constraintCompleteness` by completeness from an execution; `constraintSoundness` through the trace interface. |
| `TraceExtraction`, `checkSatisfiedBy`, `checkSatisfiedBy_eq_true_iff` (requested, beside `SatisfiedBy` in `Arithmetization/`) | The trace interface the execution-level headline takes, inhabited from Layers 9–10, and the decidable check the test vectors pass ([Boundaries](#boundaries)). |

### ArkLib

ArkLib is a Lean `module` library that carries admitted theorems under its own baseline; a
leanerVM declaration may not depend on one (the kernel axiom audit rejects `sorryAx`), so every
ArkLib theorem is checked with `#print axioms` before it is consumed. ArkLib calls the
`OracleReduction` framework below *legacy*; its typed successor has no knowledge notion at the
pin, so the spine stays on it (decision 24).

| Declaration | Contract used here |
| --- | --- |
| `ProtocolSpec n`, `MessageIdx`, `ChallengeIdx`, `FullTranscript` (`OracleReduction/ProtocolSpec/`), `Direction` (`OracleReduction/Prelude.lean`) | The message schedule of every reduction; challenges are `V_to_P` rounds. |
| `OracleInterface` (`OracleReduction/OracleInterface.lean`) | The query type and answer of an oracle message; Layer 0 gives the stack the inner-product interface. ArkLib registers no default interface for scalars or lists. |
| `Prover`, `Verifier`, `OracleVerifier`, `OracleReduction` (`OracleReduction/Basic.lean`) | The carriers. |
| `perfectCompleteness`, `completeness` (`OracleReduction/Security/Basic.lean`) | Completeness, error `ℝ≥0`. |
| `KnowledgeStateFunction`, `Extractor.RoundByRound`, `rbrKnowledgeSoundnessWorstCaseWith` (`Security/RoundByRound.lean`) | Round-by-round knowledge soundness for a named extractor and state function, error `ChallengeIdx → ℝ≥0`: the form every theorem here takes. The existential forms `rbrKnowledgeSoundness`, `rbrKnowledgeSoundnessWorstCase` prove soundness only, since the extractor may be a classical choice. |
| `rbrKnowledgeSoundness_implies_rbrSoundness` (`Security/Implications.lean`) | Proved; plain round-by-round soundness as a corollary. |
| `OracleReduction.append` (`Composition/Sequential/Append/`); `append_perfectCompleteness_of_guarded_verifiers`, `append_completeness_of_guarded_verifiers` (`Composition/Sequential/GuardedCompleteness.lean`) | Sequential composition, and its completeness, proved for guarded verifiers. |
| `Extractor.RoundByRound.append`, `Verifier.StateFunction.append` (`Composition/Sequential/Append/StateFunction.lean`) | The appended extractor, ArkLib's; its knowledge state function and bound are the local port (the ledger). |
| `Component.ReduceClaim`, `CheckClaim`, `RandomQuery`, `DoNothing` (`ProofSystem/Component/`) | Zero-round components; `CheckClaim`'s oracle variant checks nothing at run time (it carries the check in the output relation). |
| `SumcheckDomain` (`ProofSystem/Sumcheck/Domain.lean`) | Per-coordinate evaluation domains, reused by Layer 4. The classical `Sumcheck.Spec` is not consumed (the ledger). |
| `MvPolynomial.MLE`, `eqPolynomial`, `eqTilde`, `MLE_eq_zero_iff` (`Data/MvPolynomial/Multilinear.lean`) | Multilinear extensions and the equality kernel; the bridge to CompPoly's tables is `CMlPolynomialEval.eval_eq_MvPolynomial_MLE` (`ToCompPoly/Multilinear/Basic.lean`), imported only after a file importing it with CompPoly's `Multilinear/Basic` elaborates (both declare `eval_zero`). |
| `schwartz_zippel_counting`, `prob_eval_zero_le_div`, `prob_eval_zero_univ_le_div` (`Data/MvPolynomial/SchwartzZippelCounting.lean`) | Every per-challenge bound; the probability forms are stated on VCVio's uniform sampler. |
| `ReedSolomon.mcaError_affineLine_johnson_le` (`Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Probability.lean`); `johnsonComparisonEstimate`, `johnsonExceptionCount_le_comparisonEstimate` (`Data/CodingTheory/HiddenDerivative/Parameters/Johnson/FiniteBounds.lean`) | Proved: the mutual correlated agreement of the affine line `u₀ + x·u₁` at radius `1 − √ρ − η`, any finite field, with a constant that `johnsonExceptionCount_le_comparisonEstimate` bounds by `johnsonComparisonEstimate n D η`, which is Annex B's `a` (`thm:mca-johnson`). Together they inhabit `McaJohnson` (Layer 11). The admitted `rs_mcaError_le_in_johnson_range` (`ProximityGap/CapacityBounds.lean`) is not consumed. |
| `Code.agreementSet_finite_and_ncard_le_pairwiseJohnson`, `Code.pairwiseJohnsonListBound` (`Data/CodingTheory/JohnsonBound/Pairwise.lean`); `ReedSolomon.code`, `mem_code_iff_eval` (`Data/CodingTheory/ReedSolomon.lean`) | Proved: at most `⌊n(A − D)/(A² − nD)⌋` words of any code over any alphabet agree with a word on `A` positions when two codewords agree on at most `D`; the Reed–Solomon code as the evaluations of the polynomials of degree below `k`. They give `ListBound`, and the encoder's code as ArkLib's (Layer 11). |
| `RingSwitchingProfile`, `tensorProductProfile` (`ProofSystem/Binius/RingSwitching/`) | The profile structure only, for #3; ArkLib's ring-switching protocol is another protocol. |
| `ToyProblem.Codegen` (`ProofSystem/ToyProblem/Codegen.lean`) | The pattern for code-generation probes of `verify` and the honest prover. |

### VCVio, CompPoly, Clean, Mathlib

| Declaration | Contract used here |
| --- | --- |
| `SampleableType`, `uniformSample`, `$ᵗ` (VCVio `OracleComp/Constructions/SampleableType`) | Challenge sampling; Layer 0 supplies the `E` instance, built from the `K` one. |
| `OracleSpec.randomOracle`, `cachingLoggingOracle`, `QueryCache`, `QueryLog`, `withQueryLog`, `IsTotalQueryBound`, `IsUniformSpec.ofFintypeInhabited`, `𝒟`, `probEvent` (VCVio `OracleComp/QueryTracking/`, `EvalDist/`) | The hash oracle answered lazily and uniformly from a cache, the ordered logs the extractor and the charged invariant read, the query bound of an adversary, and the distribution of a run: the random-oracle model of Layer 12. |
| `NodeQueryModel`, `Skeleton.perfect`, `BatchOpening`, `getPutativeBatchRootWithHash` (VCVio `CryptoFoundations/MerkleTree/`) | Binary Merkle trees whose node hash is a query to one function, and path-pruned openings of several leaves. Layer 11 reads its trees as these (decision 32); no proof here depends on the reading. |
| `BF64`, `BF64.Ext3`, `card_bf64`, `card_ext3`, `Ext.coeff`, `Ext.ofFn` (CompPoly) | As in the leanISA roadmap; `Fintype.card E = 2^192` is the only cardinality fact the errors use. |
| `CMlPolynomialEval R n`, `evalMle`, `evalMleLayer`, `eval₂Mle`, `eqTilde`, `lagrangeBasis`, `evalManyMleByLayers` (CompPoly `Multilinear/`) | Hypercube tables and their multilinear evaluation, computable; `eval₂Mle` is the `K → E` lift. |
| `CMvPolynomial`, `CPolynomial` (CompPoly) | Constraint and flush polynomials of the instance; round polynomials. The conversion to Mathlib's `MvPolynomial` is noncomputable, so Layer 2 translates Clean expressions directly and proves the translation equal to Clean's polynomial. |
| `AdditiveNTT` (CompPoly `Fields/Binary/AdditiveNTT/`) | The novel basis and the encoder of Annex B, generic over a basis; instantiated only at `GF(2^8)`, so Layer 11 supplies the `K` basis. |
| `Expression`, `Expression.eval`, `Operations.constraints`, `Operations.interactions`, `AbstractInteraction`, `EnsembleWitness`, `Table.environment`, `Environment.fromArray` (Clean `Circuit/`, `Air/`) | Constraints and flushes as syntax over the row's variables (out-of-range variables read `0`); the witness. Clean's own balance over `K` is vacuous (#16), so `SatisfiedBy` uses `BalancedPair`. |
| `Expression.degreeBound`, `Expression.WithinWidth`, `Expression.toBoundedPolynomial` (Clean `Circuit/ExpressionPolynomial`, held as a local copy until the pin contains it) | An expression's syntactic degree, the claim that its variables lie below a width, and its noncomputable Mathlib polynomial in that many variables; Layer 2's computable translation is proved equal to it. |
| `MvPolynomial`, `Polynomial.card_roots'`, `UniqueFactorizationMonoid`, `Multiset.prod` (Mathlib) | Degrees and root counts behind every Schwartz–Zippel step; Lemma 5.2 by unique factorization. |

### The upstream ledger

What this roadmap needs that is admitted or absent upstream at the pin, what replaces it here,
and when the local copy goes. Nothing is worked around by a hypothesis.

| Needed | Upstream at the pin | Action here |
| --- | --- | --- |
| Knowledge-soundness composition (a guarded first verifier) | admitted at the pin (`Append/Security.lean`; issue #676); ArkLib #1295, merged after the pin, proves it with the names and content of the local port | Proved locally: `ToArkLib/KnowledgeAppend.lean`, the port of #615's `Append/Knowledge.lean`. Replaced by a verbatim copy of #1295's modules at its next refactor, and deleted at the bump that contains #1295, its consumers moving to the upstream names. |
| Round-by-round implies plain | admitted; ArkLib #1245 proves the soundness half for a stateless shared oracle and refutes it otherwise | Not consumed: the random-oracle theorems read the worst-case round-by-round form one squeeze at a time (Layer 12), and no theorem here needs the plain form. |
| A knowledge notion in the typed framework | absent at the pin; on ArkLib's main since #1259–#1261 | The spine stays on `OracleReduction` (decision 24); the bump that brings #1259–#1261 is when decision 24 is revisited. |
| Sumcheck, both leanVM variants, with round-by-round knowledge | the classical leaf `Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundness` is admitted and false as stated (its verifier reads the input polynomial for its next target; ArkLib #1244 repairs it); the typed sumcheck (`Sumcheck/Interaction/`) is one polynomial, plain soundness, no extractor | Written here (Layer 4), with their knowledge leaves; nothing contributed upstream until ArkLib has a knowledge notion for the sumcheck (decision 33). |
| Batching by powers | absent (#615's `gammaPowers` is a lemma, not a reduction) | Written here (Layer 4); offered upstream as its own pull request. |
| Fingerprint, product lemma, collision bound | absent; ArkLib issue #901 | Written here (Layer 5). |
| Grand-product GKR | absent (#818 is a circuit GKR, radix 2, completeness only) | Written here (Layer 5); #818 is a pattern. |
| Context lifting | admitted | Not consumed: the GKR takes its leaves as functions of the context (decision 17). |
| Stacking | absent; ArkLib issue #900 | Built here (`ToCompPoly/`); CompPoly's candidates. |
| The inner-product oracle | absent and unplanned | Written here (Layer 0, `ToArkLib/`); offered upstream. |
| WHIR over binary Reed–Solomon codes | absent (#383 binary Basefold and #992 FRI, both legacy and open, are patterns) | Written here (Layer 11). |
| Merkle trees | in VCVio, proved: completeness, and extraction for a sequence of commitments with pruned openings (`MultiExtractability/`; VCVio issue 571). Every extraction theorem takes leaves that are digests and an adversary that draws no coins; `Hashing/Defs.lean` hashes leaves in a tagged domain and proves binding only | Read, not consumed (decisions 32, 39): `merkle_fits` reads the Rust's trees as VCVio's, a cross-check. Binding with hashed leaves on the one shared function is proved here by replaying the log (`ToVCVio/MerkleLog.lean`, Layer 12), and deleted when VCVio proves it. |
| Correlated agreement up to Johnson | `ReedSolomon.mcaError_affineLine_johnson_le` proved, any characteristic, with its constant bounded by [BCHKS25]'s printed one (`johnsonExceptionCount_le_comparisonEstimate`); `rs_mcaError_le_in_johnson_range` admitted; the capacity-range theorems exclude characteristic two | `McaJohnson` at Annex B's constant, inhabited from the proved theorem (Layer 11, decision 35); it meets Annex B's per-level budget at every deployed level ([whir-mca-budget.md](../reviews/whir-mca-budget.md)). The admitted theorem is not consumed. The interface, its inhabitant at [BCHKS25]'s constant, the fold line's error and the count of bad seeds are written here (`ToArkLib/McaJohnson.lean`) and proposed to ArkLib. |
| Fiat–Shamir, BCS | `fiatShamir_completeness` admitted and for a constant oracle; `BCSTransform` commented out; `Commitment.extractability` has body `False`; the legacy state-restoration game cannot be stated for this protocol (Layer 12); #848 and #469 are single-salt and duplex-sponge Fiat–Shamir with no proof of work; #627 is a design issue. Merged after the pin: #1263, #1264 (state-restoration knowledge soundness from local round-by-round certificates, in the typed framework). Open: #1267–#1283 (cached query budgets, the Merkle terminal batch in the random-oracle model, single-salt Fiat–Shamir) | Proved here (Layer 12) by the direct route (decision 36): `core` and `misbehaves_rom` on the one hash oracle, the charged invariant (`ToVCVio/ChargedInvariant.lean`) the one generic lemma. #1263 and #1264 are a pattern only. |
| Fresh-query bounds for the random oracle | absent at the pin; VCVio #817 gives the laws of the scalar expectation `∫⁻ r, r ∂𝒟[f <$> mx]`; VCVio #823, #824, #826 and #828 bound fresh queries with a fixed error per key | #817 is copied verbatim as `ToVCVio/ScalarExpectation.lean` and deleted at the bump that contains it. #823–#828 are not copied: their per-key errors cannot depend on the cache, which the flip charge does. The charged invariant is written here (`ToVCVio/ChargedInvariant.lean`), a VCVio candidate. |
| Ring switching for `GF(2) → K` | the profile structure; every security leaf admitted; the protocol is Diamond–Posen's, not leanVM's | #3's; the profile structure only is consumed. |
| Clean expressions as polynomials | on Clean's main since #466 (2026-10-05), but in no revision built for Lean 4.34 (Clean #474, the port, does not contain it) | `ToClean/ExpressionPolynomial.lean` is a verbatim copy of Clean's module; deleted when the pin contains #466 and its file is still `b449bf59`'s, its importer then importing `Clean.Circuit.ExpressionPolynomial` and the aggregate dropping it. The computable translation and the component tables (`ToClean/ComponentPolynomial.lean`) are written over Clean's names and stay. |
| Balance counted in ℕ, direction-tagged | absent; Clean #464, #20 | leanISA's `BalancedPair` stands in. |
| Fixed columns, sound prover data | absent; Clean #446, #23 | The instance states them as known coordinates (`Coord.known`). |

## Pinned conventions

| Subject | Convention |
| --- | --- |
| Hypercube | `Fin (2^n)` indexes `{0,1}^n` with bit `k` = coordinate `k` (low bit first), the CompPoly and leanVM order. A point is `Vector E n`. |
| Tables | `Column n` wraps `CMlPolynomialEval K n` in a structure, so that its oracle interface is not ArkLib's position-query interface on `Vector`; a table over `E` is `CMlPolynomialEval E n` (`ETable n` below). Its extension is `evalMle`, lifted by `eval₂Mle` when the point is in `E`. |
| `eq` | `eq(r, x) = ∏ (1 + r_k + x_k)` over `E` (characteristic 2); on the cube, CompPoly's `lagrangeBasis r`. |
| The oracle | One committed oracle, the stack `q : Column μ_stack`, for the whole protocol, with the inner-product interface: a query is a `Weight μ` (a table `W` over the cube with an evaluator of its extension, specification Definition 3.13), the answer `⟨W, q⟩ = Σ_w W(w)·q(w)`; an evaluation `q̃(r)` is the query `eqWeight r`. No phase before the opening queries the stack, since each is a `Phase.FrontDef` (decision 31); the opening queries it once. The compilation depends on both. WHIR's codewords appear only in Layer 11. |
| Sumcheck variants | *Plain*: the round message is the polynomial of degree `d`, error `d/|F|` per round, the verifier evaluating the equality factors at the end (the table sumcheck). *Normalized*: the round message is the cofactor `h` of degree `d_c`, the verifier checks `(1 + r_t)·h(0) + r_t·h(1)` against the running claim, `r_t` the point's coordinate, the new claim is `h(χ_t)`, and the final check has no equality factor; error `d_c/|F|` (the GKR layers). |
| Sumcheck messages | The oracle protocol sends every coefficient, low degree first, and its verifier checks each round. The wire drops one (`c_1` for the plain table sumcheck, `c_0` for the normalized GKR round), which the compiled verifier derives from the running claim, so no round check remains (`transcript.rs:289-309`). Layer 4 proves the transport lemma: a verifier composed with an injective decoding of wire messages onto the messages passing its round check keeps its round-by-round knowledge soundness at the same error, with the state function composed with the decoding. Fiat–Shamir absorbs the encoded message (decision 26). |
| Statements and parameters | The public `input : I.Stmt` is the statement of the oracle protocol, and the instance `I` (for leanISA: the program and the announced sizes) indexes the protocol family; a phase's input statement carries only what earlier phases produced. The sizes are the prover's: the compiled verifier reads them, checks them against the caps and the windows before the protocol starts, and the non-interactive theorem is stated for the family, its error the maximum over admissible sizes, the challenge oracle taking the announced sizes with the statement (decision 29). |
| Errors | `ℝ≥0` per challenge, ArkLib's form. The spine fixes each phase's error as a closed form of the instance's sizes and demands each phase's knowledge soundness at it; no phase declares its own, since a declared error of 1 makes the knowledge theorem hold of a phase that checks nothing (decision 20). `piopError_le` bounds the sum at admissible sizes. `|E|` is `Fintype.card E`, rewritten to `2^192` only in the numeric test. |
| Bus | Width `m = 16`; coordinate 0 is the separator `g^0 / g^1 / g^2` for state, memory, bytecode; coordinates follow the specification's tuple order; unused coordinates are the constant `0`. Fingerprint `π_α(t) = Σ_{i<16} eq(α, bits i)·t_i` with `α : Fin 4 → E`; leaf `β − π_α(t)`, padding leaf `1`. |
| Count tree | Leaves are the tables' count columns (`α = β = 0`), padded with `1` to the depth of the push tree; the finalize counts are not in it (`layout.rs:412-414`). |
| GKR | Radix 4 from the root down; if `μ` is odd, one radix-2 layer first. The layer sumcheck is normalized: the cofactor has degree 4 (degree 2 in the radix-2 layer), four coefficients travel, the constant one is derived. A combiner `λ` is drawn after the roots and after every layer, the last included: the last is used by nothing, has error 0, and still changes every later challenge. Two combination challenges `u_0, u_1` after each radix-4 layer, one after the radix-2 layer. The three trees share every challenge and end at one point `ζ = (u_0, u_1, χ_0, …)` of the last layer, coordinate 0 the lowest bit of the leaf index (`gkr.rs:247-430`). |
| Leaf stacks | Per side, the boundary blocks of that side in the order of `I.boundary` (state, memory, bytecode), then each table's flushes of that side in order; the count side one block per count column in the order of `I.counts`. Stacked largest first at aligned offsets, ties by that index, no floor on the depth; the depth of the three trees is the push side's (`layout.rs:354-415`, `leaf.rs:149-156`). The spine's `tuples` lists flushes first, which is immaterial to `Balanced` and not the leaf order. |
| Stacks | Blocks ordered largest first at aligned offsets; `sel_b = offset_b >> κ_b`; `q̃(z, sel_b) = P̃_b(z)`. Blocks of equal size keep the order of the column index, which puts the six shared columns first, `mem_0, mem_1, mem_2`, `cntfin_mem`, `cntfin_bc`, `q_flock`, then every table's columns in table order (`witness.rs:67-79`, `cpu/layout.rs:13-49`). The eighteen BLAKE2S limb columns are strided slots of `q_flock`, not blocks. `μ_stack ∈ [15, 28]`. |
| Table sumcheck | It ranges over the *sumcheck tables*, those with a constraint, a flush or a count column (for leanISA the six opcode tables, never the column groups of the shared columns); `τ_max` is the largest log-height among them, and the final message has one value per column of each, table by table. Variables bound highest first; table `j` joins at round `τ_max − τ_j`, its summand padded by `∏_{k ≥ τ_j} X_k`; round polynomials have degree 3; `ξ` powers: constraints table by table, then the three bus sides `[push, pull, count]` sharing the last three powers; the target is derived by the verifier, never sent. |
| Claim pool order | The bus phase's column claims, then per-table column claims, then the three public-input claims (`cpu/mod.rs:656-667`), then Flock's; ring-switched claims take the low powers of `λ`, point claims the high ones (`stack_open.rs:400-401, 518-519`). |
| Fiat–Shamir | Every step is BLAKE2s-256 of 64 bytes, the chain state followed by a block: the RFC compression `F(paramIV, cv ‖ block, t = 64, f_0 = 1)` with the chain state in the message, not in the chaining value. Block lane 3 carries the tag `1` (observe), `2` (squeeze), `3` (grinding base), `4` (grinding nonce); no labels. Seeded from `"leanvm" ‖ len ‖ R1CS_DIGEST ‖ bytecodeHash` and the public input; one squeeze yields one `E` challenge (three low words); every WHIR level grinds 17 bits before its queries (`fiat_shamir/src/lib.rs:18-174`, `cpu/mod.rs:82-124`). |
| Verifier shape | `verify` is a total, computable function of a typed `Program`, a typed `PublicInput` and a `Proof`, to `Bool`; a malformed proof is `false`. The deployed rejection of a public word with a nonzero third limb, and of a bytecode that is not `2^k ≤ 2^32` decodable instructions, is the obligation of whoever builds those values from bytes (the fixture's loader, T7's encoding); the fixture records such an input as a parse failure, not as `verify = false`. |
| Load-bearing checks | Every check of a phase's verifier comes with a theorem that the verifier without it (or with it weakened) has no round-by-round knowledge soundness at the phase's seams below error 1, whatever the extractor; every check the deployed verifier does not make comes with a theorem that the verifier with it is not perfectly complete. A check is load-bearing only if the verifier commits to what it checked: a claim pooled from a prover's message pools the value *sent*. A check whose omission cannot be refuted is one the design does not rely on, and the design is revised until it does. The generic lemmas (`not_rbr`, `not_perfectCompleteness`) live in `ToArkLib/`; the refutations are tests, listed in the phase's pull request. |
| Trusted surface | Every trusted definition fits on one screen, cites its source line, and appears in [Interfaces](#interfaces-supplied-to-later-work); assumed interfaces are structures whose docstring names the owner and the witness obligation, never `variable`-block hypotheses or `axiom`s. The instance is trusted data: the spine proves nothing of it beyond its layout law, and the master theorems hold of instances whose relation is empty; the leanISA instance's non-vacuity is `m3Holds_stackOf`, its faithfulness the fixture of Layer 12. |
| Unproved targets | A statement whose dependency is not yet available is a block comment at its place, with the statement and the dependency. Never `sorry`. |
| Generic code | A definition or theorem that belongs upstream lives under `LeanerVM/Protocol/ToArkLib/`, `ToClean/`, `ToCompPoly/` or `ToVCVio/` (or `LeanerVM/Parameters/To<Library>/` when a lower layer must import it), by the library that owns its objects (read off its imports), in a module of its own saying it is a candidate for that library; the local copy is deleted in the pull request that moves the pin past its upstream merge. It is written for that library's other consumers: general definitions and helper lemmas, no special case the protocol chose (a slot, a pad value, a particular point) and no protocol vocabulary; the special case is derived in a leanVM module, which cites the specification. Comments everywhere are brief and self-contained and never cite this roadmap. |
| Module system | Production files, including Clean bridges, are modules; kernel-evaluation tests and root aggregates stay classic. The spine carries polynomials and tables, never a Clean circuit. |
| The wall | Every module of the proof system is written over an abstract `I : M3Instance` and imports nothing from `LeanerVM/Arithmetization/`, except the fixed columns (`FixedColumns.lean`), the adaptor (Layer 3), the compiled verifier (Layer 12) and the base theorems (Layer 13). `scripts/check-layers.sh` enforces it with that allow-list, and the policy tests plant a violation. A leanISA change touches the leanISA instance, the adaptor and T1, and nothing else. |
| Holes | A phase or generic component is three structures. `X.Def`: the reduction, computable, with no error in it. `X.Guarded`: the prover's output is pure and the verifier is a guard followed by a verdict. `X.Complete` extends `Guarded` with perfect completeness; `X.Security` extends `Guarded` with an extractor, a knowledge state function and `rbrKnowledgeSoundnessWorstCaseWith` at the spine's error, so that knowledge soundness does not presuppose completeness (decision 23). A `Def` lands with its `Complete` and an honest run on the toy instance; its `Security` may land later; neither contains `sorry`. Until every hole is filled, the fields of `Phases.Complete` and `Phases.Security` are assumed interfaces. |
| Seams | The output relation of a phase is the input relation of the next, by definition (`Seam.*`), never by a bridge lemma (test 26). The bus seam carries the point the bus phase ended at, since the table sumcheck runs at it, and the forms the bus phase built, their row polynomials of degree at most `I.d` by type. The zerocheck escape, "violated on the cube, zero at `ζ`", is carried by the bus phase's state function as one more conjunct (every constraint extension, restricted to the coordinates of `ζ` drawn so far, is identically zero), which a coordinate makes true with probability at most `1/|E|` whatever the number of constraints: the bus phase's error has no term for it. |
| Extractors | Every extractor is a computable definition, checked by a `def` without `noncomputable` at each `Security`. The protocol's is `piopExtractor`; the stack it extracts is `piopExtractedStack`, the fold of the phases' extractors down to the commit round, which equals the committed message on every transcript; the adaptor applies `witnessOf` to it. Knowledge soundness of `verify` is claimed in the information-theoretic sense (Lean does not measure running time); the compiled extractor takes a `ListDecoder`, whose brute-force inhabitant computes and whose efficient inhabitants are refinements (Layer 12). |
| Public input | The statement fixes *lines*, not cells: a `PublicLine` is a column with the values its cells 0 and 1 must hold, the shape §8.2 checks with one challenge on the line through the two cells. A line says whether the proof carries its value (`sent`); the verifier checks the values sent and pools, for a line whose value is sent, the value sent. The leanISA instance has three lines, on `mem_0, mem_1, mem_2`, the first two sent and the third with cells `0, 0`; the choice is pinned by a `#guard` on the leanISA instance's lines and by the fixture, which reads exactly two scalars. |

## The spine

The spine fixes everything two neighbouring pieces of work would otherwise have to agree on, and
proves the composition once. It lives under `LeanerVM/Protocol/Spine/` (`Instance`, `Seams`,
`Phase`, `Compose`, `Toy`) and, for the parts that belong in ArkLib, `LeanerVM/Protocol/ToArkLib/`
(`Oracles`, `Component`, `KnowledgeAppend`, `PassThrough`, `SendOracle`, `GuardedVerdict`,
`KeepOracles`, `Refinement`), with its tests in `tests/LeanerVMTests/Protocol/Spine.lean`. After
it, every phase, generic component, the instance and the compilation is a unit of work that
consumes spine names only, is tested on the toy instance, and lands in two halves. It restates the
shape of leanth's explore branch (a `Type 0` witness, a relation anchored to Clean, a commit stage
pinning the oracle to the witness of record, the zerocheck point carried between stages, an
abstract commitment boundary) and drops its two defects: an extractor chosen classically, and a
balance summed in the field.

### The relation ladder

| Relation | Witness | Where | What it says |
| --- | --- | --- | --- |
| `Ensemble.Statement ens pi` | `EnsembleWitness ens`, in `Type 1` | Clean | every row satisfies its component's constraints and every channel balances, multiplicities summed in the field. Over `K` the sum accepts a tuple pushed twice and never pulled, and the side condition `length < ringChar K` admits at most one interaction per channel, so it holds of no ensemble with a real bus (#16). Unusable here. |
| `SatisfiedBy prog input w` | `EnsembleWitness (leanIsaEnsemble prog)` | leanISA Layer 8 | Clean's constraints and public input; three `BalancedPair`s counted in ℕ; `CountsNonzero`, `Caps`; the three fixed-column facts; `Blake2sRowsValid`; the two public words. T1's relation. |
| `M3Holds I input q` | `q : Column I.μ`, in `Type 0` | the spine | what the verifier establishes about the stack. The protocol's relation. |
| `ValidExecution prog input t` | a trace | leanISA Layer 3 | T1's target; never the protocol's relation. |

The adaptor joins the middle two: `witnessOf` with `satisfiedBy_witnessOf : M3Holds →
SatisfiedBy`, along which knowledge transports at the same error by
`Refinement.knowledge_transport`, and `stackOf` with `m3Holds_stackOf`, which completeness needs.
ArkLib's statement and witness types are in `Type`, so an `EnsembleWitness` cannot be the
protocol's witness, and the stack can.

### The picture

```text
                    ┌──────────────────────── Semantics ────────────────────────┐
                    │  ValidExecution prog input t              (leanISA Layer 3)│
                    └───────────────────────────▲───────────────────────────────┘
                                                │ T1: constraintSoundness / constraintCompleteness
                    ┌───────────────────────────┴───────────────────────────────┐
                    │  SatisfiedBy prog input w,  w : EnsembleWitness   (Type 1) │  leanISA Layer 8
                    └───────────────────────────▲───────────────────────────────┘
   opcode tables,                               │  THE ADAPTOR (a Refinement, both directions)  Layer 3
   memory/bytecode/     witnessOf : Column μ → EnsembleWitness    satisfiedBy_witnessOf : M3Holds → SatisfiedBy
   verifier rows ──▶    stackOf   : EnsembleWitness → Column μ    m3Holds_stackOf     : SatisfiedBy → M3Holds
   (Layers 2, 3)                                │
   leanIsaInstance I ═══ the wall ══════════════╪══════  nothing above imports leanISA
                    ┌───────────────────────────┴───────────────────────────────┐
                    │  M3Holds I input q,   q : Column μ   (Type 0)              │  seam 0
                    ├───────────────────────────────────────────────────────────┤
                    │  commit ⟫ bus ⟫ table ⟫ public ⟫ flock ⟫ opening          │  the spine: seams,
                    │  Seam.bus  Seam.table  Seam.pub  Seam.flock  Seam.done     │  schedules, errors
                    ├───────────────────────────────────────────────────────────┤
                    │  piop_perfectCompleteness   piop_rbrKnowledgeSoundness     │  ideal oracle model,
                    │  at piopError I, extractor piopExtractor                   │  inner-product oracle
                    └───────────────────────────▲───────────────────────────────┘
                                                │  list binding, Merkle binding by log replay, the chain (Layer 12)
                    ┌───────────────────────────┴───────────────────────────────┐
                    │  verify : Program → PublicInput → Proof → Bool             │
                    │  core: accepts ∧ no witness extracted ⇒ HashMisbehaves     │
                    │  misbehaves_rom: Pr[HashMisbehaves] ≤ niError ε V Q (ROM)  │
                    │  at BLAKE2s: the hypothesis BlakeMisbehaves                │
                    └───────────────────────────────────────────────────────────┘
   T4  =  core  ∘  satisfiedBy_witnessOf  ∘  TraceExtraction.valid  (leanISA's),
          at BLAKE2s under BlakeMisbehaves
```

### What the spine fixes

1. **The abstract instance**, `M3Instance`: what every phase reads and nothing more, including a
   degree bound `d` with its two proofs, the *sumcheck tables* (a decidable predicate: a table
   with a constraint, a flush or a count column; the others are column groups, which take no part
   in the table sumcheck), and the Flock region where there is one (the column, the log-count of
   compressions, its height, and the predicate the auxiliary clause asserts of it; the toy has
   none). An instance is trusted data:
   the spine proves nothing of it beyond its layout law, and the master theorems hold of instances
   whose relation is empty. For leanISA its non-vacuity is `m3Holds_stackOf` and its faithfulness
   the fixture of Layer 12.
2. **The relation on the stack**, `M3Holds`, and its ArkLib form `M3Rel`.
3. **The seams**: the output relation of each phase, which is the input relation of the next by
   definition. They are the load-bearing definitions of the proof system and get the spine's
   review budget.
4. **The schedule and the error of every slot** as closed forms of the instance's sizes
   (decision 20): each phase's `Security` is at its slot's error, and `piopError I` is their
   concatenation, so no phase declares its own. The per-challenge errors are those of the layer
   sections: the bus phase `4·2^{μ_bus}/|E|` on `(α, β)` then `gkrError`; the table sumcheck
   `(B + 2)/|E|` on `ξ` and `3/|E|` per round; the public input `1/|E|`; Flock `flockError`; the
   opening `(J − 1)/|E|` on `λ`. `piopError_le` bounds their sum at admissible sizes.
5. **The hole interfaces**: per phase and per generic component a `Def` (the reduction, no
   error), a `Guarded` (output purity, derived for an empty shared oracle, and the verifier's
   guarded form), a `Complete` and a `Security` extending `Guarded` (`Component.*`, specialised to
   the one oracle as `Phase.*`); a `Security` carries its extractor, its knowledge state function
   and the bound at a given error. The knowledge-soundness composition ArkLib admits is ported
   from ArkLib #615 and proved here (`ToArkLib/KnowledgeAppend.lean`).
6. **The composition** `leanVmPiop` over a bundle `Phases I`, its extractor `piopExtractor` (the
   commit phase's followed by the phases', appended through the verdicts), the extracted stack
   `piopExtractedStack` with `piopExtractedStack_eq` (it is the committed message on every
   transcript), and the two master theorems, each conditional on the phases only. The commit
   phase is the spine's, both halves proved at error 0. The four phases before the opening are
   `Phase.FrontDef`s, whose verifier never reads the stack (decision 31).
7. **The toy instance** (one table of width 3 and height 2 on a stack of height 8: one
   constraint, one push, one boundary pull, one count column, one public line; `aux := True`, no
   Flock region) with an honest stack and, for each of the four checkable clauses, a stack failing
   it alone.

```lean
-- Spine/Instance.lean (module): the instance and the relation
inductive Side | push | pull
structure Shape where (ntab : ℕ) (τ width : Fin ntab → ℕ)
abbrev Shape.ColumnId (S : Shape) := Σ j : Fin S.ntab, Fin (S.width j)
structure Layout (μ) (ι) (κ : ι → ℕ) where               -- one datum and one law
  extend : (c : ι) → Vector E (κ c) → Vector E μ          -- z ↦ (z, sel_c), or a strided slot
  extend_cube : …                                         -- a cube point of a block goes to a cube point of the stack
def Layout.read (L) (q : Column μ) (c) : Column (κ c)      -- defined from `extend`
theorem Layout.read_eval : eval₂Mle (L.read q c) z = eval₂Mle q (L.extend c z)
inductive Coord (S : Shape) κ | const (c : K) | known (col : Column κ) | committed (c : S.ColumnId) (h : S.τ c.1 = κ)
structure BoundaryBlock (S : Shape) where (κ : ℕ) (side : Side) (coords : Vector (Coord S κ) 16)
structure PublicLine (S : Shape) where (col : S.ColumnId) (cell0 cell1 : K) (sent : Bool) (pos : 0 < S.τ col.1)
structure M3Instance extends Shape where
  Stmt : Type
  constraints : (j) → List (CMvPolynomial (width j) K)
  flushes : (j) → List (Side × Vector (CMvPolynomial (width j) K) 16)   -- separator first
  d : ℕ ; constraints_degree : … ≤ d ; flushes_degree : … ≤ d          -- leanVM: d = 2
  counts : (j) → List (Fin (width j))
  boundary : List (BoundaryBlock toShape)
  μ : ℕ ; layout : Layout μ toShape.ColumnId (fun c ↦ τ c.1)
  publicLines : Stmt → List (PublicLine toShape)
  flock : Option (FlockRegion toShape)                                  -- none for the toy
structure FlockRegion (S : Shape) where                                -- where the packed BLAKE2s witness sits
  col : S.ColumnId ; kBatch : ℕ ; height : S.τ col.1 = 8 + kBatch
  Holds : Column (8 + kBatch) → Prop ; decHolds : DecidablePred Holds   -- the Flock predicate (FlockSpec.Holds)
def M3Instance.aux I (q) : Prop := ∀ r ∈ I.flock, r.Holds (I.column q r.col)   -- what the Flock phase establishes
def M3Instance.SumcheckTable I (j) : Prop := I.constraints j ≠ [] ∨ I.flushes j ≠ [] ∨ I.counts j ≠ []
def M3Instance.τmax I ; def M3Instance.μBus I ; def M3Instance.B I    -- over the sumcheck tables
def M3Instance.ConstraintsVanish I q ; Balanced I q (List.Perm) ; CountsNonzero I q ; PublicLinesHold I input q
def M3Holds I input q : Prop :=
  I.ConstraintsVanish q ∧ I.Balanced q ∧ I.CountsNonzero q ∧ I.PublicLinesHold input q ∧ I.aux q
abbrev NoOracle ; abbrev TheOracle I : Fin 1 → Type := fun _ ↦ Column I.μ
def M3Rel I : Set ((I.Stmt × ∀ i, NoOracle i) × Column I.μ) := {p | M3Holds I p.1.1 p.2}

-- Spine/Seams.lean: the claims and the seam relations
abbrev M3Instance.RowPoly I j := {p : CMvPolynomial (I.width j) K // p.totalDegree ≤ I.d}
abbrev M3Instance.Form I j := List (E × I.RowPoly j)                  -- Σ weight · (poly on the row)
structure ColumnClaim I where (col : I.ColumnId) (point : Vector E (I.κ col)) (value : E)
structure WeightedClaim I where (weight : Weight I.μ) (value : E)    -- ⟨W, q⟩ = value; Weight is Layer 0's
structure BusOut I where                                             -- the Rust's BusVerify
  point : Vector E I.τmax                                            -- ζ_{<τ_max}
  forms : Fin 3 → (j : I.SumcheckTable) → I.Form j                   -- push, pull, count
  totals : Fin 3 → E
  columns : List (ColumnClaim I)
structure TableOut I where (columns : List (ColumnClaim I))
structure PubOut I where (columns : List (ColumnClaim I))
structure FlockOut I where (columns : List (ColumnClaim I)) (weighted : List (WeightedClaim I))
def Seam.commit I := Seam.of I (M3Holds I)
def Seam.bus I := Seam.of I fun (s : I.Stmt × BusOut I) q ↦
  (every constraint of every sumcheck table j has extension 0 at s.2.point_{<τ_j}) ∧
  (∀ side, Σ_j (s.2.forms side j)~(s.2.point_{<τ_j}) = s.2.totals side) ∧
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q
def Seam.table I (claims ∧ lines ∧ aux) ; Seam.pub I (claims ∧ aux) ; Seam.flock I (claims) ; Seam.done I (True)

-- Spine/Errors.lean: the schedules and errors of the slots
def busSpec I ; tableSpec I ; pubSpec I ; flockSpec I ; openingSpec I ; piopSpec I   -- the last: commit, then the five
def busError I ; tableError I ; pubError I ; flockError I ; openingError I
def piopError I : (piopSpec I).ChallengeIdx → ℝ≥0                    -- their concatenation
theorem piopError_le (h : I's sizes admissible) : Σ i, piopError I i ≤ …

-- ToArkLib/Component.lean: the hole interfaces (ArkLib candidate)
structure Component.Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut (pSpec) where
  red : OracleReduction []ₒ StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec   -- computable; no error
structure Component.Guarded (D) where guarded : D.red.toReduction.verifier.GuardedForm
structure Component.Complete (D) (relIn relOut) extends Guarded D where
  complete : ∀ {σ} init impl, D.red.perfectCompleteness init impl relIn relOut
structure Component.Security (D) (relIn relOut) (err : pSpec.ChallengeIdx → ℝ≥0) extends Guarded D where
  witMid ; extractor : Extractor.RoundByRound … ; kSF : … KnowledgeStateFunction …
  rbr : ∀ {σ} init impl, … rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut witMid extractor (kSF init impl) err
def Component.Def.append ; Component.Complete.append ; Component.Security.append   -- the last without completeness
-- ToArkLib/KnowledgeAppend.lean: the port of ArkLib #615's Append/Knowledge.lean
def Verifier.KnowledgeStateFunction.appendGuarded ; theorem Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
-- ToArkLib/PassThrough.lean, SendOracle.lean, GuardedVerdict.lean, KeepOracles.lean
def Component.passThrough ; Component.sendOracle ; keepOracles ; Verifier.GuardedForm.of_probEvent_pos ; …

-- Spine/Phase.lean: a phase is a component over the stack
abbrev Phase.Def I StmtIn StmtOut pSpec ; abbrev Phase.Complete ; abbrev Phase.Security
structure Phase.FrontDef I StmtIn StmtOut pSpec     -- a phase whose verifier never reads the stack; .toDef the phase

-- Spine/Compose.lean: the commit phase, the bundle, the master theorems
abbrev commitDef I := Component.sendOracle I.Stmt (Column I.μ) ; def commitComplete I ; def commitSecurity I   -- error 0
structure Phases I where
  bus : Phase.FrontDef I I.Stmt (I.Stmt × BusOut I) (busSpec I)
  table : Phase.FrontDef I (I.Stmt × BusOut I) (I.Stmt × TableOut I) (tableSpec I)
  pub : Phase.FrontDef I (I.Stmt × TableOut I) (I.Stmt × PubOut I) (pubSpec I)
  flock : Phase.FrontDef I (I.Stmt × PubOut I) (I.Stmt × FlockOut I) (flockSpec I)
  opening : Phase.Def I (I.Stmt × FlockOut I) Unit (openingSpec I)
structure Phases.Complete P ; structure Phases.Security P      -- bus : Phase.Security I P.bus.toDef (Seam.commit I) (Seam.bus I) (busError I), …
def leanVmPiop P ; leanVmVerifier P ; leanVmProver P ; piopExtractor P S
def piopExtractedStack P S : (I.Stmt × ∀ i, NoOracle i) → FullTranscript → Column I.μ
theorem piopExtractedStack_eq : piopExtractedStack P S s tr = tr ⟨0, _⟩
theorem piop_perfectCompleteness P (C : P.Complete) init impl :
    (leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I)
theorem piop_rbrKnowledgeSoundness P (S : P.Security) init impl :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel I) (Seam.done I)
      S.witMid (piopExtractor P S) (S.kSF init impl) (piopError I)

-- ToArkLib/Refinement.lean: the adaptor's generic half (ArkLib candidate)
structure Refinement (R : Set (Stmt × W₁)) (S : Set (Stmt × W₂)) where (map : Stmt → W₁ → W₂) (map_valid : …)
theorem Refinement.map_option_valid                 -- the honest direction
theorem Refinement.knowledge_transport (f : Refinement R S) (h : verifier.knowledgeSoundnessWith init impl R relOut E ε) :
    Pr[accepts ∧ ∀ w ∈ extracted, (stmt, f.map stmt w) ∉ S] ≤ ε   -- the event form, same game and extractor
```

`M3Holds` names the leanVM checks in the order the phases consume them; its five clauses leave
the caps out (decision 8): the compiled verifier rejects inadmissible sizes before the protocol
starts, and the adaptor's soundness takes admissibility as a hypothesis.

The bus seam carries the point the bus phase ended at, since the table sumcheck runs at it
(§5.5), and the forms the bus phase built; `α`, `β` and the leaf layout stay inside the bus phase.
A form is a list of weights in `E` against row polynomials over `K` whose degree is at most `I.d`
by type: the table sumcheck's round polynomials have degree `d + 1`, so its completeness is owed
only on terms within the bound, and a seam carrying terms of any degree, or any number of claims
at unrelated points, would owe the deployed table sumcheck guards leanVM does not have (the bus
seam bounds the degree, test 28). No polynomial with coefficients in `E` is built: the row
polynomials are the instance's, over `K`, and the weights carry `E`. The phases'
outputs are what their knowledge soundness forces, not what the seam's type allows.

The commit phase is ArkLib's `SendSingleWitness` shape with the stack as its one message; its
output relation is `M3Holds` on the oracle, and both halves are proved at error 0. The composed
extractor is ArkLib's `Extractor.RoundByRound.append`; its knowledge state function and bound are
the port's. The transport along the adaptor is `Refinement.knowledge_transport`: for the same
game, provers and extractor, accepting while the mapped extracted witness is invalid has
probability at most the knowledge error; it needs no prover conversion, since the game's witness
type is unchanged. The base theorems use the adaptor pointwise, `satisfiedBy_witnessOf` inside
their event (Layer 13), so they wait on no round-by-round-to-plain step (the ledger).

`piop_rbrKnowledgeSoundness_exists` (the extractor forgotten) is kept as the shortest statement to
read, but it is a soundness statement only (convention *Extractors*).

### The holes

A hole is a unit of work the spine leaves open: a phase, a generic component, the adaptor, or a
piece of the compilation. Every hole consumes spine names only, and its layer section is its
specification: what it produces, what it needs, its sources, its tests and the upstream work to
read first. The table lists every hole in build order. A name in bold is declared by this hole and
no other; the hole is built when the names in bold of its row are declared and match the section.

| Hole | Specified in | Produces | Needs |
| --- | --- | --- | --- |
| field instances | [Layer 0](#layer-0-the-arklib-dependency-and-the-field-instances) | **`instSampleableTypeE`**, **`card_E`**, `Weight`, `Weight.pair`, `eqWeight`, **`innerProductOracle`**, **`answer_eqWeight`** | nothing |
| the spine | [The spine](#the-spine) | everything under [What the spine fixes](#what-the-spine-fixes); marked by **`M3Holds`**, **`Phases`**, **`piopError_le`**, **`piopExtractedStack_eq`**, **`piop_perfectCompleteness`**, **`piop_rbrKnowledgeSoundness`**, **`Refinement.knowledge_transport`** (built, and off the base theorems' path) | field instances |
| the knowledge-soundness composition | [What the spine fixes](#what-the-spine-fixes), item 5 | **`Verifier.KnowledgeStateFunction.appendGuarded`**, **`Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`** (the port of ArkLib #615) | ArkLib only |
| tables and stacking | [Layer 1](#layer-1-hypercube-tables-stacking-the-strided-reader-the-index-and-bytecode-columns) | **`Blocks.stack_eval`**, **`Blocks.unstack_eval₂`**, **`Blocks.stack_eval_ambient`**, **`evalMle_boolVec_append`**, **`Blocks.layout`**, **`Blocks.stridedLayout`**, **`Layout.piecewise`**, **`ColumnClaim.holds_iff_weighted`**, **`idxColumn_eval`**, **`bytecodeColumn_answer_boolVec`**, `bytecodeColumn_eval` | field instances; the spine's `Layout` and claims |
| Clean expressions as polynomials | [Layer 2](#layer-2-clean-components-as-polynomials) | **`Expression.toCMvPolynomial`**, **`eval_toCMvPolynomial`**, `fromCMvPolynomial_toCMvPolynomial`, **`Component.toM3`**, **`toM3_constraints_iff`**, **`toM3_flushes_eq`** | Clean |
| the adaptor | [Layer 3](#layer-3-the-leanisa-instance-and-the-adaptor) | `Sizes`, **`Sizes.Admissible`**, `validRate`, **`leanIsaInstance`**, `Agrees`, **`tuples_perm`**, `stackOf`, `witnessOf`, **`satisfiedBy_witnessOf`**, **`m3Holds_stackOf`**, `witnessOf_stackOf` | the spine; Clean expressions as polynomials; tables and stacking; leanISA Layers 5–8; `FlockSpec` from #3 |
| sumcheck: definitions and completeness | [Layer 4](#layer-4-the-sumchecks-and-batching) | `Virtual`, **`Sumcheck.plain`**, **`Sumcheck.normalized`**, their `Complete`, **`Sumcheck.transport`** | nothing |
| sumcheck: knowledge soundness | [Layer 4](#layer-4-the-sumchecks-and-batching) | **`Sumcheck.plainSecurity`**, **`Sumcheck.normalizedSecurity`** | sumcheck: definitions and completeness |
| batching by powers | [Layer 4](#layer-4-the-sumchecks-and-batching) | **`batch`**, `batchComplete`, **`batchSecurity`** | nothing |
| fingerprint and collision bound | [Layer 5](#layer-5-fingerprints-the-grand-product-and-gkr) | `fingerprint`, `sideProduct`, **`sideProduct_poly_eq_iff`**, **`sideProduct_collision`** | nothing |
| grand-product GKR: definition and completeness | [Layer 5](#layer-5-fingerprints-the-grand-product-and-gkr) | **`gkr`**, `gkrError`, **`gkrComplete`** | sumcheck: definitions and completeness |
| grand-product GKR: knowledge soundness | [Layer 5](#layer-5-fingerprints-the-grand-product-and-gkr) | **`gkrSecurity`** | the GKR's definition; sumcheck: knowledge soundness |
| bus phase: definition and completeness | [Layer 6](#layer-6-the-bus-phase) | `pushLeaves`, `pullLeaves`, `countLeaves`, **`leaf_decomposition`**, **`busPhase`**, **`busComplete`** | the spine; the GKR's definition; tables and stacking |
| bus phase: knowledge soundness | [Layer 6](#layer-6-the-bus-phase) | **`busSecurity`** | the bus phase's definition; the GKR's knowledge soundness; fingerprint and collision bound |
| table sumcheck phase: definition and completeness | [Layer 7](#layer-7-the-table-sumcheck-phase) | `tableSummand`, **`tableSummand_target`**, **`tableSumcheck`**, **`tableSumcheckComplete`** | the spine; sumcheck: definitions and completeness |
| table sumcheck phase: knowledge soundness | [Layer 7](#layer-7-the-table-sumcheck-phase) | **`tableSumcheckSecurity`** | the table sumcheck's definition; sumcheck: knowledge soundness |
| public-input phase: the specification's check | [Layer 8](#layer-8-the-public-input-phase) | **`publicInputPhase`**, **`publicInputComplete`**, **`publicInputSecurity`**, **`PublicInput.pooledFrom`** | the spine; tables and stacking |
| public-input phase: the deployed check | [Layer 8](#layer-8-the-public-input-phase) | **`PublicInput.checkWords`**, **`PublicInput.accepts_two_challenges`**, **`deployedPublicInputPhase`**, **`deployedPublicInputComplete`**, **`deployedPublicInputSecurity`** | the specification's public-input phase |
| Flock phase: definition and completeness | [Layer 9](#layer-9-the-flock-phase) | `FlockSpec`, **`flockPhase`**, **`flockComplete`**, **`flockError_le`**, the constants in `Parameters/Flock.lean` | the spine |
| Flock phase: knowledge soundness | [Layer 9](#layer-9-the-flock-phase) | **`flockSecurity`**, an inhabitant of `FlockSpec` (#3's) | the Flock phase's definition; #3 |
| opening phase | [Layer 10](#layer-10-the-opening-phase-and-the-oracle-protocol) | **`openingPhase`**, **`openingComplete`**, **`openingSecurity`**, **`leanVmPhases`** | the spine; batching by powers; tables and stacking |
| WHIR opening | [Layer 11](#layer-11-whir-over-binary-reedsolomon-codes-and-merkle-trees) | `Level`, `encode`, **`encode_columnWeight`**, **`whirOpen`**, **`whirOpen_rbrSoundness`**, `McaJohnson`, `mcaConstant`, **`mcaJohnson_annexB`**, **`mcaError_foldLine_eq_affineLine`**, **`mcaBound_of_mcaJohnson`**, **`listBound_johnson`**, `johnsonPar`, **`deployed_rbrSoundness`** | field instances; tables and stacking; sumcheck: definitions |
| Merkle trees, the byte hasher and the WHIR parameters | [Layer 11](#layer-11-whir-over-binary-reedsolomon-codes-and-merkle-trees) | `merkleRootWith`, `merkleVerifyWith`, **`merkleRoot`**, **`merkleVerify`**, `MerkleTree.fold`, `MerkleTree.prunedRoot`, `nodeModel`, **`toBatchOpening`**, **`merkle_fits`** (a cross-check, kept as a test), **`blake2sBytes`**, **`ladder`** | leanISA Layer 1 (`compress`); VCVio's Merkle trees |
| the charged invariant | [Layer 12](#layer-12-compilation-the-transcript-the-proof-and-the-executable-verifier) | `chargedRandomOracle`, **`potential_le_expected_charge`**, **`prEvent_le_of_potential`**, **`prEvent_not_good_le_expected_charge`**, **`expected_charge_le_mul`**, **`expected_fresh_in_le`**; the logged form `chargedLoggingOracle`, **`potential_log_le_expected_charge`** | VCVio only |
| Merkle binding by log replay | [Layer 12](#layer-12-compilation-the-transcript-the-proof-and-the-executable-verifier) | `nodePreimage`, `leafPreimage`, `extractTree`, `extractLeaf`, `extractLeaves`, `extractRows`, `extractAllRows`, `Consistent`, `HasCollision`, `Fresh`, `Known`, `FreshHit`, **`binding_of_log`** (generic `MerkleTree.binding_of_log` and leanVM's), **`extractRows_determined`** (generic `MerkleTree.extractLeaf_determined`) | Merkle trees (the generic walk `MerkleTree.fold`) |
| list-binding compilation | [Layer 12](#layer-12-compilation-the-transcript-the-proof-and-the-executable-verifier) | `KWord`, `kwordOf`, `ListDecoder`, **`ListDecoder.bruteForce`**, `exactFast`, **`exactFast_eq`**, `ListDecoder.exactFirst`, `ListDecoder.exact`, **`isInK_of_cl`**, `stackOfMsgs`, `stackList`, `Component.relistRel`, **`Component.Front.relist`**, **`Component.Front.overComplete`**, `commitWord`, `commitPick`, **`commitWordSecurity`**, `openInput`, **`relist_of_relOpen`**, **`openInputSecurity`**, **`listBinding_compile`**, **`listBinding_kSF_one`**, **`listBinding_extractedStack_eq`**, **`listBinding_perfectCompleteness`**, `Whir.Transform` (`fwd`, `inv`, **`fwd_getElem`**, **`fwd_inv`**, **`inv_fwd`**, `encodeFast`, **`encodeFast_getElem`**), `exactNtt`, **`exactNtt_spec`**, **`exactNtt_of_codeword`**, `ListDecoder.nttFirst`, **`ListDecoder.decode_eq_of_codeword`**, `kwordOfFast`, **`kwordOfFast_eq`**, `deployedDecoder`, **`deployedChain_head`**, **`listBinding_deployed`**, **`listBinding_deployed_rbrKnowledgeSoundness`**, **`listBinding_deployed_perfectCompleteness`**, `deployedPick`, **`deployedPick_eq_commitPick`**, **`listBinding_deployed_kSF_one`**, **`listBinding_deployed_extractedStack_eq`**, **`commitPick_isSome_iff`**, **`commitPick_eq_some`** | the phases' knowledge soundness and completeness; WHIR opening; WHIR opening in the Johnson regime (`deployedChain`) |
| transcript, proof object and compiled verifier | [Layer 12](#layer-12-compilation-the-transcript-the-proof-and-the-executable-verifier) | `Digest`, **`card_digest`**, `hashSpec`, `hashQuery`, `runBlake2s`, `runRandom`, `FsState`, `Block`, `FsState.checkPow`, **`FsState.challengeOf`**, `chainHistory`, **`chainHistory_determined`**, `Proof`, `Proof.sizes?`, `RoundPoly.decode`, `decodePrefix`, **`decodePrefix_mono`**, `decode`, `leanVmIopp`, **`verifyWith`**, **`verify`**, **`verifyWith_simulateQ`**, `rounds`, `verifierQueries`, `proofDigests`, **`rounds_bound`**, **`verifierQueries_bound`**, **`proofDigests_bound`**, **`verify_iff_compiled`**, `settleFixedClaims` | the phases' definitions; the Flock phase's definition; WHIR opening; Merkle trees |
| the random-oracle theorems | [Layer 12](#layer-12-compilation-the-transcript-the-proof-and-the-executable-verifier) | `Adversary`, `Run`, `loggedGame`, `extract`, `Extracts`, `LogHasCollision`, `Hit`, `Bad`, **`bad_density`**, `Flip`, `HashMisbehaves`, **`core`**, `hashTerm`, `niError`, **`misbehaves_rom`**, `misbehaves_rom_coins`, **`niError_le`**, **`verify_knowledgeSound_rom`** | the compiled verifier; list-binding compilation; Merkle binding by log replay; the charged invariant in its logged form |
| the honest prover and the test vectors | [Layer 13](#the-executable-prover-and-the-test-vectors) | `proveWith`, **`prove`**, `honestAdversary`, **`baseProver_complete`**, the executable `leanervm-vectors` and its vectors | the compiled verifier; the adaptor; for the vectors, leanISA's `checkSatisfiedBy` |
| the base theorems (T4) | [Layer 13](#layer-13-the-base-theorems-t4-and-the-fixtures) | **`BlakeMisbehaves`**, `extractTrace`, **`baseVerifier_extractsWitness`**, **`baseVerifier_extractsExecution`**, `Blake2sActsAsRandomOracle`, **`blakeMisbehaves_of_comparison`**, `baseProver_complete_of_execution` | the random-oracle theorems; the adaptor; the honest prover; leanISA's `TraceExtraction` (declared beside `SatisfiedBy`); for the instantiated execution form and completeness from an execution, leanISA Layers 9–10 |

What can start is what the column *Needs* allows; the status file says what is built.

## The layers

Fourteen layers, numbered 0 to 13, are built in order, with the spine after Layer 0. Each layer
section specifies the holes of [The holes](#the-holes) that name it: what to define and prove,
its sources, its tests (which are part of it), and the upstream work to read first. The phases
(Layers 6 to 10) are written over an abstract `I : M3Instance` at the spine's slots; Layer 3
builds the leanISA instance and the adaptor. A hole lands only fully proved, and its definition
with its completeness lands apart from its knowledge soundness.

### Layer 0: the ArkLib dependency and the field instances

`lakefile.toml`, `upstreams.json`, `docs/dependencies.md`; `LeanerVM/Protocol/Field.lean`, and the
inner-product interface in `LeanerVM/Protocol/ToArkLib/InnerProduct.lean`.

ArkLib is the `Arklib` requirement (its package name). Supply what ArkLib needs of the fields and
of the messages:

```lean
structure Column (n : ℕ) where values : CMlPolynomialEval K n      -- not an abbreviation of a Vector
instance : SampleableType K                 -- only the building block of the E sampler
instance : SampleableType E                 -- three limbs through an equivalence; never enumerates
theorem card_E : Fintype.card E = 2 ^ 192
structure Weight (n) where (cube : Thunk (CMlPolynomialEval E n)) (mle : Vector E n → E) (mle_eq : …)  -- cube built on first read
def Weight.pair (W : Weight n) (q : Column n) : E := Σ_w W(w)·q(w)
def eqWeight (p : Vector E n) : Weight n                       -- eq(p, ·) with its product evaluator
/-- The stack as an oracle: a query is a weight, the answer the inner product (Definition 3.13). -/
instance innerProductOracle (n : ℕ) : OracleInterface (Column n) where
  Query := Weight n
  ...  -- answer := W.pair q
theorem answer_eqWeight {n} (q : Column n) (p) : OracleInterface.answer q (eqWeight p) = eval₂Mle q.values (algebraMap K E) p
```

The samplers go through explicit equivalences on the carriers, as ArkLib's
`KoalaBear.Ext6.sampleableType` does; `Fintype K` is proof-only. Tests: the oracle answers
`⟨W, q⟩` on a two-variable table for an equality weight and for another weight, with a mutated
column; `answer_eqWeight` on and off the cube; `card_E`. No scalar or list interface on `E` is
registered: each message schedule carries the interfaces of its own messages.

### Layer 1: hypercube tables, stacking, the strided reader, the index and bytecode columns

Two halves. The generic half is written for CompPoly, over any commutative ring and CompPoly's
tables, and names no protocol: `LeanerVM/Protocol/ToCompPoly/{Multilinear,BitProductTable,
Stacking,AmbientStacking}.lean`. The leanVM half specialises it and cites the specification:
`Stack.lean` (columns over `K`, points in `E`, the spine's `Layout`), `Padding.lean` (back-loaded
padding, §5.5), `ClaimWeights.lean` (a column claim as a weighted claim, §4.1) and
`FixedColumns.lean` (the index and bytecode columns; it names the program, so it sits below the
wall).

```lean
-- ToCompPoly/Multilinear.lean, over any commutative ring R
def sumCube (t) : R ; def hadamard (s t) ; theorem evalMle_eq_sumCube_hadamard ; theorem sumCube_lagrangeBasis
def slice (t : CMlPolynomialEval R (k + m)) (j : Fin (2 ^ m)) : CMlPolynomialEval R k       -- high index fixed
theorem evalMle_append_boolVec (t) (z) (j) : evalMle t (z ++ boolVec j) = evalMle (slice t j) z
def sliceLow (t : CMlPolynomialEval R (k + m)) (i : Fin (2 ^ k)) : CMlPolynomialEval R m    -- low index fixed
theorem evalMle_boolVec_append (t) (i) (s) : evalMle t (boolVec i ++ s) = evalMle (sliceLow t i) s
def placeSlice (t) (j) ; theorem evalMle_placeSlice ; theorem sumCube_placeSlice
-- ToCompPoly/BitProductTable.lean
def bitProductTable (f : Fin n → Bool → R) ; theorem evalMle_bitProductTable ; def powersTable ; theorem evalMle_powersTable
-- ToCompPoly/Stacking.lean, AmbientStacking.lean
structure Blocks where (n : ℕ) (size : Fin n → ℕ) (descending : Antitone size)   -- sizes only
def Blocks.stackAt ; Blocks.selector ; Blocks.extendPoint ; Blocks.offset ; Blocks.total ; Blocks.lowPoint ; Blocks.selectorWeight
theorem Blocks.pow_size_dvd_offset ; theorem Blocks.stack_eval ; def Blocks.unstack ; theorem Blocks.unstack_eval₂
theorem Blocks.stack_eval_ambient (t) (hμ) (pad) (ζ) : evalMle (B.stackAt t μ pad) ζ =
    Σ_b eq(sel_b, ζ_hi)·P̃_b(ζ_lo) + pad·(1 − Σ_b eq(sel_b, ζ_hi))          -- §5.4, equation (2)
-- Stack.lean
def Blocks.stackColumn ; Blocks.readColumn ; theorem Blocks.readColumn_eval
def Blocks.layout (hμ) : Layout μ (Fin B.n) B.size                   -- aligned blocks
def Blocks.stridedLayout (hμ) (b) (k) (slot : ι → Fin (2 ^ k)) (h : ∀ c, B.size b = k + κ c) : Layout μ ι κ
def Layout.piecewise (L₁ : Layout μ ι₁ κ₁) (L₂ : Layout μ ι₂ κ₂) : Layout μ (ι₁ ⊕ ι₂) (Sum.elim κ₁ κ₂)
def Layout.comap (L) (f : ι' → ι) (h : ∀ c, κ (f c) = κ' c) : Layout μ ι' κ'
theorem Blocks.stack_eval_ambient_one                                 -- pad 1 over E, characteristic two
-- Padding.lean
def padHigh (t) (m) := placeSlice t (onesIndex m) ; theorem sumCube_padHigh ; theorem evalMle_padHigh
-- ClaimWeights.lean
theorem ColumnClaim.holds_iff_weighted (q) (c : ColumnClaim I) :
    c.Holds q ↔ WeightedClaim.Holds q ⟨eqWeight (I.layout.extend c.col c.point), c.value⟩
-- FixedColumns.lean
def idxColumn (κ) : Column κ := ⟨powersTable g κ⟩ ; def idxColumnEval (ζ) : E
theorem idxColumn_eval ; theorem idxColumnEval_eq (ζ) : idxColumnEval ζ = ∏ k, (1 + ζ[k]·(1 + g^(2^k)))   -- §6.5
def bytecodeColumn (prog) : Column (prog.logSize + 4) ; def bytecodeColumnEval (prog) (z) (w) : E
theorem bytecodeColumn_answer_boolVec (i) (s) : … = ofK (encodeSlots (prog.code i))[s]
theorem bytecodeColumn_eval (z) (w) : … = bytecodeColumnEval prog z w
```

`stack_eval` is the one selector fact every later decomposition uses; `unstack_eval₂` is the same
fact for a table the prover chose, and `Blocks.layout` packages it as a `Layout`. leanVM reads the
eighteen BLAKE2S limb columns as *strided* slots of `q_flock`: the low eight coordinates of
`q_flock`'s block are frozen to the slot's bits and the high ones are the claim's point
(`stack_open.rs:84-97`, `SlotClaim::Strided` at `cpu/mod.rs:799-805`); `Blocks.stridedLayout`
reads them through `evalMle_boolVec_append`, and `Layout.piecewise` joins the two readers, whose
sum type Layer 3 transports to `ColumnId`. The special cases the protocol uses are derived here:
back-loaded padding is `placeSlice` at the all-ones index; the index column is the geometric table
at the generator; the public-input point `(r, 0, …, 0)` is `evalMle_append_boolVec` at slice zero.

Tests: offsets and selectors decided in the kernel on blocks of heights 4, 2, 1, the stacking
identity on them and on a column that is no honest stack, reversed selector bits, the small-first
placement no selector reads; the strided slice against the aligned slice, and a limb claim's
lifted point against the Python's `Placement.stack_point` (`py:295-297`); back-loaded padding
against the copied table; `idxColumn_eval` at `κ = 2` against the reversed bit order;
`bytecodeColumn_answer_boolVec` against reversed slot bits, and `bytecodeColumn` of a
sixteen-instruction program with distinct operands against the Rust encoder (`leaf.rs:585-604`),
written with `K.ofBits`.

### Layer 2: Clean components as polynomials

`LeanerVM/Protocol/ToClean/ExpressionPolynomial.lean` (an expression as a polynomial) and
`LeanerVM/Protocol/ToClean/ComponentPolynomial.lean` (a component as a table; generic over any
Clean component, its field and its type of bus sides). Upstream: Clean's pull request #466
defines `degreeBound`, `WithinWidth` and the Mathlib polynomial `toBoundedPolynomial`; the first
module is a verbatim copy of it until the pin contains it (the upstream ledger).

```lean
def Expression.toCMvPolynomial (n) : Expression F → CMvPolynomial n F   -- var i < n ↦ X i, else 0
theorem eval_toCMvPolynomial (row : Fin n → F) (data) (e) :
    (e.toCMvPolynomial n).eval row = e.eval (Environment.fromArray (Array.ofFn row) data)
theorem fromCMvPolynomial_toCMvPolynomial (e) (h : e.WithinWidth n) :
    fromCMvPolynomial (e.toCMvPolynomial n) = e.toBoundedPolynomial n h   -- Clean's polynomial
theorem totalDegree_toCMvPolynomial_le (n) (e) : (e.toCMvPolynomial n).totalDegree ≤ e.degreeBound
structure M3Table (F) (σ) where                                          -- σ: the bus sides
  width : ℕ
  constraints : List (CMvPolynomial width F)
  flushes : List (σ × Vector (CMvPolynomial width F) 16)                 -- separator first
  count : List (Fin width)
def Component.toM3 (c : Component F) (sep : RawChannel F → F) (dir : RawChannel F → σ)
    (counted : RawChannel F → Bool) : M3Table F σ
  -- `count`: coordinate 1 of every interaction on a counted channel, when it is a variable
theorem toM3_constraints_iff (hl : c.rowOperations.lookups = []) (row : Fin c.width → F) (data) :
    (∀ C ∈ (c.toM3 sep dir counted).constraints, C.eval row = 0) ↔
      c.operations.ConstraintsHold (Environment.fromArray (Array.ofFn row) data)
theorem toM3_flushes_eq (row) (data) : (evaluated flushes) = (Clean's interactions as 16-tuples)
def CountsAreVariables (c) (counted) : Prop                   -- decidable; every count a column
def UnitMultiplicities (c) : Prop                             -- decidable; every multiplicity ±1
```

The translation is direct and computable: Clean's polynomial is a Mathlib polynomial, and both it
and CompPoly's conversion from one are noncomputable, which would make `M3Holds` of the leanISA
instance undecidable by evaluation and `verify` noncomputable. Within the width the translation is
Clean's polynomial; the degree bound is Clean's `degreeBound` and goes through CompPoly's
`totalDegree_equiv`. The separator and direction are given per channel, so the map from Clean's
typed channels to the bus is explicit data. A component whose expressions mention a variable at or
beyond its width reads `0` there, as `Environment.fromArray` does. Tests: a two-column component
whose constraint `x·y` has `degreeBound = 2`, checked on a satisfying and a failing row; the six
tables' count columns against `count_columns()` (`layout.rs:412-414`); the memory, bytecode and
verifier components against the boundary blocks of Layer 3 on the one-row witness.

### Layer 3: the leanISA instance and the adaptor

`LeanerVM/Protocol/LeanIsa.lean` (module). Needs the spine, Layers 1 and 2, leanISA Layers 5–8,
and the Flock roadmap's `FlockSpec` (Layer 9).

```lean
structure Sizes where (logMem : ℕ) (τ : Fin 6 → ℕ)                    -- heights only; the family index
def Sizes.ofWitness (w : EnsembleWitness (leanIsaEnsemble prog)) : Option Sizes
def LeanIsa.blocks (prog) (s) : Blocks ; def leanIsaμ (prog) (s) : ℕ    -- witness.rs:67-101
theorem LeanIsa.blocks_fits : (LeanIsa.blocks prog s).total ≤ 2 ^ leanIsaμ prog s
def Sizes.Admissible (prog) (s) : Prop   -- 16 ≤ logMem ≤ 32, τ j ≤ 32, 3 ≤ τ BLAKE2S, leanIsaμ prog s ≤ 28
def validRate (ρ : ℕ) : Prop := 1 ≤ ρ ∧ ρ ≤ 4                           -- whir_config.rs:48-55
theorem caps_witnessOf (hs : s.Admissible prog) (q) : Caps (witnessOf F prog s q)
theorem sizes_of_satisfiedBy (h : SatisfiedBy prog input w) : ∃ s, Sizes.ofWitness w = some s

abbrev leanIsaInstance (F : FlockSpec) (prog) (s) : M3Instance         -- reducible
  -- flock := some ⟨q_flock, τ BLAKE2S, _, F.Holds _, _⟩

def stackOf (F) (w : EnsembleWitness (leanIsaEnsemble prog)) (hs : Sizes.ofWitness w = some s) : Column (leanIsaμ prog s)
def witnessOf (F) (prog) (s) (q : Column (leanIsaμ prog s)) : EnsembleWitness (leanIsaEnsemble prog)   -- total, computable
structure Agrees (F) (s) (q : Column (leanIsaμ prog s)) (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop
  -- w's opcode tables have 2^τ_j rows and, within their widths, q's rows; its memory and bytecode blocks are q's
theorem agrees_witnessOf : Agrees F s q (witnessOf F prog s q)
theorem agrees_stackOf (h : SatisfiedBy prog input w) (hs) : Agrees F s (stackOf F w hs) w
theorem tuples_perm (h : Agrees F s q w) (side : Side) :
    ((leanIsaInstance F prog s).tuples q side).Perm (the tuples w's interactions flush on side)
theorem satisfiedBy_witnessOf (hs : s.Admissible prog) (h : M3Holds (leanIsaInstance F prog s) input q) :
    SatisfiedBy prog input (witnessOf F prog s q)
theorem m3Holds_stackOf (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s) :
    M3Holds (leanIsaInstance F prog s) input (stackOf F w hs)
theorem witnessOf_stackOf (h : SatisfiedBy prog input w) (hs) :
    the tables' rows, the memory rows and the public input of witnessOf F prog s (stackOf F w hs) are w's
```

The instance is not a map from Clean's ensemble: an instance needs a stack height, a layout,
public lines, a Flock region and a statement type, and the program must stay public data. It is
`Component.toM3` of the six opcode tables with leanISA's separators, directions and count
columns; three column groups for the shared committed columns (`mem_0, mem_1, mem_2, cntfin_mem`
at `2^logMem`; `cntfin_bc` at `2^prog.logSize`; `q_flock` at `2^(τ_BLAKE2S + 8)`), which are tables
with no constraint, flush or count and so take no part in the table sumcheck; six boundary blocks
written from `memTable`, `bytecodeTable` and `leanIsaVerifier prog`, with the index columns
`Coord.known (idxColumn κ)`, the program's slots `Coord.known`, the final pc `Coord.const
prog.finalPc`, and the limbs and counts `Coord.committed`; the layout of `witness.rs:67-101`,
`cpu/layout.rs:13-49` and `leaf.rs:53-156`, aligned blocks joined by `Layout.piecewise` to the
strided reader of the limb slots `F.slot`; `d := 2`; three public lines, on `mem_0, mem_1, mem_2`
(for `ℓ = 0, 1` the cells are limb `ℓ` of the two public words, sent; for `mem_2` the cells are
`0, 0`, not sent); and the Flock region `q_flock` with `kBatch = τ_BLAKE2S` and the predicate
`F.Holds`. The renaming of the layout is injective, so that no column is aliased.

`M3Holds` is the target of extraction and the source of completeness; the theorems around it are
the whole bridge between polynomials and Clean's witness, and the only place the proof system
meets leanISA. `tuples_perm` is what both directions need: `SatisfiedBy`'s balances range over
the tuples the witness's interactions flush, which the instance states as the opcode tables'
flushes and the boundary tuples of the memory, bytecode and verifier rows. On each side the two
lists are permutations of each other whenever the witness `Agrees` with the stack, and
`agrees_witnessOf` and `agrees_stackOf` give that agreement in the two directions.
`satisfiedBy_witnessOf` takes admissibility as a hypothesis: `Caps` does not follow from
`M3Holds`, and `verify` checks the announced sizes first. It discharges `Blake2sRowsValid` by
`F.compress_of_holds`, and the two public-word conjuncts by the three public lines, whose third
fixes the top limb (a two-line instance would leave `SatisfiedBy.word0_eq` unprovable, since the
statement's words have a zero top limb by type). `stackOf` builds the region `q_flock` by `F.gen`,
and `m3Holds_stackOf` consumes `F.holds_gen`. `witnessOf` rebuilds the tables from the columns (the
limbs from their slots), the interactions from the components, the image from the memory
columns, the public input from cells 0 and 1 of `mem_0, mem_1`, and the program from `prog`.

Tests: a one-row witness stacked and read back (the three equalities of `witnessOf_stackOf` by
`#guard`); `Sizes.Admissible` rejects `logMem = 15`, `τ_BLAKE2S = 2` and a stack of height `2^29`,
and `validRate 5` fails; the offsets of every committed column on two size vectors where a table's
height equals `2^logMem`, where a tables-first tie order fails; a `#guard` that the instance's
public lines list `mem_2` with cells `(0, 0)` and `sent = false`; `Decidable (M3Holds …)` found by
instance search.

### Layer 4: the sumchecks and batching

`LeanerVM/Protocol/ToArkLib/Sumcheck.lean`, `ToArkLib/Batch.lean` (modules; ArkLib candidates).

leanVM runs sumcheck on polynomials the verifier cannot evaluate at the end: the summand is a
formula in the columns' extensions, so the last message is the column values at the final point,
the verifier evaluates the formula, and the values become claims. Two variants, both as
`Component.Def`s with their `Complete` and `Security` in the named form:

```lean
structure Virtual (F) (n m d : ℕ) where          -- n variables, m tables, a formula of degree d
  formula : (Fin m → F) → F ; formula_poly : ∃ p : MvPolynomial (Fin m) F, p.totalDegree ≤ d ∧ …
/-- Plain: the round message is the round polynomial; tables of different heights join late,
lifted by ∏_{k ≥ τ_j} X_k, with eq(ζ_{<τ_j}, ·) a factor the verifier evaluates at the end. -/
def Sumcheck.plain (V : Virtual F n m d) (heights) : Component.Def …
/-- Normalized: the round message is the cofactor h of degree d_c; the verifier checks
(1 + r_t)·h(0) + r_t·h(1) against the running claim and moves to h(χ_t). -/
def Sumcheck.normalized (d_c) : Component.Def …
def Sumcheck.plainComplete ; plainSecurity           -- error d/|F| per round
def Sumcheck.normalizedComplete ; normalizedSecurity -- error d_c/|F| per round
theorem Sumcheck.transport (dec : injective decoding of wire messages onto those passing the round check) :
    the verifier composed with dec is round-by-round knowledge sound at the same error, state function ∘ dec
/-- Random linear combination of k claims by the powers of one challenge. -/
def batch (k) : Component.Def … ; def batchComplete ; def batchSecurity    -- error (k − 1)/|F| on the challenge
```

The single-round knowledge bound is proved for each variant here, on the spine's notion; ArkLib's
classical leaf is not consumed (the ledger). The table sumcheck is the plain variant; the GKR's
layer sumchecks are the normalized one. The wire drops one coefficient of each round message
(`c_1` for the plain cubic, `c_0` for the normalized quartic cofactor), and `Sumcheck.transport`
is what lets the compiled verifier decode it (decision 26). The batching's state function is
"some claim is false"; escape needs the batching polynomial, of degree `< k`, to vanish at the
challenge. Tests: both variants on a two-variable degree-2 summand, honest runs accepted by
`#guard`, a wrong round polynomial rejected; `transport` on the Rust's encoding of one round.
Upstream work to read first: ArkLib's typed sumcheck (`ProofSystem/Sumcheck/Interaction/`, plain
case only) and #1128 for the honest round algebra.

### Layer 5: fingerprints, the grand product, and GKR

`LeanerVM/Protocol/ToArkLib/GrandProduct.lean`, `ToCompPoly/ProductTree.lean` (modules; ArkLib and
CompPoly candidates).

```lean
def fingerprint (α : Fin 4 → E) (t : Vector K 16) : E := Σ i, eqTilde α (bits i) * ofK t[i]
def sideProduct (α β) (P : Multiset (Vector K 16)) : E := (P.map fun t ↦ β - fingerprint α t).prod
/-- Specification Lemma 5.2: the product polynomial determines the multiset. -/
theorem sideProduct_poly_eq_iff (P Q) : (Π_P : MvPolynomial (Option (Fin 4)) K) = Π_Q ↔ P = Q
/-- Specification Theorem 5.1: unequal multisets of size ≤ 2^μ collide with probability ≤ 4·2^μ/|E|. -/
theorem sideProduct_collision (hne : P ≠ Q) (hμ) : Pr[α β ← uniform; sideProduct α β P = sideProduct α β Q] ≤ 4·2^μ/|E|
/-- The grand products of `nside` trees whose leaves are functions of the context. -/
def gkr (nside μ : ℕ) (leaves : S → (∀ i, OStmt i) → Fin nside → ETable μ)
    (riders : S → (∀ i, OStmt i) → List (Σ τ, ETable τ)) :
    Component.Def (S × (Fin nside → E)) OStmt Unit (S × Vector E μ × (Fin nside → E)) OStmt Unit (gkrSpec nside μ)
  -- relIn: the roots are the products of `leaves`, and every rider table is zero
  -- relOut: the leaf claims hold at ζ, and every rider's extension vanishes at ζ_{<τ}
def gkrError (nside μ) ; def gkrComplete ; def gkrSecurity
```

Here `Π_P` is `grandProductPoly (n := 4) P`. Its factors use
`fingerprintFactorPoly t : MvPolynomial (Option (Fin n)) R`, defined as
`MvPolynomial.X none - MvPolynomial.rename some (fingerprintPoly t)`. The separate variable
`X` is indexed by `none` and evaluates to `β`; `A_i` is indexed by `some i` and evaluates to
`α i`, so the assignment is `fun i ↦ i.elim β α`. In `Fin (n + 1)` notation, these indices
correspond to `0` and `i.succ`, respectively. This is a variable renaming; the bus challenge
remains the pair `(α, β)`.

`gkr` is radix 4 with a radix-2 first layer when `μ` is odd; each layer is a combiner `λ`, a
normalized sumcheck on the layer identity (cofactor of degree 4, degree 2 in the radix-2 layer),
and the descendants' values interpolated at the combination challenges; a combiner follows the
last layer too, unused. `gkrError` is `(nside − 1)/|E|` on each combiner but the last, `0` on the
last, `4/|E|` on each radix-4 round and `2/|E|` on each radix-2 round, and `1/|E|` on each
combination challenge (two per radix-4 layer, one for the radix-2 layer). The leaves are a
function of the statement and the oracles, so the bus phase instantiates them at the three leaf
tables of the stack without ArkLib's context lifting (admitted upstream); the *riders* are tables
that must vanish at the final point, and the GKR's state function carries "every rider's
extension, restricted to the coordinates of `ζ` drawn so far, is identically zero" beside its own
claim, which is how the bus phase pays the zerocheck (decisions 17, 18). Lemma 5.2 is proved by
unique factorization in `K[A_0, …, A_3, X]`: the factors `X − π_A(t)` are monic linear, hence
irreducible (the specification leaves the proof `TODO`).

Tests: `gkr 1 2`, `gkr 3 3`, `gkr 3 4` honest runs accepted, their message and challenge counts;
a leaf changed after the root is sent rejected; `sideProduct_poly_eq_iff` refuted on
`{t} ≠ {t, t}` at `μ = 1`; a rider nonzero at the final point rejected except at the charged
challenge. Upstream work: ArkLib #818 (a circuit GKR) as a pattern only; ArkLib issue #901.

### Layer 6: the bus phase

`LeanerVM/Protocol/Bus.lean` (module, over `I`). Needs the spine, Layer 1 and Layer 5.

```lean
def pushLeaves pullLeaves countLeaves (I) (α β) (q : Column I.μ) : ETable I.μBus   -- the leaf stacks
theorem leaf_decomposition : evalMle (pushLeaves I α β q) ζ =
    Σ_b eq(sel_b, ζ_hi)·(β − Σ_i eq(α, i)·c̃_{b,i}(ζ_lo)) + (1 + Σ_b eq(sel_b, ζ_hi))   -- §5.4, equation (2)
def busPhase (I) (h₁ : 1 ≤ I.d) (h₂ : ∀ j, I.constraints j ≠ [] → I.τ j ≤ I.μBus) :
    Phase.Def I I.Stmt (I.Stmt × BusOut I) (busSpec I)
def busComplete I h₁ h₂ : Phase.Complete I (busPhase I h₁ h₂) (Seam.commit I) (Seam.bus I)
def busSecurity I h₁ h₂ : Phase.Security I (busPhase I h₁ h₂) (Seam.commit I) (Seam.bus I) (busError I)
```

The phase is `[(α, β); (R, R_c)] ⟫ gkr ⟫ [boundary evaluations]`, with the three leaf tables as
`leaves` and the constraint tables as `riders`. The schedule: `V_to_P (α, β)`; `P_to_V (R, R_c)`,
the bus root first, one scalar for push and pull; the GKR's; `P_to_V` the boundary evaluations,
in the order in which the sides, their blocks and their coordinates first name a committed column,
a column already valued at the point skipped (for leanISA `mem_0, mem_1, mem_2, cntfin_mem` at
`ζ_{<κ_mem}`, then `cntfin_bc`). The verifier checks `R_c ≠ 0`, the GKR's layer checks, and at the
end that the leaf claims decompose as `leaf_decomposition` says, which leaves the forms of the
sumcheck tables owed. Its output is `BusOut`: the point `ζ`, the forms per side and table (the
zerocheck conjunct is the seam's), their totals `rem_s`, and the boundary column claims; the
forms' weights are `eq(sel_b, ζ_{≥τ_j})·eq(α, i)` against the flush coordinate polynomials, plus a
constant term `eq(sel_b, ζ_{≥τ_j})·β`, so the fingerprint enters the weights.

The state function after `(α, β)` asks that the two products at `(α, β)` agree, every count be
nonzero, every constraint vanish on the cube, and the lines and `aux` hold; it asks the products
to agree, not the multisets, since a collision of the products could be charged to no later
challenge. After the roots it asks the GKR's claims; on the last layer's challenges the zerocheck
conjunct joins, whose escape costs `1/|E|` per coordinate and is dominated by the GKR's own error
there; no boundary claim exists before the last message. `busError` is `4·2^{μ_bus}/|E|`
on `(α, β)` and `gkrError 3 μ_bus` on the GKR's challenges; the zerocheck adds nothing.
The two hypotheses are the bus phase's side conditions (decision 30): a count column's form has
degree 1, and a constrained table off the bus has no zerocheck point (`constraints.rs:250-253`).

Tests: `leaf_decomposition` in the kernel on a layout with two blocks; the whole phase on the toy
instance's honest stack; the zero-count mutation (acceptance test 3) and the pad-0 mutation (test
2); a size vector with `τ_j = κ_mem`, where the leaf stacks' tie order decides the offsets; the
message and challenge counts of test 17.

### Layer 7: the table sumcheck phase

`LeanerVM/Protocol/TableSumcheck.lean` (module, over `I`). Needs the spine and Layer 4.

```lean
def tableSummand (I) (s : BusOut I) (ξ : E) : Virtual E I.τmax (Σ_{sumcheck tables} width_j) 3   -- the F of §5.5
theorem tableSummand_target : Σ_x tableSummand I s ξ x = Σ_side ξ^(B + side) · s.totals side
def tableSumcheck (I) : Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I) (tableSpec I)
def tableSumcheckComplete I ; def tableSumcheckSecurity I      -- (B + 2)/|E| on ξ, 3/|E| per round
```

The schedule: `ξ`; `τ_max` rounds, highest variable first, each three coefficients and a
challenge; then one value per column of each sumcheck table, table by table (for leanISA 104
values; `3·τ_max + 104` scalars and `1 + τ_max` challenges). The target `T = Σ_s ξ^{B+s}·totals_s`
is derived, never sent. Table `t` weighs `w_t = ∏_{m<τ_t}(1 + ζ_m + r_m)·∏_{τ_t≤m<τ_max} r_m`, and
the final check is `Σ_t w_t·(Σ_i ξ^{o_t+i}·C_{t,i}(e_t) + Σ_s ξ^{B+s}·B^s_t(e_t)) = claim`. The
output carries the input's column claims forward (dropping them would forget a false boundary
claim) followed by the final values as claims at `r`. The state function after `ξ` is "some
constraint extension at `ζ_{<τ_j}` is nonzero, or some form disagrees with its total"; turning
"every extension is zero at `ζ`" into "every constraint vanishes on the cube" is the bus phase's
zerocheck conjunct, since `ζ` is drawn there, after the commitment.

Tests: `tableSummand_target` on two tables of heights 2 and 1; a row violating a constraint makes
the honest run's final check fail; the reversed variable order mismatches `eq` (test 16); on an
instance with a taller column group, the number of rounds is the sumcheck tables' `τ_max`.

### Layer 8: the public-input phase

`LeanerVM/Protocol/PublicInput.lean` (module, over `I`). Needs the spine and Layer 1's
`evalMle_append_boolVec`. Two phases on one schedule: the specification's (a check per limb),
kept as the reference of §8.2, and the deployed verifiers' (one equation on the words), which
`Phases` and Layer 12 take (decision 22; the discrepancy *the public-input check*).

```lean
namespace PublicInput
-- the schedule is the spine's pubSpec: V_to_P : E, then P_to_V : List E
def linePoint (hn : 0 < n) (r : E) : Vector E n     -- (r, 0, …, 0)
theorem eval₂Mle_linePoint : q̃(linePoint hn r) = (1 - r)·q(0) + r·q(1)
def lineValue I r l : E := (1 + r)·cell0 + r·cell1
def expectedValues I input r : List E               -- the values of the lines marked `sent`
def claimsFrom I r : List (PublicLine I.toShape) → List E → List (ColumnClaim I)
  -- a sent line takes the next value of the message; an unsent line its computed value
def pooledFrom I s r (cs : List E) : I.Stmt × PubOut I := (s.1, ⟨s.2.columns ++ claimsFrom I r (I.publicLines s.1) cs⟩)
theorem pooledFrom_expected : pooledFrom I s r (expectedValues I s.1 r) = pooled I s r
def check I s r cs : Bool := decide (cs = expectedValues I s.1 r)             -- §8.2, per limb
def checkWords I s r cs : Bool                                                 -- cpu/mod.rs:752-755
  -- two sent lines l₀ l₁ and cs = [c₀, c₁]: c₀ + y·c₁ = lineValue l₀ + y·lineValue l₁;
  -- otherwise cs = the lines' values
theorem checkWords_of_check : check I s r cs = true → checkWords I s r cs = true
theorem accepts_two_challenges (hr : r₁ ≠ r₂) (h₁ : Accepts a b w₀ w₁ r₁ c₀ c₁) (h₂ : Accepts … r₂ …) :
    w₀ = E.ofLimbs (a 0) (a 1) 0 ∧ w₁ = E.ofLimbs (b 0) (b 1) 0 ∧ a 2 = 0 ∧ b 2 = 0
def prover I ; def verifier I ; def deployedVerifier I   -- read the message, check, pool what was sent
end PublicInput
def publicInputPhase I ; def publicInputComplete I ; def publicInputSecurity I   -- the specification's
def deployedPublicInputPhase I : Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I)
def deployedPublicInputComplete I : Phase.Complete I (deployedPublicInputPhase I) (Seam.table I) (Seam.pub I)
def deployedPublicInputSecurity I : Phase.Security I (deployedPublicInputPhase I) (Seam.table I) (Seam.pub I)
    -- 1/|E| on the one challenge
```

The verifier draws `r ∈ E`; the prover sends, as one message, the values at `r` of the lines
marked `sent`, in order; the verifier checks them and rejects otherwise, then pools one claim per
line, on the line's column at `(r, 0, …, 0)`, after the earlier phases' claims. For a line whose
value was sent the value pooled is the value *sent*, as §8.2 and the pinned verifiers pool it; for
the others it is the value the verifier computes. The check is what makes the pooled claims the
statement's: without it the prover's values are pooled unchecked and the phase has no
knowledge-soundness proof. (A verifier that pools the values it computes is knowledge sound with
no check at all, which is why the pool reads the message.) For leanISA the lines are the three of
Layer 3: the prover sends `c_0, c_1` for `mem_0, mem_1`, and the claim on `mem_2` is pooled at `0`
with no scalar sent. The honest prover's values are functions of the statement and the challenge
(`cpu/mod.rs:611-613`); on a stack whose lines hold they are the extensions of its columns.

The specification checks each limb, `c_ℓ = (1 + r)·w_{0,ℓ} + r·w_{1,ℓ}`; the pinned verifiers
check `c_0 + y·c_1 = (1 + r)·w_0 + r·w_1` over `E` (`cpu/mod.rs:752-755`, `py:1400`). The limb
checks imply the word check, not conversely: the scalars are values at a point of `E`, so that `1,
y` are independent over `K` says nothing of them. Each is sound at `1/|E|`: for the limb check a
wrong line gives a nonzero polynomial of degree one in `r`; for the word check,
`accepts_two_challenges` shows that acceptance at two challenges fixes the memory cells to the
public words with zero top limbs. The message's length is fixed by the check alone, so Layer 12
serializes it without a length prefix. Both proofs start from `ToArkLib/GuardedVerdict.lean`; the
bound is `ToVCVio/UniformSample.lean`'s. The line identity is derived here from
`evalMle_append_boolVec` at slice zero: a point chosen by the protocol is not upstream material.

Tests: on the toy, the line's value accepted and a wrong, missing or extra value rejected; the
stack `badLine` rejected by the check except at the one bad challenge; three lines in the shape of
the memory limbs, where a wrong top cell passes the check and fails the third claim (`threeLimbs`);
the challenge at which the word check holds and the limb check rejects. The refutations
(convention *Load-bearing checks*): the check removed (the prover's values pooled unchecked) or
weakened to its first value has no knowledge soundness; the claims of unsent lines dropped has
none; a check with the cells swapped, or an extra check, is not perfectly complete.

### Layer 9: the Flock phase

`LeanerVM/Protocol/Flock.lean` (module, over `I`), and the constants in
`LeanerVM/Parameters/Flock.lean`. Needs the spine and, for knowledge soundness, the Flock roadmap
(#3). The phase reads the instance's Flock region (`I.flock`); for an instance with none, such as
the toy, it is the pass-through.

```lean
/-- What the Flock roadmap supplies, none of it mentioning an instance. -/
structure FlockSpec where
  slot : Fin 18 → Fin 256                                    -- hash_flock.rs:87-115
  Holds (kBatch : ℕ) : Column (8 + kBatch) → Prop            -- the R1CS with the constant position
  decHolds : ∀ k, DecidablePred (Holds k)
  compress_of_holds : Holds k c → ∀ j, Blake2sRelation (the limbs read at slot j of c)
  gen : List (Blake2sRow K) → Column (8 + kBatch)            -- keeps each limb in its slot
  holds_gen : (∀ r ∈ rows, Blake2sRelation r) → Holds k (gen rows)
def flockPhase (I) : Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I) (flockSpec I)
def flockComplete I : Phase.Complete I (flockPhase I) (Seam.pub I) (Seam.flock I)
def flockSecurity I : Phase.Security I (flockPhase I) (Seam.pub I) (Seam.flock I) (flockError I)   -- #3's
theorem flockError_le (h : I.flock = some r) : Σ flockError I ≤ (4·r.kBatch + 163)/|E| + 2^32/|E|
```

The verifier reads no claim of the pool. It hands the column claims on unchanged, the eighteen
limb claims among them (they stay in the pool and are opened as strided claims on `q_flock`),
and adds one weighted claim, the ring-switched one, `⟨W, q⟩ = T` with
`T = Σ_{i<64} x^i·Φ(s_i)` and `W(x_lo, x_hi) = eq(sel_{q_flock}, x_hi)·Φ(eq((χ'_in, χ_out), x_lo))`
(`cpu/mod.rs:799-805`, `stack_open.rs:522-527`). The schedule, with `k_batch = τ_BLAKE2S`:
`k_batch + 1` challenges; 64 values; one challenge; `8 + k_batch` rounds of two values and a
challenge; two values; one challenge; 8 rounds of two values and a challenge; 64 values; six
challenges: `162 + 2·k_batch` scalars and `2·k_batch + 25` challenges. The error per challenge:
`1/|E|` on each of the `k_batch + 1` coordinates of `r`; `127/|E|` on `z_skip`; `2/|E|` on each of
the `8 + k_batch` zerocheck rounds, `1/|E|` more on the last `k_batch`; `3/|E|` on `α_lc`; `2/|E|`
on each of the 8 lincheck rounds; `2^{2^{5−p}−1}/|E|` on ring switching's `f_p` (`2^31`, `2^15`,
`2^7`, `8`, `2`, `1`). Ring switching sends nothing and checks nothing: its six challenges build an
`F_2`-linear `Φ` by `a_{p+1} = a_p + f_p·a_p^{2^{2^{5−p}}}`, and the `s_i` were sent by the
lincheck. The bound needs three facts, owed with the proof: the 128 fixed weights are
`F_2`-independent; `1, y^{2^k}, y^{2^{k+1}}` is a `K`-basis of `E`; the 64 `c_k` are distinct
monomials.

The verifier's checks (each with its refutation): the lincheck terminal identity
(`lincheck.rs:1252-1256`); the zeros on `H` imposed by interpolating 64 received values with 64
zeros (`zerocheck/multilinear.rs:133-137`); the `α³` term of the constant position in the target
and in the terminal identity (`lincheck.rs:1202, 1240`); `T` computed from the `s_i`; the weighted
claim and the limb claims entering the pool. The derived coefficients (`c_0` in the zerocheck
rounds, `v_c = R_zc + v_a·v_b`, `c_1` in the lincheck rounds) are encodings, not checks.

Flock's circuit, its wire positions, the limb slots, the strided selector, `g_0`, `φ_8` and the
modulus of `GF(2^8)`, `k_batch = τ_BLAKE2S` and the floor `τ_BLAKE2S ≥ 3` are transcribed from the
Rust and the Python (the discrepancy *Flock's circuit and constants*). The honest prover is the
specification's and sends the coefficients of the true round polynomial; the pinned Rust prover
fails at `r_eq = 1`, a defect of the implementation (the discrepancy *the Flock prover's
exceptional challenge*), not of the protocol.

Tests: the honest run on a toy circuit accepted; the schedule and the circuit walk against the
Python verifier's (`verifier.py:1092-1295`); the round at `r_eq = 1` with `G(0) ≠ 0`, accepted for
the true coefficients and rejected for the derived ones; `Holds` fails on the zero region (the
constant position is part of the predicate). The definition and its completeness are this
roadmap's and can start now; `flockSecurity` is #3's, and the compiled verifier's fixture waits on
the definition (every proof carries at least eight compressions).

### Layer 10: the opening phase and the oracle protocol

`LeanerVM/Protocol/Opening.lean` (module, over `I`). Needs the spine and Layer 4's `batch`.

```lean
def openingPhase (I) : Phase.Def I (I.Stmt × FlockOut I) Unit (openingSpec I)   -- V_to_P : E
def openingComplete I ; def openingSecurity I        -- (J − 1)/|E| on λ, J the number of pooled claims
def leanVmPhases (I) (h₁ h₂) : Phases I
  -- busPhase, tableSumcheck, deployedPublicInputPhase, flockPhase, openingPhase
```

The opening is the batching challenge `λ` and one weighted query: the verifier turns every
pooled column claim into a weighted claim (`ColumnClaim.holds_iff_weighted`) and the limb claims
into strided ones, adds Flock's weighted claim, forms `W_λ = Σ_j λ^j·W_j` and
`C_λ = Σ_j λ^j·c_j` (ring-switched claims on the low powers, point claims on the high ones),
queries the stack once at `W_λ` and compares the answer with `C_λ`. There is no sumcheck here
(§8.5: "there is no separate reduction sumcheck"): WHIR's own sumcheck is the compilation of this
one query, and the compilation keeps `λ` and replaces the query by `whirOpen` (Layer 11). The state
function is "some pooled claim is false of `q`" before `λ`, "the batched claim is false of `q`"
after; completeness is the linearity of `Weight.pair`.

`leanVmPiop (leanVmPhases I h₁ h₂)` is the protocol; its master theorems are the spine's.
Tests: the phase on the toy, a claim value changed after `λ` rejected, the empty pool; the
protocol on the toy with the phases up to Layer 8 composed and pass-throughs after, honest run
accepted by `#guard`; `piopExtractedStack` returns the committed stack.

### Layer 11: WHIR over binary Reed–Solomon codes, and Merkle trees

`LeanerVM/Protocol/Whir/` (the opening over `E` and `K`, and its soundness; shared with #3's
concrete PCS) with the generic parts in `LeanerVM/Protocol/ToArkLib/` (the components, the schedule
of a list of steps, the sumcheck of a product of two tables), `LeanerVM/Parameters/Whir.lean`,
`LeanerVM/Protocol/Blake2sHash.lean`, `LeanerVM/Protocol/Merkle.lean` (the generic tree, its
octopus and their reading as VCVio's in `LeanerVM/Protocol/ToVCVio/Merkle.lean`),
`LeanerVM/Protocol/Pcs.lean`. Annex B is cited by label (`def:enc`,
`lem:colweight`, `def:listbinding`, `thm:rbr`), since its numbers moved.

```lean
-- Parameters (transcribed, whir_config.rs)
def initialFold := 6 ; subsequentFold := 4 ; initialReduction := 3 ; subsequentReduction := 1
def residualMaxLog := 5 ; queryGrindingBits := 17
structure Level where (fold logInvRate queries : ℕ)   -- no η: no verifier reads it
def ladder (μ R : ℕ) : Option (List Level)            -- none outside the window
def slacks (μ R : ℕ) : Option (List ℚ)                -- the deployed η per level, the exact value of the Rust's double (dumped)
theorem ladder_queries_eq : (ladder 15 1).map (·.queries) = [223, 55]   -- py:910
-- Codes (def:enc)
def novelBasis : Fin 64 → K := fun c ↦ g ^ c.val
def encode (κ R) : (Fin (2^κ) → E) → (Fin (2^(κ+R)) → E)          -- additive NTT on the K basis
theorem encode_K (f) : (∀ x, f x ∈ K) → ∀ y, encode κ R f y ∈ K   -- level 0
def columnWeight (κ R) (x) : Weight κ                             -- mle r = ∏ i, ((1 + r i) + r i · Ŵ_i x)
theorem encode_columnWeight (x) (f) : encode κ R f x = (columnWeight κ R x).pair f   -- lem:colweight
-- The opening as an IOPP (Protocol B.6), generic over the code and the field
def whirOpen (L : Ladder) : OracleReduction … (StmtIn := Weight μ × E) (OStmtIn := codeword oracles) …   -- one batched claim
theorem whirOpen_perfectCompleteness …
theorem whirOpen_rbrSoundness (L : Ladder) (ps : L.Pars) : Security (whirOpen L) (relOpen …) univ (openErr L ps)
  -- thm:rbr for the list relation, per challenge; `Par` per level: a threshold, `ListBound`, `McaBound` (counting form);
  -- the query positions at `((a − 1)/2^{κ+R})^t`: outside the language, fewer than `a` agreements (`card_agree_folded_lt`)
-- Mutual correlated agreement up to Johnson (ToArkLib/McaJohnson.lean, generic)
/-- Mutual correlated agreement up to the Johnson bound, with its constant `a` a parameter. -/
structure McaJohnson (F) [Field F] [Fintype F] [SampleableType F] (a : ℕ → ℕ → ℝ → ℝ) : Prop where
  le : ∀ n (domain : Fin n ↪ F) D η, 1 ≤ D → D ≤ n - 2 → 0 < η → √(D / n) + η ≤ 1 →
    mcaError (AffineLineGenerator F) (code domain (D + 1)) (1 - √(D / n) - η) ≤ ENNReal.ofReal (a n D η / |F|)
theorem mcaJohnson_comparisonEstimate (F) : McaJohnson F johnsonComparisonEstimate   -- the proved bound and its comparison
theorem mcaError_foldLine_eq_affineLine (MC) (δ) :   -- Annex B folds (1 − z)·u₀ + z·u₁; any field, any module code
    mcaError (FoldLineGenerator F) MC δ = mcaError (AffineLineGenerator F) MC δ
theorem natCard_isMCA_le_of_mcaError_le : mcaError G MC δ ≤ ofReal (B / |S|) → Nat.card {x // IsMCA G MC x U δ} ≤ ⌊B⌋₊
-- leanVM's codes (Whir/Johnson.lean): Annex B's constant (thm:mca-johnson), and the adaptor
theorem encode_mem_code ; theorem exists_encode_of_mem_code   -- the encoder's words are `code (domainEmb κ R hb) (2^κ)`
def mcaConstant (n D : ℕ) (η : ℝ) : ℝ := ReedSolomon.HiddenDerivative.johnsonComparisonEstimate n D η
theorem mcaJohnson_annexB (F) : McaJohnson F mcaConstant
theorem mcaBound_of_mcaJohnson (hc : McaJohnson E c) … ((√ρ + η) n ≤ a) (a ≤ n) : McaBound κ R a ⌊c n D η⌋₊
theorem listBound_johnson (m) … (2^κ ≤ a) (n D < a²) : ListBound κ R a m (Code.pairwiseJohnsonListBound n D a)
def threshold (κ R) (η : ℚ) : ℕ                       -- ⌈(√ρ + η) n⌉₊ in naturals; = the ceiling under `Fits`
def Fits (κ R) (η : ℚ) : Prop                         -- decidable: what the interfaces need of a level
def mcaCount (κ R) (η : ℚ) : ℕ                        -- ⌈Annex B's formula at a rational lower bound on √ρ⌉; ≥ mcaConstant under `Fits`
def johnsonPar (sh κ η) (h : Fits κ sh.R η) : Par sh κ  -- a = threshold, L = pairwiseJohnsonListBound n D a, N = mcaCount κ R η; computable
-- The opening at leanVM's parameters (Whir/Deployed.lean)
def deployed (μ R : ℕ) : Option Chain                 -- the ladder's levels with their `johnsonPar`
theorem deployed_isSome : Admissible μ R → (deployed μ R).isSome   -- every deployed level fits
def deployed_rbrSoundness (μ R) (h : Admissible μ R) : Security (whirOpen …) (relOpen …) univ (openErr …)   -- no hypothesis
-- Merkle trees: the Rust's, executable, read as VCVio's (decision 32)
def blake2sBytes : List UInt8 → Vector UInt32 8       -- RFC 7693 over `compress`, last-block flag only
def merkleRootWith (H : List UInt8 → Digest) : Vector (List K) (2 ^ k) → Digest   -- the leaves are leaf images
-- the generic tree (ToVCVio/Merkle.lean): the walk up a pruned opening over a node algebra, and its root
def MerkleTree.fold (A : NodeAlgebra m D T) … ; def MerkleTree.prunedRoot (hash : D → D → m D) (depth) (leaves) (sibs) : m (Option D)
def merkleVerifyWith [Monad m] (H : List UInt8 → m Digest) (root) (depth rowWords leafWords) (queries : List ℕ)
    (paths : PrunedMerklePaths) : m (Option (List (List K)))   -- a phase's pruned opening, rows in query order
def merkleRoot := merkleRootWith blake2sBytes ; def merkleVerify := merkleVerifyWith (m := Id) blake2sBytes
def nodeModel : NodeQueryModel (List UInt8) Unit Digest      -- a node queries left ‖ right; no address
def toBatchOpening (depth) (positions : List ℕ) (leaves siblings : List Digest) :
    Option (BatchOpening Digest (Skeleton.perfect depth))    -- the octopus as VCVio's path-pruned opening
theorem merkle_fits (H : List UInt8 → Digest) :             -- every hash; a reading, kept as a test
    merkleVerifyWith (m := Id) H root depth rowWords leafWords queries paths = some rows ↔
      (one stored row per distinct query, each `rowWords ≤ leafWords` wide, `rows` their leaf images in query order) ∧
      ∃ o, toBatchOpening depth (distinct queries, sorted) (H of each leaf image) paths.siblings = some o ∧
        getPutativeBatchRootWithHash (fun l r ↦ H (bytes l ++ bytes r)) o.values o.proof = root
```

`whirOpen` is Protocol B.6 with its level-0 batching challenge the opening phase's `λ`, not a
second batching, so its input is the one batched claim and not a list: `ℓ_i` plain sumcheck rounds on
the product of the weight and the table, binding the lowest variable first (a round polynomial is
three coefficients here, where the stream carries two), commit, one out-of-domain sample from level 1
on (`ood_samples[0] = 0`), the grinding nonce (17 bits, read before the positions), `t_i` queries,
and the final plaintext level. Four transcript facts are transcribed (`whir.rs`): the level-0 lane
relayout `f(u, x) = q(x, u)` and the rotated terminal point (`:2297-2306`); the out-of-domain
claim's intro round polynomial is sent before each level's `λ_i` and the query batch's after it;
the last round message is omitted; the grinding nonce precedes the positions at every level. Its
soundness is round-by-round soundness for the list relation, not knowledge soundness: the
commitment is list binding (`def:listbinding`), and the invariant is "every codeword within
`γ_i` of the current fold violates the current claim"; Layer 12 turns list binding into
extraction.

The committed stack, its relation and the prover's table are `E`-valued in `whirOpen`, while the
opening phase hands over a `K`-valued column and queries it through `pair (algebraMap K E)`; `E`
is a superset, so completeness covers the `K`-valued stack. The pull request that wires `whirOpen`
into the opening phase owes the `K`-to-`E` lift of the witness and, for soundness, that every
codeword in the list of a `K`-valued word is `K`-valued (`encode_eq_of_agree`).

`McaJohnson` is at Annex B's constant (decision 35). ArkLib's `johnsonComparisonEstimate n D η` is
Annex B's `a` of `thm:mca-johnson`. With `ρ = D/n`, the reduced rate (`whir_config.rs:426-429`),
`θ = max ⌈√ρ/η⌉ 3` and `γ = 1 − √ρ − η`, it reads
`a = (2(θ + ½)^5 + 3(θ + ½)γρ)/(3ρ^{3/2})·n + (θ + ½)/√ρ`. ArkLib proves the bound
(`ReedSolomon.mcaError_affineLine_johnson_le`) with its own exception count, and proves that count
at most `a` (`johnsonExceptionCount_le_comparisonEstimate`). Their composition is `mcaJohnson_annexB`, over
every finite field, so `whirOpen_rbrSoundness` at leanVM's parameters takes no hypothesis
(`deployed_rbrSoundness`); `card_E` turns its bound into numbers. The admitted
`rs_mcaError_le_in_johnson_range` is not consumed.

The soundness theorem takes, per level, a record `Par`: an agreement threshold `a` (the radius `γ`
as `a = ⌈(1 − γ)·2^{κ+R}⌉`, at most the number of positions), a list bound `L` and a bound `N` on the
bad folds, with `ListBound` and `McaBound` the two interfaces in counting form on interleaved words;
they are inhabited at exact agreement and, for the list bound, at unique decoding. `McaBound`'s `N`
is the `a` of `McaJohnson` (Annex B's constant), and `McaJohnson` itself stays the probabilistic
statement. The adaptor from `mcaJohnson_annexB` and the pairwise Johnson list bound to `ListBound`
and `McaBound` gives `deployed_rbrSoundness`, the opening round-by-round sound at leanVM's
parameters with no hypothesis, with `L_0` from 23 to 122 and a least margin of 128.185 bits. The
out-of-domain point is `κ` challenges at `C(L', 2)/|E|` each, whose sum is the pinned entry.
The query positions' entry is `((a − 1)/2^{κ+R})^t`: a table that satisfies the residual claim
outside its language agrees with the folded word on fewer than `a` positions
(`card_agree_folded_lt`). Annex B's `thm:rbr` states the entry as `(1 − γ)^t`; since
`a − 1 < (1 − γ)·2^{κ+R}`, the entry here is strictly below the Annex's at every level. Counting `a`
agreements, `(a/n)^t` would exceed the Annex's whenever `(1 − γ)·n` is not an integer, the deployed
case: 48 of the 224 deployed levels would be above `2^{−111}` (worst `2^{−110.34}`, stack size 16,
rate `2⁻¹`, level 2: `t = 30`, `a = 40`, `n = 2^9`); with `a − 1` every level is below `2^{−111}`
(worst `2^{−111.00024}`, stack size 23, rate `2⁻²`, level 0).

In the Johnson regime the interfaces are inhabited from ArkLib (`Whir/Johnson.lean`). The
encoder's words are exactly ArkLib's Reed–Solomon code of dimension `2^κ` on the points `x_v`
(`encode_mem_code`, `exists_encode_of_mem_code`), so `McaBad` is ArkLib's `IsMCA` event for the
fold line at radius `1 − √ρ − η`, and `mcaBound_of_mcaJohnson` gives `McaBound` at
`N = ⌊a n D η⌋₊` for every threshold `a ≥ (√ρ + η)·n`, through the counting form of an error
bound (`natCard_isMCA_le_of_mcaError_le`). The list bound is not the Annex's `1/(2η√ρ)` but
ArkLib's pairwise Johnson bound over the alphabet of rows, `L = ⌊n(a − D)/(a² − nD)⌋`
(`listBound_johnson`): two interleaved codewords agree on fewer than `2^κ` positions. It is the
smaller at every deployed level. The threshold is the exact ceiling `⌈(√ρ + η)·n⌉₊`, the least
agreement within the Annex's radius `γ`, computed in naturals from the rational `η`
(`threshold`); the Rust has no integer threshold. `Fits` is the decidable list of facts a level
needs (among them that `threshold` is that ceiling, `threshold_eq_ceil`), `johnsonPar` builds the
level's `Par` from it, with `N = mcaCount κ R η`, Annex B's formula rounded up at a rational lower
bound on `√ρ` and the exact `θ` (`mcaConstant_le_mcaCount`), so that the parameters, and every
extractor built over them, are computable; `deployed` builds the chain of every admissible
ladder with its slacks; `deployed_isSome` decides that all 224 levels fit. The slacks are a table beside the
ladder (`slacks`), not a field of `Level`, since no verifier reads them.

ArkLib's line is `u₀ + x·u₁`, while Annex B folds `(1 − z)·u₀ + z·u₁`.
`mcaError_foldLine_eq_affineLine` equates the two over any field: the substitution
`(u₀, u₁) ↦ (u₀, u₁ − u₀)` is a bijection on pairs that keeps "both rows agree with the code on
`T`". Annex B's characteristic-two remark is the special case `u₁ − u₀ = u₀ + u₁`.

At the deployed ladder, the MCA share of every fold challenge, `2^{ℓ−1}·a/|E|`, is at most
`2^{−128.18}`, with the least margin at level 0 of `(μ, R) = (27, 3)`. ArkLib's own count is
10 to 21 bits smaller, so the margin there is `2^{−143.16}`. The record, with the reproduction
of the Rust's η search, is [whir-mca-budget.md](../reviews/whir-mca-budget.md).

`η` is transcribed as the exact dyadic rational of the Rust's double, dumped by
`scripts/dump-whir-eta-rust.sh`, and `a` is computed from it exactly. The Rust tunes `η` until its
floating-point `⌈√ρ/η⌉` equals the target `m`, but at 108 of the 224 deployed levels the exact
ceiling is `m + 1`. So `θ` is computed, never set to `m`
([leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin)).

The Merkle trees `verify` runs are the Rust's, transcribed and executable: `merkleVerifyWith` is the
generic walk `MerkleTree.fold` at the byte hash. `merkle_fits` reads them as VCVio's (decision 32),
a cross-check of the transcription against an independent library, kept as a test and a step of no
proof: binding is proved by replaying the log on `MerkleTree.fold` (Layer 12, decision 39). A leaf
is BLAKE2s-256 of a row's leaf image, 512 or 384 bytes, several chained compressions, and a node is
BLAKE2s-256 of its children's 64 bytes, one compression, with no tag and no position
(`fiat_shamir/src/merkle.rs:38-67`). The random oracle of Layer 12 is BLAKE2s-256 on byte strings,
so it covers both. In VCVio's terms the node hash is `nodeModel`, a `NodeQueryModel` on that one
oracle with `Address := Unit`: VCVio allows a node hash that carries no position, and queries
outside the model, such as the Fiat–Shamir chain's 64-byte steps. The tree is
`Skeleton.perfect depth`, whose leaf order (`SkeletonLeafIndex.ofNat`, the top bit choosing the
root's child) is the Rust's; VCVio's paths run from the root, the Rust's from the leaf. A phase's
opening is the Rust's octopus: the rows at the sorted distinct positions and one list of siblings,
bottom-up (`PrunedMerklePaths::open`, `merkle.rs:163-235`). `toBatchOpening` reads it as VCVio's
path-pruned `BatchOpening`, whose shape is canonical for its leaves, so a missing or surplus sibling
has no reading, as the Rust rejects it. `merkle_fits` holds for every hash function; at
`blake2sBytes` it is the deployed check. The generic tree, its octopus and `toBatchOpening` are
VCVio candidates.

Tests:
- `encode` against CompPoly's additive NTT at `κ = 3`, over `K` and `E`;
- `merkleVerify` on the Rust's octopus vectors (`fiat_shamir/src/merkle.rs:283-351`: eight
  leaves, queries `[5, 1, 5, 3, 1]`), accepted, and each malformed phase there rejected: a
  surplus, missing or flipped sibling, a flipped or wide row, a wrong announced width or query
  count, an out-of-range query;
- `toBatchOpening` on the same vectors: VCVio's root equals the Rust's, and no malformed phase has
  a reading;
- `blake2sBytes` on the RFC 7693 vector;
- the honest `whirOpen` at toy parameters (`μ = 4`, rate `1/2`), accepted;
- the parameter tables against `py:910`;
- every pinned coding parameter, with a witness that it is achievable;
- `mcaConstant n D η` unfolded to Annex B's formula, transcribed from `thm:mca-johnson`, so that
  a pin bump that changes ArkLib's definition is caught;
- at every level of the ladder, the hypotheses of `mcaJohnson_annexB` (`1 ≤ D ≤ n − 2`,
  `√ρ + η ≤ 1`) and the bound `2^{ℓ−1}·a ≤ 2^{64}`. Each level's ceilings are proved from
  rational bounds on `√ρ`, as the record does by hand at two levels;
- the threshold and list bound at the record's two levels, the range of `L_0` over the window,
  the deployed chain's levels against the ladder, and the threshold one off in either direction
  rejected.

### Layer 12: compilation, the transcript, the proof, and the executable verifier

`LeanerVM/Protocol/Transcript.lean`, `Proof.lean`, `Compile.lean`, `Verify.lean`,
`ListBinding.lean`, `ListBindingDeployed.lean`, `RandomOracle.lean` (plain);
`LeanerVM/Protocol/Whir/Decode.lean`, `Whir/Transform.lean`, `Whir/DecodeNtt.lean`; and the
generic `ToVCVio/ChargedInvariant.lean` (with `ToVCVio/ScalarExpectation.lean`),
`ToVCVio/MerkleLog.lean` (leanVM's half `Protocol/MerkleBinding.lean`), `ToArkLib/Relist.lean`,
`ToArkLib/SendEncoded.lean`, `ToArkLib/MapOracles.lean`, `ToArkLib/FirstRound.lean` and
`ToCompPoly/LinearSolve.lean`; the `K` word `KWord` is in `Whir/Word.lean`.
`F` below is `blake2sFlockSpec`.

```lean
-- The one oracle: BLAKE2s-256 on byte strings (RandomOracle.lean)
abbrev Digest := Vector UInt32 8
noncomputable instance : Fintype Digest     -- through `Fintype.ofFinite`: nothing enumerates at load; none at the pin
theorem card_digest : Fintype.card Digest = 2 ^ 256
instance : SampleableType Digest            -- through an equivalence, as Layer 0 samples `K`
abbrev hashSpec := List UInt8 →ₒ Digest     -- `IsUniformSpec hashSpec`: a local instance, `IsUniformSpec.ofFintypeInhabited`
def hashQuery (t : List UInt8) : OracleComp hashSpec Digest := liftM (hashSpec.query t)
abbrev Adversary := OracleComp hashSpec Proof   -- a cheating prover: hash queries, no coins; `IsTotalQueryBound A Q`
def runRandom (oa : OracleComp hashSpec α) : ProbComp (α × hashSpec.QueryCache) :=
  (simulateQ hashSpec.randomOracle oa).run ∅    -- a fresh query answered uniformly, a repeat from the cache
def runBlake2s (oa : OracleComp hashSpec α) : ProbComp α := simulateQ (fun t ↦ pure (blake2sBytes t)) oa   -- one value
-- The Fiat–Shamir chain (Transcript.lean; transcribed, fiat_shamir/src/lib.rs:36-174)
structure FsState where cv : Digest
def FsState.seed (prog) (input) : FsState     -- cv₀ = compress (iv, the public input), iv from the program hash:
                                              -- constants of the statement, computed by `blake2sBytes`, not queries
inductive Block | observe (x : E) | squeeze | nonce (n : E)     -- tags 1, 2, 4 in lane 3
def FsState.step [Monad m] (H : List UInt8 → m Digest) : FsState → Block → m FsState   -- cv ← H (cv ‖ b)
def FsState.checkPow [Monad m] (H) (s : FsState) (bits : ℕ) (n : E) : m (Bool × FsState)
  -- the check `H (H (cv ‖ tag 3) ‖ n ‖ tag 4)` has `bits` low zero bits; the nonce is absorbed either way
def FsState.challengeOf (d : Digest) : E                         -- the first three 64-bit words; 2^64 preimages each
def chainHistory (log : hashSpec.QueryLog) (s : FsState) : Option (List (Block × Digest))
  -- from `s` back to `cv₀`, each step the one logged query `cv ‖ b` answered by the current state; `none` otherwise
theorem chainHistory_determined (h : no collision and no hit in log) :   -- a history, once in the log, never changes
    chainHistory (log.take k) s = some hs → chainHistory log s = some hs
-- The proof object and its transcript (Proof.lean; transcribed, transcript.rs:9-19, 280-330)
structure Proof where (stream : List E) (merkle : List PrunedMerklePaths)
def Proof.sizes? : Proof → Option Sizes                          -- the announced sizes, read off the stream
def RoundPoly.decode (d) (claim) (eq? : Option E) : List E → Option (Vector E (d + 1))
def decodePrefix (prog) : List (Block × Digest) → Option (Σ s ρ i, (leanVmIopp F prog s ρ).Transcript i)
  -- a chain history as a prefix of the compiled transcript: the sizes off its first blocks, the observed scalars as
  -- messages, a squeeze as a challenge by `challengeOf` (a query group as one challenge: WHIR's query positions)
theorem decodePrefix_mono : decodePrefix prog hs = some ⟨s, ρ, i, tr⟩ →
    decodePrefix prog (hs ++ hs') = some ⟨s', ρ', j, tr'⟩ → s' = s ∧ ρ' = ρ ∧ i ≤ j ∧ tr' extends tr
def decode (prog) (hs) : Option (Σ s ρ, (leanVmIopp F prog s ρ).FullTranscript)   -- `decodePrefix` at a full transcript
-- The compiled oracle protocol: the level-0 word committed, WHIR in place of the opening's query (Compile.lean)
def leanVmIopp (F) (prog) (s) (ρ) :=
  commitWord ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫ batch ⟫ openInput ⟫ whirOpen (ladder (leanIsaμ prog s) ρ)
-- One verifier, generic in how the hash is answered (Verify.lean; written from §8.5 first)
def verifyWith [Monad m] (H : List UInt8 → m Digest) (prog : Program) (input : PublicInput) (proof : Proof) : m Bool
  -- 1. the sizes, the caps and the windows, and the number and shapes of `proof.merkle`: no query before them,
  --    none on a proof they reject
  -- 2. the chain walk: every chain step and grinding query, in stream order; the challenges
  -- 3. every Merkle opening against its root, by `merkleVerifyWith H`; the rows
  -- 4. the algebra: every phase's checks and WHIR's terminal check on the stream, the challenges and the rows; no query
def verify (prog input proof) : Bool := verifyWith (m := Id) blake2sBytes prog input proof
theorem verifyWith_simulateQ [LawfulMonad m] (impl : QueryImpl hashSpec m) :
    simulateQ impl (verifyWith hashQuery prog input proof) = verifyWith impl prog input proof
def rounds : ℕ ; verifierQueries : ℕ ; proofDigests : ℕ          -- numerals, at the largest admissible sizes
theorem rounds_bound         -- a run of `verifyWith` closes at most `rounds` challenges (a query group once)
theorem verifierQueries_bound (prog input proof) : IsTotalQueryBound (verifyWith hashQuery prog input proof) verifierQueries
theorem proofDigests_bound   -- a run of `verifyWith` reads at most `proofDigests` digests of the proof
theorem verify_iff_compiled (prog input proof) :
    verify prog input proof = true ↔
      ∃ s ρ tr rows, proof.sizes? = some s ∧ s.Admissible prog ∧ validRate ρ ∧
        decode prog (the history of verify's chain walk) = some ⟨s, ρ, tr⟩ ∧ every grinding check passes ∧
        merkleOpenings blake2sBytes proof tr = some rows ∧
        (leanVmIopp F prog s ρ).verifier accepts (input, tr), its oracle queries answered by `rows`
  -- the level-0 rows read as `K` symbols (the committed word is a `KWord`), the other levels' as `E`
-- List binding (Whir/Word.lean, Whir/Decode.lean, ToArkLib/{Relist,SendEncoded,MapOracles,FirstRound}.lean,
-- ToCompPoly/LinearSolve.lean, ListBinding.lean)
structure KWord (ℓ b t : ℕ) where row : Fin (2 ^ b) → Vector K (2 ^ ℓ)   -- level 0's word: rows of `K` symbols
def KWord.lift (w : KWord ℓ b t) : Word E ℓ b t                         -- the same word read in `E`
def kwordOf (ℓ κ R t) (q : Vector K (2 ^ (κ + ℓ))) : KWord ℓ (κ + R) t  -- the honest word of a stack
theorem kwordOf_lift : (kwordOf ℓ κ R t q).lift = wordOf … (q in E)    -- what WHIR's honest prover commits
structure ListDecoder (κ R a ℓ : ℕ) where           -- `a` is level 0's threshold `Par.a`
  decode : LW (κ + R) → List (Msgs ℓ κ)
  mem_iff : ∀ F V, V ∈ decode F ↔ Cl κ R a ℓ F V
  nodup : ∀ F, (decode F).Nodup                     -- so that `ListBound` bounds its length (`length_le`)
def gaussSolve (n) (M : Fin n → Fin n → F) (y : Fin n → V) : Option (Vector V n)   -- `V` a module: all lanes at once
def ListDecoder.bruteForce (hdist : 2 ^ κ ≤ a) (hb : κ + R ≤ 64) : ListDecoder κ R a ℓ
  -- one elimination over `K` on every set of `2^κ` positions; computable, toy words only
def exactFast (κ R ℓ) (F : LW (κ + R)) : Option (Msgs ℓ κ)
  -- the elimination on the first `2^κ` positions, kept when its encoding is the whole word:
  -- `O(2^(3κ) + 2^(2κ+ℓ))` for the elimination and `2^(κ+R+ℓ)` encodings of `O(κ·2^κ)` for the check
theorem exactFast_eq (D : ListDecoder κ R a ℓ) (hdist : 2 ^ κ ≤ a) (hle : a ≤ 2 ^ (κ + R)) (hb)
    (h : exactFast κ R ℓ F = some V) : ∀ V', V' ∈ D.decode F ↔ V' = V   -- no unique-decoding condition
def ListDecoder.exactFirst (D) (hdist) (hle) (hb) : ListDecoder κ R a ℓ   -- `exactFast`, else `D`
def ListDecoder.exact (hb) : ListDecoder κ R (2 ^ (κ + R)) ℓ             -- at exact agreement, `exactFast` alone
theorem isInK_of_cl (hdist : 2 ^ κ ≤ a) (hb) (hF : ∀ y u, IsInK (F y u)) (h : Cl κ R a ℓ F V) :
    ∀ u x, IsInK (V u)[x]
def stackOfMsgs (hμ : κ + sh.ℓ = I.μ) (g : Msgs sh.ℓ κ) : Column I.μ     -- the lanes on top, the `K` limb of each symbol
def stackList (D) (hμ) (o : ∀ i, KOracle sh κ i) : List (∀ i, TheOracle I i)   -- `D.decode`, each member a stack
def Component.relistRel (list : (∀ i, O' i) → List (∀ i, O i)) (rel) := {((x, o'), w) | ∃ o ∈ list o', ((x, o), ()) ∈ rel}
def Component.Front.relist (hF : Component.Front D) (hF' : Component.Front D') (hcheck : hF'.check = hF.check)
    (hout : hF'.out = hF.out) (list : (∀ i, O' i) → List (∀ i, O i)) (S : Component.Security D relIn relOut ε)
    (L) (hL : ∀ o, (list o).length ≤ L) :
    Component.Security D' (relistRel list relIn) (relistRel list relOut) (fun i ↦ L • ε i)
  -- `D'` the same front verifier over other oracles (`Front.over` builds it, answering the queries it never makes);
  -- the extractor keeps the witness, the state function is `∃ q ∈ list o, kSF q`
def Component.Front.overComplete (hF : Component.Front D) (C : Complete D relIn relOut) … :
    Complete (hF.over o₀ (proverVia P read)) (viaRel good read relIn) (viaRel good read relOut)
def commitWord (I) (hμ) : Component.Def I.Stmt NoOracle (Column I.μ) I.Stmt (KOracle sh κ) (Column I.μ) _
  -- `Component.sendEncoded`: the prover sends `kwordOf` of its stack
def commitPick (I) (D) (hμ) (s) (w : KWord …) : Option (Column I.μ)   -- the first of `stackList` with `M3Holds` (decidable)
def commitWordSecurity (D) (hμ) : Component.Security (commitWord I hμ) (M3Rel I)
    (relistRel (stackList I D hμ) (Seam.commit I)) 0                    -- extractor `commitPick`, else the witness
def openInput (I) (hμ) : Component.Def (WeightedClaim I) (KOracle sh κ) _ (Weight E (κ + sh.ℓ) × E) (OneW sh κ) _ !p[]
  -- `Component.mapOracles`: the batched claim, the word read in `E` (a virtual output oracle) and the stack read in `E`
theorem relist_of_relOpen (P : Par sh κ) (D : ListDecoder κ sh.R P.a sh.ℓ) (c) (o)
    (h : OpenLang P (c.weight at height κ + sh.ℓ) c.value (o 0).lift) : ∃ q ∈ stackList I D hμ o, c.Holds q
def openInputSecurity (P) (D) : Component.Security (openInput I hμ)
    (relistRel (stackList I D hμ) (Opening.BatchedHolds I)) (relOpen P) (no challenge)
def listBinding_compile (P : Phases I) (S : P.Security) (hμ : κ + sh.ℓ = I.μ) (L : Ladder sh κ) (ps : L.Pars)
    (D : ListDecoder κ sh.R (L.headPar ps).a sh.ℓ) :
    Component.Security (commitWord ⟫ fronts.over ⟫ batch.over ⟫ openInput ⟫ whirOpen L) (M3Rel I) univ
      (listBindingError I L ps)
  -- 0 on the commitment; `(L.headPar ps).L` times the phase's error on every challenge of the four front phases and
  -- of the opening's batching (its state function is relisted too); `openErr L ps` on WHIR's, not multiplied:
  -- after `openInput` the state function is WHIR's, whose relation quantifies over the list.
  -- `relist`'s `hL` is `Par.hlist` through `length_stackList`. The bundle's opening phase is not used.
theorem listBinding_kSF_one … (k : Fin _) (hk : k.val = 1) (tr : Transcript k) (w) :   -- a symbolic round
    (listBinding_compile P S hμ L ps D).kSF.toFun k s tr w ↔ (commitPick I D hμ s.1 (committedWord tr)).isSome
theorem listBinding_extractedStack_eq … (hq : commitPick I D hμ s.1 (committedWord tr) = some q) :
    extractIn (listBinding_compile P S hμ L ps D).extractor s tr () = q
theorem listBinding_perfectCompleteness (C : P.Complete) (L) (init impl) :
    (listBindingDef P hμ L).red.perfectCompleteness init impl (M3Rel I) univ
-- generic, for the two theorems above (ToArkLib/FirstRound.lean)
theorem Component.Security.append_kSF_left : up to the seam, a sequence's state function is the first component's
def Extractor.RoundByRound.DecodesFirst (E) (hn) (f : StmtIn → pSpec.Type 0 → Option WitIn) : Prop
theorem Extractor.RoundByRound.decodesFirst_append ; theorem Extractor.RoundByRound.extractIn_eq_of_decodesFirst
-- The additive transform (Whir/Transform.lean) and the exact path by it (Whir/DecodeNtt.lean)
def fwd (φ) (j) (m : Vector S (2 ^ j)) (s : K) : Vector S (2 ^ j)   -- Lin–Chung–Han: Ŵ_j is s's value on one half, +1 on the other
def inv (φ) (j) (v : Vector S (2 ^ j)) (s : K) : Vector S (2 ^ j)   -- its inverse, the same recursion
theorem fwd_getElem (hj : j ≤ 64) : (fwd φ j m s)[w] = Σ_u X_u(x_w + s) · m[u]
theorem fwd_inv : fwd φ j (inv φ j v s) s = v ; theorem inv_fwd : inv φ j (fwd φ j m s) s = m
def encodeFast (φ κ R) (m) : Vector S (2 ^ (κ + R))                 -- one `fwd` per coset x_{c 2^κ} + U_κ
theorem encodeFast_getElem (hb : κ + R ≤ 64) : (encodeFast φ κ R m)[y] = encode φ κ R m y
def exactNtt (κ R ℓ) (F : LW (κ + R)) : Option (Msgs ℓ κ)           -- per lane: `inv` on the first coset, `encodeFast` checks the lane
theorem exactNtt_spec (hb) : exactNtt κ R ℓ F = some V → ∀ y u, encode (V u) y = F y u
theorem exactNtt_of_codeword (hb) : (∀ y u, encode (V u) y = F y u) → exactNtt κ R ℓ F = some V
theorem ListDecoder.decode_eq_of_codeword (D) (hdist) (hle) (hb) (hV : ∀ y u, encode (V u) y = F y u) :
    ∀ V', V' ∈ D.decode F ↔ V' = V                                 -- `exactFast_eq` is its instance
def ListDecoder.nttFirst (D) (hdist) (hle) (hb) : ListDecoder κ R a ℓ   -- `exactNtt`, else `D`
def kwordOfFast (ℓ κ R t) (q) : KWord ℓ (κ + R) t ; theorem kwordOfFast_eq (hb) : kwordOfFast … q = kwordOf … q
-- Level 0 of the deployed chain (Whir/Deployed.lean) and the list binding at leanVM (ListBindingDeployed.lean)
theorem deployedChain_head (h : Admissible μ r) :                    -- decided on the window
    (deployedChain μ r h).sh = deployedHeadShape μ r ∧ (deployedChain μ r h).κ = deployedHeadKap μ r ∧
      (level 0's Par).a = deployedHeadThreshold μ r                   -- = threshold (μ - 6) r η₀, johnsonPar's
def deployedDecoder (h : Admissible μ r) : ListDecoder … (level 0's Par).a …   -- `nttFirst` over `bruteForce`; computable
def listBinding_deployed (F prog s) (hs : s.Admissible prog) (ρ) (hρ : validRate ρ) :      -- computable
    Security (listBindingDef (leanVmPhases (leanIsaInstance F prog s) leanIsa_conditions) _ (deployedChain …).ladder)
      (M3Rel (leanIsaInstance F prog s)) univ (listBindingError …)  -- `leanVmSecurity` at `I.d ≤ 2`, `deployedDecoder`
theorem listBinding_deployed_rbrKnowledgeSoundness … ; theorem listBinding_deployed_perfectCompleteness …
def deployedPick (I) (h : Admissible I.μ r) : I.Stmt → KWord (level 0's computed indices) → Option (Column I.μ)
theorem deployedPick_eq_commitPick : commitPick I (deployedDecoder h) _ s w = deployedPick I h s (headWord h w)
theorem listBinding_deployed_kSF_one (k) (hk : k.val = 1) … : kSF k s tr w ↔ (deployedPick … (committedWord tr)).isSome
theorem listBinding_deployed_extractedStack_eq … (hq : deployedPick … (committedWord tr) = some q) : extractIn … = q
theorem commitPick_isSome_iff : (commitPick I D hμ s x).isSome ↔ ∃ q ∈ stackList I D hμ x, M3Holds I s q
theorem commitPick_eq_some : commitPick I D hμ s x = some q → M3Holds I s q
-- Merkle binding by log replay (ToVCVio/MerkleLog.lean, generic over the leaf and node encodings,
-- which may overlap; Protocol/MerkleBinding.lean for leanVM's; deterministic, on `MerkleTree.fold`)
def nodePreimage (node? : Q → Option (D × D)) (log : QueryLog Q D) (d : D) : Option (D × D)
  -- the children of the first logged query answered by `d` that parses as a node
def leafPreimage (leaf? : Q → Option P) (log) (d : D) : Option P   -- the first that parses as a leaf
def extractTree (node?) (log) (top : D) (h p : ℕ) : Option D       -- top-down by the bits of `p`
def extractLeaf (node?) (leaf?) (log) (root) (depth p) : Option P :=
  (extractTree node? log root depth p).bind (leafPreimage leaf? log)
def extractLeaves (node?) (leaf?) (log) (root) (depth) : List (Option P)   -- one pass, hash maps
theorem extractLeaves_eq : extractLeaves … = (List.range (2 ^ depth)).map (extractLeaf …)
def Consistent (log) : Prop      -- no input with two answers
def HasCollision (log) : Prop    -- two inputs, one answer
def Fresh (log) (q) : Prop       -- `log` never asks `q`
def Known (node?) (roots) (logA) (d) : Prop   -- a root, or a child of a query of `logA` parsing as a node
def FreshHit (node?) (roots) (logA logV) : Prop := ∃ e ∈ logV, Fresh logA e.1 ∧ Known node? roots logA e.2
theorem MerkleTree.binding_of_log (hnode : node? (nodeEnc l r) = some (l, r))
    (hans : ∀ q d, ans q = some d → ⟨q, d⟩ ∈ logA ++ logV) (hroot : root ∈ roots)
    (hlen) (hsorted : positions.Pairwise (· < ·)) (hlt : ∀ p ∈ positions, p < 2 ^ depth)
    (hleaves : Forall₂ (fun x d ↦ ∃ q, leaf? q = some x ∧ ans q = some d) payloads digests)
    (hwalk : prunedRoot (fun l r ↦ ans (nodeEnc l r)) depth (positions.zip digests) sibs = some (some root))
    (hcons : Consistent (logA ++ logV)) (hcoll : ¬ HasCollision (logA ++ logV))
    (hhit : ¬ FreshHit node? roots logA logV) :
    positions.map (extractLeaf node? leaf? logA root depth) = payloads.map some
theorem MerkleTree.extractLeaf_determined (hroot : root ∈ roots) (hcons) (hhit) :
    extractLeaf node? leaf? (logA ++ logV) root depth p = extractLeaf node? leaf? logA root depth p
-- leanVM: nodes parse as 64-byte inputs (`nodeOfBytes?`), leaves as a row's leaf image (`leafRow?`)
def extractRows (log) (root) (depth rowWords leafWords p) : Option (List K)   -- the row width strips the zero prefix
def extractAllRows (log) (root) (depth rowWords leafWords) : List (Option (List K)) ; theorem extractAllRows_eq
theorem binding_of_log (hans) (hroot)
    (hV : merkleVerifyWith (m := Option) ans root depth rowWords leafWords queries paths = some (some rows))
    (hcons) (hcoll) (hhit : ¬ FreshHit nodeOfBytes? roots logA logV) :
    queries.map (fun q ↦ (extractRows logA root depth rowWords leafWords q).map (leafImage leafWords)) = rows.map some
theorem extractRows_determined (hroot) (hcons) (hhit) :
    extractRows (logA ++ logV) root depth rowWords leafWords p = extractRows logA root depth rowWords leafWords p
-- The charged invariant (ToVCVio/ChargedInvariant.lean; generic; `𝔼[f | mx]` is `∫⁻ r, r ∂𝒟[f <$> mx]`)
def chargedRandomOracle (charge : spec.QueryCache → spec.Domain → ℝ≥0∞) :
    QueryImpl spec (StateT (spec.QueryCache × ℝ≥0∞) ProbComp)   -- `randomOracle` with a running total of fresh charges
theorem potential_le_expected_charge (Φ : spec.QueryCache → ℝ≥0∞) (charge)
    (hstep : ∀ c t, c t = none → 𝔼[fun u ↦ Φ (c.cacheQuery t u) | $ᵗ spec.Range t] ≤ Φ c + charge c t) (oa) (c) :
    𝔼[fun z ↦ Φ z.2 | (simulateQ spec.randomOracle oa).run c] ≤
      Φ c + 𝔼[fun z ↦ z.2.2 | (simulateQ (chargedRandomOracle charge) oa).run (c, 0)]   -- from any initial cache
theorem prEvent_le_of_potential ; prEvent_not_good_le_expected_charge   -- an event on the run's output and final
                                     -- state, under the potential; an invariant broken at a fresh query
theorem expected_charge_le_mul (hκ : charge ≤ κ on the caches reachable within the budget) (hn : IsTotalQueryBound oa n) :
    expected total ≤ n * κ          -- so the charges `|c|/|Y|` and `|inPlay|/|Y|` give `n·(|c₀| + n)/|Y|`
theorem expected_fresh_in_le (S : Finset Y) (hn : IsTotalQueryBound oa n) : expected fresh answers in S ≤ n * (|S| / |Y|)
def chargedLoggingOracle (charge : spec.QueryLog → spec.Domain → ℝ≥0∞) :   -- the same, its state also the ordered log
    QueryImpl spec (StateT (spec.QueryCache × spec.QueryLog × ℝ≥0∞) ProbComp)   -- for the hit clause
theorem potential_log_le_expected_charge (Φ : spec.QueryLog → ℝ≥0∞) …   -- the expected potential, read on the log
-- The game, the extractor and the hash's misbehaviour (RandomOracle.lean)
structure Run where (proof : Proof) (logA logV : hashSpec.QueryLog) (ok : Bool)   -- `ok`, the verdict
def Run.log (g : Run) := g.logA ++ g.logV
def loggedGame (prog input) (A : Adversary) : OracleComp hashSpec Run := do
  let (proof, logA) ← A.withQueryLog
  let (ok, logV) ← (verifyWith hashQuery prog input proof).withQueryLog
  return ⟨proof, logA, logV, ok⟩
def extract (prog input proof) (log : hashSpec.QueryLog) : Option (Σ s, Column (leanIsaμ prog s))
  -- as built, `extract F …` takes the Flock specification `F`, the deployed one at the headline; the level-0 wire
  -- shape it reads (rows of `level0Lanes`, leaves of `2^ℓ`, depth `deployedHeadKap + R`) is the one the verifier
  -- authenticates, and `level0Lanes` is `Verify.nLanes` by `deployedHeadKap_eq`
  -- the admissible sizes off `proof`; the level-0 `K` word off `log` by `extractAllRows` at the root in `proof`, at
  -- the row widths of those sizes, a missing row read as zero; `deployedDecoder` (`exactNtt`, else
  -- `ListDecoder.bruteForce`); the member satisfying `M3Holds`, or `none`
def Extracts (prog input proof log) : Prop :=
  ∃ s q, extract prog input proof log = some ⟨s, q⟩ ∧ M3Holds (leanIsaInstance F prog s) input q
theorem extracts_iff_isSome : Extracts prog input proof log ↔ (extract prog input proof log).isSome   -- `M3Holds` automatic
/-- Two different inputs in the log with one answer. -/
def LogHasCollision (log) : Prop := ∃ i j, log[i].1 ≠ log[j].1 ∧ log[i].2 = log[j].2
/-- A digest, on its input's first query, equal to one already in play: a 32-byte block of an earlier input, a
digest absorbed as two scalars (`scalars_to_hash (s₁, s₂)` of two consecutive observe blocks of a chain, as a root
is), or the seed's digests; for the verifier's queries, also one of the proof's roots. An earlier answer to another
input is not in play: equal to it, the answer is a collision. -/
def Hit (rootsOf) (prog input) (g : Run) : Prop :=
  ∃ k, g.log[k] is its input's first query ∧
    (g.log[k].2 ∈ inPlay prog input (g.log.take k) ∨ (g.logA.length ≤ k ∧ g.log[k].2 ∈ rootsOf g.proof))
/-- The bad challenges at a prefix of the compiled transcript ending at a challenge `i`: those that turn the state
function of `listBinding_compile` at `leanVmSecurity`, `deployedDecoder` and `F` from false to true, the
committed words given. A query group's challenge is the pair of the grinding check's digest and the positions, and a
bad one passes the check. -/
def Bad (prog s ρ i) (tr : Transcript i) (words) : Set (Chal i) := {c | ¬ kSF i tr words ∧ kSF (i + 1) (tr.concat c) words}
theorem bad_density (hs : s.Admissible prog) : Pr[fun c ↦ c ∈ Bad prog s ρ i tr words | $ᵗ Chal i] ≤ εquery
/-- A challenge of the proof's own chain in the bad set of its prefix: at its first occurrence `k` in the log, the
query closing a challenge of the verifier's chain walk on `proof` has a history decoding to an admissible prefix that
ends at a challenge, and the challenge is bad there, the words read off `log.take k` with missing rows zero. -/
def Flip (prog input) (g : Run) : Prop :=
  ∃ k hs s ρ i tr, g.log[k] closes a challenge of `g.proof`'s chain and is its input's first query ∧
    chainHistory (g.log.take k) (its state) = some hs ∧ decodePrefix prog hs = some ⟨s, ρ, i, tr⟩ ∧
    `i` is a challenge ∧ s.Admissible prog ∧ (its challenge) ∈ Bad prog s ρ i tr (zero-filled `extractRows (g.log.take k)`)
def HashMisbehaves (rootsOf) (Flip) (prog input) (g : Run) : Prop := LogHasCollision g.log ∨ Hit rootsOf prog input g ∨ Flip g
  -- the proof's roots and the flip are parameters until the transcript decoder defines both from the verifier's
  -- chain walk; `core` instantiates them with the decoder's, and `HashMisbehaves prog input` below stands for
  -- `HashMisbehaves (rootsOf prog input) (Flip prog input) prog input`
-- Deterministic, for every function answering the hash
theorem core (hcons : g.log is consistent with a function) (hV : g.logV is the log of `verifyWith` on `g.proof`,
    its verdict `true`) (hX : ¬ Extracts prog input g.proof g.logA) : HashMisbehaves prog input g
-- The random-oracle model
def hashTerm (V Q) : ℝ≥0 := (Q + V) * (4 * (Q + V) + 8) / 2 ^ 256
def niError (ε : ℝ≥0) (V Q) : ℝ≥0 := (Q + V) * ε + hashTerm V Q   -- ε the density of every bad set
-- for a statement fixed before the adversary runs; `V := verifierQueries`
theorem misbehaves_rom (hQ : IsTotalQueryBound A Q) :
    Pr[fun z ↦ HashMisbehaves prog input z.1 | runRandom (loggedGame prog input A)] ≤ niError εquery verifierQueries Q
theorem niError_le (V Q) : niError εquery V Q ≤ (Q + V) / 2 ^ 128 + hashTerm V Q
theorem verify_knowledgeSound_rom (hQ : IsTotalQueryBound A Q) :
    Pr[fun z ↦ z.1.ok = true ∧ ¬ Extracts prog input z.1.proof z.1.logA | runRandom (loggedGame prog input A)]
      ≤ niError εquery verifierQueries Q
```

`verify` is one function, phase by phase in the stream order, total and computable, and the first
module whose code-generation probe is a test. It is `verifyWith` at the deployed hash, in four
stages: the sizes, caps and windows, and the number and shapes of the openings, before the first
query, so that `verifierQueries_bound` holds for every proof; the chain walk, which the Merkle
roots enter as observed scalars; the Merkle openings; and the algebra, which makes no query. A
run's log is therefore the chain's queries followed by the openings', which is what `core` reads.
`verifyWith_simulateQ` makes it one verifier: the random-oracle run, the BLAKE2s run and the
logged run of the game are `verifyWith` at three ways of answering the oracle, and `verify` is the
one at `blake2sBytes`. Lean has no parametricity theorem, so it is proved by pushing `simulateQ`
through `verifyWith`'s body (`simulateQ_bind`, `simulateQ_query`), and `verifyWith` is written by
structural recursion on the stream, with no `partial` definition. A verifier written separately
for the random-oracle model would make every theorem below a statement about a model of `verify`
(acceptance test 38).

`verify_iff_compiled` is unconditional, a theorem about two definitions, and a check only because
`verify` is written from §8.5 before the right-hand side is unfolded. Its right-hand side is the
oracle verifier of `leanVmIopp` with its queries answered by the rows the openings authenticate,
not ArkLib's `Verifier.fiatShamir` (which would hash whole oracle messages): messages are absorbed
in their wire encoding (one round coefficient dropped, a root as two scalars, Merkle openings not
absorbed), and the grinding checks read the chain state, which a verifier does not see, so they
are conjoined. `verify`'s checks, each with a mutation of the dumped proof that it rejects
(convention *Load-bearing checks*): the setup's (upper limbs of the sizes zero, the caps, the
stacking and rate windows, the number and shapes of the openings), each phase's, the Merkle
openings' (one row per distinct sorted position, the row width the verifier's, no missing or
surplus sibling, the recomputed root), a zero third limb in each half of a root, the grinding at
each level, WHIR's terminal check, and the stream and openings fully consumed.

The list-binding compilation is where the master theorems meet WHIR: the commitment binds a
`K`-valued interleaved word (`KWord`, level 0's rows of `K` symbols) that may be close to up to
`L_0` codewords (from 23 to 122 at the deployed parameters, by the pairwise Johnson bound), every
member of the list is `K`-valued (`isInK_of_cl`) and stands for a stack (`stackOfMsgs`), and the
challenges up to `λ` pay `L_0` times their error. `Component.Front.relist` is the generic step: a
front component, whose verifier never reads the oracle (decision 31), keeps its knowledge soundness
over any oracle read through a list of at most `L` candidates, at `L` times the error, with its
extractor unchanged. It takes the component over the new oracles with a proof that its check and
verdict are the old ones; `Front.over` builds that component, answering the oracle queries the
front verifier never makes. `commitWord` commits the word, and its extractor list-decodes it and
selects the first member satisfying `M3Holds`, which is decidable (`commitPick`). `openInput`, a
step with no round, reads the word in `E` for WHIR's opening, whose relation is on `E` words; its
security is the seam `relist_of_relOpen`: a codeword of WHIR's list relation is a member of the
decoder's list, `K`-valued, and its claim is the batched claim on its stack. WHIR's own errors are
not multiplied by `L_0`. The compiled extractor returns the decoded member whenever there is one
(`listBinding_extractedStack_eq`), and past the commitment the state function holds exactly when
there is one (`listBinding_kSF_one`), which is what `core` reads: a failed extraction leaves the
state function false at round 1 for every witness. The decoder is an interface (decision 40):
`ListDecoder`'s specification is the list relation `Cl` at level 0's threshold, with no
repetition, so it meets WHIR's list relation by definition and its length is bounded by the list
bound. `ListDecoder.bruteForce` inhabits it, and `exactFast` is the path every honest word takes:
a codeword is at agreement `2^{κ+R}`, and any codeword within a threshold `a ≥ 2^κ` of it agrees
with it on `2^κ` positions, so is it; its list is the one message at every threshold up to
`2^{κ+R}`, with no unique-decoding condition. `ListDecoder.exactFirst` puts it in front of another
decoder. The exact path is an elimination over `K`, not the deployed prover's inverse additive
transform; a decoder by that transform and a Guruswami–Sudan inhabitant (CompPoly's decoder with
ArkLib's correctness proofs) are later refinements. `listBinding_perfectCompleteness` is the other
half, from the phases' completeness (`Component.Front.overComplete`) and WHIR's, which receives the
honest word of the stack in `E` (`kwordOf_lift`).

At leanVM the compilation is `listBinding_deployed`: the leanISA instance of the program at the
announced sizes, leanVM's phases with their securities, WHIR's chain and parameters at the stack
size and rate (`deployedChain`, every level in the Johnson regime), and `deployedDecoder`, the
transform's exact path in front of the brute force at level 0's threshold `johnsonPar`'s
`⌈(√ρ + η) n⌉₊`. It holds for every admissible announcement and valid rate, with no other
hypothesis, and it is a definition with no `noncomputable` (each level's bad-fold count is
computed), so its extractor compiles; `deployedPick`, the commitment's extractor at level 0's
computed indices, compiles without building the chain, and the two facts `core` reads are stated
with it (`listBinding_deployed_kSF_one`, `listBinding_deployed_extractedStack_eq`). The exact path decodes an honest word in the time of the
prover's encoder (the additive transform, `exactNtt`); the brute force behind it is exact but runs
on toy words only, so a dishonest word at a deployed size has no executable extraction yet.

**Why the generic route is not taken.** The textbook route proves state-restoration knowledge
soundness from round-by-round, keeps it through the BCS compilation, and gets the chain from a
chain lemma and a role-separation lemma. None of the four is stated here (decision 36). ArkLib's
state-restoration game cannot be stated for this protocol at the pin: it samples an eager random
function on the protocol's message types, which are infinite here (the public-input phase sends a
`List E`), and hands its extractor default logs. The chain lemma is false as an equality
(acceptance test 39). Role separation has no content beyond the tags and the lengths, since a
Merkle node is an untagged 64-byte input on the same function. The direct route states one game
on the one hash oracle, `loggedGame`: the adversary runs, then `verifyWith`, each logged.

**The core.** `HashMisbehaves` is the event the hash must avoid on that game's joint log: a
collision (two inputs, one digest), a hit (a digest, on its input's first query, equal to a value
already in play, the proof's digests counting against the verifier's queries only), or a flip (a
challenge of the proof's own chain that lies in the bad set of its prefix). `Bad` is the
round-by-round bound made into a set: the challenges that turn the state function of
`listBinding_compile` from false to true at a given prefix and committed words, of density at most
`εquery` by `bad_density`. `core` is deterministic and holds for every log consistent with a
function. The extractor reads only the adversary's log, never the verifier's queries, and reads a
row no query formed as zero, so the word it decodes is defined whenever the root is. The state
function is false at the start when the extractor fails and true at the end when the verifier
accepts, and only a challenge can turn it true, so some challenge of the verifier's chain does.
Without a collision or a hit, that challenge's first query has a history decoding to the prefix the
verifier replays, ending at that challenge (`chainHistory_determined`, `decodePrefix_mono`), the
words read off the log there are those read at the end (`extractRows_determined`), and the rows
opened later are theirs (`binding_of_log`); so that challenge is a flip. Both Merkle lemmas are
stated at a split of the log into a prefix and the rest, with consistency a hypothesis (free under
the caching oracle), and constrain only the rest's fresh queries: none may answer by a `Known`
digest, a root or a child of the prefix's node queries. The prefix's answers need not be known,
since a fresh query answered by one is a collision, nor the siblings, since the extraction never
descends into one, and `extractRows_determined` needs no collision hypothesis. A root is known only
once the chain has absorbed it, as two scalars in two observe blocks (`transcript.rs:52`,
`lib.rs:85`), never as a 32-byte block of an input; so the in-play set of a prefix holds
`scalars_to_hash (s₁, s₂)` for every two consecutive observe blocks of a chain in it, at most one
digest per observe query, and the hit charge stays linear in the log. Then `Known` is in the in-play
set of every longer prefix, and no hit at the first occurrences means no fresh hit at any split.

**The bound.** `misbehaves_rom` applies the charged invariant in its logged form twice: to the
adversary's run from the empty log, then to the verifier's run on the adversary's proof from the
adversary's final log, the proof fixed. A fresh query is charged `|log|/2^256` for a collision,
`|inPlay|/2^256` for a hit (in the second application with the `proofDigests` digests of the
proof added), and, if it closes a challenge at a decodable prefix of admissible sizes that ends
at a challenge, the density of its bad set, at most `εquery` (`bad_density`: `L_0·ε_i` at the
oracle protocol's challenges, `thm:rbr`'s fold, out-of-domain and batching terms at WHIR's);
elsewhere it is charged nothing for a flip. By `expected_charge_le_mul`, over the caches
reachable within the budget, the collision and hit charges sum to `hashTerm`'s form. WHIR's
query positions are one challenge drawn by a group of queries keyed by the chain state `cv` and
the nonce `n`: the grinding check `H(H(cv ‖ 3) ‖ n ‖ 4)`, the nonce step `H(cv ‖ n ‖ 4)` and the
squeezes of the positions (`whir.rs:1175-1193`). The group closes at the last of them to enter
the log, and has a challenge only if the check passes: its challenge is the pair of the check's
digest and the positions, and the proof of work enters as the check in its bad set, by the
potential alone. A group is charged `2^{−17}·((a_i − 1)/n_i)^{t_i}` at whichever of its queries comes
first; its potential is then the probability, given the log, that the check passes and the
positions are bad, and its later queries are martingale steps of that potential, charged
nothing. Each further nonce is a further group and costs a fresh query. That is why the charged
invariant is stated for a potential; an expected count of passing nonces would not compose with
the total charge, which is paid before the answer is seen. `challengePositions` reads the positions
as the Rust does for `1 ≤ b < 64` bits per position, and every deployed level has
`msgLog + rate < 64`.

`niError εquery V Q` is `(Q + V)` times `εquery`, the most one challenge can buy, plus
`hashTerm V Q`, with `εquery` the bad sets' density at every admissible size, which the challenge
oracle takes with the statement (decision 29). The verifier's queries are charged `εquery` each,
not only its chain rounds: a Merkle node query whose sibling bytes the prover chose can have a
squeeze step's shape. The adversary's run and the verifier's compose by the integral sequence
bound, the second run's potential starting from the first run's final potential; a supremum over
the first run's outcomes would count twice the groups the adversary left open. The hash term
counts the adversary's queries and the verifier's own, since a node the verifier recomputes is a
fresh value too, and the digests of the proof the verifier reads,
`proofDigests`, since the verifier's fresh answer equal to one of them is a hit, as the replayer's
root is. `verifierQueries` and `proofDigests` are numerals, each with a proved bound on one run.
The bound is selective: the statement is fixed before the adversary runs. A program-hash collision
does not enter, and the adaptive form would need more than that term: the chain's first state is
BLAKE2s of the statement outside the oracle, so for an adversary picking the public input after
its queries every statement's first state would be in play from the start.

`niError_le` states the closed form an auditor reads: at the deployed parameters `εquery` is at
most `2^{−128}`. A test checks `niError εquery (2^20) (2^64) ≤ 2^{−60}` by `norm_num`. The MCA
share of the fold rows is `mcaJohnson_annexB`'s bound at the ladder (Layer 11), and the query
rounds reach `2^{−128}` only with the proof-of-work factor. Without that factor the statement
certifies about 111 bits. No published theorem covers Fiat–Shamir with proof of work for a
multi-round protocol, so `misbehaves_rom` proves it.

The charged invariant holds from any initial cache, with no hypothesis at the start beyond the
initial potential, bounds events on the run's output and final state, and runs VCVio's
`randomOracle`; it is not built on VCVio's `withAddCost`, which charges cached queries too.
`misbehaves_rom` needs its logged form, whose state carries the ordered log, since the hit and
flip clauses are on the log and not on the cache. `extract` is the
straight-line extractor; it is computable (decision 11) and runs on toy instances. `Pr[p | mx]` is
VCVio's `probEvent`, deprecated at the pin in favour of `𝒟[mx]`; the sketches keep the readable
form.

The bytecode multilinear and the Flock matrices are evaluated inside `verify` through one function
`settleFixedClaims`, the seam for T5; its Flock walk is the Flock phase's.

Tests: a proof dumped from the pinned Rust prover, with its program and public input, accepted by
`verify` under `#guard`; the mutations: a flipped scalar in each phase, a wrong Merkle sibling, a
truncated path, a surplus sibling, a level-0 row of the wrong width, a duplicated position, a
wrong grinding nonce at each level, a nonzero third limb in a root half, a nonzero upper limb in
an announced size, a size above its cap, a trailing scalar, a missing or surplus opening phase,
each rejected; `RoundPoly.decode` on the Rust's encoding; in reverse, each transcript the
specification rejects run through the Rust and Python verifiers; the fixture's verifier log: its
query count within `verifierQueries`, its `chainHistory` the stream's blocks, each prefix decoded
by `decodePrefix`; `leafPreimage` on a log in which two leaf queries are answered by one digest
(the first is returned) and on a digest no leaf query is answered by (`none`); `extractRows` on
the honest toy log, and on a log missing one leaf (zero there); `ListDecoder.bruteForce` and
`exactFast` on a toy codeword, a word at the threshold and a word below unique decoding with several
codewords in its list; `exactFirst`'s fallback on a word one symbol off a codeword; `commitPick`
on the toy's honest word, on the word of a stack failing `M3Holds` and on a word one symbol off;
`runRandom`'s answer to a fresh query uniform on `Digest`, and a repeated query answered from the
cache; and `niError εquery (2^20) (2^64) ≤ 2^{−60}`. The fixture waits on the Flock phase's
definition.

### Layer 13: the base theorems (T4) and the fixtures

`LeanerVM/Protocol/Soundness.lean`, `Prover.lean` (plain). Needs Layer 12 and the adaptor; the
execution form at leanVM's program needs leanISA's Layers 9–10.

```lean
-- leanISA's, declared in LeanerVM/Arithmetization/ beside SatisfiedBy (requested; see Boundaries)
/-- A computable execution for every satisfying witness. Owner: leanISA, whose inhabitant takes the bytecode's
well-formedness, defines `traceOf` without `noncomputable`, and proves `valid` from `constraintSoundness`. -/
structure TraceExtraction (prog : Program) where
  traceOf : PublicInput → EnsembleWitness (leanIsaEnsemble prog) → Option (Trace prog)
  valid : ∀ input w, SatisfiedBy prog input w →
    ∃ t, traceOf input w = some t ∧ AssignmentRepresents w t ∧ ValidExecution prog input t
-- The hypothesis on the hash, of the headline and of nothing else
/-- BLAKE2s-256 behaves on this adversary's run, except with probability `δ`. Run the adversary with
BLAKE2s answering its hash queries, then the verifier on its proof; the joint log shows none of
- a collision: two different inputs with one digest (collision resistance);
- a hit: a digest, on its input's first query, equal to a value already in play: an earlier digest, a
  32-byte block of an earlier input, a digest the chain absorbed as two scalars (a Merkle root), or the
  statement's seed; for the verifier's queries, also a digest of the proof (unpredictability: no digest
  is known before it is computed);
- a flip: a Fiat–Shamir challenge of the proof's own chain that lies in the bad set of its prefix, a set
  fixed by the prefix and the committed words, of density at most `2^{−128}` (`bad_density`; correlation
  intractability of the chain against a sparse relation).
The bad sets are those of the deployed protocol, with `leanVmSecurity` (and so `flockSecurity`),
`deployedDecoder` and `blake2sFlockSpec` fixed inside this definition. -/
def BlakeMisbehaves (prog input) (A : Adversary) (δ : ℝ≥0) : Prop :=
  Pr[HashMisbehaves prog input | runBlake2s (loggedGame prog input A)] ≤ δ
-- The headline: the deployed verifier, the witness through the adaptor
theorem baseVerifier_extractsWitness (hB : BlakeMisbehaves prog input A δ) :
    Pr[fun g ↦ verify prog input g.proof = true ∧
          ¬ ∃ s q, extract prog input g.proof g.logA = some ⟨s, q⟩ ∧ SatisfiedBy prog input (witnessOf F prog s q)
      | runBlake2s (loggedGame prog input A)] ≤ δ
-- The execution, through leanISA's interface
def extractTrace (X : TraceExtraction prog) (input proof log) : Option (Trace prog) :=
  (extract prog input proof log).bind fun ⟨s, q⟩ ↦ X.traceOf input (witnessOf F prog s q)
theorem baseVerifier_extractsExecution (X : TraceExtraction prog) (hB : BlakeMisbehaves prog input A δ) :
    Pr[fun g ↦ verify prog input g.proof = true ∧
          ¬ ∃ t, extractTrace X input g.proof g.logA = some t ∧ ValidExecution prog input t
      | runBlake2s (loggedGame prog input A)] ≤ δ
-- The comparison form of the heuristic, a corollary
def Blake2sActsAsRandomOracle (G : OracleComp hashSpec α) (bad : α → Prop) (δ : ℝ≥0) : Prop :=
  Pr[bad | runBlake2s G] ≤ Pr[fun z ↦ bad z.1 | runRandom G] + δ
theorem blakeMisbehaves_of_comparison (hQ : IsTotalQueryBound A Q)
    (h : Blake2sActsAsRandomOracle (loggedGame prog input A) (HashMisbehaves prog input) δ) :
    BlakeMisbehaves prog input A (niError εquery verifierQueries Q + δ)
-- Completeness, for every function answering the hash, so at BLAKE2s with no hypothesis (Prover.lean)
def proveWith [Monad m] (H : List UInt8 → m Digest) (fuel : ℕ) (prog input) (w) (ρ) : m (Option Proof)   -- grinding searches
def prove (fuel prog input w ρ) : Option Proof := proveWith (m := Id) blake2sBytes fuel prog input w ρ
/-- The honest prover as an adversary: it hashes through the oracle; out of fuel, an empty proof, which `verify` rejects. -/
def honestAdversary (fuel prog input w ρ) : Adversary := do
  match ← proveWith hashQuery fuel prog input w ρ with
  | some proof => pure proof
  | none => pure ⟨[], []⟩
theorem baseProver_complete (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hadm : s.Admissible prog) (hρ : validRate ρ) (H : List UInt8 → Digest) :
    proveWith (m := Id) H fuel prog input w ρ = some proof → verifyWith (m := Id) H prog input proof = true
theorem baseProver_complete_of_execution (hwf : WellFormedBytecode prog) (h : ValidExecution prog input t)
    (hfit : ∃ w s, SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧ Sizes.ofWitness w = some s ∧ s.Admissible prog)
    (hρ : validRate ρ) :
    ∃ w, AssignmentRepresents w t ∧ ∀ fuel proof, prove fuel prog input w ρ = some proof → verify prog input proof = true
```

The headline is `baseVerifier_extractsWitness`. Its event is read off the deployed functions:
`verify` accepts the adversary's proof, and the stack `extract` reads off the adversary's queries
gives no satisfying witness through the adaptor. Its one hypothesis is `hB`. The proof is short
by design: on every run `core` puts the event inside `HashMisbehaves` (BLAKE2s is a function, so
the log is consistent with one, and `verifyWith_simulateQ` makes the game's verdict `verify`'s),
and `satisfiedBy_witnessOf` turns `M3Holds` into `SatisfiedBy` at the admissible sizes `extract`
returns. The mathematics is in `core`, `misbehaves_rom` and what they rest on.

`baseVerifier_extractsExecution` takes leanISA's trace interface as an argument (decision 41).
Its extractor is computable end to end when the interface's `traceOf` is (acceptance test 24).
Until leanISA's Layers 9–10 inhabit the interface, the corollary at that inhabitant is a block
comment (convention *Unproved targets*). `extract`, `witnessOf` and `extractTrace` keep the
extracted witness and execution, which recursion (T6) needs. The witness form takes no bytecode
hypothesis; the execution form takes it through the interface's inhabitant, and completeness from
an execution through `constraintCompleteness` (decision 27). A bytecode with a `JUMP` in the
sentinel slot has balancing steps and no execution (a proved repository test); leanVM's compiler
establishes it (`lean_compiler/src/lib.rs:162`). The existential corollary, "an accepted proof
implies some valid execution", is not stated: it carries no knowledge (decision 34).

`BlakeMisbehaves` is about one adversary, one statement and one run, and its three clauses name
what of BLAKE2s is relied on (*For zkVM engineers* says what that makes of the headline). The
statement is fixed before the adversary runs: the headline and `misbehaves_rom` are selective
(Layer 12 says why the random-oracle bound does not lift to an adversary picking the public input
after its queries). An adversary with coins is a distribution over coin-free ones (decision 38);
the headline applied to each gives it the bound with `δ` the probability, over its coins, that the
hash misbehaves, and `misbehaves_rom_coins` gives it the random-oracle bound unchanged.
`blakeMisbehaves_of_comparison` derives the hypothesis at `niError εquery verifierQueries Q + δ`
from the comparison form,
in which misbehaving is at most `δ` likelier under BLAKE2s than under a uniformly random function;
`misbehaves_rom` is the evidence that `δ` can be small. `δ` is the auditor's estimate, and the
repository never supplies it.

Two facts fix its form:
- **A statement about every adversary is false.** The replayer outputs a stored accepted proof
  and makes no query. `verify` accepts, `extract` on the empty log is `none`, and by `core` the run
  misbehaves: the verifier's recomputed root is a fresh answer equal to a digest of the proof, a
  hit. It fails `BlakeMisbehaves` at every `δ < 1` (acceptance test 36).
- **It cannot usefully be weakened.** The weakest hypothesis about one adversary that yields the
  conclusion is the conclusion itself. A per-adversary hypothesis can be improved only in form;
  this one is stated on the hash's behaviour, which an auditor can judge without the proof system.

An adversary that carries precomputed values, or uses BLAKE2s's code as the attacks of [KRS25] and
[Fen26] do, may fail it, and the theorem then says nothing about that adversary. One that hashes in
its own code at all fails it: the verifier's query on a Merkle node the adversary hashed itself is
fresh and answered by the proof's root, a hit with probability `1`. The adversary's BLAKE2s calls
must be its oracle queries; for any other adversary the hypothesis is false, not the theorem wrong. The hypothesis is
satisfiable by an adversary whose proof is accepted: the honest prover on a toy instance meets it
at `δ = 0` (acceptance test 37). That it holds at `δ = 0` for every satisfying witness is not
claimed: rows of 384 or 512 bytes hash to 32, so colliding rows exist, and nothing excludes a
satisfying witness that commits two of them.

Completeness starts from a satisfying witness with admissible sizes and a valid rate
(decision 28). `baseProver_complete` holds for every function answering the hash, so at BLAKE2s
with no hypothesis. It composes `m3Holds_stackOf`, the compiled protocol's completeness
(`listBinding_deployed_perfectCompleteness`), carried to every challenge vector
(`accepts_of_perfectCompleteness`) and to the prover's run against the chain
(`compiledProver_run`, `runWith_eq_runWithChallenges`), the compiled verifier's independence of
the nonce rounds (the oracle prover sends `0` where the wire carries the grind's nonce), the wire
read back by the walk, the executable algebra's agreement with the oracle verifiers on the decoded
transcript, Merkle completeness and the determinism of the chain. From an execution, `baseProver_complete_of_execution` adds `constraintCompleteness`
and takes `hfit`, the resource condition [architecture.md](../architecture.md) asks for: a valid
execution may need `κ_mem = 32`, whose memory columns exceed the stack the verifier accepts.

Perfect completeness does not survive the transform unconditionally. The honest prover's grinding
is a search, so `prove` takes fuel. That the search succeeds within its fuel holds for a random
function (each nonce passes with probability `2^{−17}`) and is not claimed for BLAKE2s. So the
completeness theorems conclude that every proof `prove` returns is accepted, not that one exists.

Tests:
- the replayer of Layer 12's fixture (acceptance test 36);
- the honest prover's run on a toy instance (acceptance test 37);
- `verify` as `verifyWith` at `blake2sBytes`, and `verifyWith_simulateQ` (acceptance test 38).

#### The executable prover and the test vectors

`verify` and `prove` run as a native executable, the `lean_exe` target `leanervm-vectors`, whose
root is under `tests/` because it carries the witness generator. The generator builds an
`EnsembleWitness` for a small program and input. It is test-only and untrusted: no theorem is
claimed of it (T2 stays out of scope), and a witness it builds is used only once leanISA's
decidable `checkSatisfiedBy` accepts it (`checkSatisfiedBy_eq_true_iff`); one that fails is a bug
of the generator. The executable writes test vectors (the program, the public input and the
proof, in the encoding Layer 12's fixture reads) and checks them: `verify` accepts each and
rejects its mutations. The kernel-evaluated fixtures stay on toy instances; the end-to-end run of
the honest prover is native (decision 5).

The performance target is the prover within one to two orders of magnitude of the Rust prover on
the same witness, single-threaded and in pure Lean (no FFI), measured at the smallest admissible
stack; [bench/](../../bench/README.md) records the ratio. Agreement with the Rust prover, each
side's proofs accepted by the other's verifier, is future work; the differences it finds are
recorded in [leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin).

## Acceptance tests and nearby false statements

Each names a reading that compiles and is wrong, and the witness that rejects it. Where the
witness is executable it is a test under `tests/`.

1. **Fingerprint degree.** `π_α` is multilinear in `α : E^4`, so a leaf has total degree at most 4 in
   `(α, β)` and Theorem 5.1's error is `4·2^μ/|E|`, not `2^μ/|E|`. `sideProduct_collision`
   carries the 4.
2. **Padding leaves are 1.** A `0` pad zeroes every product, and a `0` pad in the count tree
   makes `R_c = 0` reject honest proofs. The leaf stacks pad with `1`, the witness stack with `0`.
   Witness: the bus phase's honest run on the toy.
3. **`R_c ≠ 0` is load-bearing.** A read at an invalid address with count `0` pulls `(a, 0, v)`
   and pushes `(a, g·0, v) = (a, 0, v)`: balanced. Witness: the bus phase without the check has no
   knowledge soundness (the zero-count mutation).
4. **One root, not two.** The push and pull roots are one stream scalar. A proof with two roots
   and an equality check has a different stream and rejects every Rust proof.
   `verify_iff_compiled` pins the shape.
5. **Domain separators.** Without coordinate 0, a memory tuple `(a, c, v, 0…)` and a bytecode
   tuple with the same low coordinates coincide. Witness: two tuples equal after dropping
   coordinate 0, distinguished by the flush polynomials of the leanISA instance.
6. **Zerocheck point recycling.** `ζ` is drawn after `q` is committed; with `ζ` drawn before, a
   column vanishing at `ζ_{<τ}` only passes. The state function of the bus phase carries the
   zerocheck.
7. **Back-loaded padding.** Lifting table `j` by `∏_{k ≥ τ_j} X_k` keeps its sum
   (`sumCube_padHigh`); copying it multiplies the sum by `2^(τ_max − τ_j)`, which is `0` in
   characteristic two. Witnesses: `tests/LeanerVMTests/Protocol/Padding.lean`, and
   `tableSummand_target` on heights 2 and 1.
8. **Degree three, three scalars.** The table round polynomial is cubic; the wire carries three
   coefficients and `decode` derives `c_1`. A quadratic reading rejects every Rust proof. Witness:
   `RoundPoly.decode` on the dumped proof.
9. **Shared bus powers.** The three bus forms share the last three `ξ` powers across tables;
   per-table powers make the target not factor through the totals. Witness:
   `tableSummand_target` fails with per-table powers on two tables.
10. **Top limb of the public input.** The claim `mem_2(r, 0…) = 0` is pooled although no scalar
    is sent for it; omitting it lets a non-canonical public word pass. The phase and the spine
    cannot notice: an instance listing two lines has all their theorems. What fails is
    `satisfiedBy_witnessOf`, at `SatisfiedBy.word0_eq`, whose right side has a zero top limb by
    type. Witnesses: `threeLimbs` (the third claim rejects `badTopLimb`), and Layer 3's `#guard`
    on the leanISA instance's lines.
11. **Joint list binding.** WHIR is list binding, not binding; the extractor needs one member of
    the list to satisfy all pooled claims, and every oracle-protocol challenge pays the list size
    `L_0`. Per-claim soundness does not compose to a witness. Witness: `listBinding_compile`'s
    extractor selects one member.
12. **Absorb before squeeze.** The sizes and the commitment root are observed before `α`; every
    claim value before `λ`. A chain sampling `α` before the root is broken. `verify_iff_compiled`
    fails otherwise.
13. **Index column bit order.** `∏ (1 + ζ_k (1 + g^(2^k)))` reads bit `k` as coordinate `k`.
    Witness: the `#guard`s on `idxColumn 2` in `tests/LeanerVMTests/Protocol/FixedColumns.lean`.
14. **Bytecode slot bits.** The opcode is `P(z, 1, 1, 0, 0)`: slot 3 in low-first bits.
    Witnesses: `bytecodeColumn_answer_boolVec` with the oracle `#guard`s, and the
    sixteen-instruction `#guard` against `leaf.rs:585-604`.
15. **Selector alignment.** Blocks placed largest first sit at offsets that are multiples of
    their heights (`pow_size_dvd_offset`); with the smallest first no selector reads it. Largest
    first is sufficient, not necessary, and says nothing of equal heights (the tie order is
    Layer 3's test). Witness: three blocks of heights 4, 2, 1 with the small one first.
16. **Variable order.** The table sumcheck binds the highest variable first; table `j` joins at
    round `τ_max − τ_j`. Reversing it mismatches `eq(ζ_{<τ_j}, ·)`. Witness: Layer 7's run with
    two heights.
17. **Radix, parity and combiners.** For odd `μ` the first layer is radix 2; a combiner is drawn
    after every layer, the last included. From the seed to the end of the bus phase the stream
    holds `μ² + 4μ + 17` scalars (one more for odd `μ`) and the GKR draws `μ²/4 + μ + 1`
    challenges for even `μ`. Witness: the counts against the Python verifier, and
    `verify_iff_compiled` on the dumped proof.
18. **Counts in the count tree.** The tables' count columns only, not the finalize counts;
    otherwise the leaf layout, and so `ζ`, differ. Witness: the dumped proof.
19. **The extractor reads the stack.** The witness is `witnessOf` of the committed `q`, not of the
    openings or the roots. Witnesses: `piopExtractedStack_eq`, and the three equalities of
    `witnessOf_stackOf` on the one-row witness.
20. **Perfect completeness needs no exceptional-challenge clause, in any phase.** No verifier
    inverts a challenge-dependent value: the untransmitted coefficient of a round polynomial is
    `claim + r·(c_1 + … + c_d)`. Every honest prover, Flock's included, sends the coefficients of
    the true round polynomial. The pinned Rust Flock prover derives
    `G(0) = (claim + r·G(1))·(1 + r)⁻¹` and at `r = 1` emits a proof its verifier rejects: a
    defect of the implementation, recorded in [leanvm-target.md](../leanvm-target.md), no part of
    `flockError`. Witness: the Flock phase's round at `r = 1` with `G(0) ≠ 0`, accepted for the
    true coefficients and rejected for the derived ones.
21. **Sizes are parameters.** The verifier reads the sizes from the stream; the protocol is a
    family indexed by them, and the error of `verify` does not depend on the prover's choice (the
    maximum over admissible sizes). A version that puts the sizes in the oracle message type
    cannot state `OracleInterface`. `verify_iff_compiled` quantifies `∃ s`.
22. **Tags, not labels.** The chain has four numeric tags and no labels; a labelled transcript
    rejects every Rust proof. Witness: the dumped proof.
23. **What the numbers are.** `Σ piopError I < 2^{-159}` at admissible sizes, ring switching's
    `2^{-160}` dominating; it is false at the per-log caps alone (`μ_bus = 38` there), so
    `piopError_le` states the stacking window. It is the interactive error, not the security
    level of `verify`, which the WHIR query rounds set at 128 bits including 17 bits of grinding.
24. **The extractor computes.** ArkLib's extractor type admits a classical choice, so a theorem in
    an existential form (`rbrKnowledgeSoundness`, `rbrKnowledgeSoundnessWorstCase`) proves
    soundness only. Every interface and theorem here is in the `With` form, with a computable
    extractor checked by a `def` without `noncomputable` at each `Security`. The same holds for
    the random-oracle extractor `extract`, whose list decoder is `ListDecoder.exactFirst` over
    `ListDecoder.bruteForce` (an efficient decoder is another inhabitant of `ListDecoder`), and for
    `extractTrace`, whose `traceOf` leanISA's inhabitant of `TraceExtraction` defines without
    `noncomputable`. Witness: `piopExtractedStack_eq`, the `#guard` of Layer 3, and
    `extract` run on the honest prover's log on a toy instance (test 37).
25. **The wall holds.** No module above the adaptor imports `LeanerVM.Arithmetization`; a phase
    that mentions `leanIsaEnsemble` cannot be tested on the toy. Witness:
    `scripts/check-layers.sh`'s allow-list, with a planted violation in the policy tests.
26. **Seams are the contract.** A phase's output relation is the next phase's input relation by
    definition, not by a bridge lemma. Witness: `Phases.Complete.toDef` and
    `Phases.Security.toDef` typecheck only when the seams agree, and five pass-through phases
    inhabit `Phases.Complete` against exactly the spine's seams.
27. **The toy instance is honest.** `M3Holds toy input q` holds of the toy stack and fails for a
    stack with one cell changed, each checkable clause failing alone; a relation inhabited by
    every `q` proves nothing. Witness: the `#guard`s of `tests/LeanerVMTests/Protocol/Spine.lean`.
28. **The bus seam bounds the degree.** A seam carrying every true claim owes the table sumcheck's
    completeness on cubic terms it cannot prove. The row polynomials of `BusOut` are within `I.d`
    by type, so the cubic term is a typing failure; the bus phase takes `1 ≤ I.d`.
29. **The constant position is part of the Flock predicate.** The R1CS rows are homogeneous, so
    the zero block satisfies them and is no compression. Witness: `Holds` fails on the zero
    region.
30. **The sumcheck's tables.** The table sumcheck ranges over the tables with a constraint, a
    flush or a count column; over every table it would run at least 16 rounds and send 110
    values where leanVM runs `τ_max` rounds and sends 104. Witness: on an instance with a taller
    column group, the number of rounds is the smaller height.
31. **A check is load-bearing only if the verifier commits to it.** A public-input verifier that
    pools the values it computes is knowledge sound with no check at all. Pooling the values sent
    makes the check necessary. Witnesses: the refutations of Layer 8.
32. **The error is the spine's.** Five phases that draw a challenge, check nothing and declare
    error 1 satisfy knowledge soundness at their declared error. Witness: such phases do not
    inhabit the slots, whose errors are the spine's closed forms.
33. **One opening query.** After `λ` the deployed transcript is WHIR's; a reduction sumcheck in
    the opening phase adds `μ` rounds and a scalar, and `verify_iff_compiled` fails for every Rust
    proof. Witness: `openingSpec` is one challenge.
34. **The proof of work is load-bearing.** The 128-bit level needs the 17 grinding bits. Witness:
    a wrong grinding nonce at each level rejected, and the passing check in the bad set of a query
    group, whose density `bad_density` bounds by `2^{−17}·((a_i − 1)/n_i)^{t_i}`, at most `2^{−128}` at
    every deployed level.
35. **Front phases make no oracle query.** The list-binding compilation replaces the committed
    stack by a codeword and keeps the front verifiers, so a front phase that queried the stack
    would satisfy both master theorems and be uncompilable. Witness: `Phases` holds the front
    phases as `Phase.FrontDef`, and `listBinding_compile` takes no hypothesis on them
    (decision 31).
36. **The hypothesis is about one adversary.** "BLAKE2s acts as a random oracle for every
    adversary", or "BLAKE2s misbehaves on no run", is false, and a headline theorem assuming it
    would be vacuous. An adversary that outputs a stored accepted proof makes no query: under
    BLAKE2s `verify` accepts and `extract` on the empty log is `none`, so by `core` the run
    misbehaves (the verifier's recomputed root is a fresh answer equal to the proof's root, a
    hit). A comparison of the output-and-log distributions under BLAKE2s and under a random
    function fails for any adversary with one query, whose logged answer is a BLAKE2s value.
    Witness: the replayer of Layer 12's fixture, with `verify` accepting by `#guard` and `extract`
    on the empty log `none` by `#guard`; with `core`, `BlakeMisbehaves` fails for it at every
    `δ < 1`.
37. **The hypothesis is satisfiable by an accepted adversary.** A hypothesis that only rejected
    adversaries meet would make the headline vacuous where it matters. `honestAdversary` meets it
    at `δ = 0` on a toy instance: its run under BLAKE2s has no collision, no hit and no flip, its
    log holds the rows it committed, and out of fuel it returns the empty proof, which `verify`
    rejects (the stream is not consumed). Witness: on a toy instance, `#guard`s on the decidable
    clauses (no collision, no hit in the joint log) and on extraction (`extract` on the honest
    log returns the committed stack). A hit clause that counted the proof's digests against the
    adversary's own queries would fail it: the honest prover computes its roots and nodes through
    the oracle, each a fresh answer that is a digest of the proof it outputs. "It meets it at
    `δ = 0` for every satisfying witness" is not claimed: colliding rows exist, and nothing
    excludes a witness that commits two of them.
38. **One verifier.** The random-oracle theorems run `verifyWith`, and the headline is about
    `verify`. A verifier written separately for the model would make the headline a statement
    about the model. Witness: `verify` defined as `verifyWith (m := Id) blake2sBytes`, and
    `verifyWith_simulateQ`, proved by pushing `simulateQ` through the structurally recursive
    `verifyWith`, by which the random-oracle run of the game is a run of the same `verifyWith`.
39. **The chain lemma is not an equality.** "The chain of a random 64-byte map is a random oracle
    on transcript prefixes" fails as an equality of distributions: two prefixes whose chain
    states collide receive one challenge from the chain and two independent ones from a random
    oracle, so the two differ by the collision probability, about `Q²/2^256`. The route therefore
    charges collisions in `HashMisbehaves` and states no chain lemma (decision 36). Witness: a
    chain over a map on a two-element digest set, whose joint distribution of two prefixes'
    challenges differs from a random oracle's, computed exactly.
40. **WHIR's query positions are one challenge, paid for by the check.** They are drawn by several
    squeezes after the grinding check. Charged per squeeze, a squeeze of `⌊192/d⌋` positions costs
    `(1 − γ_i)^{⌊192/d⌋}`, far above `2^{−128}`. A group that closes without a passing check, or a
    flip that does not ask for one, leaves the proof of work unpaid: an adversary that steps many
    nonces and squeezes their positions, never querying the check, flips with probability
    `(1 − γ_i)^{t_i}` per nonce. The group of the check, the nonce step and the squeezes is one
    challenge, the pair of the check's digest and the positions, bad only if the check passes,
    charged once at `2^{−17}·((a_i − 1)/n_i)^{t_i}` whichever order its queries come in (so the charged
    invariant is stated for a potential). Witness: the test
    `niError εquery (2^20) (2^64) ≤ 2^{−60}`, false at the per-squeeze charge.

## Interfaces supplied to later work

These names are the reviewer's reading list: every definition a stated theorem mentions, and every
theorem a later layer or roadmap consumes. The recursion work (T5, T6), the Flock roadmap and the
upstream pull requests consume them. A declaration not listed is a proof, a helper or a test, and
is `private` where the module system allows; a layer's pull request checks its names against
this list.

```text
Field instances:      instSampleableTypeK  instSampleableTypeE  card_E
                      Column  Weight  Weight.pair  eqWeight  innerProductOracle  answer_eqWeight
Spine:                Side  Shape  Shape.ColumnId  Layout  Layout.read  Layout.read_eval  Coord  BoundaryBlock  PublicLine
                      M3Instance  M3Instance.SumcheckTable  τmax  μBus  B  column  row  tuples  FlockRegion  aux
                      ConstraintsVanish  Balanced  CountsNonzero  PublicLinesHold  M3Holds  M3Rel  NoOracle  TheOracle
                      RowPoly  Form  ColumnClaim  WeightedClaim  BusOut  TableOut  PubOut  FlockOut  theStack
                      Seam.of  Seam.commit  Seam.bus  Seam.table  Seam.pub  Seam.flock  Seam.done
                      busSpec  tableSpec  pubSpec  flockSpec  openingSpec
                      busError  tableError  pubError  flockError  openingError  piopError  piopError_le
                      Component.Def  Component.Guarded  Component.Complete  Component.Security  (each with .append)
                      Phase.Def  Phase.Complete  Phase.Security  Phase.FrontDef  Phase.FrontDef.toDef
                      Phase.passThrough
                      Component.passThrough  Component.sendOracle  keepOracles  OracleVerifier.materializeOutput_of_keepOracles
                      Verifier.GuardedForm.of_probEvent_pos  Reduction.mem_support_run_of_guarded
                      probEvent_uniformSample_le_of_subsingleton
                      Verifier.KnowledgeStateFunction.appendGuarded
                      Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
                      commitDef  commitComplete  commitExtractor  commitSecurity
                      Phases  Phases.Complete  Phases.Security  Phases.toDef
                      leanVmPiop  leanVmVerifier  leanVmProver  piopExtractor  piopExtractedStack  piopExtractedStack_eq
                      piop_perfectCompleteness  piop_rbrKnowledgeSoundness  piop_rbrKnowledgeSoundness_exists
                      Refinement  Refinement.map_option_valid  Refinement.knowledge_transport  Extractor.Straightline.map
                      Toy.shape  Toy.toy  Toy.honest  Toy.layout
Tables and stacking:  sumCube  hadamard  slice  sliceLow  placeSlice  boolVec
                      evalMle_eq_sumCube_hadamard  evalMle_append_boolVec  evalMle_boolVec_append  evalMle_placeSlice
                      bitProductTable  evalMle_bitProductTable  powersTable  evalMle_powersTable
                      Blocks  Blocks.Tables  Blocks.stackAt  Blocks.selector  Blocks.extendPoint  Blocks.offset  Blocks.total
                      Blocks.lowPoint  Blocks.selectorWeight  Blocks.stack_eval  Blocks.unstack  Blocks.unstack_eval₂
                      Blocks.stack_eval_ambient  Blocks.stackColumn  Blocks.readColumn  Blocks.readColumn_eval
                      Blocks.layout  Blocks.stridedLayout  Layout.piecewise  Layout.comap  Blocks.stack_eval_ambient_one
                      padHigh  sumCube_padHigh  evalMle_padHigh  ColumnClaim.holds_iff_weighted
                      idxColumn  idxColumnEval  idxColumn_eval  idxColumnEval_eq
                      bytecodeColumn  bytecodeColumnEval  bytecodeColumn_answer_boolVec  bytecodeColumn_eval
Clean polynomials:    Expression.toCMvPolynomial  eval_toCMvPolynomial  fromCMvPolynomial_toCMvPolynomial  M3Table  Component.toM3
                      toM3_constraints_iff  toM3_flushes_eq
The adaptor:          Sizes  Sizes.ofWitness  Sizes.Admissible  validRate  LeanIsa.blocks  LeanIsa.blocks_fits  leanIsaμ
                      leanIsaInstance  stackOf  witnessOf  Agrees  agrees_witnessOf  agrees_stackOf  tuples_perm
                      satisfiedBy_witnessOf  m3Holds_stackOf  witnessOf_stackOf  caps_witnessOf
Generic components:   Virtual  Sumcheck.plain  Sumcheck.normalized  Sumcheck.transport  batch
                      fingerprint  sideProduct  sideProduct_poly_eq_iff  sideProduct_collision  gkr  gkrError
Phases:               busPhase  leaf_decomposition  tableSummand  tableSummand_target  tableSumcheck
                      PublicInput.check  PublicInput.checkWords  PublicInput.pooledFrom  PublicInput.prover
                      PublicInput.verifier  PublicInput.deployedVerifier  PublicInput.verifierWith
                      PublicInput.verify_simulated  PublicInput.accepts_two_challenges
                      publicInputPhase  deployedPublicInputPhase
                      FlockSpec  flockPhase  flockError_le  openingPhase  leanVmPhases
                      (each phase with its Complete and Security)
WHIR and Merkle:      Level  ladder  novelBasis  encode  columnWeight  encode_columnWeight  whirOpen  whirError
                      whirOpen_rbrSoundness  McaJohnson  mcaConstant  mcaJohnson_annexB  johnsonPar  deployed_rbrSoundness
                      mcaError_foldLine_eq_affineLine  merkleRootWith  merkleVerifyWith  merkleRoot  merkleVerify
                      MerkleTree.fold  MerkleTree.prunedRoot  nodeModel  toBatchOpening  merkle_fits  blake2sBytes
Generic, Layer 12:    chargedRandomOracle  potential_le_expected_charge  prEvent_le_of_potential
                      prEvent_not_good_le_expected_charge  expected_charge_le_mul  expected_fresh_in_le
                      chargedLoggingOracle  potential_log_le_expected_charge
                      nodePreimage  leafPreimage  extractTree  extractLeaf  extractLeaves  extractLeaves_eq
                      Consistent  HasCollision  Fresh  Known  FreshHit  MerkleTree.binding_of_log
                      MerkleTree.extractLeaf_determined  extractRows  extractAllRows  extractAllRows_eq
                      binding_of_log  extractRows_determined
                      Component.relistRel  Component.Front.relist  Component.Front.over  Component.Front.overComplete
                      Component.sendEncoded  Component.sendEncodedSecurity  Component.mapOracles  Component.mapOraclesSecurity
                      Component.Security.append_kSF_left  Extractor.RoundByRound.DecodesFirst  gaussSolve
List binding:         KWord  kwordOf  kwordOf_lift  ListDecoder  ListDecoder.bruteForce  exactFast  exactFast_eq
                      ListDecoder.exactFirst  ListDecoder.exact  isInK_of_cl  stackOfMsgs  stackList
                      commitWord  commitPick  commitWordSecurity  openInput  relist_of_relOpen  openInputSecurity
                      listBinding_compile  listBinding_kSF_one  listBinding_extractedStack_eq
                      listBinding_perfectCompleteness  deployedPick  deployedPick_eq_commitPick
                      listBinding_deployed_kSF_one  listBinding_deployed_extractedStack_eq  commitPick_isSome_iff
                      commitPick_eq_some  fwd  inv  fwd_getElem  fwd_inv  inv_fwd  encodeFast  encodeFast_getElem
                      exactNtt  exactNtt_spec  exactNtt_of_codeword  ListDecoder.decode_eq_of_codeword
                      ListDecoder.nttFirst  kwordOfFast  kwordOfFast_eq  deployedChain_head  deployedDecoder
                      listBinding_deployed  listBinding_deployed_rbrKnowledgeSoundness
                      listBinding_deployed_perfectCompleteness
Compilation:          Digest  card_digest  hashSpec  hashQuery  Adversary  runBlake2s  runRandom  FsState  Block
                      FsState.seed  FsState.checkPow  FsState.challengeOf  chainHistory  chainHistory_determined
                      Proof  Proof.sizes?  RoundPoly.decode  decodePrefix  decodePrefix_mono  decode  leanVmIopp
                      verifyWith  verify  verifyWith_simulateQ  rounds  verifierQueries  proofDigests
                      rounds_bound  verifierQueries_bound  proofDigests_bound  verify_iff_compiled
                      settleFixedClaims
Random oracle:        Run  loggedGame  extract  Extracts  LogHasCollision  Hit  Bad  bad_density  Flip
                      HashMisbehaves  core  hashTerm  niError  misbehaves_rom  niError_le  verify_knowledgeSound_rom
Base theorems:        TraceExtraction  checkSatisfiedBy  checkSatisfiedBy_eq_true_iff (leanISA's)
                      BlakeMisbehaves  extractTrace  baseVerifier_extractsWitness  baseVerifier_extractsExecution
                      Blake2sActsAsRandomOracle  blakeMisbehaves_of_comparison  proveWith  prove  honestAdversary
                      baseProver_complete  baseProver_complete_of_execution
Parameters:           initialFold  subsequentFold  initialReduction  subsequentReduction  residualMaxLog
                      queryGrindingBits  the Flock constants (Parameters/Flock.lean)
```

The trust surface of the headline theorem, `baseVerifier_extractsWitness`, has three parts.
- **Its definitions:** `verify`, `loggedGame`, `runBlake2s`, `extract`, `witnessOf`,
  `SatisfiedBy`, and `BlakeMisbehaves` with `HashMisbehaves` and its three clauses. The flip
  clause's bad sets need not be read: their density is a theorem (`bad_density`), and the
  protocol they come from is fixed inside the definition. The execution form adds `extractTrace`,
  `ValidExecution` and leanISA's `TraceExtraction`, an argument whose `valid` field carries
  leanISA's obligation.
- **Its one assumption:** `BlakeMisbehaves`, for the adversary and statement at hand. It is a
  hypothesis in the statement, never an axiom, and nothing in the repository discharges it.
- **The kernel's three axioms.**

`niError`, `runRandom` and `misbehaves_rom` are not in it: they are the evidence that `δ` can be
small, through `blakeMisbehaves_of_comparison`. Everything else it rests on is proved. The
interfaces `FlockSpec`, the Flock phase's `Security`, `McaJohnson` and `ListDecoder` are
structures whose generic theorems take them as arguments. leanVM's instances of them are proved
inhabitants: `blake2sFlockSpec`, `flockSecurity`, `mcaJohnson_annexB` and
`ListDecoder.bruteForce` (and `ListDecoder.exactFirst` over it). `core` and the random-oracle bound
are theorems of Layer 12, not interfaces. A hole not yet filled leaves the theorems that need it unstated; it is never taken as
a hypothesis. The knowledge-soundness composition ArkLib admits is not in the trust surface
either: the port proves it.

## Boundaries

**With the leanISA roadmap (#4).** Its two requests are met: `Caps` requires power-of-two heights
and bytecode length, and the channels record, per channel, the domain separator and coordinate
order of the 16-slot bus tuple. This roadmap consumes `SatisfiedBy` as it stands, with its
integer-counted balance, its fixed-column conjuncts and its public-word conjunct (the top limb is
zero by type), and `constraintSoundness` and `constraintCompleteness` with their hypothesis
`WellFormedBytecode`. Two open matters for leanISA: `constraintCompleteness` returns a witness of
some heights, while base completeness from an execution needs admissible ones (the hypothesis
`hfit` of Layer 13 stands in; a minimal-height `constraintCompleteness` would replace it); and
`constraintCompleteness` itself needs a resource hypothesis (`Caps` bounds every table by `2^32`
rows, `ValidExecution` bounds only the memory). The eighteen BLAKE2S value limbs are columns of
`blake2sTable` there and strided slots of `q_flock` here, reconciled by the instance's layout.

**With the Flock roadmap (#3).** This roadmap owns the stacked WHIR, its parameters, the Merkle
trees, the transcript, and the Flock phase's definition and completeness (the schedule, the
verifier, the circuit walk, the constants transcribed from the Rust and the Python, an honest run
on a toy circuit). #3 owns the BLAKE2s circuit, the R1CS lowering, zerocheck, lincheck and ring
switching in the leanVM lane, and their security: an inhabitant of `FlockSpec` (the slot map, the
predicate on the packed column with its constant position, "the R1CS holds ⇒ the limbs compress",
the witness generator with its lemma) and the Flock phase's knowledge soundness at the spine's
error, for the specification's honest prover. Its concrete PCS is this roadmap's `whirOpen`,
developed once. The fixture of Layer 12 waits on the Flock phase's definition.

**With recursion (T5, T6).** `verify` evaluates the bytecode multilinear and the Flock matrices
through `settleFixedClaims`; the recursive verifier replaces that one function by a deferred claim
and is otherwise `verify`. `extract` and `extractTrace` hand recursion the extracted witness
and execution.
`VerifySummary`-style outputs (`cpu/mod.rs:690-704`) are not modelled.

**With leanISA, for extraction.** The execution form of the headline takes `TraceExtraction prog`
(decision 41), an interface whose fields are `traceOf`, a computable execution of a satisfying
witness, and `valid`, which is `constraintSoundness` with the trace named. leanISA declares it in
`LeanerVM/Arithmetization/`, beside `SatisfiedBy` (its fields mention only `Trace`,
`ValidExecution`, `SatisfiedBy` and `AssignmentRepresents`, and the layer order forbids an
inhabitant there of a structure declared in `Protocol/`), and inhabits it when its Layers 9–10 land,
the inhabitant taking the bytecode's well-formedness; Layer 13 consumes it. `traceOf` needs no
discrete logarithm: it walks a map from each row's pulled state to its pushed state, from
`Regs.initial` to `Regs.final prog`, with the total row count as fuel. Three facts bear on leanISA's
Layers 9 and 10, from this roadmap's reading of its statements. Layer 9 needs no change to Clean:
`SatisfiedBy` counts its balances in ℕ (`BalancedPair`) beside `CountsNonzero`, and the per-row step
is Clean's `Air.Flat.Component.weakSoundness`. `no_row_at_sentinel`, as the block comment of
`Arithmetization/Statement.lean` states it, is false: `leanIsaVerifier prog` pulls `⟨finalPc, 1⟩` on
`StatePull` and its row is among `w.interactions`; the statement is to be restated over the opcode
tables' rows. The lookup theorems and Layer 10 need only the `sentinelSafe` field of
`WellFormedBytecode`. One more request: the test vectors of Layer 13 need a decidable check of
`SatisfiedBy`, `checkSatisfiedBy` with `checkSatisfiedBy_eq_true_iff`, declared beside the relation
in `Arithmetization/`.

## Decisions

A decision taken is written into the convention, signature or acceptance test it settles, and
recorded here in one row. Each is reversible by a pull request to this document.

| Decision | The choice | Recorded in |
| --- | --- | --- |
| 1. Heights are powers of two | leanISA's `Caps` requires every table height and the bytecode length to be powers of two, so both roadmaps state one relation | leanISA Layer 8; *Boundaries* |
| 2. The statement and the family | `input : I.Stmt` is the statement; the instance, hence the sizes, indexes the protocol family | *Statements and parameters* |
| 3. Where the zerocheck is paid | the bus phase's state function carries it; there is no zerocheck phase | *Seams* |
| 4. Where generic code lives | `LeanerVM/Protocol/To<Library>/` until the upstream pull request merges | *Generic code* |
| 5. The honest prover runs natively | `verify` and `prove` run as a native executable that writes and checks test vectors, on witnesses from a test-only, untrusted generator that a decidable check of `SatisfiedBy` accepts, with the prover's target one to two orders of magnitude of the Rust prover, single-threaded, in pure Lean; the kernel-evaluated fixtures stay on toy instances | Layer 13, [The executable prover and the test vectors](#the-executable-prover-and-the-test-vectors); *Scope* |
| 6. The witness is the stack | the protocol's witness is the committed column, in `Type 0` | *The relation ladder* |
| 7. Phases over an abstract instance | every phase is written over `I : M3Instance` and tested on the toy | *The wall* |
| 8. Five clauses, caps outside | the caps are the compiled verifier's check and a hypothesis of the adaptor's soundness | *What the spine fixes* |
| 9. Balance is a permutation | the pushed and pulled tuple lists are permutations of each other | `M3Holds` |
| 10. Worst-case round-by-round knowledge, named | each component proves `rbrKnowledgeSoundnessWorstCaseWith` for a named extractor | *Holes*, *Extractors* |
| 11. Extractors compute | every extractor is a computable definition; the protocol's is `piopExtractor` | the extractor computes (test 24) |
| 12. The strong Flock predicate | `aux` is Flock's R1CS, with the constant position, on the committed region | Layers 3, 9 |
| 13. Public lines, not cells | the statement fixes cells 0 and 1 of listed columns | *Public input* |
| 14. The degree bound belongs to the instance | `M3Instance.d`, carried by the type of the bus seam's row polynomials | *Seams*; test 28 |
| 15. The public-input transcript | the prover sends the values of the lines marked `sent` | *Public input*; Layer 8 |
| 16. The GKR round is normalized | the round message is the cofactor; the layer check has no equality factor | *GKR*; Layer 4 |
| 17. GKR leaves are a function of the context | the GKR component takes its leaf tables as functions of the statement and oracles, not as oracle statements; no context lifting | Layer 5 |
| 18. Riders | tables that must vanish at the GKR's final point ride along the GKR's state function | Layers 5, 6 |
| 19. The stack's oracle is the inner product | a query is a weight, the answer `⟨W, q⟩`; the opening phase is `λ` and one weighted query, which WHIR realizes | *The oracle*; Layers 0, 10, 11 |
| 20. The spine fixes the error | each slot's schedule and error are closed forms of the instance, fixed by the spine; no phase declares its own | *Errors*; the spine |
| 21. The bus seam has leanVM's shape | `BusOut` is the Rust's `BusVerify`: one point, forms per side and sumcheck table, three totals, column claims; the seam carries the point | *Seams*; the spine |
| 22. Model the deployed checks | the oracle protocol models the checks of the deployed verifier; the specification supplies the arguments; an auditable variant is admitted only if it accepts no more and its relation to the deployed one is a theorem | *Load-bearing checks*; Layer 8 |
| 23. Completeness is perfect; the guard is separate | `Component.Guarded` carries output purity and the guard; completeness stays perfect, the Lean honest prover is the specification's | *Holes*; test 20 |
| 24. Stay on `OracleReduction` | the spine stays on ArkLib's legacy framework, the only one with a knowledge notion, until the typed framework has round-by-round knowledge soundness and its composition | the ledger |
| 25. Flock enters through two structures | an instance-free `FlockSpec` from the Flock roadmap; a `FlockRegion` in the instance, from which the auxiliary clause is defined | the spine; Layers 3, 9 |
| 26. The wire drops a coefficient | the oracle protocol sends every coefficient and checks the round; the compiled verifier decodes the wire, and Layer 4 proves the transport lemma | *Sumcheck messages* |
| 27. The program hypothesis | the theorems that reach an execution take `WellFormedBytecode prog`, the execution-level headline through the inhabitant of the trace interface (decision 41) and completeness from an execution through `constraintCompleteness`; the witness-level theorems take none | Layer 13 |
| 28. Completeness resources | base completeness starts from a satisfying witness with admissible sizes; its form from an execution takes a fit hypothesis | Layer 13 |
| 29. One theorem for the family | the non-interactive theorem is stated for the family over announced sizes, its error the maximum over admissible sizes | *Statements and parameters*; Layer 12 |
| 30. The bus phase's side conditions | `1 ≤ I.d` and "a table with a constraint is on the bus" are hypotheses of the bus phase, not fields of `M3Instance` | Layer 6 |
| 31. The front phases are `Phase.FrontDef` | `Phases` holds the four phases before the opening as `Phase.FrontDef`, a phase whose verifier never reads the stack; `FrontDef.toDef` is the phase as a component, the form its proofs are stated on; the list-binding compilation takes no hypothesis on them | *The oracle*; the spine; test 35 |
| 32. The Merkle trees read as VCVio's | the trees `verify` runs are the Rust's, transcribed and generic in the hash; `merkle_fits` reads them as VCVio's for every hash, with a node hash that carries no address and the Rust's octopus as a path-pruned `BatchOpening`, a cross-check on which no proof depends (binding is decision 39's) | Layer 11; the ledger |
| 34. The heuristic is a named hypothesis, per adversary | the headline is knowledge soundness of the deployed `verify`, with a computable extractor. Its one assumption is a hypothesis on BLAKE2s for the adversary at hand, with slack `δ`, named in the statement; its form is decision 37's. The random-oracle steps are theorems, not interfaces. One `verifyWith` serves every setting. No existential soundness corollary is stated | *For zkVM engineers*; Layers 12, 13; tests 24, 36–38 |
| 35. Correlated agreement at Annex B's constant | `McaJohnson` takes Annex B's `a` (`johnsonComparisonEstimate`), inhabited by ArkLib's proved theorem; the admitted [BCHKS25] theorem is not consumed; `η` is the exact value of the Rust's double, dumped from the pinned Rust | Layer 11; the ledger |
| 36. The direct random-oracle route | one logged game on the one hash oracle, split into the deterministic `core` and the bound `misbehaves_rom` over the generic charged invariant, takes the place of state restoration, a BCS compilation, a chain lemma and role separation, none of which is stated | Layer 12; the ledger; tests 39, 40 |
| 37. The hypothesis is about the hash | the headline assumes `BlakeMisbehaves`, a bound on the collisions, the hits (the proof's digests against the verifier's queries only) and the flips (a challenge of the proof's own chain in a bad set of density at most `εquery`, `bad_density`) of BLAKE2s on the adversary's run, and the comparison with a random function becomes the corollary `blakeMisbehaves_of_comparison` (amends decision 34's form) | Layer 13; tests 36, 37, 40 |
| 38. Adversaries draw no coins | an adversary is `OracleComp hashSpec Proof`, bounded by `IsTotalQueryBound`, and one with coins is a distribution over these | Layers 12, 13 |
| 39. Merkle binding by log replay | the rows are read top-down off the adversary's log (`extractRows`, on `MerkleTree.fold`), `extract` reading a missing row as zero, and `binding_of_log` proves the opened rows equal to them unless the joint log shows a collision or a hit; VCVio's extraction is not consumed (amends decision 32) | Layer 12; the ledger |
| 40. List binding through a decoder interface | the extractor list-decodes through `ListDecoder`, specified by WHIR's list relation at level 0's threshold with no repetition, and inhabited by brute force; the `exactFast` path proved to agree at every threshold from `2^κ` to `2^{κ+R}` (`ListDecoder.exactFirst`), and faster decoders as further inhabitants. The committed word is a `K` word (`KWord`), so every member of its list is a stack (`isInK_of_cl`), read in `E` for WHIR by the zero-round `openInput`; `relist` takes the front component over the new oracles (`F'`) and a `List` with a length bound; the compilation takes the height equation `hμ : κ + sh.ℓ = I.μ`; the deployed decoder is `ListDecoder.nttFirst` over `ListDecoder.bruteForce`: the exact path by the additive transform, proved to agree (`exactNtt_spec`, `ListDecoder.decode_eq_of_codeword`) | Layer 12; *Extractors*; test 24 |
| 41. leanISA's trace through an interface | the execution-level headline takes `TraceExtraction prog`, which leanISA declares beside `SatisfiedBy` and inhabits, and the witness-level headline is stated without it | Layer 13; *Boundaries* |

Open:

- **33. The plain sumcheck upstream.** Write the four leanVM sumcheck shapes locally (default), or
  also consume ArkLib's typed one-polynomial sumcheck for the plain case through an adaptor.

## How work is tracked

A fact has one home, and every other place links to it and restates nothing.

| Kind of fact | Home |
| --- | --- |
| What is wanted and what was decided: the targets, the conventions, the specification of every hole, the acceptance tests, the decisions, the upstream ledger | this document |
| What is built on `main`, where the built work differs from this document, what to watch upstream | [protocol-status.md](protocol-status.md) |
| Who is taking which hole | the checklist in the body of issue [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12) |
| Discrepancies between the leanVM specification, its Rust and its Python verifier at the pin | [leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin) |
| Limits of the pinned libraries | [dependencies.md](../dependencies.md) |
| Lean pitfalls met while building | [tests/README.md](../../tests/README.md) |
| What a review found at one commit | its handoff under [docs/reviews/](../reviews/), an archive |

- **This document** is the specification. It changes only by a pull request titled
  `docs(protocol): …` that names the hole, acceptance test, decision or convention it touches. It
  records no state, no date of landing, no pull request in flight and no person.
- **The status** says what is built and nothing about what is wanted. A hole is built when the
  names in bold of its row in [The holes](#the-holes) exist under `LeanerVM/` and match its layer
  section; where built work falls short of this document, the status lists what it owes. The pull
  request that lands a hole updates the status in the same change.
- **Issue #12** is the tracker: a link to this document and to the status, and one checklist line
  per hole with its name, its state (*open*, *claimed*, *in review*, *on `main`*), the claimant's
  intention issue or pull request, and a link to its layer section. It holds no specification, no
  ledger, no decision and no list of pull requests. It is changed by editing its body; no comment
  is added and no issue opened to change it. Where it and the files disagree, the files win.
- **To take a hole**, or part of one: with write access, edit its checklist line; without, open
  an issue titled `[Intention]: protocol - <name of the hole>: …` whose body names the
  declarations taken, and a maintainer links it from the line. An intention issue is closed by
  the pull request that lands it. A hole in two halves (the definition with its completeness; the
  knowledge soundness) is two lines and two pull requests.
- **Names.** Holes, ledger entries, decisions and discrepancies are called by their names. Layers,
  acceptance tests, decisions and the target theorems of [architecture.md](../architecture.md)
  keep their numbers, always with the name beside the number: "the extractor computes
  (acceptance test 24)". A layer, test or decision of the leanISA roadmap is called "leanISA …".
  No letter-number code is introduced; [Former codes](#former-codes) reads old ones.
- **Decisions.** A decision taken is written here as the convention, signature or test it
  settles, and as one row of [Decisions](#decisions); an open decision is listed there. Neither is
  copied anywhere else.
- **Upstream.** The ledger in [Dependencies and exact contracts](#the-upstream-ledger) says what
  replaces each missing upstream result and when the local copy goes; the status's watch list says
  which external work may feed a hole. Whoever bumps a pin updates both.
- **When a pin moves.** The leanVM pin: every check of the verifiers against the new rejection
  paths, the message and challenge counts of every phase, the layouts and their tie orders, the
  Flock and Fiat–Shamir constants, the parameter tables, and the discrepancies of
  [leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin). A library pin: the
  admitted theorems the ledger names, the notation of the probability bridges, the meaning of
  numerals in `K`, and every acceptance test that decides a numeral.
- **Reviews.** A review's handoff records one commit. What is accepted from it becomes text of
  this document, and any edit it asks of the tracker is made, in the pull request that meets it.
  Nothing cites a handoff as a specification.
- **To report a problem with this document**, open an issue titled `[Roadmap]: protocol - …`
  naming the hole and the acceptance test or convention it touches.
- **Pull requests** are titled `feat(protocol): …` and land with `./scripts/validate.sh` green.
  The description names the hole, the sources and the pin, whether each new definition is written
  from the specification or transcribed from its source, the ledger entries it touches, the
  target theorem it feeds, and the refutation tests of its checks. A maintainer labels it
  `awaiting-review` when the author is done and `awaiting-author` after a review that asks for
  changes. The reviewer reads the changed modules in full, in three passes: the statements against
  the specification, fidelity to the pinned sources, and hygiene. A phase or a generic component
  imports spine names only and is tested on the toy instance.

## Former codes

Earlier pull requests, issues and reviews name holes and ledger entries by letter codes. The
source findings' former codes are beside each entry of
[leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin).

| Former code | Name |
| --- | --- |
| S | the spine |
| C1 | the knowledge-soundness composition |
| L1 | tables and stacking (Layer 1) |
| I1, I2 | Clean expressions as polynomials (Layer 2); the adaptor (Layer 3) |
| G1, G2, G3 | sumcheck: definitions and completeness; its knowledge soundness; batching by powers (Layer 4) |
| G4, G5, G6 | fingerprint and collision bound; grand-product GKR, its definition and completeness, its knowledge soundness (Layer 5) |
| P1, P2; P3, P4 | the bus phase (Layer 6); the table sumcheck phase (Layer 7), each in two halves |
| P5 | the public-input phase (Layer 8) |
| P6 | the Flock phase (Layer 9) |
| P7, P8 | the opening phase (Layer 10) |
| K1, K2 | WHIR opening; Merkle trees, the byte hasher and the WHIR parameters (Layer 11) |
| K3 | transcript, proof object and compiled verifier (Layer 12) |
| K4 | the base theorems (Layer 13) |
| ledger A1 … A9 | in order: the sumcheck's knowledge leaf; the knowledge-soundness composition; round-by-round to plain; context lifting; Fiat–Shamir and BCS; grand product, GKR, batching, stacking; WHIR, Merkle, BLAKE2s; correlated agreement up to Johnson; ring switching |
| ledger C1 … C4 | Clean expressions as polynomials; the two leanISA requests; balance counted in ℕ; fixed columns |

## References

- leanVM [leanEthereum/leanVM](https://github.com/leanEthereum/leanVM) at
  [`a386121f`](https://github.com/leanEthereum/leanVM/commit/a386121f84292f6fa663aaa3e570c15bc0240ea2):
  the specification [`doc/leanvm/`](https://github.com/leanEthereum/leanVM/tree/a386121f84292f6fa663aaa3e570c15bc0240ea2/doc/leanvm)
  (§3 primitives, §4 committing, §5 arithmetization, §6 bus, §8 end-to-end, Annex A ring
  switching, Annex B WHIR, Annex C Flock); `crates/lean_vm/src/`, `crates/fiat_shamir/src/`,
  `crates/pcs/src/`, `crates/flock/src/`, `python-verifier/verifier.py`.
- ArkLib [Verified-zkEVM/ArkLib](https://github.com/Verified-zkEVM/ArkLib): `ArkLib/OracleReduction/`,
  `ArkLib/ProofSystem/`, `ArkLib/Data/`; pull requests #615 (knowledge append), #1244 (the
  sumcheck leaf), #1245 (round-by-round to plain); issues #676 (composition), #627 (BCS).
- [CMS19] A. Chiesa, P. Manohar, N. Spooner, *Succinct arguments in the quantum random oracle
  model*, TCC 2019 (ePrint 2019/834), Definition 8.5: round-by-round knowledge soundness.
- [CCHLRRW19] R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G. Rothblum, R. Rothblum, D. Wichs,
  *Fiat–Shamir: from practice to theory*, STOC 2019: round-by-round soundness.
- [CY24] A. Chiesa, E. Yogev, *Building cryptographic proofs from hash functions*: Theorems
  25.2.1, 31.3.1 and §28.3.2 (the BCS and Fiat–Shamir analyses).
- [BCS16] E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive oracle proofs*, TCC 2016-B: the
  Merkle compilation.
- [ACFY25] G. Arnon, A. Chiesa, G. Fenzi, E. Yogev, *WHIR: Reed–Solomon proximity testing with
  super-fast verification*, EUROCRYPT 2025; [NA25] A. Novakovic, G. Angeris, *Ligerito*;
  [BCHKS25] E. Ben-Sasson, D. Carmon, U. Haböck, S. Kopparty, S. Saraf, *On proximity gaps for
  Reed–Solomon codes* (ePrint 2025/2055, Theorem 4.6); [Hab25] U. Haböck, *A note on mutual
  correlated agreement for Reed–Solomon codes* (ePrint 2025/2110): for Annex B.
- [DP24] B. Diamond, J. Posen, *Polylogarithmic proofs for multilinears over binary towers*: ring
  switching and the novel basis; [LCH14] S. Lin, W. Chung, Y. Han, *Novel polynomial basis and
  its application to Reed–Solomon erasure codes*, FOCS 2014.
- [Tha22] J. Thaler, *Proofs, arguments, and zero-knowledge*: Proposition 4.1 (sumcheck), §4.6
  (GKR), §6.6.2 (multiset equality by fingerprinting); [Tha13] J. Thaler, *Time-optimal
  interactive proofs for circuit evaluation*, CRYPTO 2013, and [STW24] S. Setty, J. Thaler, R.
  Wahby, *Lasso*, for GKR-based grand products; Irreducible, *Multi-multiset matching (M3)*.
- [KRS25] D. Khovratovich, R. Rothblum, L. Soukhanov, *How to prove false statements: practical
  attacks on Fiat–Shamir*, CRYPTO 2025; [Fen26] G. Fenzi, *How to prove more false statements*
  (ePrint 2026/1838): attacks that use the hash function's code.
- [architecture.md](../architecture.md) for T4 and layer ownership;
  [leanisa-blueprint.md](leanisa-blueprint.md) for the relation;
  [leanvm-target.md](../leanvm-target.md) for the pin and its discrepancies.
- leanth (private): the explore branch `scaraven/proof-system-explore` at `db895db`, the pattern of
  [The spine](#the-spine), and the leanVM-a formalization at `23929f8c`, catalogued in
  [leanth-reuse.md](leanth-reuse.md), whose classically chosen extractor is the counterexample of
  acceptance test 24.
