# Roadmap: the leanVM proof system on ArkLib

leanVM proves that a leanISA execution exists by committing the six M3 tables as one multilinear
polynomial and running, in order, a grand-product argument for the bus (GKR), one batched
sumcheck for the tables' constraints, a two-cell public-input check, the Flock argument for the
BLAKE2S rows, ring switching, and one WHIR opening; Fiat–Shamir over BLAKE2s makes it a
non-interactive proof. This roadmap builds that verifier in Lean 4 on ArkLib's interactive oracle
reduction (IOR) framework and states the two theorems that make it a proof system for the
constraint relation of the [leanISA roadmap](leanisa-blueprint.md):

```text
piop_perfectCompleteness (I : M3Instance) :
  M3Holds I input q → the honest prover makes leanVmVerifier accept with probability 1
piop_rbrKnowledgeSoundness (I : M3Instance) :
  for every prover, leanVmVerifier accepts → except with probability piopError I,
    the extractor's column q satisfies M3Holds I input q
```

Both are stated in the *ideal oracle model*: the committed polynomial `q` is an oracle the
verifier may evaluate, and the challenges are uniform. They are stated over an abstract M3
instance `I`, the polynomial view of any Clean ensemble, and reach the leanISA relation through
the adaptor: `witnessOf` reads an `EnsembleWitness` off `q`, and `satisfiedBy_witnessOf` says
`M3Holds` on `q` gives `SatisfiedBy prog input (witnessOf q)`, so knowledge of `M3Holds` is
knowledge of `SatisfiedBy` at the same error ([The spine](#the-spine)). That is the proof-system
half of target T4 of [architecture.md](../architecture.md); composed with `constraintSoundness`
(leanISA Layer 10) the second becomes "an accepted proof has an execution". The non-interactive verifier `verify`,
the one the Rust prover's proofs are checked against, is specified in full and proved to be the
Fiat–Shamir compilation of that oracle verifier; its own security theorem is *conditional* on
three named upstream results (the WHIR opening, the Merkle/BCS compilation, and Fiat–Shamir in
the random-oracle model) that ArkLib does not yet prove. Each is an interface with an upstream
issue, never an axiom.

The route is chosen so that the **trusted surface** stays small and cites its source line: the
relation is Clean's `EnsembleWitness` under the leanISA `SatisfiedBy`, unchanged; every protocol
piece is an ArkLib `OracleReduction` with ArkLib's own `perfectCompleteness` and
`rbrKnowledgeSoundness`; and the generic pieces ArkLib lacks (grand products, batching, the
binary-field WHIR) are written in ArkLib's shape and upstreamed.

Suggested home: `LeanerVM/Protocol/Spine/` (the spine), `LeanerVM/Protocol/` (the phases over an
abstract instance, the adaptor, the compilation) with the Clean bridge in
`LeanerVM/Arithmetization/` and the transcribed constants in `LeanerVM/Parameters/`, following
[architecture.md](../architecture.md). Generic components live under
`LeanerVM/Protocol/ToArkLib/` (and `ToCompPoly/`, `ToVCVio/`) only until their upstream pull request merges.

This document is the specification. The Lean signatures pin the shapes most likely to drift;
they are not exhaustive. Where things stand is recorded separately in
[protocol-status.md](protocol-status.md), which is a snapshot and never the authority on what is
wanted. Work on a layer is claimed through the tracking issue
([#12](https://github.com/Verified-zkEVM/leanerVM/issues/12)); see
[How work is tracked](#how-work-is-tracked).

## For zkVM engineers

ArkLib formalizes a proof system as a chain of *reductions*. A reduction is a short interactive
protocol, with a fixed message schedule (`ProtocolSpec`), that turns a claim "the statement `x`
is in relation `R₁` with some witness" into a claim about a relation `R₂`, typically smaller:
sumcheck turns "this sum equals `T`" into "this polynomial has value `v` at the random point
`r`"; a random-linear-combination step turns ten claims into one. Some prover messages are
*oracles*: the verifier does not read the message, it queries it at points of its choosing. A
committed polynomial is exactly such an oracle. Two properties are proved per reduction and then
composed: **perfect completeness** (an honest prover always passes) and **round-by-round
knowledge soundness**, the standard form since [CCHLRR19]: an invariant on partial transcripts
that a cheating prover can only escape when a fresh verifier challenge lands badly, with an error
bound per challenge. Summing the bounds gives the interactive error; after Fiat–Shamir the
largest bound is what a random-oracle query buys the adversary. The knowledge part is
*straight-line*: an extractor reads the witness off the oracles, no rewinding.

Four things are built. **The relation**: `M3Holds I input q`, a checklist on one committed
column `q`, every table's columns stacked into one table of height `2^μ`: every constraint
polynomial of every table, of degree at most two in the row's columns, vanishes on that table's
rows read out of `q`; the pushed and pulled bus tuples read out of `q` are the same multiset;
every read count is nonzero; cells 0 and 1 of the memory block hold the two public words;
Flock's circuit holds of the committed BLAKE2s region, so the BLAKE2s rows are valid. The caps on
the announced sizes are not a clause: the compiled verifier checks them before the protocol
starts. It is stated over an abstract instance `I` (the tables' widths, log-heights, constraint
polynomials and their degree bound, flush tuples, count columns, boundary blocks, public lines
and stack layout), which `Ensemble.toM3` derives from any Clean `Ensemble`. **The
adaptor**: the witness maps `stackOf` (an `EnsembleWitness` to its stack) and `witnessOf` (a
stack to an `EnsembleWitness`, total and computable) with the two theorems `m3Holds_stackOf`
and `satisfiedBy_witnessOf`; the second carries a knowledge extractor from `M3Holds` to leanISA's
`SatisfiedBy` at the same error, and it is the only place the proof system meets leanISA. **The
oracle protocol**: the leanVM protocol of specification §8, phase by phase, as ArkLib reductions
over the one oracle `q`, composed sequentially, with the master theorems above; the spine fixes
its seams so that the phases are independent units of work. **The compilation**: WHIR realizes
the oracle, Merkle trees realize WHIR's oracles, and a BLAKE2s chain replaces the verifier's
coins; `verify : Proof → Bool` is that compiled verifier, executable, and is what Rust-produced
proofs are checked against.

What a reader should expect to be proved without hypotheses: everything about the oracle
protocol, given ArkLib's framework and the two sumcheck/grand-product components this roadmap
contributes upstream. What is stated but conditional: the security of `verify` itself, which
rests on WHIR's soundness in the list-decoding regime, on Merkle extraction, and on Fiat–Shamir,
all three tracked as ArkLib work. What is not attempted here: recursion (T5, T6) and zero
knowledge (leanVM has none).

Why the relation is polynomial and not "a valid execution exists": sumcheck, GKR and WHIR
manipulate polynomials, and a knowledge extractor recovers column data from a transcript, never
an execution; a protocol stated against `ValidExecution` would demand of the extractor what it
cannot produce and would couple every phase to the semantics. The extractor here is
`piopExtractor`, which reads the stack `q` off the oracle message, followed by `witnessOf`
applied to it in the adaptor: straight-line (no rewinding) and computable (one pass over `q`).
Neither ArkLib nor this roadmap models running time; "computable" is the enforceable form of
that requirement (acceptance test 24).

## Scope

### In scope

- ArkLib as a Lake dependency at `dca90385`, with the field, sampling and oracle-interface
  instances that make `E = GF(2^192)` a challenge space and the stacked columns an oracle;
- the spine: the abstract instance `M3Instance` and its relation `M3Holds`, the seam relations
  and message schedules of the six phases, the hole interfaces `Phase.Def`, `Phase.Security` and
  their generic counterparts, the composition `leanVmPiop` with the two master theorems over
  `Phases I`, the adaptor's transport lemma, and a toy instance every phase is tested on;
- hypercube tables over `K` and `E`, stacking with selectors, the index column, the bytecode
  multilinear, and their evaluation identities;
- the polynomial view of a Clean `Ensemble`: constraint polynomials and flush tuples extracted
  from a component's operations, the degree bound, and the bridge lemma to Clean's row-wise
  `Constraints`;
- the M3 instance for leanISA: announced sizes, caps, stack and leaf layouts, the stack of an
  `EnsembleWitness`, and the extractor reading a witness back from the stack;
- a sumcheck for eq-weighted virtual polynomials with a terminal claim and back-loaded padding,
  and a batching component by powers of one challenge (generic; upstream);
- the fingerprinted grand product, its multiset lemma, and the batched radix-4 GKR (generic;
  upstream);
- the bus phase (§5.2–§5.4, §6), the table sumcheck (§5.5), the public-input check (§8.2), the
  claim pool and the opening sumcheck, as ArkLib reductions with perfect completeness and
  round-by-round knowledge soundness;
- the Flock and ring-switching *interface* consumed from the Flock roadmap (#3);
- the composed oracle protocol `leanVmPiop`, its honest prover, its error `piopError`, and the
  two master theorems;
- WHIR over Reed–Solomon codes in the novel polynomial basis of `K`, Merkle trees over BLAKE2s,
  and leanVM's WHIR parameters (Annex B; generic parts upstream, shared with #3);
- Fiat–Shamir with leanVM's BLAKE2s chain, the `Proof` object and its serialization, the
  executable `verify`, and the theorem that `verify` is the compiled oracle verifier;
- the conditional non-interactive theorems and the T4 corollary through `constraintSoundness`;
- executable fixtures: kernel-checked identities on small instances and a Rust-produced proof
  accepted by `verify`, with mutations rejected.

### Out of scope

- the tables, channels, `SatisfiedBy` and `AssignmentRepresents`: leanISA Layers 5–10 (#4);
  this roadmap consumes `SatisfiedBy` and changes nothing in it beyond the two requests in
  [Boundaries](#boundaries);
- the BLAKE2s Boolean circuit, Flock's zerocheck and lincheck, and ring switching: the Flock
  roadmap (#3); consumed here as one interface (Layer 9);
- witness generation from an execution (T2): the honest prover here starts from an
  `EnsembleWitness`;
- the recursion guest, deferred claims, the verifier-in-circuit (T5), and any extraction bridge
  across recursion (T6); `verify` is the *native* verifier, which evaluates the bytecode and
  Flock matrices itself, and is shaped so that the deferred variant is a one-function change;
- zero knowledge;
- proximity-gap and list-decoding theorems for Reed–Solomon codes (mutual correlated agreement
  up to the Johnson bound, [BCHKS25] Theorem 4.6): consumed as a coding-theory interface,
  tracked in ArkLib;
- Fiat–Shamir and BCS security in the random-oracle model, and the round-by-round to
  state-restoration implications: consumed as interfaces, tracked in ArkLib;
- performance of the honest prover: it is a specification that runs, not an implementation.

## Dependencies and exact contracts

A prerequisite below is a named declaration at a pinned revision, an earlier layer here or in
the leanISA roadmap, or a cited section of a source. The pins are in `upstreams.json` and
[dependencies.md](../dependencies.md): leanVM
[`a386121f`](https://github.com/leanEthereum/leanVM/commit/a386121f84292f6fa663aaa3e570c15bc0240ea2),
ArkLib
[`dca90385`](https://github.com/Verified-zkEVM/ArkLib/commit/dca90385fb40dd5eb8da9145da6348ed17f5cd8b),
CompPoly `3468b38c`, Clean `93c9d1ef`, VCVio `f9dc47d9` (through ArkLib), Lean `v4.33.1`.

### The leanVM specification and implementation

Two kinds of source, with opposite disciplines (the authoring skill `lean-spec-authoring` sets
the rules). **Category A** content — what the verifier accepts and why it is sound — is written
from the specification document first and then diffed against the Rust and the Python verifier;
the Lean is intended to become the standard. **Category B** content — transcript tags, absorption
order, message encodings, layouts, WHIR parameters, hash constants — is transcribed from its
source and is wrong if it deviates. Every module docstring names its category, its source section
or file and lines, and the pin.

| Artifact | Category | Source at the pin |
| --- | --- | --- |
| M3 model, grand product, GKR, leaf stacking, table sumcheck | A | specification §5 (`doc/leanvm/body/05-arithmetization.tex`) |
| Lookup and count arguments, index column | A | specification §6.2–§6.5 |
| Unrolled protocol, public input, filling | A | specification §8.2, §8.3, §8.5 |
| Ring switching, WHIR, novel basis and additive NTT | A (protocol) / B (parameters) | specification Annex A, Annex B; `crates/pcs/src/whir.rs`, `whir_config.rs:38-86` |
| Flock | A, owned by #3 | specification Annex C; `crates/flock/src/` |
| Fiat–Shamir chain: tags, seeding, sampling, grinding | B (§8.4 is `TODO`; finding F1) | `crates/fiat_shamir/src/lib.rs:18-174`; `crates/lean_vm/src/cpu/mod.rs:82-124` |
| Proof object and stream order | B | `crates/fiat_shamir/src/transcript.rs:9-19, 280-330`; `cpu/mod.rs:711-779` |
| Round-polynomial encoding (one coefficient derived) | B | `crates/fiat_shamir/src/transcript.rs:289-309` |
| Stack and leaf layouts, block order, selectors | B | `crates/lean_vm/src/witness.rs:85-101`, `leaf.rs:53-156`, `cpu/layout.rs:400-445` |
| Count blocks (tables' count columns only) | B | `cpu/layout.rs:412-414`; `leaf.rs:664-668` |
| Bytecode multilinear, sixteen slots | B | specification §8.1; `leaf.rs:585-637` |
| Caps and the stacking bound `μ ∈ [15, 28]` | B | `cpu/mod.rs:45-64, 130-178`; `lean_vm/src/pcs.rs:49-51` |
| GKR radix, combiner resampling, root sharing | B | `crates/lean_vm/src/gkr.rs:32-76, 247-430` |
| ξ-power assignment, derived target | B | `cpu/mod.rs:404-441, 726-735` |
| WHIR fold factors, rates, queries, grinding | B | `crates/pcs/src/whir_config.rs:38-86, 260-370`; `python-verifier/verifier.py:910` |
| Merkle hashing, digest encoding | B | `crates/fiat_shamir/src/merkle.rs:14-67`; `crates/pcs/src/merkle.rs` |
| BLAKE2s byte hasher (Merkle, transcript, seed) | B | `crates/primitives/src/hash.rs`; RFC 7693 §3.3 |
| Second verifier (cross-check only) | A cross-check | `python-verifier/verifier.py:1365-1414` |

### The leanISA roadmap

The relation and everything below it. Consumed as named declarations of the layers listed in
[Interfaces supplied to later work](leanisa-blueprint.md#interfaces-supplied-to-later-work);
nothing is restated here.

| Declaration | Contract used here |
| --- | --- |
| `K`, `E`, `y`, `ofK`, `E.limb`, `E.ofLimbs`, `g`, `gpow`, `orderOf_g` (Layer 0) | The fields, limbs and generator. Challenges are `E`; columns are `K`; `gpow` is the index column. |
| `iv`, `sigma`, `compress` (Layer 1) | The compression the transcript, Merkle hashing and the Flock circuit share; the byte hasher (Layer 11 here) is the RFC 7693 wrapper over `compress` with the last-block flag only (finding R21). |
| `Program`, `PublicInput`, `word0`, `word1`, `minLogMem`, `maxLogMem`, `maxLogRows`, `maxLogBytecode`, `minLogRowsBlake2s` (Layer 2) | The public statement and the caps. |
| `encodeSlots` (Layer 4) | The bytecode multilinear is `encodeSlots` laid out on `2^(k_bc + 4)` points. |
| `leanIsaEnsemble`, `xorTable` … `blake2sTable`, `memTable`, `bytecodeTable`, `leanIsaVerifier` (Layers 6–8) | The components whose operations are read as polynomials (Layer 2 here). |
| `StatePull` … `BytecodePush`, `MemMsg`, `StateMsg`, `BytecodeMsg` (Layer 5) | The channel of an interaction names its domain separator and coordinate order on the 16-slot bus. |
| `SatisfiedBy`, `BalancedPair`, `CountsNonzero`, `Caps`, `imageOf` (Layer 8) | The relation the adaptor targets: `satisfiedBy_witnessOf` proves it from `M3Holds`, and nothing above the adaptor mentions it (convention *The wall*). `Caps` includes power-of-two heights (#13, taken). |
| `constraintSoundness`, `HasFillBlocks`, `constraintCompleteness` (Layer 10) | Consumed only by Layer 13. |

### ArkLib

ArkLib is a Lean `module` library, so every file here that imports it and not Clean may be a
`module`. ArkLib carries admitted theorems under a committed baseline
(`scripts/axiom_baseline.json`); a leanerVM declaration may not depend on one, because the kernel
axiom audit (`axiom-audit-root: LeanerVM`) rejects `sorryAx`. The second table lists the admitted
results this roadmap would otherwise consume and what replaces each.

| Declaration | Contract used here |
| --- | --- |
| `ProtocolSpec n`, `Direction`, `MessageIdx`, `ChallengeIdx`, `FullTranscript`, `Transcript` (`OracleReduction/ProtocolSpec/Basic.lean`) | The message schedule of every reduction; challenges are `V_to_P` rounds. |
| `OracleInterface` with `Query`, `Response`, `answer` (`OracleReduction/OracleInterface.lean:53-73`) | The query type and answer of an oracle message. Layer 0 gives the stack the evaluation interface. |
| `Prover`, `Verifier`, `OracleVerifier`, `Reduction`, `OracleReduction`, `OracleProof` (`OracleReduction/Basic.lean:222-669`) | The carriers. An `OracleVerifier` receives challenges and queries; `outputOracle` names which oracles it hands on (`OracleOutputEmbedding`) or derives (`OracleOutputSimulation`). |
| `Reduction.completeness`, `perfectCompleteness`, `OracleReduction.perfectCompleteness` (`Security/Basic.lean:89-103, 460-469`) | Completeness: honest prover and verifier agree on the output statement and the output relation holds, with probability `≥ 1 - ε`; `ε : ℝ≥0`. |
| `Verifier.knowledgeSoundness`, `Extractor.Straightline` (`Security/Basic.lean:248-359`) | Knowledge soundness with a universal straight-line extractor. |
| `Verifier.KnowledgeStateFunction`, `Extractor.RoundByRound`, `rbrKnowledgeSoundness`, `rbrKnowledgeSoundnessWorstCase`, `rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness` (`Security/RoundByRound.lean:77-190, 416, 534, 606`) | Round-by-round knowledge soundness, error `pSpec.ChallengeIdx → ℝ≥0`; the worst-case form for a named extractor and knowledge state function, `rbrKnowledgeSoundnessWorstCaseWith` (`:553`), is what each layer proves. |
| `Verifier.rbrKnowledgeSoundness_implies_rbrSoundness` (`Security/Implications.lean:85`) | Proved; used to state plain soundness as a corollary. |
| `OracleReduction.append`, `OracleReduction.seqCompose`, `ProtocolSpec.seqCompose` (`Composition/Sequential/Append/Basic.lean:709`, `General.lean:255`) | Sequential composition of the phases. |
| `Reduction.seqCompose_perfectCompleteness_of_pure`, `OracleReduction.append_perfectCompleteness_of_pure_verifiers`, `seqCompose_completeness_of_guarded_verifiers` (`Composition/Sequential/{Completeness,Append/Completeness,GuardedNary}.lean`) | Completeness composition, proved; needs pure prover output and pure or guarded verifiers, and suffix completeness from every deterministic shared-oracle state. |
| `Verifier.append_rbrSoundnessWorstCase_of_pure_first`, `Verifier.StateFunction.append`, `Extractor.RoundByRound.append` (`Composition/Sequential/Append/RoundByRound.lean:37`, `Append/StateFunction.lean:292, 75`) | Round-by-round *soundness* composition, proved for a pure first verifier; extractors appended through the first verifier's verdict. The knowledge form is ArkLib #615's, ported to `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean` (ledger A2). |
| `Component.ReduceClaim`, `CheckClaim`, `RandomQuery`, `DoNothing` (`ProofSystem/Component/`) | Zero-round claim rewriting and checking, the final oracle query; all proved. |
| `Sumcheck.Spec.reduction`, `StatementRound`, `relationRound`, `Sumcheck.Domain` (`ProofSystem/Sumcheck/Spec/General.lean:171`, `SingleRound.lean:130-144`, `Domain.lean`) | The shape of a sumcheck statement and round; the leanVM sumcheck (Layer 4) reuses `Domain` and states its relations in this shape. |
| `MvPolynomial.MLE`, `eqPolynomial`, `eqTilde`, `eqTilde_append`, `MLE_eq_zero_iff`, `MLEEquivFin` (`Data/MvPolynomial/Multilinear.lean`) | Multilinear extensions and the equality kernel, proved; the bridge to CompPoly's tables is `CMlPolynomialEval.eval_eq_MvPolynomial_MLE` (`ToCompPoly/Multilinear/Basic.lean:56`). |
| `MvPolynomial.schwartz_zippel_counting`, `prob_eval_zero_le_div` (`Data/MvPolynomial/SchwartzZippelCounting.lean`) | Every per-challenge error bound. |
| `Reduction.fiatShamir`, `Verifier.fiatShamir`, `fsChallengeOracle` (`OracleReduction/FiatShamir/Basic.lean:114-138`) | The Fiat–Shamir transform as a definition; its security is ledger A5. |
| `Commitment.Scheme`, `binding`, `perfectCorrectness_of_opening_perfectCompleteness` (`Commitments/Functional/Basic.lean`) | The commitment interface WHIR's commit and open instantiate. |
| `ToyProblem.Codegen` (`ProofSystem/ToyProblem/Codegen.lean`) | The pattern for code-generation probes; copied for `verify` and the honest prover. |
| `SampleableType`, `uniformSample`, `$ᵗ` (VCVio `OracleComp/Constructions/SampleableType.lean:44`) | Challenge sampling; Layer 0 supplies the `E` instance. |

**Admitted at the pin, and what this roadmap does about it.** Each row is an ArkLib issue or
pull request to open (the tracker records the numbers); none is worked around by a local
hypothesis.

| Ledger | ArkLib state at `dca90385` | Needed by | Action |
| --- | --- | --- | --- |
| A1 sumcheck round-by-round knowledge soundness | `Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundness` and the lens instances are `sorry` | Layers 4, 5, 10 | Layer 4 proves the single-round bound for its own sumcheck shape and contributes it as the missing leaf. |
| A2 knowledge-soundness composition | `Verifier.append_knowledgeSoundness`, `append_rbrKnowledgeSoundness`, `seqCompose_rbrKnowledgeSoundness` are admitted (issue #676) | the spine (`Component.Security.append`) | Admitted upstream, proved locally: `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean` (hole C1) is the port of ArkLib pull request #615's `Append/Knowledge.lean`, the worst-case round-by-round *knowledge* append for a guarded first verifier; the port is deleted, and its two names in `Component.lean` replaced by ArkLib's, when the pin moves past #615. |
| A3 round-by-round implies plain | `rbrKnowledgeSoundness_implies_knowledgeSoundness`, `rbrSoundness_implies_soundness` admitted | Layer 12 (statement of the plain corollary) | The master theorems are stated round-by-round; the plain corollary is stated once the implication lands upstream. |
| A4 context lifting | every `liftContext_*` security theorem admitted | none | Not consumed: statements are shaped so that no lens is needed. |
| A5 Fiat–Shamir and BCS | `fiatShamir_completeness` admitted; `BCSTransform` commented out (issue #627); `DuplexSponge` security admitted | Layer 12 | Named interfaces `FiatShamirSecurity` and `BcsSecurity` with the upstream theorem as witness obligation; the *definitions* of the compiled verifier are consumed. |
| A6 grand product, GKR, batching, stacking | absent | Layers 1, 4, 5 | Written here in ArkLib's shape, upstreamed. |
| A7 WHIR, Merkle, BLAKE2s | absent (only coding-theory lemmas) | Layer 11 | Written here; the coding-theory theorem it needs is ledger A8. |
| A8 mutual correlated agreement up to Johnson | `rs_mcaError_le_in_johnson_range` is an external admit | Layer 11 | Interface `McaJohnson`, witness obligation [BCHKS25] Theorem 4.6 in ArkLib. |
| A9 ring switching packing leaves | `RingSwitching/Packing` leaves are `sorry`, and no `GF(2) → GF(2^64)` profile | Layer 9 | Owned by #3 (F5); consumed through the Flock interface. |

### CompPoly

| Declaration | Contract used here |
| --- | --- |
| `BF64`, `BF64.Ext3`, `card_bf64`, `card_ext3`, `Ext.coeff`, `Ext.ofFn`, `Ext.eval₂`-style lifts | As in the leanISA roadmap; `Fintype.card E = 2^192` is the only cardinality fact the error bounds use. |
| `CMlPolynomialEval R n` (`Multilinear/Basic.lean:47`), `evalMle`, `evalMleLayer`, `evalMle_succ`, `eval₂Mle`, `eval_mle_eq_eval` | Hypercube tables and their multilinear evaluation, computable; `eval₂Mle` is the `K → E` lift; `evalMleLayer` fixes the first variable, which every sumcheck prover reuses. |
| `eqTilde`, `eqTilde_eq_prod`, `eqTilde_append`, `lagrangeBasis` (`Multilinear/Basic.lean:410-632`) | The equality kernel as a table; `eqTilde_append` is the block factorization of selectors. |
| `evalManyMleByLayers` (`Multilinear/ManyEval/`) | Many tables at one point: the column claims at the sumcheck's end. |
| `CPolynomial`, `Lagrange.interpolate` (`Univariate/`) | Round polynomials of a sumcheck as coefficient vectors. |
| `AdditiveNTT.{U, W, normalizedW, additiveNTT, computableAdditiveNTT}` (`Fields/Binary/AdditiveNTT/`) | The novel polynomial basis and the encoder of Annex B.3, generic over a basis; Layer 11 instantiates the `K` basis `x^0 … x^63`. |
| `CMlPolynomialEval.toMvPolynomialDeg1`, `equivMvPolynomialDeg1` (`Multilinear/Equiv.lean`) | Tables as Mathlib multilinears, for the identities proved in `MvPolynomial`. |

CompPoly has no hypercube sum, no pointwise product of tables, no `GF(2^8) ↪ E` embedding and no
Frobenius on `Ext`; the first two are Layer 1 here, the last two are #3's (F1). The eager
`Fintype BF64` instance (finding P3) still forbids a leanerVM executable; `verify` is exercised
by compile-time `#guard` and by the code-generation probes, not by a binary.

### Clean

| Declaration | Contract used here |
| --- | --- |
| `Expression F` with `var`, `const`, `add`, `mul`; `Expression.eval : Environment F → Expression F → F` (`Circuit/Expression.lean:6-90`) | Constraints and tuple coordinates are syntax trees over the row variables; variable `i` is column `i`. |
| `Component.operations : Operations F`, `Operations.constraints : List (Expression F)`, `Operations.interactions : List (AbstractInteraction F)` (`Air/FlatComponent.lean:21`, `Circuit/Operations.lean:404-432`) | The row-independent constraint and flush lists of a component. |
| `constraintsHold_iff_forall_mem`, `Table.Constraints`, `Table.environment`, `Environment.fromArray` (`Operations.lean:168-182`, `FlatComponent.lean:151-186`, `Expression.lean:71`) | The row-wise meaning the polynomial view must agree with; out-of-range variables read `0`. |
| `AbstractInteraction` (`channel`, `mult : Expression F`, `msg : Vector (Expression F) arity`), `Interaction`, `AbstractInteraction.eval` (`Circuit/Channel.lean:101-105, 305-329`) | A flush as expressions and its value on a row. |
| `EnsembleWitness` (`tables : List (Table F)`, `data`, `publicInput`), `Table.table : List (Array F)`, `Table.width` (`Air/FlatEnsemble.lean:19-25`, `FlatComponent.lean:151-156`) | The witness. A table of height `2^τ` is `2^τ` rows of `width` cells; heights are not powers of two in Clean, hence the request in [Boundaries](#boundaries). |
| `Circuit.witgen` (`Circuit/WitnessGeneration.lean:82`) | Per-row witness generation; not consumed here (T2). |

Clean has no polynomial, degree, height or padding notion (findings C5, C6); Layer 2 supplies the
polynomial view and is Clean's upstream candidate.

### Mathlib

| Declaration | Contract used here |
| --- | --- |
| `MvPolynomial`, `Polynomial.card_roots'`, `Polynomial.eq_of_degree_le_of_eval_finset_eq` | Degrees and root counts behind every Schwartz–Zippel step. |
| `UniqueFactorizationMonoid` on `MvPolynomial`, `Polynomial.Monic`, `Multiset.map`, `Multiset.prod` | Lemma 5.2: a product of distinct linear forms determines its multiset of factors. |
| `Finset.sum_product`, `Fintype.sum_pow`, `Finset.prod_pow_eq_pow_sum` | The hypercube identities of Layer 1. |

## Pinned conventions

| Subject | Convention |
| --- | --- |
| Hypercube | `Fin (2^n)` indexes `{0,1}^n` with bit `k` = coordinate `k` (low bit first), the CompPoly and leanVM order. A point is `Vector E n` (CompPoly's shape; ArkLib's `Fin n → E` is `Vector.ofFn` away). |
| Tables | `Column n` wraps `CMlPolynomialEval K n` (values) in a structure, so that its evaluation oracle is disjoint from ArkLib's position-query interface on `Vector`; `ETable n := CMlPolynomialEval E n`. A "multilinear" is its value table; its extension is `evalMle`, lifted by `eval₂Mle` when the point is in `E`. |
| `eq` | `eq(r, x) = ∏ (1 + r_k + x_k)` over `E` (characteristic 2); `eqTable r : ETable n` holds `eq(r, ·)` on the cube. |
| Sumcheck messages | A round polynomial travels as its coefficient list, low degree first, of length `d + 1`; the oracle protocol sends all of them. Dropping one is the *encoding* of Layer 12 (`transcript.rs:289-309`), inverted by the running claim. |
| Statements and parameters | The public `input : I.Stmt` is the statement of the oracle protocol and the instance `I : M3Instance` (the program and the announced sizes, for leanISA) indexes the protocol family; a phase's `StmtIn` carries only what earlier phases produced (claims). The relation of the first phase is `M3Rel I`, that is `M3Holds I input q` on the stack `q`; the caps are checked by the compiled verifier on the announced sizes before the oracle protocol starts (Layer 12), and are a hypothesis of the adaptor's soundness theorem (Layer 3). |
| The oracle | One committed oracle `q : Column μ_stack` for the whole protocol (`OStmt : Unit → Type`), with `OracleInterface` query `Vector E μ_stack` and answer `eval₂Mle q`. No other oracle exists in the oracle protocol; WHIR's codewords appear only in Layer 11. |
| Errors | `ℝ≥0`, per verifier message, as ArkLib's `rbrKnowledgeError`; the closed form is a `def` next to the theorem, and the interactive error is its sum. `|E|` is `Fintype.card E`, rewritten to `2^192` only in the numeric acceptance test. |
| Bus | Width `m = 16`; coordinate 0 is the separator `g^0 / g^1 / g^2` for state, memory, bytecode; coordinates follow the specification's tuple order; unused coordinates are the constant `0`. Fingerprint `π_α(t) = Σ_{i<16} eq(α, bits i) · t_i` with `α : Fin 4 → E`; leaf `β − π_α(t)`, padding leaf `1`. |
| Count tree | Leaves are the tables' count columns themselves (`α = 0`, no `β`), padded with `1` to the bus trees' depth; the finalize counts are not in it (`layout.rs:412`). |
| GKR | Radix 4 from the root down; if `μ` is odd, one radix-2 layer first. A fresh combiner `λ` per layer; two combination challenges after each radix-4 layer; the three trees share every challenge and end at one `ζ`. Layer sumcheck messages have degree 5 (eq × four multilinears); the round check is on the cofactor (Gruen). |
| Stacks | Blocks ordered largest first at aligned offsets; `sel_b = offset_b >> κ_b`; `q̃(z, sel_b) = P̃_b(z)`. The witness stack holds every table column in table order, then `mem_0, mem_1, mem_2`, `cntfin_mem`, `cntfin_bc`, `q_flock` (`witness.rs:85-101`); `μ_stack ∈ [15, 28]`. |
| Table sumcheck | Variables bound highest first; table `j` joins at round `τ_max − τ_j`; its summand is padded by `∏_{k ≥ τ_j} X_k`; round polynomials have degree 3; `ξ` powers: constraints table by table, then the three bus sides in `[push, pull, count]` order sharing the last three powers; the target is computed by the verifier, never sent (finding F4). |
| Claim pool order | Bus (framework block) claims, then per-table column claims, then the three public-input limb claims (`finish_claims`, `cpu/mod.rs:656-667`); ring-switched claims take the low powers of `λ`, point claims the high ones (finding F8). |
| Fiat–Shamir | A Merkle–Damgård chain of `compress` on a 256-bit state; block lane 3 carries the tag `1` (observe), `2` (squeeze), `3` (grinding base), `4` (grinding nonce); no labels (finding F1); seeded by `compress(iv, input)` with `iv` the BLAKE2s of `"leanvm" ‖ len ‖ R1CS_DIGEST ‖ bytecodeHash`; one squeeze yields one `E` challenge (three low words). |
| Verifier shape | `verify` is a total, computable function of `(prog, input, proof)` to `Bool`; it never panics; a malformed proof is `false`. Structure checks on public data that the Rust `assert!`s (finding F10) are theorems about the layout, not branches of `verify`. |
| Trusted surface | Every trusted definition fits on one screen, cites its source line, and appears in [Interfaces](#interfaces-supplied-to-later-work); assumed interfaces are structures with a docstring naming the upstream witness obligation, never `variable`-block hypotheses or `axiom`s. |
| Unproved targets | A statement whose dependency is not yet available is a block comment at its place, carrying the statement and the dependency (leanISA convention). Never `sorry`. |
| Generic code | A definition or theorem that belongs upstream lives under `LeanerVM/Protocol/ToArkLib/`, `LeanerVM/Protocol/ToCompPoly/` or `LeanerVM/Protocol/ToVCVio/` by destination, in a module of its own with a docstring saying it is a candidate for that library, so that it can be ported file by file; when the upstream pull request merges and the pin moves, the local copy is deleted in the same pull request. Comments everywhere are brief and self-contained: they cite the specification, never this roadmap. |
| Module system | ArkLib is a `module` library; a file importing ArkLib and not Clean (nor a plain file) is a `module`. The Clean bridge (Layer 2), the adaptor (Layer 3) and T4 (Layer 13) are plain; the spine and every phase are modules, since `M3Instance` carries polynomials and tables, never a Clean circuit. |
| The wall | Every module of the proof system is written over an abstract `I : M3Instance` and imports nothing from `LeanerVM/Arithmetization/`; the only exceptions are the Clean bridge (Layer 2), the adaptor (Layer 3) and T4 (Layer 13). `scripts/check-layers.sh` enforces the import rule (acceptance test 25). A leanISA change touches `leanIsaInstance`, the adaptor and T1, and nothing else. |
| Holes | A phase or generic component is two structures: `X.Def` (the reduction, its relations and its per-challenge error) and `X.Security` (perfect completeness, and round-by-round knowledge soundness over a `Def` for an extractor and a knowledge state function it carries: ArkLib's `rbrKnowledgeSoundnessWorstCaseWith` form, so the extractor is named, not merely shown to exist). A `Def` lands with its completeness proof and an honest-run test on the toy instance; its `Security` may land later, as its own pull request; neither ever contains `sorry`. Until every hole is filled, `Phases.Security` is an assumed interface in the sense of *Trusted surface*. |
| Seams | The output relation of a phase is the input relation of the next, by definition (`Seam.*`), never by a bridge lemma (acceptance test 26). `Seam.bus` carries the reused zerocheck point, `∀ j i, C̃_{j,i}(ζ_{<τ_j}) = 0`, and the escape "violated on the cube, zero at ζ" is charged in the bus phase, coordinate by coordinate as ζ is drawn, `1/|E|` per coordinate per constraint (leanth's `ZerocheckClaim` pattern); there is no separate zerocheck phase. `Seam.bus` also bounds the total degree of every term of every linear claim by the instance's `d`, the degree the table sumcheck is built for (acceptance test 28). |
| Extractors | Every extractor is a computable definition. The protocol's is `piopExtractor`, the commit phase's (which reads the stack off the oracle message) followed by the phases', straight-line; `witnessOf` is applied to its output by the adaptor. An extractor chosen by `Classical.choose` proves soundness, not knowledge (acceptance test 24). |
| Public input | The statement fixes *lines*, not cells: a `PublicLine` is a column with the values its cells 0 and 1 must hold (`PublicLinesHold`), the shape the public-input phase of §8.2 checks with one challenge, on the line through the two cells. The leanISA instance has three, on `mem_0, mem_1, mem_2`, the third with cells `0, 0`. An arbitrary list of cells would admit statements no phase with that schedule can serve. |

## The spine

The spine is the one pull request (hole S; its specification is a section of the [hole
comment](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) on the dashboard #12) that fixes everything two neighbouring pieces of work would
otherwise have to agree on, and proves the composition once. It is built under
`LeanerVM/Protocol/Spine/` (`Instance`, `Seams`, `Phase`, `Compose`, `Toy`) and, for the parts
that belong in ArkLib, `LeanerVM/Protocol/ToArkLib/` (`Oracles`, `Component`, `KnowledgeAppend`,
`PassThrough`, `SendOracle`, `Refinement`), with its tests in
`tests/LeanerVMTests/Protocol/Spine.lean`; the sketch below names what is there. After it, every
phase, every generic component, the instance and the compilation is a unit of work that
consumes spine names only, is tested on a toy instance, and lands in two halves (`Def`, then
`Security`). It restates the shape the leanVM-a formalization used in leanth (explore branch: a
`Type 0` witness, a relation anchored to Clean, a round skeleton indexed by the sizes, a commit
stage pinning the oracle to the witness of record, the reused zerocheck point carried as a
clause between stages, an abstract PCS boundary) on this roadmap's names, and drops its two
defects: an extractor chosen classically instead of read off the commitment, and a balance
summed in the field.

### The relation ladder

| Relation | Statement | Witness | Where | What it says |
| --- | --- | --- | --- | --- |
| `Ensemble.Statement ens pi` | `pi` | `EnsembleWitness ens`, in `Type 1` | Clean `Air/FlatEnsemble.lean:361` | every row of every table satisfies its component's constraints and every channel balances, multiplicities summed in the field with the side condition `interactions.length < ringChar F`. Over `K` the side condition fails for every real ensemble and a tuple pushed twice and never pulled balances (#16). leanth's relation; unusable here as it stands. |
| `SatisfiedBy prog input w` | `input` | `EnsembleWitness (leanIsaEnsemble prog)` | leanISA Layer 8 | thirteen conjuncts: Clean's constraints and public input; three `BalancedPair`s counted in ℕ; the verifier's `CountsNonzero` and `Caps`; the three fixed-column facts Clean cannot yet express; Flock's `Blake2sRowsValid`; the two public words. T1's relation. |
| `M3Holds I input q` | `input`, and the sizes in `I` | `q : Column I.μ`, in `Type 0` | the spine | everything the verifier establishes about the stack (below). The protocol's relation. |
| `ValidExecution prog input t` | `input` | a trace | leanISA Layer 3 | T1's target; never the protocol's relation, because the extractor recovers columns, not an execution. |

The adaptor joins the middle two: `witnessOf : Column μ → EnsembleWitness` with
`satisfiedBy_witnessOf : M3Holds → SatisfiedBy`, along which knowledge transports at the same
error (pointwise, `Refinement.map_option_valid`), and `stackOf` with `m3Holds_stackOf`, which completeness
needs. T4 is `verify_knowledgeSound` composed with the adaptor and `constraintSoundness`. `Type 1`
matters because ArkLib's statement and witness types are in `Type`: an `EnsembleWitness` cannot
be the protocol's witness, and the stack can.

### The picture

```text
                    ┌──────────────────────── Semantics ────────────────────────┐
                    │  ValidExecution prog input t              (leanISA Layer 3)│
                    └───────────────────────────▲───────────────────────────────┘
                                                │ T1: constraintSoundness / constraintCompleteness
                    ┌───────────────────────────┴───────────────────────────────┐
   Clean            │  R_isa:  SatisfiedBy prog input w                          │  leanISA Layer 8
   Ensemble ──────▶ │          w : EnsembleWitness (leanIsaEnsemble prog)        │  Type 1, 13 conjuncts
   (components,     └───────────────────────────▲───────────────────────────────┘
    channels,                                   │  ADAPTOR (a Refinement, both directions)   Layer 3
    verifier)           witnessOf : Column μ → EnsembleWitness    satisfiedBy_witnessOf : M3Holds → SatisfiedBy
        │               stackOf   : EnsembleWitness → Column μ    m3Holds_stackOf     : SatisfiedBy → M3Holds
        │ Ensemble.toM3 (generic; Layer 2)      │
        ▼                                       │
   M3Instance I  ═══════ the wall ══════════════╪══════  nothing above imports leanISA
   (log-heights, widths, constraint polynomials,│
    flush tuples with side + separator, count   │
    columns, boundary blocks, stack layout, μ)  │
                    ┌───────────────────────────┴───────────────────────────────┐
                    │  R_m3(I):  M3Holds I input q,   q : Column μ   (Type 0)    │  seam 0
                    ├───────────────────────────────────────────────────────────┤
                    │  commit ⟫ bus ⟫ table ⟫ public ⟫ flock ⟫ opening          │  the spine: seams,
                    │  Seam.bus  Seam.table  Seam.pub  Seam.flock  Seam.done     │  claims, composition
                    │  phase i: Phase.Def (hole)   Phase.Security (hole)         │  holes P1 to P8
                    │  generic: Sumcheck.*  Gkr.*  Batch.*  (holes G1 to G6)     │
                    ├───────────────────────────────────────────────────────────┤
                    │  piop_perfectCompleteness   piop_rbrKnowledgeSoundness     │  ideal oracle model
                    │  extractor := piopExtractor (q read off the transcript)    │  computable, straight-line
                    └───────────────────────────▲───────────────────────────────┘
                                                │  compile: WHIR + Merkle + Fiat–Shamir (Layers 11, 12)
                    ┌───────────────────────────┴───────────────────────────────┐
                    │  verify : Program → PublicInput → Proof → Bool             │
                    │  verify_knowledgeSound (fs) (bcs) (mca) (flock): conditional│
                    └───────────────────────────────────────────────────────────┘
   T4  =  verify_knowledgeSound  ∘  Refinement.map_option_valid satisfiedBy_witnessOf  ∘  constraintSoundness
```

### What the spine fixes

1. **The abstract instance**, `M3Instance`: what every phase reads and nothing more, including
   a degree bound `d` with its two proofs, `constraints_degree` and `flushes_degree`: every
   constraint and every flush coordinate has total degree at most `d` (leanVM's is 2).
2. **The relation on the stack**, `M3Holds`, and its ArkLib form `M3Rel`.
3. **The seam relations**: the output relation of each phase, which is the input relation of
   the next by definition. They are the load-bearing definitions of the whole proof system and
   get the spine's review budget.
4. **The message schedule of each phase** travels with its `Def` (the fields `n`, `pSpec`),
   so that Layer 12's `verify` depends on the phases' definitions and not on their proofs; the
   spine fixes only the commit phase's (`commitSpec`, one prover message). The stream order of
   `cpu/mod.rs:711-779` (Category B) is each phase's to transcribe and Layer 12's to check.
5. **The hole interfaces**: a `Def`, a `Complete` and a `Security` per phase and per generic
   component (`Component.*`, specialised to the one oracle as `Phase.*`); a `Security` carries
   its extractor and knowledge state function with the bound for them. The composition ArkLib
   admits (ledger A2), the knowledge state function of the appended extractor and the bound, is
   ported from ArkLib #615 and proved here, in `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean`
   (`Verifier.KnowledgeStateFunction.appendGuarded`,
   `Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`); the file is deleted,
   and its two names replaced by ArkLib's, when the pin moves past #615.
6. **The composition** `leanVmPiop` over a bundle `Phases I`, its error `piopError`, its
   extractor `piopExtractor` (the commit phase's followed by the phases', appended through the
   verdicts), and the two master theorems, each conditional on the phases only:
   `piop_perfectCompleteness` on `Phases.Complete`, `piop_rbrKnowledgeSoundness` on
   `Phases.Security`, stated for `piopExtractor` (`piop_rbrKnowledgeSoundness_exists` forgets
   it). The commit phase is the spine's: defined and proved in both halves (`commitComplete`,
   `commitSecurity`; its extractor `commitExtractor` reads the stack off the message).
7. **The toy instance** (one table of width 3 and height 2 on a stack of height 8: one
   constraint, one push, one boundary pull, one count column, one public line) with an honest
   `q` satisfying `M3Holds` and, for each of the four checkable clauses, a stack failing it alone.

```lean
-- LeanerVM/Protocol/Spine/Instance.lean (module): the instance and the relation
inductive Side | push | pull
structure Shape where (ntab : ℕ) (τ width : Fin ntab → ℕ)   -- the tables: count, log-heights, widths
abbrev Shape.ColumnId (S : Shape) := Σ j : Fin S.ntab, Fin (S.width j)
structure Layout (μ) (ι) (κ : ι → ℕ) where            -- the stack layout, as data with its one law
  read : Column μ → (c : ι) → Column (κ c)
  extend : (c : ι) → Vector E (κ c) → Vector E μ       -- z ↦ (z, sel_c) for an aligned block
  read_eval : ∀ q c z, eval₂Mle (read q c) z = eval₂Mle q (extend c z)
inductive Coord (S : Shape) κ | const (c : K) | known (col : Column κ) | committed (c : S.ColumnId) (h : S.τ c.1 = κ)
structure BoundaryBlock (S : Shape) where (κ : ℕ) (side : Side) (coords : Vector (Coord S κ) 16)
structure PublicLine (S : Shape) where (col : S.ColumnId) (cell0 cell1 : K) (pos : 0 < S.τ col.1)
structure M3Instance extends Shape where
  Stmt : Type                                          -- the public statement (leanISA: PublicInput)
  constraints : (j) → List (CMvPolynomial (width j) K)  -- CompPoly's computable polynomials
  flushes : (j) → List (Side × Vector (CMvPolynomial (width j) K) 16)   -- separator first
  d : ℕ                                                -- the degree bound (leanVM: 2)
  constraints_degree : ∀ j, ∀ C ∈ constraints j, C.totalDegree ≤ d
  flushes_degree : ∀ j, ∀ f ∈ flushes j, ∀ k, (f.2.get k).totalDegree ≤ d
  counts : (j) → List (Fin (width j))
  boundary : List (BoundaryBlock toShape)
  μ : ℕ ; layout : Layout μ toShape.ColumnId (fun c ↦ τ c.1)
  publicLines : Stmt → List (PublicLine toShape)       -- columns whose cells 0 and 1 are fixed
  aux : Column μ → Prop ; decAux : DecidablePred aux   -- what the Flock phase establishes
def M3Instance.column I q c ; def M3Instance.row I q j x ; def M3Instance.tuples I q (s : Side)
def M3Instance.ConstraintsVanish I q ; Balanced I q (List.Perm) ; CountsNonzero I q ; PublicLinesHold I input q
def M3Holds (I) (input : I.Stmt) (q : Column I.μ) : Prop :=
  I.ConstraintsVanish q ∧ I.Balanced q ∧ I.CountsNonzero q ∧ I.PublicLinesHold input q ∧ I.aux q
deriving instance Decidable for M3Holds                -- and for each clause
abbrev NoOracle : Fin 0 → Type ; abbrev TheOracle I : Fin 1 → Type := fun _ ↦ Column I.μ
def M3Rel (I) : Set ((I.Stmt × ∀ i, NoOracle i) × Column I.μ) := {p | M3Holds I p.1.1 p.2}

-- LeanerVM/Protocol/Spine/Seams.lean: the claims and the seam relations
structure ColumnClaim I where (col : I.ColumnId) (point : Vector E (I.κ col)) (value : E)
structure VirtualTerm I where (weight : E) (j) (poly : CMvPolynomial (I.width j) K) (point : Vector E (I.τ j))
structure LinearClaim I where (terms : List (VirtualTerm I)) (value : E)   -- Σ weight · (poly on rows)~(point) = value
structure Weight μ where (onCube : CMlPolynomialEval E μ) (mle : Vector E μ → E) (mle_eq : …)
structure WeightedClaim I where (weight : Weight I.μ) (value : E)         -- ⟨W, q⟩ = value
structure BusOut I where (linear : List (LinearClaim I)) (columns : List (ColumnClaim I))
structure TableOut I where (columns : List (ColumnClaim I))
structure PubOut I where (columns : List (ColumnClaim I))
structure FlockOut I where (columns : List (ColumnClaim I)) (weighted : List (WeightedClaim I))
def Seam.of I (P : S → Column I.μ → Prop) : Set ((S × ∀ i, TheOracle I i) × Unit) := {p | P p.1.1 (theStack p.1.2)}
def Seam.commit I := Seam.of I (M3Holds I)                                -- M3Holds of the oracle itself
def Seam.bus I := Seam.of I fun (s : I.Stmt × BusOut I) q ↦               -- claims, degree ≤ d, lines, aux
  (∀ c ∈ s.2.linear, c.Holds q) ∧ (∀ c ∈ s.2.linear, ∀ t ∈ c.terms, t.poly.totalDegree ≤ I.d) ∧
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q
def Seam.table I (claims ∧ lines ∧ aux) ; Seam.pub I (claims ∧ aux) ; Seam.flock I (claims) ; Seam.done I (True)

-- LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean: the knowledge-soundness append, ported from ArkLib #615
def Verifier.KnowledgeStateFunction.appendGuarded (G : V₁.GuardedForm) (K₁) (K₂) :
    (V₁.append V₂).KnowledgeStateFunction … (E₁.append E₂ G.out)   -- ArkLib's extractor append
theorem Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first (G) (K₁) (K₂)
    (h₁ : V₁.rbrKSWorstCaseWith … W₁ E₁ K₁ ε₁) (h₂ : V₂.rbrKSWorstCaseWith … W₂ E₂ K₂ ε₂) :
    (V₁.append V₂).rbrKSWorstCaseWith … (E₁.append E₂ G.out) (appendGuarded G K₁ K₂)
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm)           -- each challenge keeps its error

-- LeanerVM/Protocol/ToArkLib/Component.lean: the hole interfaces and their composition (ArkLib candidate)
structure Component.Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut where
  n : ℕ ; pSpec : ProtocolSpec n ; [msgOracle] ; [chalSample]
  red : OracleReduction []ₒ StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec
  err : pSpec.ChallengeIdx → ℝ≥0
structure Component.Complete (D) (relIn relOut) where
  outputPure : D.red.prover.OutputIsPure ; guarded : D.red.toReduction.verifier.GuardedForm
  complete : ∀ {σ} init impl, D.red.perfectCompleteness init impl relIn relOut
structure Component.Security (D) (relIn relOut) extends Complete D relIn relOut where
  witMid : Fin (D.n + 1) → Type
  extractor : Extractor.RoundByRound []ₒ (StmtIn × ∀ i, OStmtIn i) WitIn WitOut D.pSpec witMid
  kSF : ∀ {σ} init impl, D.red.verifier.toVerifier.KnowledgeStateFunction init impl relIn relOut extractor
  rbr : ∀ {σ} init impl, D.red.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
    witMid extractor (kSF init impl) D.err
def Component.Def.append ; def Component.Complete.append (proved, ArkLib's guarded append)
def Component.Security.append (S₁) (S₂)   -- proved: ArkLib's extractor append, the port's bound
-- LeanerVM/Protocol/ToArkLib/PassThrough.lean, SendOracle.lean (ArkLib candidates)
def Component.passThrough OStmt (f : StmtIn → StmtOut) ; def Component.passThroughComplete   -- no round; proved
def Component.passThroughExtractor ; passThroughStateFunction ; theorem passThrough_rbr     -- the witness is kept
def Component.passThroughSecurity OStmt f (h : f reflects relOut into relIn) (hc)            -- proved, error 0
def Component.sendOracle S M : Component.Def S NoOracle M S (OneOracle M) Unit                -- one message, the oracle
def Component.sendOracleComplete rel ; def Component.sendOracleSecurity rel                    -- both proved, error 0
-- LeanerVM/Protocol/Spine/Phase.lean
abbrev Phase.Def I StmtIn StmtOut := Component.Def StmtIn (TheOracle I) Unit StmtOut (TheOracle I) Unit
abbrev Phase.Complete ; abbrev Phase.Security ; abbrev Phase.passThrough
def Phase.passThroughComplete ; def Phase.passThroughSecurity

-- LeanerVM/Protocol/Spine/Compose.lean: the commit phase, the bundle, the master theorems
abbrev commitSpec I ; abbrev commitDef I := Component.sendOracle I.Stmt (Column I.μ) ; abbrev commitExtractor I
def commitComplete I : Component.Complete (commitDef I) (M3Rel I) (Seam.commit I)      -- proved
def commitSecurity I : Component.Security (commitDef I) (M3Rel I) (Seam.commit I)      -- proved, error 0
structure Phases I where
  bus     : Phase.Def I I.Stmt (I.Stmt × BusOut I)
  table   : Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)
  pub     : Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I)
  flock   : Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I)
  opening : Phase.Def I (I.Stmt × FlockOut I) Unit
structure Phases.Complete (P) where (bus : Phase.Complete I P.bus (Seam.commit I) (Seam.bus I)) … (opening : … (Seam.flock I) (Seam.done I))
structure Phases.Security (P) where (bus : Phase.Security I P.bus (Seam.commit I) (Seam.bus I)) … (opening : …)
def Phases.Complete.toDef (C) ; def Phases.Security.toDef (S)   -- commit, then five appends
def Phases.toDef (P) := (((((commitDef I).append P.bus).append P.table).append P.pub).append P.flock).append P.opening
def leanVmPiop (P) := P.toDef.red ; leanVmVerifier ; leanVmProver ; piopError (P) := P.toDef.err
def piopExtractor (P) (S : P.Security) := S.toDef.extractor   -- commitExtractor, then the phases'
theorem piop_perfectCompleteness (P) (C : P.Complete) init impl :
    (leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I)
theorem piop_rbrKnowledgeSoundness (P) (S : P.Security) init impl :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel I) (Seam.done I)
      S.toDef.witMid (piopExtractor P S) (S.toDef.kSF init impl) (piopError P)
theorem piop_rbrKnowledgeSoundness_exists …   -- the same, rbrKnowledgeSoundnessWorstCase (extractor forgotten)

-- LeanerVM/Protocol/ToArkLib/Refinement.lean: the adaptor's generic half (ArkLib candidate)
structure Refinement (R : Set (Stmt × W₁)) (S : Set (Stmt × W₂)) where (map : Stmt → W₁ → W₂) (map_valid : …)
theorem Refinement.map_option_valid       -- an extracted witness slot valid for R is valid for S after the map
def Extractor.Straightline.map (f) (E)    -- post-compose ArkLib's straight-line extractor
```

`M3Holds` names the leanVM checks in the order the phases consume them; its five clauses settle
decision 8 (the caps are not a clause: the compiled verifier rejects inadmissible sizes before the
oracle protocol starts, so the protocol is a family over admissible instances, and the adaptor's
soundness theorem takes admissibility as a hypothesis), and the witness type, the stack, settles
decision 6. The seams carry *claims*, not challenges: what a phase emits is fixed by its
knowledge soundness, not by the seam's type (a bus phase emitting no claim typechecks and cannot
be proved knowledge sound), which is what lets the table sumcheck consume any list of linear
claims without knowing the bus.

A linear claim is a list of terms, each an `E` weight times the extension of a `K`-polynomial of
one table's row: a zerocheck claim is one term, of weight 1, with the constraint; a bus form
`B^s_j = Σ_b eq(sel_b, ζ_hi)·(β − Σ_i eq(α, i)·c_{b,i})` is the terms of weight
`eq(sel_b, ζ_hi)·eq(α, i)` with the coordinate polynomials `c_{b,i}`, plus one constant term of
weight `eq(sel_b, ζ_hi)·β`. No polynomial with coefficients in `E` is ever built: CompPoly has no
`LawfulBEq E` at the pin, hence no ring operations on `CMvPolynomial n E`. `Seam.bus` bounds the
total degree of every term by `I.d`. The table sumcheck's round polynomials have degree `d + 1`
(the eq factor times a term of degree `d`), so its completeness is owed only on claims within the
bound; a seam carrying every *true* linear claim would owe it on terms of any degree, which no
sumcheck of that schedule can prove (acceptance test 28).

The commit phase is ArkLib's `SendSingleWitness` shape with the message the stack itself; its
output relation is `M3Holds` on the oracle, the "strengthened intermediate relation" leanth used
to pin the oracle to the witness of record, and both its halves are proved in the spine (zero
knowledge error; its extractor reads the message). Knowledge soundness is stated for the named
extractor `piopExtractor`, the commit phase's followed by the phases'. The composed extractor is
ArkLib's own `Extractor.RoundByRound.append`; its knowledge state function and the bound are the
ported ones of item 5. The transport of knowledge along the adaptor is pointwise
(`Refinement.map_option_valid`), because the adaptor's target witness lives in `Type 1`, which
ArkLib's games cannot quantify over; the probabilistic transport of `knowledgeSoundnessWith`
along a `Type 0` refinement is not proved (it needs a prover conversion and `Nonempty WitIn`)
and has no consumer yet.

### The holes

Every hole consumes spine names only. Its specification is a section of the hole comment on the
dashboard #12 (the `[Hole]` issues were folded there on 2026-09-25); `L1` groups the leaves of
Layer 1 already in flight; the generic holes carry the ledger letters of the ArkLib work they will
become.

| Hole | Unit | Produces | Consumes | Existing work | Issue |
| --- | --- | --- | --- | --- | --- |
| S | the spine | everything under [What the spine fixes](#what-the-spine-fixes); built under `LeanerVM/Protocol/Spine/` | Layer 0 only (#18's `Blocks` inhabit `Layout` later) | leanth's explore branch | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| G1 | virtual sumcheck, `Sumcheck.Def` and completeness (Layer 4) | `Virtual`, `sumcheck`, `sumcheck_perfectCompleteness` | nothing | #42, ArkLib #1128, ArkLib `main`'s `Sumcheck/Interaction/` | [#37](https://github.com/Verified-zkEVM/leanerVM/issues/37) |
| G2 | sumcheck rbr knowledge, `Sumcheck.Security` (Layer 4, A1) | `sumcheck_rbrKnowledgeSoundness`, `d/\|F\|` per round | G1 | ArkLib #1129, `Interaction/Soundness.lean` | [#37](https://github.com/Verified-zkEVM/leanerVM/issues/37) |
| G3 | batching by powers, `Batch.Def` and `Security` (Layer 4) | `batchClaims`, `(k − 1)/\|F\|` | nothing | #43, ArkLib #615's `gammaPowers` | [#31](https://github.com/Verified-zkEVM/leanerVM/issues/31) |
| G4 | fingerprint, Lemma 5.1, the collision bound (Layer 5) | `fingerprint`, `sideProduct`, `sideProduct_poly_eq_iff`, `sideProduct_collision` | nothing | #39, ArkLib #901 | [#33](https://github.com/Verified-zkEVM/leanerVM/issues/33) |
| G5, G6 | GKR: `Gkr.Def` and completeness; `Gkr.Security` (Layer 5) | `gkr`, `gkrError`, its two theorems | G1 (G6 also G2) | ArkLib #818 as a pattern | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| L1 | Layer 1's leaves | `stack_eval_ambient` (#40), `unstack` and `BlockClaim` (#38), `idxColumn_eval` and `bytecodeColumn_slot` (#41), coefficient transport (#26) | #18 | in review | #27, #32, #35, #36 |
| I1 | Clean components as polynomials (Layer 2) | `Expression.toMvPolynomial`, `degreeBound`, `Component.toM3`, `Ensemble.toM3`, the two bridge theorems | Clean | Clean #466 | [#28](https://github.com/Verified-zkEVM/leanerVM/issues/28) |
| I2 | the adaptor (Layer 3) | `leanIsaInstance`, `stackOf`, `witnessOf`, `satisfiedBy_witnessOf`, `m3Holds_stackOf`, `witnessOf_stackOf` | S, I1, leanISA Layers 5–8, #38, #40; #3 (the Flock witness generator, "the R1CS holds ⇒ the limb slots compress") | | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| P1, P2 | the bus phase (Layer 6) | `busPhase`, `leaf_decomposition`, `busError`; its `Security` | S, G5 (P2 also G6, G4), #40, #41 | | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| P3, P4 | the table sumcheck phase (Layer 7) | `tableSummand`, `tableSummand_target`, `tableSumcheck`; its `Security` | S, G1 (P4 also G2) | #42 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| P5 | the public-input phase (Layer 8) | `publicInputPhase`, both halves | S | | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| P6 | the Flock phase at the flock seam (Layer 9) | `FlockOut`, `limbColumns`, `flockError_le`; the inhabitant is #3's | S | #3, ArkLib #383, #893 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| P7, P8 | the claim pool and the opening phase (Layer 10) | `Weight`, `WeightedClaim`, `openingPhase`; its `Security` | S, G3, G1, #38, #43 | | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| C1 | the knowledge-soundness append (ledger A2) | `Verifier.KnowledgeStateFunction.appendGuarded`, `Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first` in `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean`, the port of ArkLib #615's `Append/Knowledge.lean`: done on the spine's branch, as the port; deleted at the pin bump | ArkLib only | ArkLib #615, #676 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| K1 | WHIR over binary Reed–Solomon codes (Layer 11) | `encode`, `whirOpen`, `whirOpen_rbrSoundness`, `McaJohnson` | `WeightedClaim`, Layers 0, 1 | #3 F6, ArkLib #383, #992 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| K2 | Merkle, BLAKE2s bytes, the WHIR parameters (Layer 11) | `merkleRoot`, `merkleVerify`, `blake2sBytes`, `ladder` | leanISA Layer 1 | ArkLib #4 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| K3 | transcript, `Proof`, `verify`, `verify_iff_compiled`, the FS and BCS interfaces (Layer 12) | as Layer 12 | S (schedules, phase `Def`s), K1, K2 | ArkLib #848, #469, #627 | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |
| K4 | T4 (Layer 13) | `baseVerifier_extractsExecution`, `baseProver_complete` | K3, I2, leanISA Layer 10 | | [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) |

## The build: the spine, then fourteen layers

Every layer names what to define and what to prove, intrinsically. Each layer's tests are part
of the layer. The spine (hole S) is built after Layer 0 and Layer 1's generic half; the layers
keep their numbers and are read as the holes of the table above. Layers 3 and 6 to 10 are written
over `I : M3Instance`; where a signature below says `(prog) (s)`, read `leanIsaInstance prog s`.
A layer lands only fully proved; a hole's `Def` and `Security` are separate landings.

### Layer 0: the ArkLib dependency and the field instances

`lakefile.toml`, `upstreams.json`, `docs/dependencies.md`; `LeanerVM/Protocol/Field.lean`.

Add ArkLib at `dca90385` as the `Arklib` requirement (its package name). ArkLib requires CompPoly
at the `v4.33.1` tag; the root pin `3468b38c` wins the resolution, and ArkLib's
`ToCompPoly` modules build against it. Supply what ArkLib needs of the fields:

```lean
instance : SampleableType K          -- a uniform `Fin (2^64)` read as a bit pattern
instance : SampleableType E          -- three independent limbs through `Ext.ofVector`; never enumerates
theorem card_E : Fintype.card E = 2 ^ 192   -- CompPoly `card_ext3`, the one cardinality fact
/-- The stacked columns as an oracle: a query is a point of `E^n`, the answer `q̃` there. -/
instance evalOracle (n : ℕ) : OracleInterface (Column n) where
  Query := Vector E n
  ...  -- answer := eval₂Mle q (algebraMap K E)
theorem evalOracle_answer (q : Column n) (r : Vector E n) :
    OracleInterface.answer q r = CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) r
```

The sampler is the point at which a wrong `Fintype` would enumerate `2^64` or `2^192` elements
(finding P3); it is `SampleableType.ofEquiv` on the carrier views, as ArkLib's own
`KoalaBear.Ext6.sampleableType`, and a test probes that it has compiler IR. Points are CompPoly's
`Vector E n`; ArkLib's `Fin n → E` is `Vector.ofFn` away. Tests: `#guard`s that the oracle
answers `evalMle` on a two-variable table, on and off the cube, with a mutated column;
`example : Fintype.card E = 2 ^ 192 := card_E`.

### Layer 1: hypercube tables, stacking, the index and bytecode columns

`LeanerVM/Protocol/Multilinear.lean` (generic), `LeanerVM/Protocol/Stack.lean` (leanVM).

```lean
structure Column (n : ℕ) where values : CMlPolynomialEval K n     -- Layer 0; not an abbreviation
abbrev ETable (n : ℕ) := CMlPolynomialEval E n
def sumCube (t : ETable n) : E                                  -- Σ over the cube
def ETable.mul (s t : ETable n) : ETable n                     -- pointwise
def eqTable (r : Fin n → E) : ETable n                         -- values of eq(r, ·)
theorem eval_eq_sum_eqTable (t : ETable n) (r) : evalMle t r = sumCube (eqTable r).mul t
theorem sumCube_prod_vars : sumCube (∏ X_k) = 1                -- Σ_x x_0 ⋯ x_{n-1} = 1

structure Block where (κ : ℕ) (values : Column κ)
def stack (blocks : List Block) : (μ : ℕ) × Column μ           -- largest first, aligned, 0-pad
def selector (blocks) (b : Fin blocks.length) : Fin (μ - κ_b) → E   -- the bits of offset_b >> κ_b
theorem stack_eval (b) (z : Fin κ_b → E) :
    evalMle (stack blocks).2 (z ++ selector blocks b) = evalMle blocks[b].values z
theorem stack_eval_pad (ζ) : evalMle (stack …).2 ζ = Σ_b eq(sel_b, ζ_hi) · P̃_b(ζ_lo) + pad(ζ)

def idxColumn (κ : ℕ) : Column κ                               -- g^i at index i
theorem idxColumn_eval (ζ : Fin κ → E) :
    evalMle (idxColumn κ) ζ = ∏ k, (1 + ζ k * (1 + ofK (g ^ (2 ^ k.val))))     -- §6.5
def bytecodeColumn (prog : Program) : Column (prog.logSize + 4)   -- slot s of instruction z
theorem bytecodeColumn_slot (z s) : (bytecodeColumn prog)[z + 2^k_bc * s] = (encodeSlots (prog.code z))[s]
```

`stack_eval` is the one selector fact every later decomposition uses; `stack_eval_pad` is
specification (5.4) with `pad(ζ) = 1 + Σ_b eq(sel_b, ζ_hi)` when the padding value is `1` (a
second version pads with `0` for the witness stack). Generic parts are ArkLib's `Data/MvPolynomial`
candidates. Tests: `stack_eval` decided in the kernel on three blocks of sizes 4, 2, 1;
`idxColumn_eval` at `κ = 2`; `bytecodeColumn_slot` on a two-instruction program.

### Layer 2: Clean components as polynomials

`LeanerVM/Arithmetization/M3.lean` (plain; generic over any `Ensemble`).

```lean
def Expression.toMvPolynomial : Expression F → MvPolynomial ℕ F     -- var i ↦ X i
theorem eval_toMvPolynomial (env : Environment F) (e) :
    MvPolynomial.eval env.get e.toMvPolynomial = e.eval env
def Expression.degreeBound : Expression F → ℕ                      -- syntactic; add max, mul sum
theorem totalDegree_le_degreeBound (e) : e.toMvPolynomial.totalDegree ≤ e.degreeBound

structure M3Table (F) where
  width : ℕ
  constraints : List (MvPolynomial (Fin width) F)
  flushes : List (Direction × Vector (MvPolynomial (Fin width) F) 16)   -- separator first
  count : List (Fin width)                                             -- the count columns
def Component.toM3 (c : Component F) (sep : RawChannel F → F) (dir : RawChannel F → Direction) :
    M3Table F
theorem toM3_constraints_iff (t : Table F) (row ∈ t.table) :
    (∀ C ∈ (t.component.toM3 …).constraints, eval row C = 0) ↔ t.component.operations.ConstraintsHold (t.environment row)
theorem toM3_flushes_eq (t : Table F) : (multiset of evaluated flush tuples) = (multiset of `t.interactions` mapped to 16-tuples)
```

The direction and separator are given per channel, so the mapping from Clean's typed channels to
the M3 bus is explicit data. `toM3_constraints_iff` is the bridge that turns the zerocheck into
`w.Constraints`; `toM3_flushes_eq` turns bus balance into `BalancedPair`. Out-of-range variables
are excluded by `width`; a component whose expressions mention a variable at or beyond
`circuit.size` has no `M3Table` (a theorem `vars_lt_width` per table). Upstream candidate: Clean
(`Expression.toMvPolynomial`, `degreeBound`). Tests: a two-column example component whose
constraint `x * y` has `degreeBound = 2`, and whose `toM3_constraints_iff` is checked on a
satisfying and a failing row.

### Layer 3: the M3 instance of leanISA

`LeanerVM/Protocol/M3.lean` (plain). Needs the spine (`M3Instance`, `M3Holds`), Layer 2 and
leanISA Layers 5–8. This layer is the adaptor: hole I2.

```lean
structure Sizes where
  logMem : ℕ
  τ : Fin 6 → ℕ
  logInvRate : ℕ                                   -- WHIR rate exponent, announced with the sizes
def Sizes.ofWitness (w : EnsembleWitness leanIsaEnsemble) : Option Sizes   -- `none` unless every height is 2^τ
def Sizes.Admissible (prog : Program) (s : Sizes) : Prop      -- the caps; decidable
theorem admissible_iff_caps : s.Admissible prog ↔ (Caps w ∧ Sizes.ofWitness w = some s)

def leanIsaInstance (prog : Program) (s : Sizes) : M3Instance   -- `Ensemble.toM3` of the eight tables with
                                                               -- leanISA's separators and directions; the
                                                               -- layout of `witness.rs:85-101`, `leaf.rs:53-156`
theorem leanIsaInstance_degree (j) (C ∈ (leanIsaInstance prog s).constraints j) : C.totalDegree ≤ 2
theorem leanIsaInstance_flush_degree …  ≤ 2
theorem leanIsaInstance_fits : (leanIsaInstance prog s).layout.total ≤ 2 ^ (leanIsaInstance prog s).μ

-- The adaptor. `M3Holds` is the spine's; these are Layer 3's.
def stackOf (gen : FlockWitnessGen) (w : EnsembleWitness (leanIsaEnsemble prog))
    (hs : Sizes.ofWitness w = some s) : Column (leanIsaInstance prog s).μ   -- gen: #3's
def witnessOf (prog) (s) (q : Column (leanIsaInstance prog s).μ) :
    EnsembleWitness (leanIsaEnsemble prog)                            -- total and computable
theorem satisfiedBy_witnessOf (hs : s.Admissible prog)                 -- the caps: a hypothesis
    (h : M3Holds (leanIsaInstance prog s) input q) : SatisfiedBy prog input (witnessOf prog s q)
theorem m3Holds_stackOf (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s) :
    M3Holds (leanIsaInstance prog s) input (stackOf gen w hs)
theorem witnessOf_stackOf (hs) : witnessOf prog s (stackOf gen w hs) = w  -- on the committed fields
```

`M3Holds` (the spine's, over `I`) is the target of extraction and the source of completeness; the
two theorems around it are the whole bridge between polynomials and Clean's witness, and the only
place the proof system meets leanISA (convention *The wall*). `satisfiedBy_witnessOf` takes the
admissibility of the sizes as a hypothesis: `SatisfiedBy`'s `Caps` conjunct does not follow from
`M3Holds`, whose clauses leave the caps out (convention *Statements and parameters*), and
`imageOf` truncates above `maxLogMem`, so for sizes beyond the caps the conclusion is false. The
hypothesis is available where the theorem is consumed (Layer 13): `verify` checks the announced
sizes before the oracle protocol starts (`read_public`, `cpu/mod.rs:130-178`), and
`verify_iff_compiled` quantifies `∃ s, s.Admissible prog ∧ …`. `m3Holds_stackOf` needs no such
hypothesis, since `SatisfiedBy` carries `Caps`.

`leanIsaInstance` supplies `d := 2`, its two degree fields from `leanIsaInstance_degree` and
`leanIsaInstance_flush_degree`, and three public lines, on `mem_0, mem_1, mem_2` (§8.2): for
`ℓ = 0, 1` the line on `mem_ℓ` has as cells limb `ℓ` of the two public words, and the line on
`mem_2` has cells `0, 0`. The stack columns that belong to no opcode table (`mem_0, mem_1, mem_2`,
`cntfin_mem`, `cntfin_bc`, `q_flock`; `witness.rs:85-101`) are tables of the instance with no
constraints and no flushes, so that `Shape.ColumnId` and `Coord.committed` reach them; the
boundary blocks and the public lines name them that way.

The layout has two readers. The table columns and the non-table columns are aligned blocks, read
by #18's `Blocks` (`extend c z = (z, sel_c)`). The eighteen BLAKE2S value limbs are virtual
columns (`layout.rs:20-28`, `tables.rs:829`), read as strided slots of `q_flock`: a claim on a
limb column at `z` is the claim on `q_flock` at the point whose low eight coordinates are frozen
to the slot's bits and whose high coordinates are `z` (`cpu/mod.rs:790-814`,
`SlotClaim::Strided`), lifted to the stack by `q_flock`'s selector. `Layout` admits both readers;
`Blocks` expresses only the first, so `leanIsaInstance.layout` combines the two, the slot map
being #3's `FlockInterface.limbColumns` (Layer 9).

The auxiliary predicate is the strong reading: `aux q` says that Flock's R1CS holds of the bits
packed into the `q_flock` region (Annex C.1, §4.2). It is not the compression of the eighteen
limb slots: the Flock phase's completeness is owed on every stack with `aux q`, and Flock's
argument checks the R1CS wires committed in `q`, which cannot change after the commitment, so a
stack whose limb slots compress while its other wires are wrong has no honest Flock proof. The
compression is #3's soundness consequence of the predicate, and two adaptor obligations follow
from the choice, both #3's to supply: `satisfiedBy_witnessOf` discharges `blake2s_valid` through
#3's lemma "the R1CS holds ⇒ the limb slots compress"; `stackOf` computes the R1CS wires of each
BLAKE2S row from its limbs with #3's witness generator, which it takes as an explicit argument
until #3 supplies it. `FlockWitnessGen` names that argument: the generator, keeping the limbs in
their slots, with #3's lemma that the generated wires satisfy the R1CS when the limbs compress,
which `m3Holds_stackOf` consumes.

`witnessOf` rebuilds the tables from the columns (the BLAKE2S limbs from their slots), the
interactions from the components, the image from the memory columns, and the program from `prog`.
The stack layout transcribes `witness.rs:85-101` and `leaf.rs:53-156`; every offset is a
`decide`. Tests: a witness with one row per table stacked and read back (`witnessOf_stackOf` by
`decide +kernel` on the columns); `Sizes.Admissible` rejects `logMem = 15` and `τ_BLAKE2S = 2`.

### Layer 4: sumcheck for eq-weighted virtual polynomials

`LeanerVM/Protocol/ToArkLib/Sumcheck.lean` (module; ArkLib upstream, ledger A1).

leanVM runs sumcheck on polynomials the verifier cannot evaluate at the end: the summand is a
formula in the columns' extensions, so the last step is "the prover sends the column values at
`r`, the verifier evaluates the formula, and the values become claims". Define, over a field `F`
with `[Fintype F] [SampleableType F]`:

```lean
/-- A virtual polynomial: `n` variables, a list of `m` oracle tables, and a formula of degree `d`. -/
structure Virtual (F) (n m d : ℕ) where
  formula : (Fin m → F) → F            -- a polynomial of total degree ≤ d in its m inputs
  formula_poly : ∃ p : MvPolynomial (Fin m) F, p.totalDegree ≤ d ∧ ∀ v, formula v = eval v p
def Virtual.eval (V) (tables : Fin m → ETable n) (x : Fin n → F) : F := V.formula (fun i ↦ evalMle (tables i) x)

def sumcheck (V : Virtual F n m d) : OracleReduction []ₒ
    (StmtIn := F)                       -- the claimed sum
    (OStmtIn := fun _ : Fin m ↦ ETable n) Unit
    (StmtOut := (Fin n → F) × (Fin m → F))   -- the point and the claimed table values
    (OStmtOut := fun _ : Fin m ↦ ETable n) Unit
    (pSpec := round schedule: n × (P_to_V : Fin (d + 1) → F ; V_to_P : F), then P_to_V : Fin m → F)
def sumcheck.relIn : Set ((F × (Fin m → ETable n)) × Unit) := {⟨⟨T, t⟩, _⟩ | Σ_x V.eval t x = T}
def sumcheck.relOut := {⟨⟨(r, v), t⟩, _⟩ | ∀ i, evalMle (t i) r = v i ∧ V.formula v = (final running claim)}
theorem sumcheck_perfectCompleteness : (sumcheck V).perfectCompleteness init impl relIn relOut
theorem sumcheck_rbrKnowledgeSoundness :
    (sumcheck V).verifier.rbrKnowledgeSoundnessWorstCase init impl relIn relOut (fun _ ↦ d / |F|)
```

with the *eq-weighted, back-loaded* variant built on it: tables of different heights `τ_j ≤ n`
lifted to `n` variables by `∏_{k ≥ τ_j} X_k` with `sumCube_prod_vars`, the verifier's running
weight `∏ (challenges of the rounds a table sat out)`, and `eq(ζ_{<τ_j}, ·)` as an explicit
factor whose evaluation at `r` the verifier computes itself (so `d` counts the cofactor plus one).
Add the batching component:

```lean
/-- Random linear combination of `k` claims by the powers of one challenge. -/
def batchClaims (k : ℕ) : OracleReduction … (StmtIn := Fin k → claim) (StmtOut := F × claim) …
theorem batchClaims_rbrKnowledgeSoundness : … (fun _ ↦ (k - 1) / |F|)
```

Its invariant is "some claim is false"; escape needs the batching polynomial, of degree `< k`, to
vanish at the challenge. Tests: `sumcheck` on a two-variable degree-2 virtual polynomial, honest
run accepted by `#guard`, a wrong round polynomial rejected.

### Layer 5: fingerprints, the grand product, and GKR

`LeanerVM/Protocol/ToArkLib/GrandProduct.lean` (module; ArkLib upstream, ledger A6).

```lean
def fingerprint (α : Fin 4 → E) (t : Vector K 16) : E := Σ i, eqTilde α (bits i) * ofK t[i]
def sideProduct (α β) (P : Multiset (Vector K 16)) : E := (P.map fun t ↦ β - fingerprint α t).prod
/-- Specification Lemma 5.2: the product polynomial determines the multiset. -/
theorem sideProduct_poly_eq_iff (P Q : Multiset (Vector K 16)) :
    (Π_P : MvPolynomial (Fin 5) K) = Π_Q ↔ P = Q
/-- Specification Theorem 5.1: unequal multisets of size ≤ 2^μ collide at (α, β) with probability ≤ 4·2^μ/|E|. -/
theorem sideProduct_collision (hne : P ≠ Q) (hμ) :
    Pr[α β ← uniform; sideProduct α β P = sideProduct α β Q] ≤ 4 * 2 ^ μ / |E|

structure ProductTree (μ : ℕ) where leaves : ETable μ            -- layers are derived
def ProductTree.root : E
def gkr (nside μ : ℕ) : OracleReduction []ₒ
    (StmtIn := Fin nside → E)                                    -- the claimed roots
    (OStmtIn := fun _ : Fin nside ↦ ETable μ) Unit               -- the leaf tables
    (StmtOut := (Fin μ → E) × (Fin nside → E))                   -- ζ and the leaf claims Ṽ₀ˢ(ζ)
    (OStmtOut := fun _ : Fin nside ↦ ETable μ) Unit …
theorem gkr_perfectCompleteness : (gkr nside μ).perfectCompleteness …
theorem gkr_rbrKnowledgeSoundness :
    (gkr nside μ).verifier.rbrKnowledgeSoundnessWorstCase … (gkrError nside μ)
```

`gkr` is radix 4 with the odd first layer, a fresh `λ` per layer, and the two combination
challenges per layer, exactly as pinned; `gkrError` assigns `(nside − 1)/|E|` to each `λ`, `5/|E|`
to each sumcheck round and `2/|E|` to each combination pair. Lemma 5.2 is proved by unique
factorization in `K[A_0, …, A_3, X]`: the factors `X − π_A(t)` are monic linear, hence
irreducible, and two products of irreducibles agree only up to associates, which for monic
factors is equality; the specification leaves this proof `TODO` (finding S9). Tests: `gkr 1 2`
and `gkr 3 3` honest runs accepted; a leaf changed after the root is sent rejected;
`sideProduct_poly_eq_iff` refuted on `{t} ≠ {t, t}` by `decide` at `μ = 1`.

### Layer 6: the bus phase

`LeanerVM/Protocol/Bus.lean` (module, over `I : M3Instance`; holes P1 and P2). Needs the spine,
Layer 1 and Layer 5's `Gkr.Def`; `prog` and `s` below abbreviate `leanIsaInstance prog s`.

```lean
def pushLeaves pullLeaves countLeaves (L : LeafLayout prog s) (α β) (q : Column μ) : ETable μ_bus
def busPhase (prog) (s) : OracleReduction []ₒ
    (StmtIn := Unit) (OStmtIn := fun _ : Unit ↦ Column μ) Unit
    (StmtOut := BusOut) (OStmtOut := fun _ : Unit ↦ Column μ) Unit
    (pSpec := V_to_P : (Fin 4 → E) × E ; P_to_V : E × E ; gkr 3 μ_bus's rounds ; P_to_V : boundary evaluations)
structure BusOut where
  ζ : Fin μ_bus → E
  rem : Fin 3 → E                         -- what the tables owe per side (§5.4 "Settling it")
  pool : List Claim                      -- boundary-block column claims at ζ_lo
  α : Fin 4 → E ; β : E
def busPhase.relOut : Set (…) :=
  {…| (∀ j, Σ_x eq(ζ_{<τ_j}, x) · B_j^s(x) = rem s) ∧ every pooled claim holds for q ∧ (count root ≠ 0)}
/-- Specification (5.4): the leaf extension splits into public selectors, block extensions and padding. -/
theorem leaf_decomposition (L) (ζ) : evalMle (pushLeaves L α β q) ζ = Σ_b eq(sel_b, ζ_hi) · (β − Σ_i eq(α, i) · c̃_{b,i}(ζ_lo)) + pad ζ
theorem busPhase_perfectCompleteness …
theorem busPhase_rbrKnowledgeSoundness : … (busError s)
```

The verifier checks `R_c ≠ 0`; the push and pull roots are one message (finding F3), so their
equality is structural. `busError` is `4·2^μ_bus/|E|` on the `(α, β)` message plus
`gkrError 3 μ_bus`. The knowledge state function's invariant after `(α, β)` is "the pushed and
pulled multisets of `q` differ, or some count is zero, or a boundary claim is false"; the proof
that acceptance under a true invariant is a GKR escape is `sideProduct_collision` plus Layer 5.
Tests: `leaf_decomposition` in the kernel on a layout with two blocks; the whole phase run on
the Layer 3 one-row witness.

### Layer 7: the table sumcheck phase

`LeanerVM/Protocol/TableSumcheck.lean` (module, over `I`; holes P3 and P4). Needs the spine and
Layer 4's `Sumcheck.Def`; `prog` and `s` below abbreviate `leanIsaInstance prog s`.

```lean
def tableSummand (prog) (s) (ζ) (ξ : E) (α β) (rem) : Virtual E τ_max (Σ_j width_j) 3   -- the F of §5.5
def tableSumcheck (prog) (s) : OracleReduction []ₒ (StmtIn := BusOut) … (StmtOut := BusOut × ColumnClaims) …
    (pSpec := V_to_P : E ; the sumcheck's rounds ; P_to_V : Fin (Σ width) → E)
theorem tableSummand_target : Σ_x tableSummand … x = Σ_s ξ^(B + s) · rem s    -- the verifier's target
theorem tableSumcheck_relOut_implies_constraints (h : relOut …) :
    (∀ j C, C̃_j(ζ_{<τ_j}) = 0 → …) -- see below
theorem tableSumcheck_perfectCompleteness …
theorem tableSumcheck_rbrKnowledgeSoundness : … ((B + 2)/|E| on ξ, 3/|E| per round)
```

The output relation says every column claim is a true evaluation of `q`'s column and the
formula reproduces the final value; the knowledge state function's invariant after `ξ` is "some
constraint extension `C̃_{j,i}(ζ_{<τ_j})` is nonzero or some bus form disagrees with `rem`".
Turning "every `C̃_{j,i}(ζ_{<τ_j}) = 0`" into "every constraint vanishes on the cube" is the
zerocheck argument with `ζ` sampled after the commitment (§5.5 "point recycling"): it is charged
to the `(α, β)` and GKR challenges of Layer 6, where `ζ` is drawn, as an extra `τ_max/|E|` per
constraint by `MLE_eq_zero_iff` and Schwartz–Zippel. Tests: `tableSummand_target` on two tables
of heights 2 and 1; a row violating a JUMP identity makes the honest run's final check fail.

### Layer 8: the public-input phase

`LeanerVM/Protocol/PublicInput.lean` (module, over `I`; hole P5). Needs the spine.

```lean
def publicInputPhase (I : M3Instance) : Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I)
    -- pSpec := V_to_P : E; the prover sends nothing
def publicInputComplete I : Phase.Complete I (publicInputPhase I) (Seam.table I) (Seam.pub I)
def publicInputSecurity I : Phase.Security I (publicInputPhase I) (Seam.table I) (Seam.pub I)
    -- err: 1/|E| on the one challenge
```

The phase is over `I.publicLines input`. The verifier draws one `r ∈ E` and pools, for each line,
the column claim `col~(r, 0, …, 0) = (1 + r)·cell0 + r·cell1`; the prover sends nothing, since
the verifier computes every value. For leanISA the lines are the three of Layer 3, so the claims are
the three limb claims on `mem_0, mem_1, mem_2`, the third with value `0` (acceptance test 10). A
line whose two cells differ from the statement's makes its claim a nonzero polynomial of degree
one in `r`, so the error is `1/|E|`, one line's, whatever the number of lines.

The Rust verifier instead reads two scalars `c_0, c_1`, the claimed values of `mem_0, mem_1` at
the point, checks the one combined equation `c_0 + Y·c_1 = interp(pi_0, pi_1, r)` over `E` and
pools the claims at the sent values (`cpu/mod.rs:745-755`). The two checks accept the same
stacks: the cells are `K`-valued and `1, Y, Y²` is a `K`-basis of `E`, so either says, except with
probability `1/|E|`, that cells 0 and 1 of the memory block hold the public words. They are not
the same challenge by challenge (each has at most one bad `r`, not the same one), and the two
scalars are redundant with values the verifier computes: reading them and reconciling the
combined check with the per-line claims is Layer 12's encoding, like the dropped round
coefficient. Tests: on the toy, the honest run accepted; on the stack `badLine`, whose cell 1
differs from the statement's, the pooled claim false at a sampled `r`.

### Layer 9: the Flock and ring-switching boundary

`LeanerVM/Protocol/Flock.lean` (module, over `I`; hole P6). Needs the spine and #3.

```lean
/-- What the Flock roadmap supplies: the `Phase.Def` and `Phase.Security` at the flock seam. Every
field is a declaration of #3; this structure only names them. -/
structure FlockInterface (I : M3Instance) where
  reduction : OracleReduction []ₒ (StmtIn := ColumnClaims) (OStmtIn := fun _ : Unit ↦ Column μ) Unit
      (StmtOut := WeightedClaim) (OStmtOut := fun _ : Unit ↦ Column μ) Unit pSpecFlock
  limbColumns : Column μ → Fin 18 → Column (s.τ 5)      -- the limbs: strided slots of q_flock
  relIn : Set _   -- the eighteen column claims are true of `limbColumns`, and aux (Flock's R1CS)
  relOut : Set _  -- the weighted claim holds for q
  perfectCompleteness : reduction.perfectCompleteness …
  rbrKnowledgeSoundness : reduction.verifier.rbrKnowledgeSoundnessWorstCase … flockError
  flockError_le : Σ flockError ≤ (4 * k_batch + 163) / |E| + 2 ^ 32 / |E|
```

`relIn` carries the strong auxiliary predicate of Layer 3: Flock's R1CS holds of the bits packed
into `q_flock` (Annex C.1, §4.2). That the eighteen limb slots hold a valid compression is #3's
soundness consequence of it, consumed by the adaptor, never the predicate itself: the Flock
phase's completeness needs the R1CS wires already committed in `q`. `limbColumns` is the strided
reader of Layer 3, the slot map of the virtual limb columns (`cpu/mod.rs:790-814`).

The weighted claim is `⟨W, q⟩ = c` with `W` MLE-friendly (Definition 3.13): a `Weight μ` is a
function evaluating `W̃` at any point together with its cube values and their agreement. This
is an assumed interface in the sense of the authoring skill: it names a real external boundary,
its witness obligation is #3's F3–F5 and F8, and nothing here unfolds it. Until #3 supplies it,
Layer 10 takes a `FlockInterface` as a parameter and the theorems say so in their signatures.
Tests: none beyond typechecking; the instance's tests belong to #3.

### Layer 10: the claim pool, the opening sumcheck, and the oracle protocol

`LeanerVM/Protocol/Opening.lean` (module, over `I`; holes P7 and P8). Needs the spine, Layer 4's
`Sumcheck.Def` and `Batch.Def`. `leanVmPiop`, `piopError` and the two master theorems below are
the spine's, stated over `Phases I`, and their composition is proved there (hole C1, ledger A2,
done as the port of ArkLib #615); this layer fills the opening phase.

```lean
structure Weight (μ) where (onCube : ETable μ) (mle : (Fin μ → E) → E) (mle_eq : ∀ r, mle r = evalMle onCube r)
structure WeightedClaim (μ) where (W : Weight μ) (c : E)
def Claim.toWeighted (L : StackLayout prog s) : Claim → WeightedClaim μ     -- eq((ζ, sel), ·) or strided
def openingPhase (μ) (J : ℕ) : OracleReduction []ₒ (StmtIn := Fin J → WeightedClaim μ) … (StmtOut := Unit) …
    (pSpec := V_to_P : E ; sumcheck (W_λ · q) rounds ; the final evaluation query)
theorem openingPhase_rbrKnowledgeSoundness : … ((J − 1)/|E| on λ, 2/|E| per round)

def leanVmPiop (prog) (s) (input) (flock : FlockInterface prog s) : OracleReduction []ₒ
    (StmtIn := PublicInput) (OStmtIn := fun _ : Empty ↦ Unit) (M3Witness prog s)
    (StmtOut := Unit) (OStmtOut := fun _ : Empty ↦ Unit) Unit (pSpec := …) :=
  commitPhase ⟫ busPhase ⟫ tableSumcheck ⟫ publicInputPhase ⟫ flock.reduction ⟫ openingPhase
def leanVmVerifier … : OracleVerifier …  := (leanVmPiop …).verifier
def leanVmProver … : OracleProver … := (leanVmPiop …).prover
def piopError (s : Sizes) : (pSpec …).ChallengeIdx → ℝ≥0

theorem piop_perfectCompleteness (hs : s.Admissible prog) :
    (leanVmPiop prog s input flock).perfectCompleteness init impl
      (m3Relation prog s) Set.univ
theorem piop_rbrKnowledgeSoundness (hs : s.Admissible prog) :
    (leanVmVerifier prog s input flock).rbrKnowledgeSoundness init impl
      (m3Relation prog s) Set.univ (piopError s)
theorem piopError_le (hs : s.Admissible prog) : Σ i, piopError s i ≤ 2 ^ 40 / |E| + flockError
```

`commitPhase` sends `q` as the one oracle message; its output relation is `M3Holds`, and the
extractor of the whole protocol is `piopExtractor`: the commit phase's, which reads the stack off
that message, followed by the phases', straight-line; the adaptor applies `witnessOf` to its
output. `⟫` is `OracleReduction.append`; the composition theorems are ArkLib's for completeness
and, for round-by-round knowledge soundness of an append with a guarded first verifier (ledger
A2), the port of ArkLib pull request #615's
`ArkLib/OracleReduction/Composition/Sequential/Append/Knowledge.lean` (at `ca7a2577`), with its
attribution: `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean`, whose
`Verifier.KnowledgeStateFunction.appendGuarded` and
`Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first` rest on the kernel's three
axioms only. The port is done and closes hole C1; the file is deleted when the pin moves past
#615. `Set.univ` as the output relation says the last phase leaves nothing to check. The honest
prover is computable: each phase's prover is a function of `w`, the challenges so far and the
layer tables. Tests: the whole protocol on the Layer 3 witness with #3's toy Flock instance (or,
until it exists, with the phases up to Layer 8 composed), honest run accepted by `#guard`; the
knowledge extractor recovers the witness; `piopError_le` by `norm_num` at the caps.

### Layer 11: WHIR over binary Reed–Solomon codes, and Merkle trees

`LeanerVM/Protocol/ToArkLib/Whir.lean` (module; ArkLib upstream, ledger A7; shared with #3 F6),
`LeanerVM/Parameters/Whir.lean`, `LeanerVM/Parameters/Blake2sHash.lean`,
`LeanerVM/Protocol/Pcs.lean`.

```lean
-- Parameters (Category B, whir_config.rs)
def initialFold : ℕ := 6
def subsequentFold : ℕ := 4
def initialReduction : ℕ := 3
def subsequentReduction : ℕ := 1
def residualMaxLog : ℕ := 5
def queryGrindingBits : ℕ := 17
def ladder (μ logInvRate : ℕ) : List Level          -- fold, rate exponent, queries per level
theorem ladder_queries_eq : (ladder 15 1).map (·.queries) = [223, 55]   -- verifier.py:910

-- Codes (Annex B.3)
def novelBasis : Fin 64 → K := fun c ↦ g ^ c.val          -- x^c
def encode (κ R : ℕ) : Column κ → (Fin (2^(κ+R)) → K)     -- additive NTT on the K basis
theorem encode_column_weight (x) : ∃ W_x : Weight κ, ∀ f, encode κ R f x = ⟨W_x, f⟩   -- Lemma B.7

-- The opening as an IOPP (Annex B.4), generic over the code and the field
def whirOpen (params) : OracleReduction … (StmtIn := Fin J → WeightedClaim μ) (OStmtIn := codeword oracles) …
theorem whirOpen_perfectCompleteness …
theorem whirOpen_rbrSoundness (mca : McaJohnson) : … (whirError params)   -- Theorem B.2, per message
/-- [BCHKS25] Theorem 4.6, the only coding-theory input; ArkLib ledger A8. -/
structure McaJohnson where …

-- Merkle (Category B)
def blake2sBytes : List UInt8 → Vector UInt32 8       -- RFC 7693 §3.3 over `compress`, last-block flag only
def merkleRoot : List (Vector K leafWords) → Digest
def merkleVerify : Digest → ℕ → Vector K leafWords → Path → Bool
```

`whirOpen` is stated exactly as Protocol B.1: batch, `ℓ_i` sumcheck rounds, commit, one
out-of-domain sample from level 1 on (`ood_samples[0] = 0`), `t_i` queries, and the final
plaintext level. Its soundness is *round-by-round soundness for the list relation* `relopen`, not
knowledge soundness: the commitment is list binding (Definition B.1), and the theorem is stated
on the invariant "every codeword within `γ_i` of the current fold violates the current claim".
Layer 12 turns list binding into extraction of the one `q` that satisfies every pooled claim.
Tests: `encode` against CompPoly's additive NTT at `κ = 3`; `merkleVerify` on a four-leaf tree
with a wrong sibling rejected; the honest `whirOpen` at toy parameters (`μ = 4`, rate `1/2`)
accepted; the parameter tables against `verifier.py:910`.

### Layer 12: compilation, the transcript, the proof, and the executable verifier

`LeanerVM/Protocol/Transcript.lean`, `LeanerVM/Protocol/Proof.lean`,
`LeanerVM/Protocol/Verify.lean` (plain).

```lean
-- Fiat–Shamir chain (Category B, fiat_shamir/src/lib.rs)
structure FsState where cv : Vector UInt32 8
def FsState.seed (prog : Program) (input : PublicInput) : FsState     -- compress(iv prog, input words)
def FsState.observe (x : E) : FsState → FsState                      -- lane 3 = 1
def FsState.sample : FsState → E × FsState                            -- lane 3 = 2; three low words
def FsState.grind (bits : ℕ) (nonce : E) : FsState → Bool × FsState   -- lanes 3 = 3, 4

-- Proof object (Category B, transcript.rs:9-19)
structure Proof where
  stream : List E
  merkle : List MerklePaths
def RoundPoly.decode (d : ℕ) (claim : E) (eq? : Option E) : List E → Option (Fin (d+1) → E)  -- transcript.rs:289-309

-- The compiled oracle protocol: WHIR in place of the evaluation oracle
def leanVmIopp (prog) (s) (input) (flock) : OracleReduction … (OStmtIn := codeword oracles) …
-- The verifier (Category A: written from §8.5 before cpu/mod.rs:711-779 is opened)
def verify (prog : Program) (input : PublicInput) (proof : Proof) : Bool
theorem verify_iff_compiled (prog input proof) :
    verify prog input proof = true ↔
      ∃ s, s.Admissible prog ∧ (Verifier.fiatShamir (leanVmIopp prog s input flock).verifier …)
        accepts (decode s proof) under the BLAKE2s challenge oracle

/-- Assumed interfaces, each an ArkLib theorem to come (ledger A5). -/
structure FiatShamirSecurity where …   -- rbr knowledge soundness of the IOPP ⇒ knowledge soundness of its FS compilation in the ROM, error Q · max_i ε_i
structure BcsSecurity where …          -- Merkle-compiled oracles: extraction from collision resistance / ROM
theorem verify_knowledgeSound (fs : FiatShamirSecurity) (bcs : BcsSecurity) (mca : McaJohnson) (flock) :
    … knowledge soundness of `verify` with error niError s Q
```

`verify` is one function, phase by phase in the stream order of the conventions, total and
computable, and is the first module whose code-generation probe is a test. `verify_iff_compiled`
is the refinement theorem and is unconditional: it is about two definitions. The non-interactive
theorem is stated with the three interfaces as explicit arguments, so the reader sees exactly
what is assumed; `niError` is the round-by-round maximum times the query bound plus the
grinding-adjusted WHIR terms. The bytecode multilinear and the Flock matrices are evaluated
natively inside `verify` through one function `settleFixedClaims`, the seam for T5. Tests: a
proof dumped from the pinned Rust prover (`scripts/dump-proof.sh`, recorded with its program and
public input) accepted by `verify` under `#guard`; each of six mutations (a flipped stream
scalar in each phase, a wrong Merkle sibling) rejected; `RoundPoly.decode` on the Rust's
encoding.

### Layer 13: T4 and the fixtures

`LeanerVM/Protocol/Soundness.lean` (plain). Needs Layer 12 and leanISA Layer 10.

```lean
theorem baseVerifier_extractsExecution (fs bcs mca flock) (h : verify prog input proof = true) :
    except with probability niError, ∃ t, ValidExecution prog input t
theorem baseProver_complete (hfill : HasFillBlocks prog) (h : ValidExecution prog input t) :
    verify prog input (prove prog input (witness of t)) = true
```

The first composes `verify_knowledgeSound`, the adaptor's pointwise transport `Refinement.map_option_valid`
with `satisfiedBy_witnessOf`, and `constraintSoundness`;
the second composes `constraintCompleteness`, `m3Holds_stackOf`, `piop_perfectCompleteness` and
the determinism of the Fiat–Shamir chain (perfect completeness survives the transform without
any assumption). Both are the T4 statements of [architecture.md](../architecture.md), the
first conditional exactly as the ledger says. Tests: the differential fixture of Layer 12,
re-stated as an instance of `baseVerifier_extractsExecution`'s hypothesis.

## Acceptance tests and nearby false statements

Each names a reading that compiles and is wrong, and the witness that rejects it. Where the
witness is executable it is a test under `tests/`.

1. **Fingerprint degree.** `π_α` is multilinear in `α : E^4`, so a leaf has total degree 4 in
   `(α, β)` and Theorem 5.1's error is `4·2^μ/|E|`, not `2^μ/|E|`. `sideProduct_collision`
   carries the 4; a version with 1 is unprovable.
2. **Padding leaves are 1.** A `0` pad zeroes every product, and a `0` pad in the count tree
   makes `R_c = 0` reject honest proofs. `pushLeaves` pads with `1`; the witness stack pads
   with `0`. Witness: the honest run of Layer 6 on a one-row witness (whose trees are padded).
3. **`R_c ≠ 0` is load-bearing.** A read at an invalid address with count `0` pulls `(a, 0, v)`
   and pushes `(a, g·0, v) = (a, 0, v)`: balanced. Witness: the Layer 6 mutation with a zero
   count is accepted by a verifier that skips the check and rejected by `busPhase`.
4. **One root, not two.** The push and pull roots are one stream scalar (finding F3). A `Proof`
   with two roots and an equality check would have a different stream layout and reject every
   Rust proof. `verify_iff_compiled` pins the shape.
5. **Domain separators.** Without coordinate 0, a memory tuple `(a, c, v, 0…)` and a bytecode
   tuple with the same eight low coordinates coincide. Witness: two tuples equal after dropping
   coordinate 0, distinguished by `leanIsaTables` flush polynomials.
6. **Zerocheck point recycling.** `ζ` is drawn after `q` is committed. A version with `ζ` drawn
   before the commitment is unsound: commit a column vanishing at `ζ_{<τ}` only. The state
   function of Layer 7 charges the zerocheck to Layer 6's challenges.
7. **Back-loaded padding.** Lifting table `j` by `∏_{k ≥ τ_j} X_k` sums to the table's own sum
   (`sumCube_prod_vars`). Lifting by nothing multiplies it by `2^(τ_max − τ_j)`. Witness:
   `tableSummand_target` on heights 2 and 1.
8. **Degree three, three scalars.** The table round polynomial is cubic; the wire carries three
   coefficients and `decode` reconstructs `c_1`. A quadratic reading rejects every Rust proof
   (finding F6). Witness: `RoundPoly.decode` on the dumped proof.
9. **Shared bus powers.** The three bus forms share the last three `ξ` powers across tables
   (finding F5); per-table powers make the target not factor through `rem_s`. Witness:
   `tableSummand_target` fails with per-table powers on two tables.
10. **Top limb of the public input.** The claim `mem_2(r_m, 0…) = 0` is pooled although no
    scalar is sent for it; omitting it lets a non-canonical public word pass the line. Witness:
    the Layer 8 mutation with a nonzero `mem_2` at cell 0 and the third claim dropped.
11. **Joint list binding.** WHIR is list binding, not binding; the extractor needs *one* member
    of the list to satisfy *all* pooled claims. Per-claim soundness ("each claim holds for some
    nearby codeword") does not compose to a witness. The invariant of `whirOpen_rbrSoundness` is
    joint by construction; `verify_knowledgeSound` extracts the member.
12. **Absorb before squeeze.** The sizes and the commitment root are observed before `α`;
    every claim value is observed before `λ`. A chain sampling `α` before the root is broken.
    `FsState` follows the stream order; `verify_iff_compiled` fails otherwise.
13. **Index column bit order.** `∏ (1 + ζ_k (1 + g^(2^k)))` reads bit `k` as coordinate `k`;
    high-first order evaluates a different column. Witness: `idxColumn_eval` at `κ = 2` by
    `decide +kernel`.
14. **Bytecode slot bits.** The opcode is `P(z, 1, 1, 0, 0)`: slot 3 in low-first bits.
    Witness: `bytecodeColumn_slot` on a two-instruction program.
15. **Selector alignment.** Blocks sit at offsets that are multiples of their size, largest
    first; `stack_eval` fails for any other placement. Witness: three blocks of sizes 4, 2, 1
    with the small one first.
16. **Variable order.** Sumcheck binds the highest variable first; table `j` joins at round
    `τ_max − τ_j`. Reversing it mismatches `eq(ζ_{<τ_j}, ·)`. Witness: the honest run of Layer 7
    with two heights.
17. **Radix and parity.** For odd `μ` the root layer is radix 2 and the rest radix 4; a
    uniformly radix-2 GKR has a different message count. `verify_iff_compiled` on the dumped
    proof (whose `μ_bus` is recorded) is the test.
18. **Counts in the count tree.** The tables' count columns only, not the finalize counts
    (`layout.rs:412`); the spec's "nothing checks the finalize counts" holds either way, but the
    leaf layout, and so `ζ`, differ. Witness: the dumped proof.
19. **The extractor reads the stack.** The witness is `witnessOf` of the committed `q`, not of
    the openings or the roots; a "witness" built from the transcript alone is not an
    `EnsembleWitness`. `witnessOf_stackOf` pins it.
20. **Perfect completeness needs no exceptional-challenge clause** in Layers 4–8 and 10: no
    inverse of a challenge is taken. Flock's `(1 + r_eq)⁻¹` at `r_eq = 1` is #3's, inside
    `flockError`. Witness: `piop_perfectCompleteness` has no side condition on challenges.
21. **Sizes are parameters.** The verifier reads `sizes` from the stream and dispatches; the
    oracle protocol is a family indexed by them. A version that puts `sizes` in the oracle
    message type cannot state `OracleInterface`. `verify_iff_compiled` quantifies `∃ s`.
22. **Tags, not labels.** The chain has four numeric tags and no per-challenge labels
    (finding F1); a labelled transcript rejects every Rust proof. Witness: the dumped proof.
23. **Numeric error.** `piopError_le`: at the caps, `Σ piopError < 2^{-150}` plus Flock's
    `< 2^{-183}`; a reading that bounds each term by `1/|E|` and forgets `2^μ` is off by `2^40`.
24. **The extractor computes.** The protocol's extractor is `piopExtractor`, a definition: the
    commit phase's, whose `extractOut` reads the stack off the oracle message, followed by the
    phases'; the adaptor applies `witnessOf`, also computable, to its output. An extractor chosen
    by `Classical.choose` over "some valid witness exists" proves soundness, not knowledge
    (leanth-project's `coreSelectedAssignment`, catalog audit FW-1). Witness: the spine's test
    proves by `rfl` that `piopExtractor` returns the committed stack on the honest transcript,
    whatever the phases' extractors; `#guard witnessOf (stackOf w) = w` on the one-row witness
    (Layer 3).
25. **The wall holds.** No module above the adaptor imports `LeanerVM.Arithmetization`; a phase
    that mentions `leanIsaEnsemble` cannot be tested on the toy instance and breaks with every
    leanISA change. Witness: `scripts/check-layers.sh`.
26. **Seams are the contract.** A phase's output relation is the next phase's input relation by
    definition, not by a bridge lemma; two relations joined by an `iff` at a seam double the
    trusted surface. Witness: `Phases.Complete.toDef` and `Phases.Security.toDef` typecheck only
    when the seams agree, and the test's `trivComplete` (five pass-through phases) inhabits
    `Phases.Complete` against exactly the spine's seams.
27. **The toy instance is honest.** `M3Holds toy input q` holds of the toy stack and fails for
    the stack with one cell changed, each of the four checkable clauses failing alone, the public
    line on either of its cells (a wrong statement for cell 0, the mutation `badLine` for cell
    1); a spine whose relation is inhabited by every `q` proves nothing. Witness: the `#guard`s of
    `tests/LeanerVMTests/Protocol/Spine.lean`, decided by evaluation.
28. **The bus seam bounds the degree.** A seam carrying every true linear claim owes the table
    sumcheck's completeness on cubic terms it cannot prove; `Seam.bus` carries
    `totalDegree ≤ I.d` and the tests reject the cubic term.

## Interfaces supplied to later work

These names are the public boundary and the reviewer's reading list. The recursion work (T5,
T6), the Flock roadmap, and the ArkLib upstream pull requests consume them.

```text
Spine:                Side  Shape  Shape.ColumnId  Layout  Coord  BoundaryBlock  PublicLine  M3Instance
                      M3Instance.d  M3Instance.column  row  tuples
                      ConstraintsVanish  Balanced  CountsNonzero  PublicLinesHold
                      M3Holds  M3Rel  NoOracle  TheOracle  Ensemble.toM3 (Layer 2)
                      ColumnClaim  VirtualTerm  LinearClaim  Weight  WeightedClaim  (each with .Holds)
                      BusOut  TableOut  PubOut  FlockOut  theStack
                      Seam.of  Seam.commit  Seam.bus  Seam.table  Seam.pub  Seam.flock  Seam.done
                      Component.Def  Component.Complete  Component.Security  (and their .append)
                      Component.Security.{witMid, extractor, kSF, rbr}
                      Phase.Def  Phase.Complete  Phase.Security  Phase.passThrough
                      Phase.passThroughComplete  Phase.passThroughSecurity
                      NoOracle  OneOracle  Component.passThrough  Component.passThroughSecurity
                      Component.sendOracle  Verifier.KnowledgeStateFunction.appendGuarded
                      Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
                      commitSpec  commitDef  commitComplete  commitExtractor  commitSecurity
                      Phases  Phases.Complete  Phases.Security  Phases.toDef
                      leanVmPiop  leanVmVerifier  leanVmProver  piopError  piopExtractor
                      piop_perfectCompleteness  piop_rbrKnowledgeSoundness  piop_rbrKnowledgeSoundness_exists
                      Refinement  Refinement.map_option_valid  Extractor.Straightline.map
                      Toy.shape  Toy.toy  Toy.honest  Toy.layout
Protocol (generic):   Column  ETable  sumCube  eqTable  stack  selector  stack_eval  stack_eval_pad
                      Virtual  sumcheck  sumcheck_rbrKnowledgeSoundness  batchClaims
                      fingerprint  sideProduct  sideProduct_poly_eq_iff  sideProduct_collision
                      ProductTree  gkr  gkrError  gkr_rbrKnowledgeSoundness
                      Weight  WeightedClaim  openingPhase
                      encode  encode_column_weight  whirOpen  whirError  whirOpen_rbrSoundness  McaJohnson
                      merkleRoot  merkleVerify  blake2sBytes
Arithmetization:      Expression.toMvPolynomial  degreeBound  M3Table  Component.toM3  Ensemble.toM3
                      toM3_constraints_iff  toM3_flushes_eq
Protocol (leanVM):    instSampleableTypeE  evalOracle  card_E
                      idxColumn  idxColumn_eval  bytecodeColumn  bytecodeColumn_slot
                      Sizes  Sizes.Admissible  leanIsaInstance  stackOf  witnessOf
                      satisfiedBy_witnessOf  m3Holds_stackOf  witnessOf_stackOf
                      busPhase  BusOut  leaf_decomposition  tableSumcheck  tableSummand
                      publicInputPhase  FlockInterface
                      piopError_le
                      leanVmIopp  FsState  Proof  RoundPoly.decode  verify  settleFixedClaims
                      verify_iff_compiled  FiatShamirSecurity  BcsSecurity  verify_knowledgeSound  niError
                      baseVerifier_extractsExecution  baseProver_complete
Parameters:           initialFold  subsequentFold  initialReduction  subsequentReduction
                      residualMaxLog  queryGrindingBits  ladder  novelBasis
```

Everything not listed is a proof, a helper, or a test. The assumed interfaces a reviewer must
know are exactly: `FlockInterface` (#3), `McaJohnson` (ArkLib, ledger A8), `FiatShamirSecurity`
and `BcsSecurity` (ArkLib, ledger A5), and, until every hole is filled, the fields of
`Phases.Complete` and `Phases.Security`; until #3 supplies them, also the Flock witness generator
`FlockWitnessGen` (Layer 3). Each is a structure whose fields are the statements of theorems
another roadmap or hole owes, with the constructions those statements name: a `Security` carries
its extractor and knowledge state function beside its theorem, so it is data rather than a
proposition. None is an axiom, and every theorem that uses one takes it as an argument. There are
no `variable`-block hypotheses. The knowledge-soundness composition ArkLib admits (ledger A2) is
not among them: it is proved here, by the port
`LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean`, deleted when the pin moves past #615.

## Boundaries

**With the leanISA roadmap (#4).** Two requests, filed as `[Roadmap]: leanISA` issues:
`Caps` should require every table height to be a power of two and the bytecode length `2^k_bc`,
since the verifier accepts only log-heights (`cpu/mod.rs:158-170`) and `constraintCompleteness`
already pads; and Layer 5's channels should record, per channel, the domain separator and the
coordinate order of the 16-slot bus tuple (`Component.toM3`'s `sep`/`dir` arguments), so that
the bus of this roadmap is a transcription of leanISA's channels rather than a second table.
Nothing else in `SatisfiedBy` is touched; the eighteen BLAKE2S value limbs are columns of
`blake2sTable` there and virtual columns here (finding F3 of the status file), reconciled by
`FlockInterface.limbColumns`.

**With the Flock roadmap (#3).** This roadmap owns the single stacked WHIR, its parameters, the
Merkle trees and the transcript, and consumes Flock plus ring switching as `FlockInterface`. #3
owns the BLAKE2s circuit, the R1CS lowering, zerocheck, lincheck, ring switching in the leanVM
lane, and their security theorems; its F6 (the concrete PCS) is the generic `whirOpen` of
Layer 11, developed once and shared. The value `g_0` of the fixed zerocheck coordinates is a
Category B constant with no stated provenance (finding F2) and is #3's to transcribe.

**With recursion (T5, T6).** `verify` evaluates the bytecode multilinear and the Flock matrices
through `settleFixedClaims`; the recursive verifier replaces that one function by a deferred
claim and is otherwise `verify`. `VerifySummary`-style outputs (`cpu/mod.rs:690-704`) are not
modelled here.

## Ordering and parallelism

The spine (S) needs Layer 0 and Layer 1's generic half (#18) and nothing else; it is the first
pull request. G1 to G6, I1, K1 and K2 consume nothing from the spine but the shape of their
interface, so they can start on the spine's signatures before it merges; C1, the port of one
ArkLib file, is done on the spine's branch. I2 and P1 to P8 need the spine merged; P2, P4 and P8
additionally need the `Security` of the generic component they use. K3 needs the spine's
schedules and the phase `Def`s, not their `Security`, plus K1 and K2. K4 needs K3, I2 and leanISA
Layer 10. Within a hole the `Def` and the `Security` are separate pull requests, and a `Security`
may be split further along phase-internal seams when the phase's author states them.

Each hole is one or two pull requests, titled `feat(protocol): …`, landing with
`./scripts/validate.sh` green, its modules registered in `LeanerVM.lean` and
`tests/LeanerVMTests.lean`, and a description naming the hole, the sources and pin, the category
of each new definition, the ledger entries it touches, and the T4 obligation it feeds. A generic
hole's pull request links the ArkLib issue it will become.

## How work is tracked

- **This document** says what is wanted. It is edited by pull request and does not record
  history, status, or who is doing what.
- **[protocol-status.md](protocol-status.md)** says where things stand: coverage per layer,
  the frontier, the upstream ledger with issue numbers, open findings against the sources, and
  the decisions still pending. It is hand-maintained, headed by the commit it describes, and
  rewritten whole when a layer lands.
- **Issue [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12)** is the dashboard: the
  layer checklist with one of *open / claimed / in review / landed* per layer, links to the
  intention issue and pull request of each, the upstream ledger, and the frontier. It links to
  this document and to the status file at `main`, holds nothing that is not in them, and is
  updated when the status file is. Where the issue and the files disagree, the files win.
- **Holes.** Each unit of [The holes](#the-holes) is a section of the hole comment on the
  dashboard #12, stating what it consumes from the spine, what it produces, its tests and its
  upstream-watch rows. To claim a hole, or a slice of one, comment on #12 naming the hole and
  the exact declarations taken; the checklist line moves to *claimed*. No `[Hole]` or
  `[Intention]` issue is opened for it (the tracker stays small and readable whole); an issue is
  opened only when a slice needs its own discussion thread, titled
  `[Intention]: protocol - <hole>: …`, and it is closed by the pull request that lands the slice.
  A hole's `Def` with its `Complete`, and its `Security`, are separate slices and separate pull
  requests. Whoever takes a hole reads its upstream-watch rows first.
- **Upstream watch.** The status file keeps a table of external pull requests and issues that
  would replace or feed a hole: repository and number, the hole, the state, the condition under
  which it is adopted (usually a pin bump), and the date last checked. Whoever bumps a pin
  rewrites the table; whoever opens a hole's pull request cites the rows it consumed.
- **To report a problem with this roadmap** — a wrong or unclear target, a source discrepancy, a
  missing prerequisite — open an issue titled `[Roadmap]: protocol — …` naming the layer and
  the acceptance test or convention it touches. Durable source discrepancies are also recorded
  in [leanvm-target.md](../leanvm-target.md).
- **To change this document**, open a pull request that edits it, titled `docs(protocol): …`,
  and reference the dashboard in the description; say which layer, acceptance test, ledger entry
  or convention it touches. A pull request that lands a layer rewrites
  [protocol-status.md](protocol-status.md) whole in the same change and ticks the layer on the
  dashboard. A decision taken on a pending item is written here, as the convention or
  acceptance test it settles, and removed from the status file and the dashboard.
- **Upstream work** is tracked in the ledger of the status file: each entry carries the ArkLib
  (or Clean, CompPoly) issue or pull request number once opened, and the leanerVM layer that
  deletes its local copy when the pin moves.
- Pull requests carry `awaiting-review` when the author is done and `awaiting-author` after a
  review that asks for changes; the reviewer runs the `leanerVM-review` skill's three passes
  (specification, fidelity, hygiene) and reads the changed modules in full. A phase or component
  pull request imports spine names only, never `LeanerVM.Arithmetization`, and its tests run on
  the toy instance.

## References

- leanVM repository [leanEthereum/leanVM](https://github.com/leanEthereum/leanVM), pinned at
  [`a386121f`](https://github.com/leanEthereum/leanVM/commit/a386121f84292f6fa663aaa3e570c15bc0240ea2);
  specification source [`doc/leanvm/`](https://github.com/leanEthereum/leanVM/tree/a386121f84292f6fa663aaa3e570c15bc0240ea2/doc/leanvm)
  at the pin (§3 primitives, §4 committing, §5 arithmetization, §6 bus, §8 end-to-end, Annex A
  ring switching, Annex B WHIR, Annex C Flock); implementation `crates/lean_vm/src/`,
  `crates/fiat_shamir/src/`, `crates/pcs/src/`, `crates/flock/src/`, `python-verifier/verifier.py`.
- ArkLib [Verified-zkEVM/ArkLib](https://github.com/Verified-zkEVM/ArkLib) at
  [`dca90385`](https://github.com/Verified-zkEVM/ArkLib/commit/dca90385fb40dd5eb8da9145da6348ed17f5cd8b):
  `ArkLib/OracleReduction/`, `ArkLib/ProofSystem/{Sumcheck,Component,ToyProblem}/`,
  `ArkLib/Data/MvPolynomial/`, `docs/wiki/sequential-composition.md`,
  `blueprint/src/oracle_reductions/defs.tex`; issues #676 (composition), #627 (BCS).
- A. Chiesa, Y. Cheng, M. Holmgren, A. Lombardi, R. Rothblum, R. Rothblum, *Fiat–Shamir: from
  practice to theory* (CCHLRR19), for round-by-round soundness.
- G. Arnon, A. Chiesa, G. Fenzi, E. Yogev, *WHIR: Reed–Solomon proximity testing with super-fast
  verification* (ACFY25); B. Nazarov, *Ligerito* (NA25); and *Mutual correlated agreement up to
  the Johnson bound* (BCHKS25), for Annex B.
- B. Diamond, J. Posen, *Polylogarithmic proofs for multilinears over binary towers* (DP24), for
  ring switching and the novel basis; S. Lin, W. Chung, Y. Han, *Novel polynomial basis and its
  application to Reed–Solomon erasure codes* (LCH14).
- J. Thaler, *Proofs, arguments, and zero-knowledge*, chapter 4, for GKR and grand products;
  Irreducible, *Multi-multiset matching (M3)*.
- E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive oracle proofs* (BCS16), for the Merkle
  compilation.
- [architecture.md](../architecture.md) for T4 and layer ownership;
  [leanisa-blueprint.md](leanisa-blueprint.md) for the relation;
  [leanvm-target.md](../leanvm-target.md) for the pin and its obligation table.
- leanth (private): the explore branch `scaraven/proof-system-explore` at `db895db`, whose
  `Protocol/{Witness,Relation,Spec,Dimensions,Stacked,Zerocheck,PCS,Measures}.lean` and
  `docs/wiki/proof-system-status.md` are the pattern of [The spine](#the-spine), and the leanVM-a
  formalization at `23929f8c`, catalogued in `docs/roadmap/leanth-reuse.md` (on #18's branch until
  it lands), whose
  end-to-end extractor is the counterexample of acceptance test 24.
