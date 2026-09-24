# Status: the leanVM proof system on ArkLib

This file records where the [protocol roadmap](protocol-blueprint.md) stands as of `main` at
`8563b05` (leanISA Layer 8, PR #24), checked on 2026-09-24, together with the open pull requests
and the roadmap's revision 2 (the spine), which this snapshot accompanies. It is a hand-maintained
snapshot, rewritten whole when a layer or hole lands or a decision is taken; the roadmap is the
authority on what is wanted, and the tracking issue
[#12](https://github.com/Verified-zkEVM/leanerVM/issues/12) mirrors the hole checklist below.
Open pull requests and prerequisite-branch adoption are not changes landed on `main`. The
dependency pins are unchanged.

## Where this roadmap stands

**At a glance.** Layer 0 is on `main` (#15, 2026-09-11). Layer 1's generic half is in the draft
#18 (`feat/leanth-reuse` at `5cc944a`, forked from `4b95a60` and behind `main`; #25 and #26 are
merged into it) and must be rebased and landed before anything stacked on it can get CI. Six pull
requests are open on top of it or on `main` (#38 to #43): every one is algebra underneath a phase,
none defines an `OracleReduction`, a verifier, a prover, a state function or a security theorem,
and nothing on any branch is a trunk for them to hang on. Revision 2 of the roadmap answers that
with the spine (hole S, #45): the abstract instance `M3Instance`, the relation `M3Holds` on the
committed stack, the seams, the schedules, the hole interfaces and the composition, landed first
so that every other unit sits in isolation. The relation the proof system proves is `M3Holds`;
the adaptor (`witnessOf`, `satisfiedBy_witnessOf`) carries knowledge of it to leanISA's
`SatisfiedBy`, and T1 carries that to `ValidExecution`.

### Coverage by hole

| Hole | Unit | Status | Issue |
| --- | --- | --- | --- |
| 0 | ArkLib dependency and field instances (Layer 0) | landed | #15 |
| L1 | Layer 1: generic tables and stacking, and the leaves | generic half in draft #18 (rebase pending); `stack_eval_ambient` in #40, `unstack` and `BlockClaim` in #38, `idxColumn_eval` and `bytecodeColumn_slot` in #41; coefficient transport #26 merged into #18 | #27, #32, #35, #36 |
| S | the spine | open; pending decisions 2 and 6–11 | #45 |
| G1 | virtual sumcheck, `Sumcheck.Def` and completeness (Layer 4) | claimed; the honest round algebra and the ArkLib bridge in #42 | #37 |
| G2 | sumcheck round-by-round knowledge, `Sumcheck.Security` (Layer 4, A1) | claimed; a one-round leaf prepared, unpublished | #37 |
| G3 | batching by powers (Layer 4) | claimed; the algebra and the `(J − 1)/\|F\|` count in #43; the fresh-challenge game prepared | #31 |
| G4 | fingerprint, Lemma 5.1, the collision bound (Layer 5) | claimed; the fingerprint in #39; the multiset-product slice prepared | #33 |
| G5, G6 | GKR (Layer 5) | open | #46 |
| I1 | Clean components as polynomials (Layer 2) | claimed; Clean #466 approved, unmerged | #28 |
| I2 | the adaptor (Layer 3) | open; needs S, I1 | #47 |
| P1, P2 | the bus phase (Layer 6) | open; needs S, G5 | #48 |
| P3, P4 | the table sumcheck phase (Layer 7) | open; needs S, G1 | #49 |
| P5 | the public-input phase (Layer 8) | open; needs S | #50 |
| P6 | the Flock phase (Layer 9) | open; needs S and #3 | #51 |
| P7, P8 | the claim pool and the opening phase (Layer 10) | open; needs S, G1, G3 | #52 |
| C1 | the knowledge-soundness append (A2) | open; ArkLib #615 is the candidate | #53 |
| K1 | WHIR (Layer 11) | open; shared with #3 F6 | #54 |
| K2 | Merkle, BLAKE2s bytes, the parameters (Layer 11) | open | #55 |
| K3 | transcript, proof, `verify` (Layer 12) | open; needs S, K1, K2 | #56 |
| K4 | T4 (Layer 13) | open; needs K3, I2, leanISA Layer 10 | #57 |
| — | VCVio controls for K3 and P7 | landed upstream (VCVio #784) | #29, #30 |

### Open pull requests

| PR | Hole | Base | CI | Content | Review order |
| --- | --- | --- | --- | --- | --- |
| #18 (draft) | L1 | `4b95a60` | none until rebased | `Multilinear.lean`, `Stacking.lean`, the reuse catalog; #25 and #26 merged in | land first |
| #40 | L1, feeds P1 | #18 | none | `stack_eval_ambient` (specification (5.4) with any pad), `stack_eval₂_ambient` | 2 |
| #38 | L1, feeds P7 | #18 | none | `Blocks.unstack`, `BlockClaim`, `isValid_iff_pairing`, window locality | 3 |
| #41 | L1, feeds P1 | #18 | none | `idxColumn`, `idxColumn_eval`, `bytecodeColumn`, `bytecodeColumn_slot`, `bytecodeColumn_eval` (Category B against §8.1 and `leaf.rs:570-637`) | 4 |
| #43 | G3 | #18 | none | `powerBatch`, `pairing_batchWeight`, `batch_complete`, `card_false_batch_le` | 5 |
| #39 | G4 | #18 | none | `fingerprintPoly`, its injectivity, `fingerprintFactorPoly` of total degree at most 4 | 6 |
| #42 | G1 | `main` | runs | the honest round polynomials and their four identities; equality with ArkLib's `projectedRoundPolynomial` | independent; decide which representation Layer 4 builds on |
| #44 | docs | `main` | runs | rewrote this file | held; its content is folded into this revision |

The reading audit of these pull requests (2026-09-24) found no defect. Its questions: §5.2's
`5·2^μ/|E|` against the proved factor degree 4 (S13 below); #42's two definitions of the honest
round polynomial; #43's bound stated as a count in `ℚ` rather than in ArkLib's probability form;
#38's `BlockClaim`, which cannot hold Flock's weighted claim (the pool needs `WeightedClaim`);
#41's `bytecodeColumn`, which encodes the sentinel slot through `prog.code`. Kernel axioms were
not run: the five stacked pull requests have no CI, and only #18's body records
`propext, Classical.choice, Quot.sound`.

### The frontier

- **#18** is the base of five pull requests and is behind `main`: rebase and land it (the two
  modules and the catalog), then retarget #38, #39, #40, #41 and #43 to `main`.
- **The spine** (#45) is the next pull request after #18. Its review budget goes to
  `M3Instance` and the seam relations; the pending decisions 2 and 6–11 are settled on its issue
  first.
- **Holes that can start now**, on the spine's signatures: G1 to G6, I1, K1, K2 (generic), and
  C1 (ArkLib only).
- **The pins have not moved.** ArkLib `main` is 246 commits past `dca90385` (finding A18); the
  next bump is one planned change (Lean 4.34, a CompPoly containing #331, `card_E` restated:
  findings P3 and P7).
- Finding F9 (the Python verifier omits four caps) is still to be reported to leanVM; S13 (the
  degree of the product factor) is new.

## Upstream ledger

Each entry names the ArkLib (or Clean, CompPoly, leanISA) state at the pin, the hole that needs
it, and the upstream issue or pull request.

| Ledger | At the pin | Hole | Upstream |
| --- | --- | --- | --- |
| A1 sumcheck single-round rbr knowledge soundness (`Sumcheck/Spec/SingleRound.lean`; 14 sorries remain on `main`) | admitted | G2 | ArkLib #1 (umbrella; #3 closed 2026-09-22); #1128, #1129 (honest identities, executor controls); ArkLib `main`'s `ProofSystem/Sumcheck/Interaction/Soundness.lean` proves the one-round committed-message bound on the new typed executor |
| A2 rbr knowledge-soundness append (guarded first verifier) | admitted (`Append/Security.lean`, 4 sorries, also on `main`) | C1 | ArkLib #676; ArkLib #615 carries `Append/Knowledge.lean` and `KnowledgeNary.lean` |
| A3 rbr ⇒ plain knowledge soundness | admitted | K3 (corollary) | ArkLib #676 |
| A5 Fiat–Shamir and BCS security | admitted / absent | K3 | ArkLib #627 (BCS); #848 and #469 (duplex-sponge Fiat–Shamir, Theorems 6.1 and 6.2; the single-salt transfer is the shape of `FiatShamirSecurity`) |
| A6 grand product, GKR, batching, stacking | absent | L1, G3, G4, G5 | stacking: ArkLib #900 (#26, #38, #40 staged); fingerprints and the product: ArkLib #901 (#39 staged); batching: ArkLib #615's `gammaPowers`; GKR: to open (ArkLib #818 is a different protocol shape) |
| A7 WHIR over binary Reed–Solomon codes, Merkle trees | absent | K1, K2 | ArkLib #4 (Merkle); #383 and #992 adjacent; coordinate with #3 F6 |
| A8 mutual correlated agreement up to Johnson | admitted | K1 | ArkLib's coding-theory track (the #907 slices landing on `main`) |
| A9 ring switching packing leaves | admitted (packing coordinates repaired after the pin, ArkLib #896) | P6 | #3, ArkLib #893, #383 |
| C1 `Expression.toMvPolynomial`, `degreeBound` | absent | I1 | Clean #466 (approved, unmerged) |
| C2 power-of-two heights, bus data per channel | leanISA | I2 | done: #13 closed by #14; `Caps.heights` (#24), `channelSep`, `channelDir`, `busTuple` (#17) |
| C3 ℕ-counted, direction-tagged balance | absent | I2 (the adaptor's balance clause) | Clean #464 (draft, the maintainer's), #20; Clean #452 (the capacity side condition) |
| C4 fixed columns and sound prover data | absent | I2 (the three fixed-column conjuncts become `M3Instance` tags) | Clean #446 (draft), #23 |

## Upstream watch

Read the rows of your hole before starting it; whoever bumps a pin rewrites this table.

| Repository and number | State (checked 2026-09-24) | Hole | What it would replace or feed here | Adopt when |
| --- | --- | --- | --- | --- |
| ArkLib #615 (ring-switching packing proofs; `Append/Knowledge.lean`, `KnowledgeNary.lean`, `BatchingStrategy.gammaPowers`) | open since 2026-09-08 | C1, G3 | the `KnowledgeAppend` inhabitant; the scalar batching bound | merged and the pin bumped; C1's local proof is deleted then |
| ArkLib #818 (GKR with perfect completeness, Thaler's line reduction, radix 2; inherits composition sorries) | open since 2026-09-04 | G5 | a pattern for a layer as a reduction; not the leanVM protocol (radix 4, four values combined by two challenges) | never as is; cite |
| ArkLib #503 (LogUp) | open | none | not applicable: the leanVM-b bus is a product | never |
| ArkLib #383 (FRI-Binius: Binary Basefold, ring switching, additive NTT; completeness and rbr knowledge soundness; `OracleReduction/Cast.lean`) | open, updated 2026-09-24 | P6, K1, S | ring switching for the Flock phase; the binary-code encoder; a cast of reductions between statement types, useful at seams | merged and the pin bumped; coordinate with #3 |
| ArkLib #992 (end-to-end soundness of a computable FRI IOP) | open since 2026-09-22 | K1 | a pattern for the WHIR soundness statement | never as is; cite |
| ArkLib #848, #469 (duplex-sponge Fiat–Shamir, Sections 5 and 6) | open, updated 2026-09-17 | K3 | the shape, and possibly the theorem, behind `FiatShamirSecurity` (the single-salt straightline transfer) | merged; then state `FiatShamirSecurity` as its instance |
| ArkLib #1128, #1129 (honest round polynomial identities; sumcheck executor controls) | open since 2026-09-24 | G1, G2 | #42's `HonestSumcheckUpstream.lean` | merged and the pin bumped; the adapter is deleted then |
| ArkLib #926 (lift-context structural obligations) | draft | none (ledger A4) | nothing consumed | never |
| ArkLib #900, #901 (issues) | open | L1, G4 | the owning issues for the staged generic modules | when the ArkLib pull requests open |
| ArkLib `main` (`Interaction/Oracle/*`, `ProofSystem/Sumcheck/Interaction/*`) | landed after the pin | G1, G2, S | the typed executor (findings A14, A18); the one-round committed-message bound | the pin bump; the spine stays on `OracleReduction`, whose security definitions the new executor does not yet carry |
| Clean #466 (expressions as bounded-degree polynomials) | open, approved | I1 | `Expression.toMvPolynomial`, `degreeBound` | merged and the pin bumped; until then a local copy under the generic-code rule |
| Clean #464 (bus balance over binary fields) | draft, the maintainer's | I2 | the adaptor's balance clause; retires `BalancedPair` | merged and the pin bumped |
| Clean #446 (fixed columns, sound prover data) | draft since 2026-08-16 | I2 | the three fixed-column conjuncts of `SatisfiedBy` (#23) | merged and the pin bumped |
| VCVio #784 | merged 2026-09-24 | K3, P7 | query-budget and product-relation controls (#29, #30) | done |
| leanth #16 at `23929f8c` (private) | — | L1, G1, G3, G4 | port sources, per the catalog | never as code; derived material carries its notice |

## Decisions pending

Confirm before the spine (#45) opens; each is discussed on that issue. Decision 1 was taken with
#13, and decision 3 with revision 2 (blueprint convention *Seams*: the zerocheck escape is charged
in the bus phase where ζ is drawn; no separate phase).

2. **Statement versus parameter.** `input` is the statement and `(prog, sizes)` index the
   protocol family, the compiled verifier reading the sizes from the proof and dispatching
   (leanth's decision 4); or `(prog, input)` is the statement. Recommended: the former, as the
   roadmap's convention says.
4. **Generic code location.** `LeanerVM/Protocol/Generic/` until the ArkLib pull request merges
   (convention *Generic code*), versus developing directly on an ArkLib branch and pinning
   leanerVM to that branch's commit. Default is the former.
5. **The honest prover's shape.** Computable by construction is the default; whether it is also
   the object of a compile-time end-to-end `#guard` on a tiny instance depends on the cost of the
   WHIR encoder in the interpreter, measured at K1.
6. **The witness at the protocol boundary.** (a) `q : Column μ` itself, with `witnessOf` as the
   adaptor and a computable extractor, and no universe issue (`EnsembleWitness` lives in
   `Type 1`, ArkLib's witness types in `Type`); or (b) a `Type 0` proxy of `EnsembleWitness`
   (leanth's `Witness ens`), the stack derived inside the commit phase. Recommended: (a).
7. **Generic instance.** Phases over an abstract `M3Instance` derived from any Clean ensemble by
   `Ensemble.toM3`, leanISA being one instance (the wall, toy-instance tests, reuse for the
   recursion guest), or phases written over `leanIsaEnsemble`. Recommended: generic.
8. **Conjunct placement.** Which of `SatisfiedBy`'s thirteen conjuncts are clauses of `M3Holds`
   and which are the adaptor's work. Proposal: every fact a phase or the verifier establishes
   about `q` is a clause (constraints, multiset balance, counts nonzero, caps, public words, the
   Flock claim); the three fixed-column conjuncts are `M3Instance` data (a *public* coordinate
   tag for the bytecode block, a *committed* tag for the memory block), as Clean #446 models them.
9. **Balance.** `M3Holds` states balance as multiset equality of the flush tuples read from `q`,
   which is what Lemma 5.1 proves; the adaptor maps it to `BalancedPair` now and to Clean #464's
   ℕ-counted balance later, so the proof system is insulated either way. Confirm that
   `BalancedPair` is retired only through the adaptor.
10. **Security notion.** Round-by-round knowledge soundness per phase, composed, with plain
    knowledge soundness and plain soundness as corollaries once ledger A3 lands; or plain
    soundness only (cheaper, does not compose, does not serve recursion). Recommended:
    round-by-round knowledge.
11. **Extractor discipline.** Every extractor a computable definition, with
    `#guard witnessOf (stackOf w) = w` on the toy stack (acceptance test 24); the enforceable form
    of "reasonable running time", which neither ArkLib nor leanth models. Recommended: adopt.

## Open findings against the sources

Numbered for citation from pull requests and `docs/leanvm-target.md`. **S** = internal to the
specification; **F** = Rust versus specification, continuing the leanISA numbering where the
subject overlaps; **A** = ArkLib versus the roadmap's expectations; **E** = the Lean environment.

**Specification.** S6 (from leanISA) §8.4 Fiat–Shamir is `TODO`; the roadmap transcribes the
Rust chain (F1). S9 Lemma 5.2's proof is `TODO` (`05-arithmetization.tex`, "Proof of Lemma 5.2");
Layer 5 proves it by unique factorization. S10 §5.3 does not state the degree of a radix-4 layer's
round polynomial; it is 5 (eq times four multilinears), and the Rust sends four coefficients of
the degree-4 cofactor (`gkr.rs:399-401`). S11 §8.5 lists the bus roots as "the count root `R_c`
and one bus root `R`" but does not say the push and pull roots are one scalar; the Rust makes it
structural (F3). S12 Annex B's Protocol B.1 takes an out-of-domain sample at every level
`i ≥ 1`; the Rust's `ood_samples[0] = 0` and ≥ 1 afterwards agree, and additionally grinds 17
bits per level before the queries (`whir_config.rs:60`), which Annex B does not mention. S13 (2026-09-24) §5.2 charges the product check `5·2^μ/|E|`, reading each factor as "degree four in α and one in β"; the factor `β − π_α(t)` is a sum, so its total degree is 4 and the bound is `4·2^μ/|E|`, as the roadmap's acceptance test 1 states and PR #39's `totalDegree_fingerprintFactorPoly` proves. The specification's bound is loose, not wrong.

**Rust versus specification** (`crates/lean_vm`, `crates/fiat_shamir`, `crates/pcs`). F1 no
domain-separation labels: four numeric tags in lane 3 and positional order
(`fiat_shamir/src/lib.rs:31-39`); `from_label` is test-only. F2 Flock's fixed coordinate `g_0`
is the hexadecimal expansion of π, hardcoded without provenance
(`flock/src/zerocheck/univariate_skip_optimized.rs:104-106`); #3's to transcribe. F3 one root
for push and pull (`gkr.rs:363-367`, `leaf.rs:890-894`). F4 the table sumcheck's target is
derived, never transmitted (`cpu/mod.rs:728-735`). F5 the three bus forms share the last three
`ξ` powers across tables (`cpu/mod.rs:404-422`). F6 the table round polynomial is a cubic sent
whole, four nodes, three wire scalars (`constraints.rs:187-194, 267`). F7 one coefficient of
every round polynomial and Flock's `ĉ` are never transmitted (`transcript.rs:289-309`,
`zerocheck.rs:91-94`). F8 ring-switched claims take the low powers of `λ` in the opening batch
(`stack_open.rs:400-401, 518-519`). F9 the Python verifier omits the caps `log_mem ∈ [16, 32]`,
`τ_j ≤ 32`, the bytecode power-of-two bound and `τ_BLAKE2S ≥ 3` (`verifier.py:1372-1379` versus
`cpu/mod.rs:158-170`): a divergence between the two verifiers, soundness-relevant, to report
upstream. F10 the Rust verifier's rejection set is four predicates plus truncations
(`PublicInput`, `ZeroCount`, `LayerMismatch`, `FinalMismatch`) with Flock's and WHIR's inside;
structure checks on public data are `assert!`s (`leaf.rs:123-146`). F11 the count tree holds the
tables' count columns only (`layout.rs:412-414`), settling leanISA finding F4. F12 the fill
blocks make announced heights exact, so no truthfulness obligation exists
(`filler.rs:1-25`). F13 grinding binds the nonce even when the check fails
(`lib.rs:165-174`). F14 the seed hashes `"leanvm" ‖ len ‖ R1CS_DIGEST ‖ bytecodeHash`, where
`R1CS_DIGEST` is one constant naming the circuit, not the matrices (`cpu/mod.rs:82-93`,
`flock/src/hash.rs:276-280`). F15 the stacking bound `μ ∈ [15, 28]` is checked separately from
the per-log caps (`cpu/mod.rs:174-176`). F16 `SECURITY_BITS = 128` round-by-round with the
Johnson slack, and `assert_grinding_unnecessary` proves the bus needs no grinding for
`μ ≤ 61` (`leaf.rs:945-950`).

**ArkLib** (`dca90385`). A1–A9 are the ledger. Further: A10 relations are `Set (Stmt × Wit)`;
the documented refactor to `Stmt → Wit → Prop` has not happened (`Security/Basic.lean:45-65`).
A11 `rbrKnowledgeSoundness` averages over prover-sampled prefixes and is weaker than the
literature's; the worst-case form (`rbrKnowledgeSoundnessWorstCase`) is the one every layer
proves, and the implication to the averaged form is proved. A12 `Commitments/Functional/Basic.lean`'s
`extractability` is `∀ …, False`; not cited. A13 two statements in `Security/Implications.lean`
contain `sorry` in their *types* (the `addSalt` implications); never cited. A14 `ArkLib/Interaction/`
(the typed-interaction replacement) has no security definitions yet; the roadmap builds on
`OracleReduction/` and expects to migrate. A15 `ProofSystem/ToyProblem/` is sorry-free end to end
with an uninstantiated error; its `Codegen` probes are the pattern for `verify`. A16 ArkLib's
CompPoly pin is the `v4.33.1` tag; leanerVM's root pin wins the resolution (Layer 0). A17
`OracleInterface (Vector α m)` (position queries) is a global instance, so any type reducible
to a `Vector` inherits it; a column type with an evaluation oracle must not be an abbreviation of
`Vector` (Layer 0). A18 (2026-09-24) ArkLib `main` (`66f39b4`) is 246 commits past the pin, on Lean 4.34 with a CompPoly containing #331; the `OracleReduction` carriers, `rbrKnowledgeSoundnessWorstCase` and `OracleReduction.append` are unchanged in shape, the composition knowledge theorems are still admitted, `Sumcheck/Spec/SingleRound.lean` still carries 14 sorries, and a typed executor under `ArkLib/Interaction/Oracle/` with `ProofSystem/Sumcheck/Interaction/` (a proved one-round committed-message bound) has appeared; the pin bump is one planned change.

**Clean** (`93c9d1ef`). C5, C6 (from leanISA): no degree, no height. C10 `EnsembleWitness` has
no generator; `Circuit.witgen` is per row (T2's concern). C11 `Ensemble.Statement`'s
`BalancedChannels` assumes the non-overflow side condition (`FlatEnsemble.lean:353-360`); this
roadmap never states through it (leanISA acceptance test 14).

**CompPoly** (`3468b38c`). P1, P3 (from leanISA). P4 no hypercube sum and no pointwise product
on `CMlPolynomialEval`; Layer 1. P5 the additive NTT is generic over a basis and instantiated
only at `GF(2^8)`; Layer 11 supplies the `K` basis. P6 no `Ext.frobenius`; ring switching's
Frobenius ladder is #3's (F1 there).

**Environment.** E6 (2026-09-10) `lake build` with several explicit ArkLib targets scheduled
`ArkLibLintPlugin:shared` twice and one link failed with "no such file or directory" on the
`.so`; the file existed afterwards and a second `lake build` proceeds. The plugin is loaded
while elaborating every ArkLib module (`lakefile.toml:48`), so a consumer needs it built.

## Survey record

Kept so the searches are not repeated.

- **2026-09-24, the open pull requests and leanth.** #38 to #43 read in full (the reading audit
  is recorded on the dashboard's history); leanth's explore branch `scaraven/proof-system-explore`
  at `db895db` (`Protocol/{Witness,Relation,Spec,Dimensions,Layout,Stacked,Zerocheck,PCS,
  Measures}.lean`, `docs/wiki/proof-system-status.md`) and leanth-project at `23929f8c`
  (`Security/{Relation,Protocol,RBR}.lean`, `LeanVM/{Main,Protocol}.lean`,
  `LeanVM/Arith/{Glue,Refinement}.lean`) read for the spine pattern; Clean `Air/FlatEnsemble.lean`
  (`Statement` :361, `BalancedChannels` :342) and `Air/Balance.lean` (`BalancedInteractions` :24);
  ArkLib `Security/Basic.lean` (`knowledgeSoundness` :339, `Extractor.Straightline` :248),
  `Security/RoundByRound.lean` (`rbrKnowledgeSoundnessWorstCase` :534),
  `CoordinateWiseSpecialSoundness/Guarded.lean` (`GuardedForm` :112); ArkLib `main` at `66f39b4`.
- **2026-09-10**, the original survey:

- **ArkLib** at `dca90385`: `OracleReduction/{Basic,Execution,OracleInterface,Security/*,
  Composition/Sequential/*,LiftContext/*,FiatShamir/*,BCS,Salt,VectorIOR}.lean`,
  `ProofSystem/{Sumcheck,Component,ConstraintSystem,Binius,RingSwitching,Spartan,Plonk,Fri,
  BatchedFri,Stir,ToyProblem}/`, `Commitments/{Functional,Ordinary}/`, `Data/{MvPolynomial,Hash,
  CodingTheory,Probability}/`, `ToCompPoly/`, `Interaction/`, `docs/{wiki,design}/`,
  `blueprint/src/oracle_reductions/defs.tex`. 58 files under `ProofSystem`, `Commitments`,
  `Data` contain `sorry`, 18 more under `FiatShamir/`; `scripts/axiom_baseline.json` is the
  allowlist and `lake exe axiomsweep` the authority. No GKR, grand product, multiset check,
  lookup argument, WHIR, Ligerito, Merkle tree, BLAKE2s, batching component, or stacking
  anywhere; `ConstraintSystem/MemoryChecking.lean` has the relations only. Hachi
  (`Commitments/Functional/Hachi/`) is the most complete assembly (nine chained reductions,
  lattice-based) and has the only eq-batched zerocheck. Composition: completeness proved
  (`docs/wiki/sequential-composition.md`), rbr soundness proved for a pure first verifier,
  knowledge and plain soundness admitted (#676).
- **leanVM** at `a386121f`: verifier `cpu/mod.rs:711-779` (phases at 712–769; `read_public`
  130–178; caps 45–64; `fs_seed` 82–93; ξ 404–441; public input 745–755; `finish_claims`
  656–667; `slot_claims` 790–814); `leaf.rs` (blocks 53–57, layout 149–156, fingerprint 89–98,
  decomposition 389–461, `verify_balance` 864–936); `gkr.rs` (layers 32–76, batching 258–430);
  `constraints.rs` (module doc 1–35, round polynomial 187–194, verifier 243–292);
  `fiat_shamir/src/lib.rs` (compress 18–24, tags 36–39, state 56–104, grinding 106–174),
  `transcript.rs` (proof 9–19, traits 36–110, `next_round_poly` 289–309);
  `pcs/src/whir_config.rs` (38–86, ladder 260–311), `stack_open.rs` (claims 75–118, batching
  400–401, verifier 473–548), `ring_switch.rs` (challenges 160–162), `merkle.rs`;
  `flock/src/hash.rs` (constants 105–116, 139–155, `R1CS_DIGEST` 276–280, floor 283–286),
  `zerocheck.rs` (47–58, 340–347), `univariate_skip_optimized.rs` (65–115);
  `python-verifier/verifier.py` (`verify_execution` 1365–1414, queries 910). Counted-column
  blocks `layout.rs:412-414`. No proof fixtures are checked in; `scripts/dump-proof.sh` is
  Layer 12's.
- **Clean** at `93c9d1ef`: `Operations.constraints` (`Operations.lean:404`),
  `Operations.interactions` (`:428`), `constraintsHold_iff_forall_mem` (`:168-182`),
  `Component.operations` (`FlatComponent.lean:21`), `Table` (`:151-156`), `EnsembleWitness`
  (`FlatEnsemble.lean:19-25`), `Expression` (`Expression.lean:6-16`), `Environment.fromArray`
  (`:71`), `AbstractInteraction` (`Channel.lean:101-105`), `Circuit/Json.lean` (an untyped JSON
  export of operations, consumed by no verified path). Zero occurrences of `MvPolynomial`,
  `degree`, `multilinear`, `height`, `power of two`.
- **CompPoly** at `3468b38c`: `Multilinear/Basic.lean` (`CMlPolynomialEval` 47, `evalMleLayer`
  475, `evalMle` 499, `eval₂Mle` 520, `eqTilde` 543, `eqTilde_eq_prod` 600, `eqTilde_append`
  632, transforms 672–767), `Multilinear/Equiv.lean` (200, 337–342), `ManyEval/`,
  `Fields/Binary/AdditiveNTT/{NovelPolynomialBasis,Domain,Algorithm,Impl,Correctness}.lean`,
  `Fields/Binary/BF64/{Impl,Ext3}.lean` (`Fintype` at `Impl.lean:391`, `card_ext3` at
  `Ext3.lean:199`). No benchmark of `BF64`/`Ext3`; the generic `Ext` multiplication is
  ~25–64 µs in the interpreter (ROADMAP figures).
- **VCVio** at `f9dc47d9` (through ArkLib): `SampleableType` (`OracleComp/Constructions/
  SampleableType.lean:44`), `SampleableType.ofEquiv`, instances for `Fin n`, `Vector α n`,
  `BitVec n`.
- **Environment**: `lake update Arklib` cloned Arklib, VCVio, PolyFun, loom2, cslib, leansqlite,
  UnicodeBasic, BibtexQuery, MD4Lean, doc-gen4 and checkdecls and ran Mathlib's cache hook
  (no download; the same revision). The first build of the OracleReduction cone compiled
  ToMathlib, cslib, PolyFun and VCVio's `OracleComp` modules in about fifteen minutes on the
  author's machine before the plugin race (E6).
