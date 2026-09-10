# Status: the leanVM proof system on ArkLib

This file records where the [protocol roadmap](protocol-blueprint.md) stands as of the branch
that introduces it, on top of `main` at `1fa9cf1` (leanISA Layer 4 merged, PR #9) on 2026-09-10.
It is a hand-maintained snapshot, rewritten whole when a layer lands or a decision is taken; the
roadmap is the authority on what is wanted, and the tracking issue
[#12](https://github.com/Verified-zkEVM/leanerVM/issues/12) mirrors the coverage table below.

## Where this roadmap stands

**At a glance.** Nothing is built. ArkLib is wired in at `dca90385` (`lakefile.toml`,
`lake-manifest.json`, `upstreams.json`; the Lake resolution keeps CompPoly at `3468b38c` and the
one Mathlib `0df444a3`), and `LeanerVM/Protocol/Field.lean` is the first consumer. The
roadmap was written after a survey of ArkLib, Clean, CompPoly, the leanVM specification and the
Rust and Python verifiers; the survey's findings that bind the roadmap are recorded below, the
rest in the survey record.

### Roadmap coverage

| Layer | Status | Notes |
| --- | --- | --- |
| 0 — ArkLib dependency, field instances | built, awaiting review | `Protocol/Field.lean`: `Column` (a structure, see the frontier), `instSampleableTypeK/E`, `card_E`, `evalOracle`; axiom closure `propext, Classical.choice, Quot.sound` |
| 1 — tables, stacking, index and bytecode columns | open | independent of leanISA |
| 2 — Clean components as polynomials | open | independent of leanISA; Clean upstream candidate |
| 3 — the M3 instance | open; needs leanISA Layers 5–8 | two `[Roadmap]: leanISA` requests filed (#13) |
| 4 — virtual sumcheck and batching | open | ArkLib ledger A1, A6 |
| 5 — fingerprints, grand product, GKR | open | ArkLib ledger A6 |
| 6 — bus phase | open; needs 3, 5 | |
| 7 — table sumcheck phase | open; needs 3, 4, 6 | |
| 8 — public-input phase | open; needs 3 | |
| 9 — Flock and ring-switching boundary | open; needs 3 and #3 | interface only |
| 10 — claim pool, opening, the oracle protocol | open; needs 6–9 | ArkLib ledger A2 |
| 11 — WHIR, Merkle, parameters | open; needs 0, 1 | shared with #3 (F6); ledger A7, A8 |
| 12 — compilation, transcript, `verify` | open; needs 10, 11 | ledger A5 |
| 13 — T4 and fixtures | open; needs 12 and leanISA Layer 10 | |

### The frontier

- **Layer 0.** `lakefile.toml` requires `Arklib` at `dca90385`; `lake update Arklib` resolved
  VCVio `f9dc47d9`, PolyFun `c0c92369`, loom2, cslib and doc-gen4's dependencies and left
  CompPoly at the root pin `3468b38c` (ArkLib asks for the `v4.33.1` tag, fifteen commits
  earlier; the diff is additive on everything ArkLib's `ToCompPoly` imports). The first
  `lake build` of the OracleReduction cone hit a Lake race building ArkLib's lint plugin
  (`ArkLibLintPlugin:shared` scheduled twice, one link failing with "no such file"); a second
  invocation proceeds (environment finding E6). `Protocol/Field.lean` supplies
  `SampleableType K` (a uniform `Fin (2^64)` as a bit pattern) and `SampleableType E` through
  `SampleableType.ofEquiv` on `Vector K 3 ≃ E` (ArkLib does the same for `KoalaBear.Ext6`), the
  evaluation `OracleInterface` on `Column n`, and `card_E`. `Column n` became a structure
  wrapping `CMlPolynomialEval K n` rather than the roadmap's abbreviation: as an abbreviation it
  unfolds to `Vector K (2^n)`, and instance search then also finds ArkLib's position-query
  `OracleInterface (Vector α m)`, which a test literal did (finding A17); the roadmap's Layer 1
  signature and *Tables* convention now say so. The `#guard`s answer on and off the cube; the
  samplers are probed by compiling `$ᵗ K` and `$ᵗ E`.
- **Layers 1, 2, 5** can start now: they need only Layer 0's instances (Layer 1), Clean
  (Layer 2), or nothing beyond ArkLib (Layer 5 with the sampler as a parameter).
- **Layer 11** is the largest independent piece and should start early; its generic half is
  #3's F6 and the ArkLib WHIR track, developed once.
- **Layer 3** waits for leanISA Layers 5–8; the two requests to #4 are filed as
  [#13](https://github.com/Verified-zkEVM/leanerVM/issues/13).
- **Upstream ledger.** No ArkLib issue is filed yet; the drafts are below, to be opened when
  Layer 4, 5 or 11 is claimed, so that each carries a concrete consumer.

## Upstream ledger

Each entry names the ArkLib state at `dca90385`, the leanerVM layer that needs it, the action,
and the issue or pull request once opened. Drafted titles are in quotes.

| Ledger | Layer | Action | Upstream |
| --- | --- | --- | --- |
| A1 sumcheck single-round rbr knowledge soundness (`Sumcheck/Spec/SingleRound.lean` sorries) | 4 | prove for the virtual-summand shape; contribute the leaf | to open: "sumcheck: prove the single-round rbr knowledge-soundness leaf" (ArkLib #3 is the umbrella) |
| A2 rbr knowledge-soundness append for a pure first verifier (`Append/Security.lean` admitted) | 10 | prove `append_rbrKnowledgeSoundnessWorstCase_of_pure_first` mirroring the soundness version | to open, referencing ArkLib #676 |
| A3 rbr ⇒ plain knowledge soundness (`Implications.lean` admitted) | 12 (corollary only) | none here; plain corollaries stated when it lands | ArkLib #676 |
| A5 Fiat–Shamir and BCS security | 12 | interfaces `FiatShamirSecurity`, `BcsSecurity` | ArkLib #627 (BCS design); FS: to open "Fiat–Shamir: rbr knowledge soundness transfers in the ROM" |
| A6 grand product, GKR, batching, stacking | 1, 4, 5 | write in ArkLib's shape under `Protocol/Generic/`, upstream as `ProofSystem/GKR/GrandProduct`, `Component/Batching`, `Data/MvPolynomial/Stacking` | to open: "grand-product GKR and multiset fingerprinting", "batch claims by powers of a challenge" |
| A7 WHIR over binary Reed–Solomon codes, Merkle trees | 11 | write generically, upstream as `ProofSystem/Whir/` and `Commitments/Merkle` | to open; ArkLib #4 (Merkle) is the umbrella; coordinate with #3 F6 |
| A8 mutual correlated agreement up to Johnson (`rs_mcaError_le_in_johnson_range` admitted) | 11 | interface `McaJohnson` | ArkLib's coding-theory track (#854 is adjacent) |
| A9 ring switching packing leaves; no `GF(2) → GF(2^64)` profile | 9 | owned by #3 (F5) | ArkLib #893 |
| C1 `Expression.toMvPolynomial`, `degreeBound` | 2 | write here, upstream to Clean | to open on Clean |
| C2 power-of-two heights, bus separator data | 3 | leanISA `Caps` and channels | leanerVM #13 |

## Decisions pending

Confirm before Layer 3 or Layer 10 is opened:

1. **`Caps` includes power-of-two heights** (leanerVM #13): the relation of this roadmap is
   `SatisfiedBy` alone only if it does; otherwise Layer 3 adds the conjunct locally and the two
   roadmaps state two relations.
2. **Statement versus parameter.** The roadmap makes `prog` and `sizes` Lean parameters and
   `input` the statement (convention *Statements and parameters*). The alternative, `(prog,
   input)` as the statement and `sizes` a parameter, changes nothing in the theorems and makes
   the Fiat–Shamir seeding read more naturally; decide at Layer 3.
3. **Where the zerocheck error is charged.** Layer 7 charges the "`C̃(ζ) = 0` implies `C` vanishes
   on the cube" step to Layer 6's challenges (where `ζ` is drawn). The alternative is a separate
   `ReduceClaim`-shaped phase between Layers 6 and 7 whose only content is that implication; it
   is cleaner to audit and costs one more composition. Decide at Layer 7.
4. **Generic code location.** `LeanerVM/Protocol/Generic/` until the ArkLib pull request merges
   (convention *Generic code*), versus developing directly on an ArkLib branch and pinning
   leanerVM to that branch's commit. The former keeps CI green on one pin; the latter avoids a
   deletion step. Default is the former.
5. **The honest prover's shape.** Computable by construction (each phase's prover a function of
   the witness and the challenges) is the default; whether it is also made the object of a
   compile-time end-to-end `#guard` on a tiny instance depends on the cost of the WHIR encoder
   in the interpreter, measured at Layer 11.

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
bits per level before the queries (`whir_config.rs:60`), which Annex B does not mention.

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
`Vector` (Layer 0).

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

Kept so the searches are not repeated (2026-09-10).

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
