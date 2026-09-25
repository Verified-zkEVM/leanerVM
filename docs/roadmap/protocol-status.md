# Status: the leanVM proof system on ArkLib

Snapshot of `main` at `8563b05b03434851badc19715f6162fb70ffc093`, checked on 2026-09-24.
The [blueprint](protocol-blueprint.md) defines the intended protocol;
[#12](https://github.com/Verified-zkEVM/leanerVM/issues/12) tracks its implementation.
Open pull requests and prerequisite-branch adoption below are not changes landed on `main`.
The dependency pins are unchanged.

## Landed and adopted prerequisites

The field and oracle-interface foundation landed on `main` in
[#15](https://github.com/Verified-zkEVM/leanerVM/pull/15). The leanISA constraint statement
landed in [#24](https://github.com/Verified-zkEVM/leanerVM/pull/24), including the announced
height caps. The protocol's concrete M3 assembly still has to consume that relation.

Scaraven's draft [#18](https://github.com/Verified-zkEVM/leanerVM/pull/18), at
`5cc944a5441c2cbcd12385bfb575f4976c994347`, supplies the generic multilinear-table and
aligned-stacking prerequisite. The reuse-catalog corrections in
[#25](https://github.com/Verified-zkEVM/leanerVM/pull/25) and coefficient transport in
[#26](https://github.com/Verified-zkEVM/leanerVM/pull/26) merged into that branch only.
Adoption into it remains with its owner; the branch has not landed on `main`.

## Contributions awaiting review or adoption

These six pull requests are open and marked ready for review. The five targeting
`feat/leanth-reuse` need owner adoption or a CI-trigger change to run upstream Lean CI, whose
pull-request trigger currently targets `main`.

| Contribution | Pull request | Base and scope |
| --- | --- | --- |
| Claims on arbitrary committed columns | [#38](https://github.com/Verified-zkEVM/leanerVM/pull/38) | #18; weight-table pairing and block locality after coefficient transport |
| Symbolic tuple fingerprints | [#39](https://github.com/Verified-zkEVM/leanerVM/pull/39) | #18; injective symbolic encoding, separate product challenge, coefficient transport |
| Ambient stack evaluation with arbitrary padding | [#40](https://github.com/Verified-zkEVM/leanerVM/pull/40) | #18; includes uncovered padding weight for zero- and one-padded stacks |
| Fixed public-column evaluation | [#41](https://github.com/Verified-zkEVM/leanerVM/pull/41) | #18; index and explicit-program bytecode evaluations equal their oracle answers |
| Honest sumcheck polynomial algebra | [#42](https://github.com/Verified-zkEVM/leanerVM/pull/42) | main; Boolean suffix sums, polynomial transport, high-first order and selected-coordinate degree |
| Power-batched weight-table pairing | [#43](https://github.com/Verified-zkEVM/leanerVM/pull/43) | #18; zero-based powers, pairing and the `(J - 1) / |F|` collision bound |

Three child contributions have complete source: a fresh-challenge batching game after a
probabilistic prefix ([#31](https://github.com/Verified-zkEVM/leanerVM/issues/31), after #43),
a rejecting single-round sumcheck knowledge result with a fixed extractor and honest completeness
([#37](https://github.com/Verified-zkEVM/leanerVM/issues/37), after #42), and symbolic multiset
products with collision bounds ([#33](https://github.com/Verified-zkEVM/leanerVM/issues/33),
after #39). Their branches await the corresponding parents' adoption into upstream base
branches before separate pull requests can show just the child changes. They are not landed.

The multiset-product result fixes both multisets before a uniform joint challenge is sampled.
It retains natural multiplicities in every characteristic and gives `4 * cap / |F|` for
sixteen-coordinate tuples. It does not supply conditional freshness for recycled challenges.
The batching and single-round knowledge results do not assemble the full virtual or
multi-round sumcheck protocol.

## Upstream contributions

- [VCVio #784](https://github.com/Verified-zkEVM/VCVio/pull/784) landed the random-oracle query
  controls and the counterexamples separating component soundness from target refinement,
  superseding [#767](https://github.com/Verified-zkEVM/VCVio/pull/767) and
  [#768](https://github.com/Verified-zkEVM/VCVio/pull/768). Current VCVio main retains these
  controls. The positive shared-oracle product-extraction theorem
  remains open in [#30](https://github.com/Verified-zkEVM/leanerVM/issues/30).
- [Clean #466](https://github.com/Verified-zkEVM/clean/pull/466) supplies the expression-polynomial
  evaluation and degree bridge for [#28](https://github.com/Verified-zkEVM/leanerVM/issues/28).
  It remains open and approved. Squash merge requires a maintainer with merge
  permission; it has not been merged or adopted into leanerVM's pin.
- Current sumcheck work follows [ArkLib #1](https://github.com/Verified-zkEVM/ArkLib/issues/1).
  The operational game already exists on current ArkLib.
  [#1128](https://github.com/Verified-zkEVM/ArkLib/pull/1128) adds polynomial substitution and
  selected-coordinate degree lemmas;
  [#1129](https://github.com/Verified-zkEVM/ArkLib/pull/1129) adds executor regression controls.
  Both are open for review, separately from the pinned compatibility in #42.
- [ArkLib #615](https://github.com/Verified-zkEVM/ArkLib/pull/615) remains open and unavailable at
  the pinned revision. Separate compatibility probes check its `gammaPowers` correspondence
  and rejection through guarded append; they do not make it a dependency of the pinned ports.
- [ArkLib #900](https://github.com/Verified-zkEVM/ArkLib/issues/900) tracks stacking algebra;
  [#901](https://github.com/Verified-zkEVM/ArkLib/issues/901) tracks fingerprints and multiset
  products. Generic leanerVM modules remain local until their upstream adoption and a reviewed
  pin update.

The derived algebra retains the attribution documented in
[the prerequisite branch’s reuse catalog](https://github.com/Verified-zkEVM/leanerVM/blob/5cc944a5441c2cbcd12385bfb575f4976c994347/docs/roadmap/leanth-reuse.md), from
[leanth #16](https://github.com/Verified-zkEVM/leanth/pull/16) at
`23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`. Existing source notices, file authors and commit
coauthors are preserved; newly written controls do not expand the original results' scope.

## Roadmap coverage and remaining work

| Layer | Current status |
| --- | --- |
| 0 — dependency and field instances | Landed on main |
| 1 — tables, stacking and public columns | Generic prerequisite in #18; further algebra and public evaluations under review; concrete assembly remains |
| 2 — Clean components as polynomials | Expression bridge under review upstream; operation/ensemble polynomial assembly remains |
| 3 — M3 instance | leanISA constraint statement landed; protocol-specific layout and witness assembly remain |
| 4 — virtual sumcheck and batching | Honest algebra and batching under review; single-round child results prepared; full virtual/multi-round protocol remains |
| 5 — fingerprints, grand product and GKR | Fingerprints under review; multiset-product child prepared; concrete bus wrappers, product trees and GKR remain |
| 6 — bus phase | Open; needs the concrete M3 and grand-product/GKR interfaces |
| 7 — table sumcheck phase | Open; needs the bus phase, virtual sumcheck and operational challenge argument |
| 8 — public-input phase | Open; fixed public-column evaluations alone do not assemble the phase |
| 9 — Flock and ring switching | Open protocol interface; coordinated through [the Flock roadmap](https://github.com/Verified-zkEVM/leanerVM/issues/3) |
| 10 — claim pool, opening and oracle protocol | Open; composition and extraction interfaces remain |
| 11 — WHIR, Merkle and parameters | Open; requires its protocol, commitment and coding-theory interfaces |
| 12 — compilation, transcript and verifier | Open; requires the composed protocol and cryptographic interfaces |
| 13 — base-proof extraction, completeness and fixtures | Open; requires the compiled protocol and leanISA extraction |

The remaining assembly choices include statement versus parameter placement, where to charge
the recycled-point zerocheck error, and the executable honest prover's shape. Full ensemble
reconstruction, positive product extraction, recycled-challenge freshness, recursion extraction,
and unconditional end-to-end soundness are not established by these contributions. Witness
generation from executions, zero knowledge, and the other exclusions in the blueprint retain
their existing scope. No base-proof extraction or completeness theorem is claimed complete.

## Historical source findings

The findings and survey below record the pinned-source audit of 2026-09-10. Their original
labels are retained for existing citations. They are not claims about current upstream main
or a fresh validation receipt; the current contribution status is given above.

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

**ArkLib** (`dca90385`). A1–A9 refer to the original blueprint ledger. Further: A10 relations are `Set (Stmt × Wit)`;
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

## Historical survey record

Scope of the 2026-09-10 survey; retained as historical evidence.

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
