# Archive: the proof-system survey record

The survey log of [protocol-status.md](../roadmap/protocol-status.md) up to `main` at `144c5aa`
(2026-09-29), moved here unchanged when the status was reduced to what is built. It records what
was read, and when, so that the searches are not repeated; it is history, not a source of truth.
Names, paths, codes and line numbers are those of the day each entry was written; the blueprint
is the specification. One claim below is known false: "each of five wrong verifiers breaks a
stated theorem" does not hold of the merged public-input phase, whose check is not load-bearing
while the verifier pools the values it computes (the blueprint, Layer 8).

- **2026-09-29, the adversarial review of the public-input phase** (the `adversarial-review`
  skill, a context-free agent; [public-input-phase.md](../reviews/public-input-phase.md)): no
  theorem wrong or vacuous, and each of five wrong verifiers breaks a stated theorem. Findings,
  all met on the branch: the documents' claim that the two checks are equivalent on evaluations
  of `K`-valued columns was false (B1: finding F18, with a test); the output dropped a claim on
  a short message (A1: one output, `PublicInput.pooled`); `sent` was bound by nothing (A2:
  `PublicLine.sent`, decision 15, and a test in the shape of the memory limbs); three proofs
  rested on the normal form `simp` happened to leave (C1: the shared lemmas of
  `ToArkLib/GuardedVerdict.lean`, explicit `simp only` lists, no restated goal); ten unprefixed
  names (C2: `namespace PublicInput`); the audit surface (H1 to H6: 35 public declarations to
  23 in the phase module). The same day the branch was merged with Layer 1 (#59): nine conflict
  hunks, in the two aggregate imports and in this file, none in a Lean proof; the phase's
  private helper for the zero point duplicated `evalMle_boolVec` and is gone, the line identity
  being derived from `evalMle_append_boolVec`.
- **2026-09-29, the public-input phase rebuilt as §8.2 writes it.** The first build
  (2026-09-28) had no prover message: the verifier computed the lines' values and pooled them.
  On the user's instruction the phase has the specification's transcript: a challenge, the
  prover's values, a check that can reject. Read: `cpu/mod.rs:745-755` (the two scalars and the
  equation on the words, finding F18) and `:611-613` (the pinned prover computes the two values
  from the public words); `ProofSystem/ToyProblem/Spec/General.lean` (a three-round verifier
  that reads a prover message through `OracleSpec.query` and guards, `:493-527`, and the staged
  simulation of its body, `:563-640`); `ProofSystem/Component/{SendClaim,CheckClaim}.lean`
  (ArkLib's oracle versions keep the verifier pure and carry the check in the output relation,
  which the spine's fixed seams rule out here); VCVio `SimSemantics/OptionT/Basic.lean`
  (`simulateQ_optionT_bind_run` `:49`, `simulateQ_optionT_failure` `:214`); ArkLib
  `Data/Fin/Basic.lean` (`Fin.induction_two` `:93`),
  `Security/CoordinateWiseSpecialSoundness/Guarded.lean` (`GuardedForm` `:112`).
- **2026-09-28, building the public-input phase (P5).** Specification §8.2
  (`08-end-to-end-protocol.tex:27-33` at the pin: `c_ℓ = (1 + r_m)·mem[g⁰]_ℓ + r_m·mem[g¹]_ℓ`,
  error `1/|E|` by Lemma 3.8, Schwartz-Zippel, on a polynomial of degree one); ArkLib
  `OracleReduction/Execution.lean` (`Prover.run_of_verifier_first` `:642`,
  `Reduction.run_of_prover_first` `:663`, `Reduction.support_run_pure_verifier` `:343`),
  `Security/RoundByRound.lean` (`KnowledgeStateFunction` `:164`, its `toFun_next` for prover
  rounds only, `rbrKnowledgeSoundnessWorstCaseWith` `:553`, the event quantified over the
  intermediate witness), `Security/Basic.lean` (`perfectCompleteness_of_run_support` `:193`),
  `ProtocolSpec/Basic.lean` (`Transcript.concat` = `Fin.snoc` `:519`), `Basic.lean` (`PureForm`
  `:1011`); VCVio `SampleableType.lean` (`probEvent_uniformSample` `:225`:
  `Pr[p | $ᵗ α] = |filter p| / |α|`); CompPoly `Multilinear/Basic.lean` (`evalMleLayer_get`
  `:482`, `evalMle_succ` `:512`), `Fields/Binary/BF64/Ext3.lean` (`CharP Ext3 2` `:171`, used for
  `1 - r = 1 + r` in `E`), `Fields/Extension/Field.lean` (`Fintype (Ext P)` `:60`,
  `Field (Ext P)` `:159`).
- **2026-09-29, the adversarial review of Layer 1 at `8bc9bbd`** (the `adversarial-review`
  skill, three context-free agents, one per pass, so that fidelity was read from the pinned
  sources before any Lean; [protocol-layer1.md](../reviews/protocol-layer1.md)): no theorem
  false, vacuous or of the wrong strength. Specification: `BlockClaim` unusable by a phase over
  an abstract instance and unrelated to the spine's `Weight.pair` (A1, met by
  `ClaimWeights.lean`); `Blocks.layout` not of the type of `M3Instance.layout` (A2, met by
  `Layout.comap` and the toy instance with the aligned layout in its field);
  `bytecodeColumn_slot` provable on the opposite bit order (A3, met by
  `bytecodeColumn_answer_boolVec`); three weak tests (A4 to A6, met). Fidelity: every object is
  the leanVM object, checked numerically against the pinned Python verifier; the order of equal
  sizes (B1: findings S15, F17), "equation (5.4)" (B3: finding S16), two citations (B2, B4).
  Documentation: sixteen mismatches between the roadmap documents and the branch, applied here.
- **2026-09-29, consolidating Layer 1** (#59). Read in full: #18 at `5cc944a` (with #25, #26),
  #38 at `ea71db8`, #40 at `574d346`, #41 at `124d124`, and their tests; the specification at
  the pin, §4.1 (`04-committing-the-witness.tex:4-18`), §5.4 (`05-arithmetization.tex:97-109`),
  §6.5 (`06-bus-interactions.tex:95-100`) and §8.1 (`08-end-to-end-protocol.tex:4-25`), against
  which `stack_eval`, `stack_eval_ambient`, `idxColumn_eval` and `bytecodeColumn_slot` were
  checked. The nine commits cherry-pick onto `main` with conflicts in the two import aggregates
  and the documentation only; the Lean files are byte-identical to the pull requests' heads
  before the adaptation commits. Adaptation: the one build repair (E14); the move of
  `Multilinear`, `PowerColumn`, `Stacking`, `AmbientStacking` and `Claims` to `ToCompPoly/`
  (the last three first to `ToArkLib/`, corrected the same day: finding E16), then the
  generic refactor of finding E17; roadmap bookkeeping removed from the docstrings; `idxColumnEval_eq`,
  the characteristic-two form of §6.5 the roadmap states; `Stack.lean` and its tests. The
  per-file copyright and author notices of #38 and #40 are kept as their author wrote them,
  although `CONTRIBUTING.md` asks for the repository history instead: a decision for the
  maintainer.
- **2026-09-28, the adversarial review of the spine at `00ab835`** (the `adversarial-review`
  skill, a context-free agent; [protocol-spine.md](../reviews/protocol-spine.md)): no theorem
  statement wrong; five interface findings, all applied on the branch: the bus seam admitted
  linear claims of any degree (A1: `d`, `K` terms with `E` weights, the degree conjunct), the
  Flock predicate was under-determined (A2: the strong reading, decision 12), the knowledge
  theorem did not name its extractor (A3: the `With` form, `piopExtractor`), a list of public
  cells cannot be served by the public-input phase (A4: `PublicLine`), and the adaptor's
  soundness theorem needs the caps (A5: `s.Admissible` a hypothesis); and six compressions (H1 to
  H6: `Shape`, derived `Decidable` instances, `Seam.of`, a one-line `read_eval`, a shorter
  `guardedAppend`, the pass-through's knowledge half), also applied. Read: ArkLib #615's
  `Append/Knowledge.lean` at `ca7a2577`, ported the same day to
  `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean` (verbatim under `LeanerVM.Protocol`, except
  that its two witness lemmas reuse the pinned ArkLib's proofs, and without the wrappers into the
  existential and averaged forms); the history of `05-arithmetization.tex` at `63b6fe01`
  (S13, S14); the six tables' read gadgets for the count columns (`memRead`, `bytecodeRead`:
  every Layer 6 table passes `count` as a column).
- **2026-09-28, comments and the `To*` folders.** Every comment of the spine rewritten to be
  brief and self-contained (no roadmap references); the parts that belong in ArkLib moved to
  `LeanerVM/Protocol/ToArkLib/` (`Oracles`, `Component`, `PassThrough`, `SendOracle`,
  `Refinement`), the commit phase and the pass-through phase generalised there over any
  statement, message and oracle family; convention *Generic code* now names the `To*` folders,
  which #38 to #43 should adopt on rebase (`Generic/` becomes `ToArkLib/` or `ToCompPoly/`).
- **2026-09-25, the adversarial review of the spine** (a context-free agent, the
  `adversarial-review` skill): no theorem statement wrong or vacuous; findings applied: two toy
  mutations did not isolate their clause (now tested at statement `2`, and a char-2 balance
  witness `badBalanceSum` added), `Phases`/`Phases.Complete` had no inhabitant (now
  `trivPhases`/`trivComplete` from `Phase.passThrough`), citation drift (§6.2 for `R_c`,
  Definition 3.13, §5.4 equation (2)), the `Layout` docstring now says it is a reading law, the
  knowledge theorem's docstring names ledger A3 for its plain reading, this roadmap's
  `Seam.pool`/`knowledgeSound_of_refinement`/`prog, sizes` leftovers fixed. Observation kept:
  the non-table stack columns are instance tables without constraints (Layer 3 sketch).
- **2026-09-25, building the spine.** ArkLib `Composition/Sequential/{Append/Basic,
  Append/Completeness,Append/Security,Append/RoundByRound,OracleCompleteness}.lean`
  (`OracleReduction.append`, `append_perfectCompleteness_of_guarded_verifiers` proved,
  `append_rbrKnowledgeSoundness` admitted, `append_rbrSoundnessWorstCase_of_pure_first`
  proved), `Security/{Basic,RoundByRound,Implications}.lean` (`rbrKnowledgeSoundnessWorstCase`,
  `KnowledgeStateFunction`, `Extractor.RoundByRound`; `rbrKnowledgeSoundness_implies_knowledgeSoundness`
  admitted, ledger A3), `CoordinateWiseSpecialSoundness/Guarded.lean` (`GuardedForm`, its
  `append`), `ProofSystem/Component/SendWitness.lean` (the commit shape; its oracle completeness
  is admitted upstream, proved here for `commitDef`), `OracleReduction/Basic.lean`
  (`OracleOutputEmbedding`, `toVerifier`, `materializeOutput`); CompPoly
  `Multivariate/{CMvPolynomial,Lawful,MvPolyEquiv/*}.lean` (`CMvPolynomial`, `eval`,
  `totalDegree`, `fromCMvPolynomial` with `eval_equiv`) and `Multilinear/Basic.lean`
  (`evalMle_succ`, `evalMleLayer_get`); leanth `db895db` `Protocol/{Spec,Stacked,Relation,
  Witness,Zerocheck,PCS,Measures}.lean` and `23929f8c` `Security/{Relation,Protocol}.lean`
  (`Refinement`, `knowledgeSound_mapRelation`); the descriptions of every open pull request
  and issue of this repository (the table above).
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
- **leanth** (private, pull request #16, branch `leanth-project` at `23929f8c`; audit branch
  `scaraven/leanth-project-audit`): surveyed 2026-09-10 in eight clusters, every load-bearing
  declaration read with its proof; the result is [leanth-reuse.md](../roadmap/leanth-reuse.md). Its
  security framework is on `PMF`, not ArkLib (only `ProtocolSpec` and `CommitmentScheme.Basic`
  are imported); its cube indexing is big-endian in `Shift`, `Stacking` and `Residual` and
  little-endian elsewhere; no `sorry`, no axiom, extraction by `Classical.choose`; the
  production WHIR pins are refuted on the audit branch. ArkLib at `dca90385` has no
  `ProofSystem/Whir/` directory (ledger A7 confirmed).
- **Environment**: `lake update Arklib` cloned Arklib, VCVio, PolyFun, loom2, cslib, leansqlite,
  UnicodeBasic, BibtexQuery, MD4Lean, doc-gen4 and checkdecls and ran Mathlib's cache hook
  (no download; the same revision). The first build of the OracleReduction cone compiled
  ToMathlib, cslib, PolyFun and VCVio's `OracleComp` modules in about fifteen minutes on the
  author's machine before the plugin race (E6).
