# Dependency policy

The repository tracks eight upstreams and six direct Lake packages:

| Component | Tracked ref | Role |
| --- | --- | --- |
| Lean | `v4.35.0` | Root toolchain |
| Mathlib | `v4.35.0` (`56a00585`) | Algebra, finite types, probability measures, and tactics |
| leanVM | `a386121f84292f6fa663aaa3e570c15bc0240ea2` | Audited Rust/specification target; not a Lake dependency |
| CompPoly | `e28da34817c3775cfb935376acf5d416f555d64f` (current main) | Computable polynomial and field infrastructure |
| Clean | `a985c76c845e1d69ab320831d535072fcadb7c76` (current main; needs Clean #513, see below) | Circuit, AIR, channel, and witness-generation infrastructure |
| ArkLib | `011391e592df184540b4b52edc2c64ee300b00ab` (current main) | Oracle reductions, security definitions, composition, sumcheck, and multilinear theory |
| VCVio | `fc54dd3d7691d6f5db7dc829e321a727f095bc2d` (ArkLib main's pin) | Native probability measures and oracle computation security carriers |
| PolyFun | `d3ec3a414c233203e2050ed0f33fae8647f57eb7` (ArkLib main's pin) | Polynomial functors and free monads underlying oracle computations |

The machine-readable baseline is `upstreams.json`; `lake-manifest.json` records the resolved
Lake graph. The weekly drift workflow reports newer releases or commits but never rewrites
dependency files automatically. The leanVM pin names the exact behavior being formalized and
tested even though its branch is monitored for drift. See
[leanvm-target.md](leanvm-target.md) before updating it.

A `lakefile.toml` change that adds or edits a first-party target (a `[[lean_lib]]` or
`[[lean_exe]]` over this repository's sources, such as `LeanerVMBench` and `leanervm-bench`) is not
a dependency change and needs none of the review below; see
[development.md](development.md#benchmarks).

Add a dependency only with a named first-party use and a narrow import. A dependency PR must:

1. update the toolchain/Lake requirement, `upstreams.json`, and manifest together;
2. build and test the complete affected import cone;
3. review API changes used by theorem statements;
4. audit the first-party namespace's transitive kernel dependencies;
5. record semantic changes separately from mechanical porting; and
6. delete every `LeanerVM/Protocol/To*/` and `LeanerVM/Parameters/To*/` file or declaration that
   the new pin contains, move its consumers to the upstream names, and update the protocol
   blueprint's upstream ledger and the status page's watch list.

## Lean 4.35 port review

The previous baseline was Lean and Mathlib `v4.34.1` (`d13f23b7`), CompPoly `572f9973`, Clean
`ce2eee63`, ArkLib `7653a901`, VCVio `a4232d08` (the compatibility commit of VCVio #820 over
`f5119c64`) and PolyFun `41d3b21d`. Lean and Mathlib move to `v4.35.0`, the release every upstream's
manifest requires (Mathlib `56a00585`), so the root Mathlib requirement agrees with the inherited
ones. ArkLib, Clean and CompPoly move to their current main. VCVio and PolyFun move to the
revisions ArkLib's main pins, `fc54dd3d` and `d3ec3a41`, not to their own main: VCVio's later
commits refactor `simulateQ` and its program logic, and ArkLib `011391e5` is built against
`fc54dd3d`. #820 is upstream in that range (`bc3433e3`), so the compatibility pin is retired.
CompPoly `e28da348` overrides ArkLib's requirement `a1ac8925` and Clean's `06686e4c`; the two
commits past ArkLib's (#406, #409) change only documentation and CI. VCVio #921 brings a new
transitive package, QuantumFoundations (`901aaab7`).

Regenerate the graph with plain `lake update`, then fetch Mathlib's artifacts with
`lake exe cache get`, and check the resolved revisions in the manifest. Do not use
`lake --keep-toolchain update`: in Lake 4.34 that option also changed dependency traversal, so
that an inherited manifest could resolve a package before a later root requirement.

**The Clean import clash.** At `a985c76c`, `Clean.Utils.Vector` declares
`Vector.get_eq_getElem`, which `Batteries.Data.Vector.Lemmas` also declares with the same
statement. A module whose imports reach both fails at import; `ToClean/ComponentPolynomial.lean`
reaches Batteries' through CompPoly's multivariate polynomials. Clean PR #513 deletes Clean's copy
and imports Batteries' lemma. Until it merges, `a985c76c` does not build this repository unpatched:
the port was built with #513's change applied to the package checkout, and the committed manifest
names `a985c76c` with no local override. Owed: when #513 merges, move the Clean pin to its merge
commit (`lakefile.toml`, `lake-manifest.json`, `upstreams.json` and this page).

The semantic changes were reviewed separately from the mechanical port (renames, imports, proof
steps). None changes the statement of a headline theorem, `verify`, `prove`, `SatisfiedBy`,
`ValidExecution`, `PaddedFrom`, `Trace.Fits` or `WellFormedBytecode`.

* **ArkLib #1373: a one-way initial law.** `Extractor.RoundByRound.eqIn : WitMid 0 = WitIn` is
  replaced by a field `extractIn : StmtIn → WitMid 0 → WitIn`, and the initial law of a knowledge
  state function is now one-way, `toFun 0 s default w → (s, E.extractIn s w) ∈ relIn`; it was an
  equivalence through `cast eqIn`. A knowledge state function owes less, so `Component.Security`,
  every phase certificate built on it, and `piop_rbrKnowledgeSoundness` are weaker statements than
  at the old pin. No local proof used the dropped direction. No headline theorem moves: they are
  stated on `verify` and `extract`, not on state functions. The local full-transcript extraction
  is rebuilt on ArkLib's `foldPrefix` as `Extractor.RoundByRound.extractFull` (the local name
  `extractIn` would collide with the new field), and `ReadsFirst` and `DecodesFirst` read the fold
  from round 1, which is the first step for every extractor here (their `extractIn` is the
  identity).
* **ArkLib #1413 and #1421: names.** The fixed-prefix round-by-round notions are
  `rbrKnowledgeSoundnessWith` and `rbrKnowledgeSoundness` (formerly
  `rbrKnowledgeSoundnessWorstCaseWith` and `rbrKnowledgeSoundnessWorstCase`), with unchanged
  bodies; #1421 deletes the averaged and one-shot notions, which nothing here used.
  `Component.rbrKnowledgeSoundnessWorstCaseWith_of_eq` follows as
  `Component.rbrKnowledgeSoundnessWith_of_eq`.
* **ArkLib #1347.** `knowledgeSoundnessWith` quantifies the type of the prover's auxiliary input,
  so `Refinement.knowledge_transport` now holds for every prover: a stronger statement.
* **ArkLib #1295, adopted.** `ToArkLib/KnowledgeAppend.lean`, the port of #615, is deleted. Its
  consumers use `Composition/Sequential/Append/GuardedRoundByRound.lean`:
  `Verifier.append_rbrKnowledgeSoundnessWith_of_guarded_first`,
  `KnowledgeStateFunction.appendGuarded` and `Transcript.fstUpTo`/`sndUpTo`, the same theorem with
  the same extractor, error and witness family. ArkLib's `OracleVerifier.appendGuardedForm`,
  `Verifier.GuardedForm.check_and_of_prEvent_pos`, `Verifier.GuardedForm.prEvent_pos_of_check` and
  `Reduction.run_eq_of_guarded_verifier` replace local lemmas of the same content.
* **ArkLib #1344, adopted.** `ToArkLib/TupleCompiledForms.lean` and `ToArkLib/AppendLazy.lean` are
  deleted: ArkLib's `@[csimp]` forms of `Fin` tuple appends (`ArkLib.Data.Fin.Tuple.Lemmas`) read an
  entry by one comparison with the seam, and ArkLib compiles its appended-schedule instances and
  `FullTranscript.append` after them.
* **ArkLib #1423 and `ReduceClaim`, adopted.** The commit phase's component
  (`ToArkLib/SendOracle.lean`) is `SendSingleWitness.Adapter` at the identity: the adapter's
  prover, verifier, transcript extractor, knowledge state function, zero-error bound and perfect
  completeness. The pass-through and map-witness components (`ToArkLib/PassThrough.lean`,
  `ToArkLib/MapWitness.lean`) are `ReduceClaim.oracleReduction` at the identity embedding of the
  oracles, with its completeness, `ReduceClaim.extractor` and its knowledge state function. The
  verifiers are definitionally the old ones and their pure forms keep their verdicts; the
  pass-through and map-witness provers equal the old ones, and the commit prover keeps the
  statement beside the message (`(S × ∀ i, NoOracle i) × M` for `S × M`) with the same run. The
  extractors return the same values. One signature narrows: `Component.mapWitness`'s witness map
  reads the statement and the witness (`StmtIn → W → W'`), not the oracles, as `ReduceClaim`'s
  does; all three consumers ignored the oracles, and their statements are unchanged.
* **VCVio's measure-only probability API** (#829–#837, names standardized by #839). The discrete
  layer is removed. `prEvent mx` is the mass the output measure of a `Prop`-valued computation puts
  on `True`, and `Pr{let x ← mx}[p x]` elaborates the last draw to a map, `prEvent (p <$> mx)`; the
  headline mixtures over coins are therefore folded with `map_bind`. Modules are renamed
  (`SampleableType/NativeMeasure` to `SampleableType/Measure`; `StateT/Basic/Native` merged into
  `StateT/Basic`), and `OracleComp.prEvent_mono_of_support` gives way to the root
  `prEvent_mono_of_support` with explicit events. These change proof terms only. VCVio's
  `docs/agents/probability-migration.md` lists the symptoms.
* **VCVio #817 and #766, adopted.** #817's scalar-expectation laws are upstream, so the verbatim
  copy `ToVCVio/ScalarExpectation.lean` is deleted. `ToVCVio/ChargedInvariant.lean` is rebuilt on
  #766's budgeted supermartingale bound `OracleComp.lintegral_run_le_of_isQueryBoundP`, every query
  charged (`isQueryBoundP_true_iff`). The charged oracle and its expected-charge bounds are
  deleted. `QueryHistory.prEvent_le_of_potential` and `QueryHistory.prEvent_bind_le_of_potential`
  now take a query bound `n` and a per-query bound `κ` that need hold only within the budget, and
  conclude `Φ s + n * κ` (plus `ε` for two runs); as statements they are incomparable to the old
  ones, and each consumer (`ProofOfWork`, `HashMisbehaves`) reaches the same final bound.
  `ToVCVio/RandomOracleReplay.lean` is deleted for #766's caching lemmas
  (`QueryImpl.le_snd_of_mem_support_run_simulateQ_withCaching`,
  `QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching`,
  `QueryCache.evalWithAnswerFn_eq_of_agreesWithFn`).
* **VCVio #858: `QueryLog.Consistent`.** The local predicate of that name (`ToVCVio/QueryLog.lean`)
  is deleted for VCVio's `OracleSpec.QueryLog.Consistent` (`QueryTracking/QueryLogCheck.lean`):
  two entries with the same query are equal. On a log of one function, `X →ₒ Y`, this is the
  local form, two entries with the same input have the same answer (`consistent_iff`), so every
  statement that assumed it, among them the headline hypotheses of `Headline.lean`, keeps its
  meaning. The text of the headlines is unchanged: `Headline.lean` opens `OracleSpec`, so
  `QueryLog.Consistent g.log` now names VCVio's predicate. Its `Decidable` instance and
  `Consistent.of_prefix` stay in `ToVCVio/QueryLog.lean`, stated for any oracle specification.
* **Upstream lemmas in the polynomial and random-oracle modules.** `card_false_batch_le` counts the
  roots of Mathlib's `Polynomial.ofFn` with CompPoly's `card_eval_zero_le_natDegree`, so the
  difference polynomial `batchDifference` and its degree bound are deleted; `powerBatch_sub` moves
  from `Whir/Glue.lean` to `ToCompPoly/PowerBatching.lean`. `QueryHistory.enncard_le_of_mem_support`
  is VCVio's `IsQueryBoundP.resource_le_add_of_mem_support_run_simulateQ`, and the no-oracle and
  guarded-verifier facts of `ToArkLib/RunCodec.lean`, `Refutation.lean` and `SendChecked.lean` are
  ArkLib's `eq_pure_runEmpty`, `completeness_iff_of_guarded_verifier` and
  `toVerifier_verify_of_query_guard`. `pow_eq_prod_testBit` holds in any commutative monoid (it was
  stated for commutative rings), a stronger statement; it replaces the private copy in
  `FlockFields.lean`. The statements of the consumers are unchanged.
* **Clean's prover data.** `ProverData` is a structure `{tables, publicInput}` (with
  `ProverData.empty` and `publicEnvironment`), `deriveProverData` takes the public input (the old
  function is `deriveTables`), and `Circuit.witgen` and `proverEnvironment` take the data (#511).
  `witnessOfTables_data` is restated with the public input, with the same meaning.
* **Clean's balance without an interaction bound** (`21247235`). `Balance.multiset` is the
  multiplicities `0` or `1` and the permutation of active pushes and pulls; it no longer requires
  fewer than `FiniteField.size F` interactions per channel. `SatisfiedBy` keeps its text and its
  meaning: the old relation is the new one together with "each channel has fewer than `2^64`
  interactions", and that conjunct follows from the field `caps` for each of the three channels.
  The test theorem `interactionsWith_length_lt` (`tests/LeanerVMTests/Protocol/LeanIsaSound.lean`)
  proves it from `caps`, and `balanced_multiset_iff_bounded` there states Clean's balance in its
  old form within the caps. The production proofs of the bound (`padSends_length_lt`, the
  library's `interactionsWith_length_lt`, the `hlen` hypothesis of `padWitness_balanced`) are
  deleted, and `balanced_multiset_iff` states the three permutations.
* **Clean #511 and the field instance.** `jump_exec_complete` is stated in Clean's honest
  environment `proverEnvironment`, so the hand-built `jumpEnv` is deleted and `jump_env_iff` moves
  to the tests (only tests consume the theorem). The restatement is a choice, not forced by #511:
  its relation is the soundness-side `Operations.ConstraintsHold` (the one `SatisfiedBy.constraints`
  reads, through `constraintsHold_of_usesLocalWitnesses`) rather than
  `ConstraintsHold.Completeness`, and the row enters as the cell variables `varFromOffset JumpRow 0`
  rather than as constants. It is not weaker. The test theorem `jump_proverEnvironment_slots`
  (`tests/LeanerVMTests/Arithmetization/Tables.lean`) applies `jump_env_iff` to Clean's honest
  environment: on every row it holds `v_cond⁻¹` (or `0`) and `[v_cond ≠ 0]` in the two witness
  slots. `Parameters/CleanField.lean` and `instFiniteFieldK` are deleted for Clean's
  `instFiniteFieldBF64` (`Clean.Utils.BinaryField`), whose `val`, `fromNat` (`K.ofBits`) and `size`
  agree by `rfl`.
* **Hypotheses dropped: stronger statements.** `Component.passThroughSecurity`
  (`ToArkLib/PassThrough.lean`) and `Phase.passThroughSecurity` (`Spine/Phase.lean`) no longer take
  the forward hypothesis that `f` carries `relIn` into `relOut`: it fed only the certificate's
  `guarded` field through `passThroughComplete`, and that field is
  `(passThroughPure OStmt f).toGuardedForm` either way, so it is now built directly.
  `Flock.pointDrawsSecurity` drops `hIn` for the same reason. `Whir.listBound_johnson` drops
  `2 ^ κ ≤ a`; ArkLib's `pairwiseJohnsonListBound` has the same body at both pins, so the list bound
  is the same number. The cache form of `enncard_le_of_mem_support` is deleted; its consumer
  (`HashMisbehaves`) uses `QueryHistory.enncard_le_of_mem_support`, the same bound for every query
  history.
* **Lean 4.35's `Vector` and `Array` equality (finding L1).** Core derives `Vector`'s
  `DecidableEq` with `@[expose]` and exposes `Array`'s, so `decide` and the kernel reduce
  equalities of vectors across module boundaries. The `CompressCells` instance unfolds to the
  conjuncts' instances and the BLAKE2s tests decide vector equalities directly; the kernel time is
  unchanged.
* **Lean 4.35's `Fin.foldl` (finding L2).** `Fin.foldl` is structural, compiled through
  `@[csimp] Fin.foldl_eq_foldlTR`, and reduces in the kernel and in `whnf`. Products in `K` fold
  over `Fin`, so elaborator-side `rfl` and `decide` on `K` arithmetic now unfold further and can
  exhaust the recursion depth; those sites rewrite first or decide in the kernel. `congr 1` now
  closes goals in `Vector R 0`.
* **Mathlib's private imports.** Many of Mathlib's `public import`s became `import`s, so names stop
  reaching modules transitively. Direct imports are added where a module used one:
  `Mathlib.Data.List.GetD` (`List.getD_eq_getElem`), `Mathlib.Control.Lawful` (the `ExceptT` simp
  lemmas) and `Batteries.Control.Lemmas` (`StateT` lemmas). No Mathlib name that the repository uses
  is deprecated or removed.

CompPoly #404 and #405 supply facts leanerVM proved locally (see the CompPoly limits below); their
consumers' statements are unchanged.

## Dependency boundaries

CompPoly supplies leanVM's fields (see [leanvm-target.md](leanvm-target.md)):

- `K = GF(2^64)`: `CompPoly.Fields.Binary.BF64`, the flat quotient
  `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` on a computable polynomial-basis carrier, with
  Rabin-certified irreducibility;
- `E = GF(2^192)`: `CompPoly.Fields.Binary.BF64.Ext3`, the cubic extension
  `K[y]/(y^3 + y + 1)` on a `Vector BF64 3` carrier via `CompPoly.Fields.Extension`.

Since CompPoly `572f9973`, `BF64` is a structure wrapping `BitVec 64`, with characteristic-two
natural-number casts: `(2 : K) = 0`. Encoded words use
`K.ofBits n = BF64.ofBitVec (BitVec.ofNat 64 n)` instead. The generator remains the encoded word
`0x2`; BLAKE2s cells, Clean's `val`/`fromNat` interface, protocol fixtures, and exported Rust
contract fixtures retain their original bit coordinates. Regression tests distinguish casts from
encoded words explicitly. `DecidableEq K` compares bit coordinates through an equivalence proof: the
upstream derived wrapper instance makes kernel checks of computed words stall on dependent
transport. The existing register-equality regression checks this boundary without unchecked
evaluation. The `Fintype K` instance is proof-only; executable samplers use coordinate equivalences
without enumerating `2^64` words.

ArkLib's Lake package name is `Arklib`, which is what the `[[require]]` must say. Its first
consumer is `LeanerVM/Protocol/Field.lean`. VCVio is an explicit root requirement because the
`ToVCVio/` modules (for example `ChargedInvariant.lean` and `UniformSample.lean`) and
`ToArkLib/TranscriptMap.lean` consume its native measure and security interfaces. PolyFun is an
explicit root requirement for the free-monad carrier of the oracle computations used by
`LeanerVM/Protocol/ToArkLib/Oracles.lean` through VCVio. These requirements select current source
over the older revisions in inherited manifests. ArkLib also brings cslib, checkdecls, and
doc-gen4's dependencies into the graph, and VCVio brings QuantumFoundations. Tooling and
Mathlib-owned transitive packages retain the revisions selected by those upstream manifests.
The consumer tables and the upstream ledger
are in [roadmap/protocol-blueprint.md](roadmap/protocol-blueprint.md). Upstream admitted results
are not proof evidence: the first-party kernel axiom audit rejects `sorryAx` transitively,
including through upstream theorems. ArkLib's own axiom baseline is an allowlist, not a proof.

Package-level `leanOptions.warningAsError = true` rejects every first-party elaboration warning,
including imported production and test leaves. Tests deliberately remain classic and their
library has `allowNonModules = true` for full-body kernel checks; this does not relax
elaboration warning errors. CI and `scripts/validate.sh` use plain
`lake build` so Lake's dependency release-lookup warnings do not fail the build.
`scripts/test-warning-policy.py` verifies both positive builds and planted imported-leaf
warnings; it does not change upstream options. Mathlib's artifacts come from
`lake exe cache get` before building, since compiling all of Mathlib does not fit CI's time limit.
CompPoly's current source may have no matching release archive; its affected source is rebuilt
under the root Lean patch version.

Clean's first consumers are the leanISA table components in
[roadmap/leanisa-blueprint.md](roadmap/leanisa-blueprint.md); `K`'s `FiniteField` instance is
Clean's own `instFiniteFieldBF64` (`Clean.Utils.BinaryField`). Its core is generic over
`FiniteField F`; its `ZMod p` gadget tree is not used. `Expression` still has no degree bound.
Clean's pinned source and first-party Clean bridges now use Lean's module system; the
historical import restriction C8 no longer applies. Message-flattening proofs use Clean's
public normalization lemmas for its now sealed struct conversions. Small literal row equations
in the witness tests unfold those conversions explicitly; block equations compare rows
pointwise before applying `List.ofFn`, avoiding enumeration of the `2^16`-row memory block. See
[CONTRIBUTING.md](../CONTRIBUTING.md) and the historical finding C8 in
[roadmap/leanisa-status.md](roadmap/leanisa-status.md).

leanVM's existing `formal/xmss/` project is not imported wholesale. At the target revision it
uses Lean `v4.31.0` and VCVio revision `cbd4144`; moving that reviewed security theorem onto this
repository's dependency set requires a deliberate port and statement/correspondence review.

## Limits that bind the proof system

Facts about the pinned libraries that shape the [protocol blueprint](roadmap/protocol-blueprint.md),
checked at the pins of `upstreams.json` unless a line names another revision.

**ArkLib.**

- Relations are `Set (Stmt × Wit)`. `OracleReduction` is the framework ArkLib calls legacy. Its
  typed `Interaction` framework now has knowledge, round-by-round and state-restoration notions
  (`Interaction/Oracle/Security/`; #1259, #1260, #1473–#1481) and an embedding of the legacy
  framework (#1480) whose transfer of knowledge back to it yields a classically chosen extractor.
  Decision 24's condition for revisiting the framework has therefore fired; the revisit is owed,
  and until it is made the spine stays on the legacy framework.
- A round-by-round extractor is any function: the existential form `rbrKnowledgeSoundness` is met
  by an extractor chosen by classical choice (ArkLib's `Extractor.RoundByRound.ofRelation` is one)
  and proves soundness only; the named form `rbrKnowledgeSoundnessWith` is the one used. Both are
  fixed-prefix notions (#1413 gave them these names; #1421 deleted the averaged ones). An
  extractor's input witness passes through its field `extractIn`, and a knowledge state function's
  initial law is one-way (#1373).
- Admitted: nothing outside two solicited capacity-range results,
  `CodingTheory.exists_rs_epsCa_large_near_capacity` and `CodingTheory.rs_random_domain_lambda_le`
  (ArkLib issue #1352), on which ArkLib's baseline lets no other declaration depend. Proved since
  the previous pin: the guarded knowledge-soundness composition (#1295), the guarded
  round-by-round-to-plain bridges (`Security/GuardedBridges.lean`, #1349, which deleted the
  unrestricted implications), context lifting (#1371, #1374, #1380, #1395), Fiat–Shamir completeness
  (#1362), the classical sumcheck with its round-by-round knowledge soundness (#1244, #1382, #1391),
  and `rs_mcaError_le_in_johnson_range` (#1369). `Commitments/Functional/Basic.lean`'s
  extractability is a real experiment (#1422); the duplex-sponge Fiat–Shamir tree (#1368) and the
  legacy state restoration (#1409) are retired.
- Proved and usable: `ReedSolomon.mcaError_affineLine_johnson_le` (a Johnson-range correlated
  agreement bound with its own constant, any characteristic, no longer assuming `√ρ + η ≤ 1`),
  `johnsonExceptionCount_le_comparisonEstimate` (no longer assuming `1 ≤ D`), and
  `rs_mcaError_le_in_johnson_range` (any characteristic, at [BCHKS25]'s printed constant); the
  capacity-range theorems assume characteristic 0 or `k − 1 < ringChar F`, false over `E` (not
  rechecked at `011391e5`).
- `OracleInterface (Vector α m)` (position queries) is a global instance, so a column type with
  another interface is a structure, not an abbreviation of `Vector`; no default interface is
  registered for scalars or lists (`OracleInterface.instDefault` is for no type).
- The instances for the messages and challenges of two schedules side by side
  (`instOracleInterfaceMessageAppend`, `instSampleableTypeChallengeAppend`) are not found by
  instance search when the schedules are concrete; ArkLib's own files apply them by name, and so
  does `ToArkLib/Schedule.lean` (`msgAppend`, `chalAppend`).
- The typed framework's computable sumcheck (`ProofSystem/Sumcheck/Impl/Representation.lean`,
  `ProofSystem/Sumcheck/Interaction/Protocol.lean`, and the interaction-layer protocol
  `ProofSystem/Sumcheck/Core/` of #1474, perfectly complete and round-by-round sound, with no
  extractor) sums a round message, a polynomial with a degree bound queried by evaluation, over its
  domain with unit weights, and nothing adapts a protocol of the typed framework to an
  `OracleReduction`; the proof system's normalized round (`ToArkLib/SumcheckRound.lean`) sends the
  coefficients as one message and weights the domain. ArkLib's message contracts
  (`Sumcheck/Message/`: decoding may use the running claim, and a compressed quadratic message
  drops `c_1` on `{0, 1}`) and prover models are unit-weight and noncomputable in their model, so
  they do not replace the wire codec of `ToArkLib/Sumcheck.lean`.
- `lake build` with several explicit ArkLib targets can schedule `ArkLibLintPlugin:shared` twice
  and fail one link; a second build proceeds.

**CompPoly.** No hypercube sum and no pointwise product of tables (the proof system's Layer 1
supplies them). The polynomial-basis additive NTT is instantiated only at `GF(2^8)`. The coset
additive NTT and its inverse over any field and basis (`Fields/Binary/AdditiveNTT/Coset.lean`,
#405) act on functions `ℕ → V`, with no executable array form, and are not instantiated at `K`;
`Protocol/NovelBasis.lean` takes its subspace-polynomial facts (`vanishing`, `vanishing_add`,
`vanishing_succ'`, `vanishing_basis_ne_zero`) through a private bridge, and `Whir/Transform.lean`
keeps its own executable network. Boolean vertices and multilinear uniqueness
(`Multilinear/Unique.lean`, #404): `ToCompPoly/Multilinear.lean` takes `vertex`,
`lagrangeBasis_vertex` and `eval_vertex` (its `boolVec` is `vertex` by definition). No Frobenius on
`Ext`; the conversion of `CMvPolynomial` to Mathlib's `MvPolynomial` is noncomputable; inside a
`module`, `decide` cannot unfold `CMvPolynomial`'s `X` and `*`. `LawfulBEq (Ext P)` exists at
`e28da348`.

**Clean.** No degree notion. Table heights are an argument of `Ensemble.Statement`; with the
`.multiset` balance it is counted in ℕ, but it is existential over witnesses and lacks leanISA's
counts, caps, BLAKE2s validity and public words, so it is not the protocol's relation. #511 gives
per-circuit completeness as the existence of an environment and the honest environment
`FormalCircuitBase.proverEnvironment` (used for `JUMP`), and no ensemble-level completeness
theorem; the ensemble generator (`Clean/Air/WitnessGeneration`) has no correctness theorem, and no
leanerVM theorem uses it. leanISA's counted memory is not a Clean sound channel (Clean #494, open).

**VCVio.** Merkle trees with proved completeness and random-oracle extraction, for one opening
and for a sequence of commitments with path-pruned openings (`CryptoFoundations/MerkleTree/`,
`MultiExtractability/`), for leaves that are digests and an adversary that draws no coins; trees
with hashed leaves (`Hashing/`) come with binding only. `MerkleTreeHashing.QueryEncoding` (#858)
encodes leaves and nodes in one domain, and salted Merkle trees on one shared oracle have
deterministic binding over a collision-free full table (`SaltedMerkle.extract_binding`) with
extraction in the quantum random-oracle model; classical extraction with hashed leaves from a log
prefix is still absent. `OracleComp.lintegral_run_le_of_isQueryBoundP` (#766), a budgeted
supermartingale bound, is what `ToVCVio/ChargedInvariant.lean` instantiates.
`SampleableType.prEvent_uniformSample_le_div_iff` is the counting bound behind
`ToVCVio/UniformSample.lean`'s subsingleton form.
