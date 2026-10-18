# Dependency policy

The project tracks seven upstreams and six direct Lake packages:

| Component | Tracked ref | Role |
| --- | --- | --- |
| Lean | `v4.34.1` | Root toolchain |
| Mathlib | `v4.34.1` (`d13f23b7`) | Algebra, finite types, probability measures, and tactics |
| CompPoly | `572f997390aa4fc131ef30b1186fa1dcf292ca10` (current main) | Computable polynomial and field infrastructure |
| Clean | `42fe4b268132a46604d40cc73f642a1995f26547` (PR #474, includes current main) | Circuit, AIR, channel, and witness-generation infrastructure |
| ArkLib | `4dae3acff846125521b7b3998010885071746f16` (current main) | Oracle reductions, security definitions, composition, sumcheck, and multilinear theory |
| VCVio | `afa6593f15e1e79ecb3cf22fc56191cecb452bb0` (current main) | Native probability measures and oracle computation security carriers |
| PolyFun | `41d3b21dcc99817fe4f9f24ca7b2b58f0578083d` (current main) | Polynomial functors and free monads underlying oracle computations |

The machine-readable baseline is `upstreams.json`; `lake-manifest.json` records the resolved
Lake graph. `scripts/check-upstreams.sh` reports newer releases or commits but never rewrites
dependency files.

leanVM is not an upstream: the project lives in it, under `formal/leanvm`, and its target is the
containing commit. The last external pin was `a0ca7858f2533ce51abdc20bb635c007e19b26b3`; the
reviews below record each move of that pin. A change to a leanVM source the project models runs
its CI job, whose Rust-vs-Lean differential fails when the Rust verifier stops agreeing with the
Lean one on the fixtures. See [leanvm-target.md](leanvm-target.md) and [ci.md](ci.md).

`formal/lean_xmss` and `formal/lean_sphincs` are path dependencies: `Spec/Node.lean` imports
their `Scheme` modules, which Lake builds with this project's toolchain and pins. Their `lean-toolchain`,
Mathlib, VCVio and PolyFun pins are therefore this project's, and a bump moves all three together.

Add a dependency only with a named first-party use and a narrow import. A dependency PR must:

1. update the toolchain/Lake requirement, `upstreams.json`, and manifest together;
2. build and test the complete affected import cone;
3. review API changes used by theorem statements;
4. audit the first-party namespace's transitive kernel dependencies;
5. record semantic changes separately from mechanical porting; and
6. delete every `LeanerVM/Protocol/To*/` file or declaration that the new pin contains, move its
   consumers to the upstream names, and update the protocol blueprint's upstream ledger and the
   status page's watch list.

## ArkLib `4dae3acf` and VCVio `afa6593f` review

The previous pins were ArkLib `7653a901` and VCVio `a4232d08` (the head of VCVio #820 over
`f5119c64`, which `main` merged as `bc3433e3`). VCVio `afa6593f` is `main`, 22 commits after
`f5119c64`; ArkLib `4dae3acf` is `main`, 13 commits later, and is the ArkLib commit that targets
exactly this VCVio. Lean,
Mathlib, CompPoly, Clean and PolyFun are unchanged.

VCVio removed its discrete probability layer (`SPMF`, `Pr[…]`, `probOutput`, `probEvent`,
`NeverFail`) and renamed modules; its migration guide is `docs/agents/probability-migration.md`
and its codemod `scripts/migrate-native-probability.py`. This project used none of the removed
API by name. What it adapted to, all mechanical:

1. *Module renames.* `VCVio.OracleComp.Constructions.SampleableType.NativeMeasure` is now
   `…SampleableType.Measure` (six imports, rewritten by the codemod).
2. *The event normal form.* `Pr{let x ← mx}[p x]` is a `do` sequence whose selector is mapped
   last, so `bind_map_left` no longer moves an output map out of an event; `LeanVM.completeness`
   uses `prEvent_map` instead. Its statement is unchanged.
3. *Names.* VCVio's lemmas about events are now named `prEvent_…`, and the codemod reports a
   local `probEvent_…` name as legacy. The four local ones are renamed:
   `Verifier.GuardedForm.of_prEvent_pos`, `Verifier.GuardedForm.prEvent_pos_of_check`,
   `guarded_prEvent_pos` and `prEvent_uniformSample_le_of_subsingleton`, statements unchanged.
   A docstring of `ToVCVio/Rom/Bounds.lean` no longer says that VCVio states its birthday bound
   with `Pr[…]`.

ArkLib needed no change. Its legacy `OracleReduction` framework changed only in proofs and in
the binders of `Extractor.Straightline.IsMonotone`; the admitted results this project avoids are
still admitted, and the kernel axiom audit passes. The definitions under `LeanerVM/Spec/` and
the front-page theorems are unchanged.

Nothing was upstreamed: no `To*` declaration is contained in either pin. VCVio's new
random-oracle bounds (#823, #824, #826: fresh-query bad events by table resampling and expected
distinct-query charges, over a log of every query) and its subsingleton union bound
(`prEvent_exists_and_le_of_subsingleton`) are other statements than `ToVCVio/Rom/`'s potential
bounds over the log of fresh queries and `ToVCVio/UniformSample.lean`'s bound. ArkLib's typed
`Interaction` framework now has round-by-round soundness, round-by-round knowledge certificates
with backward witness maps, their sequential composition, and state-restoration knowledge
soundness (#1259, #1260, #1261, #1263, #1264), but still nothing adapts it to an
`OracleReduction` and its sumcheck has no knowledge notion, so the spine stays on the legacy
framework and `ToArkLib/KnowledgeAppend.lean` stays; decision 24 is due for review
([protocol-status.md](roadmap/protocol-status.md#upstream-watch)).

## leanVM `a0ca7858` review

The previous pin was `127510d14c98ade4e8a97646c44fa7f1ff5e752d`; the new one is
`a0ca7858f2533ce51abdc20bb635c007e19b26b3` (`main`, 2026-10-17), one commit later ("Guest: certify the native bus tiling order"). It
changes only `crates/rec_aggregation/guests/lean_ethereum.py` and a comment of
`crates/rec_aggregation/src/aggregation.rs`: the aggregation guest's in-circuit verifier,
`verify_sub`, now checks that the hinted order of the bus blocks is the native verifier's
(descending size, then ascending index), as the verifier does (`stack_offsets`,
`crates/verifier/src/multilinear.rs:127-137`); before, it accepted any aligned tiling, so it
accepted proofs the verifier rejects. No Lean definition changes. `python-verifier/verifier.py`,
`crates/verifier`, the prover and the specification are identical at both pins, so the proof
fixtures stand, the scripts' checksums are unchanged, and every citation of them keeps `127510d1`;
citations of the guest name `a0ca7858`.

## leanVM `127510d1` review

The previous leanVM pin was `a386121f84292f6fa663aaa3e570c15bc0240ea2` (2026-09-03); the new one
is `127510d14c98ade4e8a97646c44fa7f1ff5e752d` (`main`, 2026-10-15), 81 commits later. The review
read `python-verifier/verifier.py`, the protocol's executable specification, whose diff between
the pins is 52 lines, the new self-contained Rust verifier `crates/verifier` (8c31abd7, a
line-for-line port of the Python that replaced the verifier halves of `gkr.rs`, `leaf.rs`,
`constraints.rs`, `cpu/mod.rs`, Flock, the transcript and the stacked opener), and the
specification's tex. The ISA, the memory model, the tables, the bus and its flushes, the Flock
circuit and `R1CS_DIGEST`, the fields, BLAKE2s, the Merkle format, the Fiat–Shamir tags, seed
and query sampling, and the WHIR ladder are unchanged.

Semantic changes, each visible to the verifier, and what they change here:

1. *The GKR combiner* (40bdeac6). Each layer draws its combiner first; nothing is drawn after the
   roots or after the last layer, one challenge fewer per run (`verifier.py:438-452`,
   `crates/verifier/src/bus.rs:21`). The transcription (`Verifier.lean`), the oracle protocol's
   schedule (`gkrSpec`, without its trailing combiner; `gkrError`'s total is unchanged, the
   trailing combiner having been charged `0`), the grand product (`gkr`, `gkrComplete`,
   `gkrSecurity`), the program's doom (`EndToEnd/Front/BusGkr.lean`: a step goes from the layer
   relation to the step's output relation, its combiner first), completeness and the cost (`2`
   for the roots, the per-layer cost unchanged) follow. §5.3 now matches the verifiers.
2. *The public input* (9084d317, #322). The verifier computes each memory limb's claim, the line
   through that limb of the public input's two halves at the challenge; the prover sends nothing,
   and the check `c₀ + y·c₁ = (1 + r)·w₀ + r·w₁` and `Y` are gone (`verifier.py:1390-1396`,
   `crates/verifier/src/lib.rs:251-264`, §8.2 `08-end-to-end-protocol.tex:27-37`). The
   specification and the deployed verifiers now coincide: the leanISA instance sends no public
   line, the oracle protocol's public-input phase is the specification's (`publicInputPhase`;
   the schedule `pubSpec` is kept, its message empty on leanISA, which the compiled program does
   not read), and the deployed branch (`checkWords`, `deployedPublicInputPhase` and their
   theorems) is deleted. The program's phase is a challenge and a return
   (`EndToEnd/Front/PubPhase.lean`); its challenge joins Flock's first group, whose bound grows
   from `L₀·1/|E|` and `L₀·(k+1)/|E|` to `L₀·47/|E|` at most (`pubLead_le`), still under `2^-128`.
3. *The WHIR query table* (b977f5fa, #370). 25 of the 56 shapes need one to three queries fewer,
   from the fold error without the row-union factor (Annex B, after Jo 2026). The certificates
   are regenerated with the row-union bound this repository proves, which still covers every
   shape at 128 bits (`Parameters/Whir.lean`, `Whir/Params/Deployed.lean`).

The end-to-end theorems keep their statements but for the verifier's query count, `13213`
(`leanVmQueryBound`; it was `13300`), at the same `2^-128` per query and with no new hypothesis.
The pure refactors (`verify_bus_balance`'s hoisted values, `table_sumcheck`'s `table_point`,
`verify_whir`'s dead `running_target`, `blake2s_row_values`) change no Lean definition.

Mechanical porting, recorded separately: the crate `lean_vm` is now `leanvm_core` (01bf5283)
and the Rust verifiers moved into `crates/verifier`, so source citations re-point: every
citation of leanVM in the sources and the living documentation now names `127510d1`, with its
paths and lines checked against that tree, and says so where the cited code is gone. The dated
review records under `docs/reviews/` keep their pin, as does every record of something produced
or observed at `a386121f`. The Rust executor's error contract, its read pinning (a fix of
status finding R28) and its fill-frame placement changed, which bear on the leanISA status
findings and the Rust contract harness, not on a Lean definition. The proof fixtures of
`tests/fixtures/verifier` and the scripts that export them are at the old pin and must be
regenerated at the new one (`scripts/export-verifier-fixtures-rust.sh`, compared with the Rust
verifier by `scripts/fuzz-verifier.py`); the mock trace of
`tests/LeanerVMTests/Protocol/Verifier/Replay.lean` and the vectors of `Helpers.lean` and
`Compiled.lean` were rerun against the new `verifier.py`.

## Lean 4.34 port review

The previous baseline was Lean `v4.33.1`, CompPoly `3468b38c`, ArkLib `dca90385`, and Clean
`93c9d1ef`. Lean `v4.34.1` is the patch release in the requested 4.34 series. Compiled artifacts
from `v4.34.0` have incompatible headers, so Mathlib is now an explicit root requirement at
`v4.34.1`. Existing first-party consumers include `LeanerVM.Parameters.Generator` and the
polynomial and probability bridges under `LeanerVM.Protocol`. This requirement overrides the
`v4.34.0` Mathlib requirements inherited from CompPoly and ArkLib.

Regenerate the graph with `lake update`, then fetch matching artifacts with
`lake exe cache get`. Do not use `lake --keep-toolchain update`: in Lake 4.34 that option also
changes dependency traversal, allowing inherited manifests to resolve a package before later
root requirements. Check the resolved revisions in the manifest after an update.

CompPoly's current main revision overrides ArkLib's `v4.34.0` CompPoly requirement. The
complete first-party import cone must be compiled against that single resolved revision.
`BF64` is now a structure wrapping `BitVec 64`, with characteristic-two natural-number casts:
`(2 : K) = 0`. Encoded words use `K.ofBits n = BF64.ofBitVec (BitVec.ofNat 64 n)` instead.
The generator remains the encoded word `0x2`; BLAKE2s cells, Clean's `val`/`fromNat` interface,
protocol fixtures, and exported Rust contract fixtures retain their original bit coordinates.
Regression tests distinguish casts from encoded words explicitly. `DecidableEq K` compares bit
coordinates through an equivalence proof: the upstream derived wrapper instance makes kernel
checks of computed words stall on dependent transport. The existing register-equality
regression checks this boundary without unchecked evaluation. The `Fintype K` instance is
proof-only; executable samplers use coordinate equivalences without enumerating `2^64` words.

ArkLib's current source supplies native dependent composition and computable sumcheck as well
as the security definitions migrated to VCVio's native measure API. The guarded
verdict, guarded append, and uniform counting bridges use `Pr{let x ← computation}[P x]`
and native event lemmas. Their relations, extraction conditions, and error bounds are retained.
The retired `Pr[P | computation]` interface is no longer used by first-party probability proofs.
Review these statement changes alongside the kernel audit, rather than relying on successful
elaboration alone.

Clean is pinned to the compatibility commit in [PR #474](https://github.com/Verified-zkEVM/clean/pull/474),
with current Clean main (`fba2a29f`) merged into the compatibility branch. Mathlib 4.34 rejects
`ring_nf at ih'` in
`Clean.Air.Balance.balanceOf_active_append_eq` because normalization makes no progress at that
hypothesis. The fix applies the induction equality under addition explicitly and proves the
reassociation goals with `ring`, retaining the theorem statement and assumptions. The affected
Clean import cone is built under the root Lean 4.34.1 toolchain; Clean CI checks the branch under
its own toolchain. The published commit is pinned directly; local package overrides must never
be written into the committed manifest.

VCVio's query-log counting bridge needs one proof adjustment for current PolyFun's sealed
free-monoid trace interface. The compatibility commit in [VCVio #820](https://github.com/Verified-zkEVM/VCVio/pull/820)
over `f5119c64` normalizes the target to
list counting before induction, retaining the theorem statement. The complete source file is
checked against both PolyFun `3710d71b` and current `41d3b21d` under Lean 4.34.1.

## Dependency boundaries

CompPoly supplies leanVM's fields (see [leanvm-target.md](leanvm-target.md)):

- `K = GF(2^64)`: `CompPoly.Fields.Binary.BF64`, the flat quotient
  `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` on a computable polynomial-basis carrier, with
  Rabin-certified irreducibility;
- `E = GF(2^192)`: `CompPoly.Fields.Binary.BF64.Ext3`, the cubic extension
  `K[y]/(y^3 + y + 1)` on a `Vector BF64 3` carrier via `CompPoly.Fields.Extension`.

ArkLib's Lake package name is `Arklib`, which is what the `[[require]]` must say. Its first
consumer is `LeanerVM/Protocol/Field.lean`. VCVio is an explicit root requirement because
`LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean` and the probability bridges consume its native
measure and security interfaces. PolyFun is an explicit root requirement for the free-monad carrier of the oracle computations
used by `LeanerVM/Protocol/ToArkLib/Oracles.lean` through VCVio.
These requirements select current source over the older revisions in inherited manifests.
ArkLib also brings cslib, checkdecls, and doc-gen4's dependencies into the graph. Tooling and
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

Clean's first consumers are the leanISA table components and the `FiniteField BF64` instance
in [roadmap/leanisa-blueprint.md](roadmap/leanisa-blueprint.md). Its core is generic over
`FiniteField F`; its `ZMod p` gadget tree is not used. Two limitations remain: push and pull
multiplicities `±1` coincide in characteristic two, and `Expression` has no degree bound.
Clean's pinned source and first-party Clean bridges now use Lean's module system; the
historical import restriction C8 no longer applies. Message-flattening proofs use Clean's
public normalization lemmas for its now sealed struct conversions. Small literal row equations
in the witness tests unfold those conversions explicitly; block equations compare rows
pointwise before applying `List.ofFn`, avoiding enumeration of the `2^16`-row memory block. See
[CONTRIBUTING.md](../CONTRIBUTING.md) and the historical finding C8 in
[roadmap/leanisa-status.md](roadmap/leanisa-status.md).

leanVM's `formal/lean_xmss/` and `formal/lean_sphincs/` projects are not imported wholesale:
only their `Scheme` modules are. Using their reviewed security theorems here requires a deliberate
statement and correspondence review.

## Limits that bind the proof system

Facts about the pinned libraries that shape the [protocol blueprint](roadmap/protocol-blueprint.md),
checked at the pins of `upstreams.json` unless a line names another revision.

**ArkLib.**

- Relations are `Set (Stmt × Wit)`. `OracleReduction` is the framework ArkLib calls legacy; its
  typed `Interaction` framework proves soundness, round-by-round soundness, round-by-round
  knowledge certificates (backward witness maps) and their composition, but nothing adapts it to
  an `OracleReduction` and its sumcheck has no knowledge notion, so the spine stays on the
  legacy one.
- A round-by-round extractor is any function: the existential forms `rbrKnowledgeSoundness` and
  `rbrKnowledgeSoundnessWorstCase` are met by an extractor chosen by classical choice (ArkLib's own
  `toRoundByRoundOfRel` is one) and prove soundness only. The averaged `rbrKnowledgeSoundness` is
  weaker than the literature's; the worst-case named form `rbrKnowledgeSoundnessWorstCaseWith` is
  the one used.
- Admitted: the knowledge-soundness composition (`Append/Security.lean`; ArkLib #615 proves it,
  open), the round-by-round-to-plain implications, context lifting, `fiatShamir_completeness`
  (for a constant oracle), the sumcheck's classical leaf, the correlated-agreement theorem
  `rs_mcaError_le_in_johnson_range`, and the ring-switching packing leaves. `BCSTransform` and the
  round-by-round to state-restoration implication are commented out;
  `Commitments/Functional/Basic.lean`'s `extractability` has body `False`; two `addSalt`
  implications carry `sorry` in their types.
- False as stated: the classical leaf `Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundness`
  (the verifier reads the input polynomial for its next target; ArkLib #1244 repairs it), and
  `rbrSoundness_implies_soundness` for a stateful shared oracle (ArkLib #1245 proves it for a
  stateless one).
- Proved and usable: `ReedSolomon.mcaError_affineLine_johnson_le` (a Johnson-range correlated
  agreement bound with its own constant, any characteristic); the capacity-range theorems assume
  characteristic 0 or `k − 1 < ringChar F`, false over `E`.
- `OracleInterface (Vector α m)` (position queries) is a global instance, so a column type with
  another interface is a structure, not an abbreviation of `Vector`; no default interface is
  registered for scalars or lists (`OracleInterface.instDefault` is for no type).
- The instances for the messages and challenges of two schedules side by side
  (`instOracleInterfaceMessageAppend`, `instSampleableTypeChallengeAppend`) are not found by
  instance search when the schedules are concrete; ArkLib's own files apply them by name, and so
  does `ToArkLib/Schedule.lean` (`msgAppend`, `chalAppend`).
- The typed framework's computable sumcheck (`ProofSystem/Sumcheck/Impl/Representation.lean`,
  `ProofSystem/Sumcheck/Interaction/Protocol.lean`) sums a round message, a polynomial with a
  degree bound queried by evaluation, over its domain with unit weights, and nothing adapts a
  protocol of the typed framework to an `OracleReduction`; the proof system's normalized round
  (`ToArkLib/SumcheckRound.lean`) sends the coefficients as one message and weights the domain.
- `lake build` with several explicit ArkLib targets can schedule `ArkLibLintPlugin:shared` twice
  and fail one link; a second build proceeds.

**CompPoly.** No hypercube sum and no pointwise product of tables (the proof system's Layer 1
supplies them); the additive NTT is instantiated only at `GF(2^8)`; no Frobenius on `Ext`; the
conversion of `CMvPolynomial` to Mathlib's `MvPolynomial` is noncomputable; inside a `module`,
`decide` cannot unfold `CMvPolynomial`'s `X` and `*`. `LawfulBEq (Ext P)` exists at `572f9973`.

**Clean.** No degree, height or padding notion; `EnsembleWitness` has no generator
(`Circuit.witgen` is per row); `Ensemble.Statement`'s balance over `K` is vacuous (leanerVM #16).

**VCVio.** Merkle trees with proved completeness and single-opening random-oracle
extractability (`CryptoFoundations/MerkleTree/`); `SampleableType.prEvent_uniformSample_le_div_iff`
is the counting bound behind `ToVCVio/UniformSample.lean`'s subsingleton form.
