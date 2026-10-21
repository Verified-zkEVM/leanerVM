# W2: the guest's soundness over a hash model

Package W2 of [`e2e-security.md`](e2e-security.md) (§4 T2, §6): `guest_knowledge`
(`Guest/EndKnow.lean`) proves that every valid execution of the deployed guest decodes to a
witness of `NodeRel`, every hash `blake2sBytes`. T2 needs the same proof under any
`HashModel` (`Guest/Value/HashModel.lean`, decision W0-5): executions `ValidExecutionB M.sem`,
conclusion `NodeRelWith M.H s0 pc pr`. This note records the foundation (done), the conversion
pattern for each kind of proof site, and the plan for the rest of B1, split for parallel agents.

## 1. Architecture

### 1.1 The semantics layer: parallel `…B` modules (decision W2-1)

The guest's semantics enters at one place: the relation a `BLAKE2S` row (bytecode) or atom (core
IR) checks, `CompressCells`. Everything above it only carries that fact. The generic semantics
is a parameter `S : BlakeSem` (`Spec/IsaWith.lean`), and every definition and lemma of the B2
soundness chain that mentions the semantics has a `B` copy over `S`:

| deployed | generic | content |
|---|---|---|
| `Core.lean`, `CoreLemmas.lean` | `CoreB.lean` (624 lines) | `Atom.HoldsB S`, `Stmt.HoldsB S`, `Fn.SemB S`, `Program.relNB S`, `Program.RelB S`, every `CoreLemmas` lemma (`holdsListB_append`, `holdsB_mono`, `relB_iff`, …), `relB_iff_sem`; bridges and transfers below |
| `Logic.lean` | `LogicB.lean` (452) | `HoldsB S`, `SafeB S` over `runB S`, `executeB_iff_holds`, `SafeB.fallThrough`, …, `funSpecB_induction`, `ReachB S`, `returnsB_induction`, `safeB_of_validExecution` |
| `Exec.lean` (semantic half) | `ExecB.lean` (861) | `St.HoldsB`, `Atom.HoldsB`, `RunKB`, `FollowsB`, `execB_sound`, `execB_complete`, `execWinB_sound`, … (the executor itself, `EnvHolds`, `MemHolds` stay `Exec.lean`'s) |
| `CoreLoc.lean` | `CoreLocB.lean` (165) | `Program.RelLB S`, `relLB_iff`, `relLB_le_rel`, `relLB_deployed` |
| `CheckSound.lean` | `CheckSoundB.lean` (1610) | `BookHoldsB`, `blakeOkB_sound`, `PostB S`, `RLB S`, `checkWinsB_run` (`Pre`, `valG`, `MemKnown`, `SemHolds` stay deployed: they do not mention the semantics) |
| `Sound.lean`, `End.lean`, `EndLoc.lean` | `SoundFacts.lean` (119, split out of `Sound.lean`), `SoundB.lean` (244) | `b2B_step`, `b2B_mainL`, `safeB_jumpTables`, **`mainBodyLB_of`** |

**Why copies.** The generated kernel-checked families import `Core`, `Logic`, `Exec` (all four
families: `Checked` 374 modules, `B2C/Shared` 605, `B2C/Cplw` 275, `Memory/Guest*` 516) and
`CheckSound` (`Cplw`, through `B2C/Cells`); an edit of `Core.lean` makes 2,344 modules stale,
1,770 of them generated at 2–5 GB each (estimated tens of hours at `WIDTH=3`). The copies
rebuild nothing generated: editing a `B` module rebuilds `SoundB` and B1 (≈470 modules), the
same as editing `B1/Basic`. This is decision W0-1's choice for the Spec, applied to the guest.

**How the copies were made.** Mechanically: every declaration whose text mentions the semantics
(transitively) is copied with `S` threaded and a `B` in its name (`holdsList_append` →
`holdsListB_append`, `Safe.fallThrough` → `SafeB.fallThrough`, `exec_sound` → `execB_sound`),
the rest is reused. Proofs are verbatim but for a dozen one-word fixes (`(S := S)` where `S`
appears only in a conclusion). A change to a deployed proof module is mirrored the same way.

**Consolidation (optional, later).** When the certificate families are regenerated anyway
(`lake exe guest-cert`, which rebuilds all three), the deployed modules can become the generic
ones with the deployed definitions as abbreviations at `blakeDeployed`, and the copies deleted.
Not needed for W2.

**What the layer gives.**

* `Core.relB_deployed : P.RelB blakeDeployed rd = P.Rel rd` (and `holdsListB_deployed`,
  `fnSemB_deployed`, `relLB_deployed`): a generic statement at the deployed semantics is the
  deployed one, by rewriting. `tests/LeanVMTests/Guest/Model.lean` recovers `mainBodyL_of` from
  `mainBodyLB_of` this way.
* `Core.relB_monoS`: a semantics implying another gives its relations.
* `Core.relB_iff_rel_of_freeOn`: **a function free of `BLAKE2S`** (no `BLAKE2S` atom, every
  callee such, `Program.FreeOn P F`, checked by `decide +kernel`) **has its deployed relation
  under every semantics**, so its B1 lemma carries over without a new proof. Of the guest's
  1,043 core functions, 322 are free and closed under calls; the 721 others are 458 named
  functions (the hashing families: `claims_tail__L*`, `child_claims_tail__L*`,
  `da_hash_roots__L*`, `sp_forest_key__L*` (256), `opening_queries__*`, `open_stacked__L*`,
  `verify_merkle_cap__L*`, `statement_digest`, `claim_list_digest`, `child_claim_list_digest`,
  `da_list_digest`, `da_verify*`, `sumcheck_round4`/`5`, `opening_fold`, `grind_check`, the
  callers `verify_tables`, `verify_bus_gkr`, `verify_flock`, `verify_sub`, `aggregate_claims`,
  `main`) and 263 loop helpers.
* `End.mainBodyLB_of (hvs : VsKnownB S) (hexp : ExpKnownB S) (hv : ValidExecutionB S guest
  input t)`: `main`'s body under `S` at its frame, every call located — the B2 part of
  `guest_knowledge` over any semantics. Its two hypotheses are B1 facts the windows of `main`
  and `verify_sub` start from: `ExpKnownB S` is proved for every `S` (`B1.expKnownB`, by the
  transfer); `VsKnownB S` is the VerifySub agent's (§4).

### 1.2 The chain layer (`Value/ModelChain.lean`, 204 lines)

`Value/Hash.lean`'s chain lemmas over a `HashModel`, every hash answered and no chaining value
named: `HashModel.one_block` (`blake2s_default`), `HashModel.empty` (`blake2s_empty`),
`HashModel.prefix_run` (`chain_nonfinal`, from the IV or any prefix), `HashModel.final_block`
and `HashModel.final` (`chain_final`), `HashModel.chain_blocks`
(`chain_eq_blake2sBytes_blocks`), `HashModel.chain_bytes` (`chain_eq_blake2sBytes`), and
`HashModel.deployed_H : deployed.H x = some d ↔ d = blake2sBytes x`.

### 1.3 The run layer

* `Value/RunSome.lean` (111): `run_some`, `runProof_some`, `openAll_some`, `climb_some`:
  `Compile.run` over `Option` with `fun x ↦ some (f x)` is `some` of the run over `Id` with `f`.
* `Value/NodeSome.lean` (72): `statementDigestWith_some`, `childClaimsWith_some`,
  `verifyDeferredWith_some`, `observeWith_some`, `squeezeWith_some`, `batchRoundsWith_some`,
  `forIn_some`, `batchWith_some` (from `blake2sBytes batchLabel`).
* `B1/Basic.lean` (+200): `runM M` (`Compile.run` at `Option` over `M.H`), `RunsToM M p cv xs a
  cv'`, with `RunsTo`'s interface over answered steps: `obsCvM`, `sqCvM`, `obsAllM`, `sqAllM`,
  `runM_bind`, `RunsToM.bind`, `.unique`, `.iff`, `.of_eq`, `runsToM_ret`, `runsToM_readE`,
  `runsToM_sampleE`, `runsToM_readN`, `runsToM_sampleN`; and `runsToM_deployed : RunsToM
  HashModel.deployed … ↔ RunsTo …`, `obsAllM_deployed`, `sqAllM_deployed`. `RunsTo`, `obsCv`,
  `sqCv` are unchanged, so every completeness proof that unfolds them by `rfl` or `decide`
  (B2C, `EndComplete*`, `B1/*Complete*`) is untouched.

### 1.4 The pilot

* `Value/FiatShamir.lean`: `fs_compress_model`, `squeeze_state_model`, `squeeze_spec_model`,
  `grind_check_model` (and `powOk_of_lane`, the hash-free half of `grind_check_sound`); the
  deployed `fs_compress_iff`, `squeeze_state_iff`, `squeeze_spec`, `grind_check_sound` derive
  their soundness from them at `HashModel.deployed`.
* `B1/FsBlocks.lean`: `holdsB_pack64x2T`, `holdsB_canonicalLimbsT` (iffs, any `S`: no hash),
  `holdsB_fsCompressT`, `holdsB_fsNextT`, `holdsB_squeezeStateT`, `holdsB_squeezeT` (over a
  model; honest values with the output digest given: `fsValsD`, `sqStateValsD`, `sqValsD`);
  each deployed `holds_*T` derives its forward direction from the generic one.
* `B1/FiatShamir.lean`, `sumcheck_round4` (the worked example of §2): `MeaningSumcheckRound4With
  M`, `runsToM_roundPoly4`, `sumcheck_round4_model`, `meaningSumcheckRound4With_deployed`, and
  `sumcheck_round4_iff`'s forward direction from them.

All deployed statements are unchanged; the end theorems, their tests and the generated
families are untouched (`git diff` of the deployed files: proofs and additions only).

## 2. Conversion patterns

Every B1 soundness lemma is an iff on `coreProgram.Rel rd "f"`. Its generic form is the forward
direction over `coreProgram.RelB M.sem rd "f"`, concluding a `…With M` meaning; the deployed iff
is reassembled from the generic forward direction at `HashModel.deployed` and its unchanged
backward direction. **Worked example** (`B1/FiatShamir.lean`):

```lean
def MeaningSumcheckRound4With (M : HashModel) (rd : Reader) : List E → List E → Prop
  | [s0, s1, cur, claim], rets => ∃ cv c0 c2 c3 claim' r cv', (s0, s1) = digestScalars cv ∧
      ReadsAt rd cur [c0, c2, c3] ∧ RunsToM M (roundPoly 4 claim none) cv [c0, c2, c3] (claim', r) cv' ∧
      rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 3, claim', r]
  | _, _ => False

theorem sumcheck_round4_model {M : HashModel} (rd) (args rets)
    (h : coreProgram.RelB M.sem rd "sumcheck_round4" args rets) : MeaningSumcheckRound4With M rd args rets := by
  rw [relB_iff_sem find_sumcheck_round4, core6_body, core6_params] at h
  obtain ⟨σ, rfl, h⟩ := h
  simp only [holdsListB_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, …] at h
  obtain ⟨h4, h5, h⟩ := h
  obtain ⟨⟨hl0, cv, d1, hcv, hd1, e0⟩, h⟩ := holdsB_fsNextT _ _ _ _ _ h   -- one block at a time
  …
  obtain rfl : cv1 = d1 := digestScalars_injective (by rw [← hcv1, f19, f20])  -- the next state is the answered digest
  exact ⟨…, runsToM_roundPoly4 _ _ _ _ hd1 hd2 hd3 hd4, …⟩

theorem sumcheck_round4_iff (rd args rets) : coreProgram.Rel rd "sumcheck_round4" args rets ↔ … := by
  constructor
  · intro h; rw [← relB_deployed] at h
    exact (meaningSumcheckRound4With_deployed rd args rets).mp (sumcheck_round4_model (M := HashModel.deployed) rd args rets h)
  · …  -- the deployed backward direction, unchanged
```

The generic block lemmas are implications, so a body is consumed by `obtain` one block at a
time (`holdsB_fsNextT … h` returns the block's facts and the continuation), where the deployed
proof rewrites with the block iffs under `simp`.

| site | pattern |
|---|---|
| **(A)** relation only (`Core.lean:205`, `Logic.lean:77`, `CheckSound.lean:258`, B1 meaning definitions over `Rel`) | rename: `Stmt.HoldsList` → `Stmt.HoldsListB M.sem`, `coreProgram.Rel rd` → `coreProgram.RelB M.sem rd`, `rel_iff_sem` → `relB_iff_sem`, `holdsList_append` → `holdsListB_append`, … (the `B` lemma of `CoreB` has the deployed one's name with a `B`). A function free of `BLAKE2S`: no new proof, `f_iffB := by rw [relB_iff_rel_of_freeOn hfree hmem]; exact f_iff …` with `hfree : coreProgram.FreeOn F = true := by decide +kernel` for the function's call closure `F` (`B1/ExpKnownB.lean`). |
| **(B)** hash = chain output (`blake2s_default`, `blake2s_empty`, `chain_eq_blake2sBytes_blocks`, `compress_two_iff.mp`, `compress_final_iff.mp`, `chain_nonfinal`/`chain_final` at the IV) | the `HashModel` lemma of §1.2, which gives `∃ d, M.H x = some d ∧ out = digestScalars d`; the digest `d` replaces `blake2sBytes x` in the meaning. An iff used in soundness keeps only its forward direction. Canonical cells come from `M.canonical hc` (not `hc.1`). |
| **(C)** intermediate chaining values (`Digest/Common` `chainRun`, `ChainCells`, `chain_eq_chainRun`, `chainRun_nonfinal`, `chainRun_blocks`; `Digest/ClaimSpec` `prefixDigest`, `chainCells_prefix`; loop invariants storing `digestScalars (prefixDigest …)` in `ClaimList`, `ChildList`; window and tail states `cwS`, `ctS`, `Statement:419`, `Da/Cell`, `Da/ListDigest`, `Da/Columns`, `Da/Vector`, `Da/RowHash`, `Da/Witness`, `Whir/QueriesIter`; `Sig/HashValues` `hvState`, `Sig/Hashing` `hmid`) | a state is a **prefix**: `st = digestScalars (absorbBlocks iv 0 bs)` becomes `M.Prefix bs st`; `chainRun` from a state becomes `HashModel.prefix_run` from a prefix; a window's or loop's invariant carries `M.Prefix bs st` for the bytes absorbed so far; only the last block reads a hash (`HashModel.final`, `final_block`). A function that runs blocks from a state handed to it (`ChainCells`, the windows and tails) states the rows it checked (each block's `M.sem.check` from the state it received, at its counter), and its caller, which knows that state is a prefix (from the IV, or from the previous window), extends the prefix by `HashModel.prefix_run`. |
| **(D)** constants evaluated by `decide` (`Da/Pad.lean` → `Link.lean` `paddingCell_eq`/`paddingRow_eq` → `Da/Witness` `commitCodewords_eq`; `Main/Consts.lean` `aggSeed_eq` used by `Main/AggSound:240`) | parameters, as `NodeRelWith s0 pc pr` takes them: the generic meaning uses the baked digest itself (`s0 := digestOfScalars` of `AGG_SEED`'s cells, `pc`, `pr` the baked padding digests), never its preimage; the deployed lemma rewrites with the existing `decide` fact (`aggSeed_eq`, `paddingCell_eq`) to get `blake2sBytes batchLabel`, `LeanDa.paddingCell Da.blake2s`. |
| **(E)** conclusions with `statementDigest`, `xmssVerify`/`sphincsVerify`, `Da.Witness.Opens`, `verifyDeferred`, `batch` | the `…With` forms at `M.H`, `= some _`: `statementDigestWith M.H seed s = some pi`, `xmssVerifyWith M.H … = some true`, `w.OpensWith M.H pc pr r v`, `verifyDeferredWith M.H … = some true`, `batchWith M.H s0 cs h = some (some d)`; at the deployed model `Value/NodeSome.lean`'s bridges (and package W2-S below) give the deployed ones. |
| **(F)** B1 definitions over `blake2sBytes` (`runId`, `obsCv`, `sqCv`, `obsAll`, `FsBlocks.absorbCv`, `Grind.gcDigest`, `Sig/Hashing` `hb`/`hcell`, `Main/Callees` `stmtDigestOf`, `Main/Basic:334-339`, `Da/Witness` `cellDOf`/`rowDOf`, `VerifySub/CData:85`, `AggSound` `sqIt*`, Whir's `openAll (m := Id) blake2sBytes`) | keep the deployed definition (completeness unfolds it); add the answered form taking `M` (`obsCvM`, `sqCvM`, `obsAllM`, `sqAllM`, `runM`), or, for values the guest computes, a form taking the output digest (`fsValsD`, `sqValsD`); Whir's `openAll (m := Id) blake2sBytes` becomes `openAll (m := Option) M.H` (`openAll_some` is the bridge). |
| **(G)** canonicity read off `BLAKE2S` (`hc.1 i`, `hc.2.1`, … of `CompressCells`) | `M.canonical hc` (`.1 i` the message cells, `.2.1`/`.2.2.1` the chaining value, …). |

**Obstruction check.** No pattern needs an intermediate chaining value to be a function of the
bytes: soundness only extends prefixes and reads final digests. A proof that compared two
chaining values to conclude that their byte strings agree (prefix injectivity) would need a law
neither model satisfies (the oracle model's prefixes are table chains, the deployed one's
`absorbBlocks` collides in principle), so such an argument belongs to a binding lemma outside
T2 (as `decode_binds` is), not to B1. The survey found none in `guest_knowledge`'s closure; an
agent meeting one stops and reports it. Prefix *existence* for a state read from memory is never
needed: every chain starts at the IV constant, and each later state is a prefix by the rows
checked before it.

## 3. Order of conversion

```text
layer 0  CoreB LogicB ExecB CoreLocB CheckSoundB SoundB · ModelChain RunSome NodeSome · B1/Basic (RunsToM) · FsBlocks · Value/FiatShamir     [done]
layer 1  B1 root (FiatShamir rest, Sumcheck, Grind, Opening, OpeningOod)        Digest/*   Da/*   Sig/*
layer 2  Tables/* (GKR, Flock, VerifyTables)        Whir/*
layer 3  VerifySub/* (VsKnownB, verify_sub_model)
layer 4  Main/* (callees_proved over M, main_sound_w over M, AggSound from s0) · Located · EndKnowB (guest_knowledge over M)
```

Layer 1's four subtrees are independent of each other; layer 2 needs the root's `Sumcheck` and
`FiatShamir` lemmas; layer 3 needs `SoundGkr`/`SoundTables` over `M` (their statements first,
so VerifySub can start against them); layer 4 needs every callee's generic statement
(`Main.Callees` over `M`), which can be written first and proved last.

## 4. Per-subtree plan (one agent each)

Counts are of files in `guest_knowledge`'s import closure; "generalize" files carry hash
reasoning (patterns B–G), "rename/transfer" files only the relation (pattern A, or the
free-of-`BLAKE2S` transfer), the rest (completeness, counting, placement) is unchanged and keeps
using the deployed iffs. Files named `C*`, `*Complete*`, `Honest*` among "generalize" are
completeness files in the closure: only the soundness halves they export change.

| agent | subtree | generalize | rename/transfer | first targets |
|---|---|---|---|---|
| 1 | B1 root + Whir | `FiatShamir` (`sumcheck_round5`, `opening_fold`), `Grind`, `Opening`, `OpeningOod`, `Sumcheck`; `Whir.Cap`, `CapAgrees`, `Queries`, `StackedBlocks`, `StackedEnd`, `StackedLevel(s)`, `StackedLoops`, `StackedQueries`, `StackedRun`, `StackedSound` (≈8.4k lines) | `EqWeight`, `Exponent`, `FoldFinal`, `Lag64`, `Log2`, `Loops`, `QueryBits`, `RowWeights`, `Tables`, `Uniform`; `Whir.QueriesSpec`, `QueriesW`, `StackedInst0-3` (mostly by transfer) | `Sumcheck` (agents 2, 3 need it), Whir's `openAll` over `M.H` |
| 2 | Tables | `Flock*`, `Gkr*`, `VerifyTables*` and `Vt*` with FS runs (44 files, 14.4k lines; `GkrRun`/`VerifyTablesRun`-style `RunsTo` traces become `RunsToM`) | `ColumnSelector`, `Padding`, `Placement`, `Terminal*`, `TermAt*`, `FlatAt*`, the hash-free `VerifyTables*` (44 files, by transfer where the callee is free) | `SoundGkr`, `SoundTables` statements over `M` |
| 3 | VerifySub | `Front`, `Run`, `Challenges`, `Consume`, `Interface`, `Ring`, `Sound`, `SoundW`, `Tail`, and the `C*` files' soundness halves (18 files, 6.8k lines) | `Known` (**`VsKnownB S`**, for `SoundB`), `Extract`, `Loops`, `InterfaceW`, `CRel`, `CLoops`, `CGroup1` | `vsKnownB` (it needs only GKR, tables, placement, log2: mostly transfer), then `verify_sub_model` concluding `verifyDeferredWith M.H … = some true` |
| 4 | Digest + Da | `Digest.Common` (the prefix layer: `chainRun` → `prefix_run`), `ClaimSpec`, `ClaimWindow`, `ClaimTail`, `ClaimList`, `ChildWindow`, `ChildTail`, `ChildList`, `Statement`; `Da.Pad` (parameters `pc`, `pr`), `Link`, `Tree`, `RowHash`, `Cell`, `Columns`, `Vector`, `ListDigest`, `Verify`, `VerifyBody`, `Witness` (20 files, 7.9k lines) | `Digest.ScaledLog`; `Da.Column`, `Loops`, `Named`, `RowShape`, `VerifyColumn` | `Digest.Common` over `Prefix` (pattern C), then `statement_digest_model : … → statementDigestWith M.H seed s = some pi` |
| 5 | Sig | `Bytes`, `Hashing` (`hb`, `hcell`, `hmid` over `M`), `HashValues` (`hvState` as a prefix), `XmssLayer`, `SphincsBody`, `SphincsKey`, `SphincsCoord` (7 files, 2.5k lines) | 17 files (`Arm`, `Chain`, `Codeword`, `Frame`, `Group`, `Merkle`, `Steps`, `Walk`, `WotsW`, `Xmss*`, `Sphincs*`): rename | the `compress_two_iff`/`compress_final_iff` forward halves over `M`; conclusions `xmssVerifyWith M.H … = some true` |
| 6 | Main + End | `Main.Basic`, `Consts` (`s0`), `BatchSpec`, `AggChain`, `AggSteps`, `AggStepsC`, `AggSound` (batching from `s0`: `batchWith M.H s0`), `Callees`, `CalleesW`, `Children`, `LoopsW`, `Sound`, `SoundW`, `Discharge` (14 files, 4.2k lines); `Located/*`; new `EndKnowB.lean` | `Main.AggEqtree`, `AggLoop99`, `LoopAt`, `Loops`, `LoopsC`, `WeightLoop` | `Main.Callees` over `M` (the interface every other agent proves into), then `guest_knowledge_model : ∀ M, ValidExecutionB M.sem guest input t → … NodeRelWith M.H s0 pc pr …` from `mainBodyLB_of` |

Each agent edits only its subtree. Shared vocabulary needed by several (a new `HashModel`
lemma, a `CoreB` lemma) goes into the foundation modules by one owner (agent 1 for `B1/Basic`,
`Value/*`; agent 6 for `CoreB`/`SoundB`), announced before use.

**Package W2-S (bridges to the deployed statements).** Done: `run_some`, `runProof_some`,
`statementDigestWith_some`, `childClaimsWith_some`, `verifyDeferredWith_some`,
`batchRoundsWith_some`, `batchWith_some`, `runsToM_deployed`. Missing: `Witness.OpensWith ↔
Witness.Opens` at the deployed hash and padding (`commitCodewordsWith`, `vectorDigestWith`), and
the scheme verifiers (`xmssVerifyWith_some_blake2s`, `sphincsVerifyWith_some_blake2s`, in
`LeanVM/E2E/Runs.lean` on `mumbai`); with them, `NodeRelWith (fun x ↦ some (blake2sBytes x))
(blake2sBytes batchLabel) (LeanDa.paddingCell Da.blake2s) (LeanDa.paddingRow Da.blake2s) bc seed s
w ↔ NodeRel bc seed s w`. Agent 6 needs it last (to rederive `guest_knowledge`); it can be done
in parallel by a seventh agent or by agent 4 (DA) and 5 (schemes).

## 5. Build costs

| step | stale modules | generated families rebuilt |
|---|---|---|
| layer 0 (this package) | 497 (B1, Main, End, tests) | none |
| an edit of a `B` module of §1.1 | ≈470 (B1 and above) | none |
| an edit of `B1/Basic` or `Value/*` | ≈460–500 | none |
| an edit inside one B1 subtree | that subtree and its importers (Tables ≈130, VerifySub ≈60, Main ≈60 + End) | none |
| an edit of `Core`/`Logic`/`Exec` (avoid) | 2,344 | 1,770 |
| an edit of `CheckSound` (avoid) | 339 | 275 (`B2C/Cplw`) |

Agents iterate with `lake env lean File.lean` on built imports and rebuild their subtree with
`lake build <Module>` after `lake build --no-build` shows few stale modules; the full gate is
`WIDTH=3 python3 -I scripts/ci-build.py`. A cap of `ulimit -v 40000000` is too low for some B1
modules (`Whir/QueriesSpec.lean`: about 65 GB of address space for the deep-recursion thread
stacks of its `maxRecDepth 100000` proofs, 2 GB resident), which then abort with "failed to
create thread"; cap the throttled build at `ulimit -v 200000000` instead.
