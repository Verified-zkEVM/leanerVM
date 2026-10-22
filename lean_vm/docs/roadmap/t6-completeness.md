# T6-det: deterministic completeness of V_I

Package T6-det of [`e2e-security.md`](e2e-security.md) (§4, §6): the end theorem is not vacuous.
For every hash `H` and every honest witness tree within the deployed limits, an explicit honest
idealized prover `I(H)` outputs a root statement and an idealized proof that V_I
(`LeanVM/E2E/Statement.lean`, `idealVerify`) accepts. This note fixes the Lean statement, checks
it against the V_I of `Statement.lean` (two findings, §2), decomposes it (§3, §4), and records
what is proved (§6).

## 1. The statement

### 1.1 Objects

* **The honest witness tree** (`HonestTree`): a node is its claims (`NodeClaims`: the leanXMSS,
  leanSPHINCS and DA lists), their holders (`Holder` lists as in `NodeWitness`: a signature, a DA
  opening, or `.child i`) and its children (`List HonestTree`). Everything else of a node — its
  deferred claim, the children's proofs and fresh claims, the batching hints — is the prover's.
  `HonestTree.Valid H T`: at every node each direct holder verifies with every hash answered by
  `some ∘ H` (`xmssVerifyWith`, `sphincsVerifyWith`, `Witness.OpensWith` at the deployed padding
  digests), each `.child i` points to a child whose claims contain the claim, and every root DA
  claim's vector digest is `vectorDigestOfWith H` of its root.
* **The honest prover** `honestIdeal H T ρ pfuel : Option (NodeStatement × IdealProof)`, bottom up
  (a specification: it makes classical choices):
  1. the children first; a child is `⟨s_c, fresh_c, π_c⟩`;
  2. the node's deferred claim: at a leaf the bytecode's true value at the zero point
     (`AtZero`, matrices `0`); at an inner node the batching (`batchWith H s0`) of the children's
     claims with honest round messages, the bytecode part true, the matrix part closed by
     `(a*, b*)` with `a*·weightA + b*·weightB = matrixFinal` — **fails** (`none`) when
     `weightA = weightB = 0`;
  3. the node's witness `w` (the holders, the children, the hints), `NodeRelWith (some ∘ H) s0 pc pr`
     by construction (§3, L12);
  4. the node's execution: the guest's run under the honest table semantics `chainSem I H`
     (`E2E/Complete/Table.lean`) for `D` the strings the node's checks hash (L1, L2);
  5. the node's stack: the execution's witness with the Flock region written by `gen°` (L4);
  6. the node's proof `π := prove H (blindProgram …) S° seed pfuel` for the Flock-blind honest
     strategy `S°` (L5) — **fails** when a proof-of-work search exhausts `pfuel`;
  7. the node's fresh claims for its parent: the transcript's `alpha`, `zSkip`, points and slices,
     the bytecode's true value, and `matrixValue := rLc − α²·eq·⟨skip, s⟩ − α³·wCol[const]`, which
     closes the deferring verifier's terminal (always solvable: coefficient `1`);
  8. `ip.words` lists `(root, word)` of every node's level-0 word.
* **The good events.** (G1) every proof-of-work search finds a nonce within `pfuel`; (G2) at every
  inner node the matrix-batching weights are not both zero — together exactly
  `honestIdeal H T ρ pfuel ≠ none`; (G3, **new**, §2.1) the honest tree's commitments do not
  collide: two entries of `ip.words` with one root are one entry (`RootsInj ip`).
* **Within limits** (`HonestTree.WithinLimits H T ρ pfuel`): at every node the deployed limits
  (`End.Limits`) and the guest's budget (`b2cBudget'.size (work s w) ≤ 2^28`) of the witness
  `honestIdeal` builds, and the node's hashing absorbs fewer than `2^64` block prefixes (L17).

### 1.2 T6-det

```lean
theorem idealVerify_complete (H : Bytes → Digest) (T : HonestTree) {ρ pfuel fuel : ℕ}
    (hρ : validRate ρ) (hT : T.Valid H) (hlim : T.WithinLimits H ρ pfuel)
    {s : NodeStatement} {ip : IdealProof} (hI : honestIdeal H T ρ pfuel = some (s, ip))
    (hroots : RootsInj ip) (hfuel : T.size ≤ fuel) :
    s.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ pure (H x)) guest ip fuel s = true
```

with `honestIdeal_ne_none_iff : honestIdeal H T ρ pfuel ≠ none ↔ PowFound H T ρ pfuel ∧
WeightsNonzero H T ρ pfuel` (the good events by name), and the game's form
(`idealVerify_complete_budget`): when the `Id` run's query count (V_I run in `StateT ℕ Id`
counting `H`) is at most `budget`, `(idealVerify (budgetedQuery budget) guest ip fuel s).run`
from any state with `spent = 0` answers `some true` (L16). `T.size` counts the nodes with
multiplicity; the closure takes at most `1 + Σ |children|` steps over the distinct nodes.

## 2. Is it true for the V_I of `Statement.lean`? Two findings

### 2.1 Colliding commitment roots (false as designed; fix: good event G3)

`nodeStep` looks a node's word up by its stack root (`ip.word r`, the *first* entry with root `r`)
and rejects unless it is well shaped for the node's announced layout. For a constant `H ≡ c`
every Merkle root is `c`; in any honest tree with two nodes whose stacks have different shapes
(e.g. sibling leaves holding one and sixteen signatures, whose tables differ by far more than a
factor of two), one of the two lookups returns the other's word, of the wrong shape, and V_I
rejects. With `c` chosen so that every proof-of-work search succeeds at its first
nonce and the batching weights are nonzero (both are conditions on the single value `c`), G1 and
G2 hold, so T6-det as stated in §4 of the design is **false**. Minimal fix (decision text):

> **E2E-4 (T6-det's third good event).** T6-det assumes the honest tree's commitments do not
> collide (`RootsInj`: two `(root, word)` entries of the honest idealized proof with one root
> are equal). Why: an idealized proof gives one word per root, and V_I finds a node's word by
> its root; under a hash with colliding roots the honest prover cannot give two nodes their
> words. In the random-oracle model the event fails with probability at most the collision
> probability of the honest tree's Merkle hashing, `Q_T²/2^256`. (Alternative, not taken: key
> `IdealProof.words` by root and shape; it changes V_I and not the soundness chain's cost, but
> the good event is free.)

Same-shape collisions are harmless: the lookup returns another honest node's word, whose single
candidate is honest (and whose relation fails on a different public input, so it has no
children), and V_I still accepts.

### 2.2 The decoder's first frame (unprovable as designed; fix: frames named by Π)

V_I follows `(End.decodeB (tableSem rows) t.image).witness.children`. A child's *statement* is
read off `main`'s frame (`valG L 1`), a fixed place. A child's *proof* is read off the first frame
of the memory at which `verify_sub`'s code holds under the table semantics on that call's words
(`Located.frameOfB`, `Located.wVsLB`: `vsProofOf` reads `verify_sub`'s frame-local hint buffer
`σ 14`). T6-det needs that frame to be the honest one (`nodeStep` reads the child proof's
announced sizes and stack root), i.e. that no frame below the honest call's satisfies
`verify_sub`'s whole body on the same words. That is a property of the entire honest memory
image, true in practice but with no proof route short of an analysis of every word of the honest
memory (the completeness side never relates `decode` to the honest witness; `GuestComplete`
does not mention the decoder). Since T2 only uses that the decoded frame holds the callee's code
(`frameDecB_spec`), the minimal fix is:

> **E2E-5 (V_I decodes at the frames Π names).** An idealized proof also names frames
> (`IdealProof.frames : E × E → String → List E → Option ℕ`, by the node's stack root, the
> callee and its words); V_I decodes a candidate with `End.decodeAt (tableSem rows) (ip.frames r)`:
> a located call at the named frame when the callee's code holds there under the table
> semantics, else at the first such frame (`frameOfB`). Why: the first frame is not provably the
> honest call's frame, so the honest prover could not show V_I follows its children's proofs.
> T2 holds unchanged in substance: every decoded witness comes from a frame where the callee's
> code holds (`frameDecB_spec`), so `guest_knowledge_model` generalizes to any frame choice
> (the `Located/*B` decoders take the chooser as a parameter; `decodeB S = decodeAt S none`).

Completeness then needs `DecodeHonest` (L9): at the honest frame of child `i`'s `verify_sub`
call, the code holds under `tableSem rows` and `vsProofOf` reads the honest proof's stream (it is
the buffer `VsMem0.stream` pins, `B1/VerifySub/CData.lean`), and `main`'s frame decodes the honest
children's statements.

### 2.3 Checked and true

* **Precheck and table check with the stateful rows** (`E2E/Complete/Table.lean`, proved, §6):
  if every row is a canonical *chain row* of the strings `D` — non-final rows from the code of the
  prefix absorbed so far to the code of the next one, codes injective on `D`'s prefixes and never
  the IV, final rows `H` of the string — then every standard chain among the rows is the chain of
  a string of `D` and ends at its `H` (`stdChain_chainRows`), so `chainInputs rows ⊆ D` is finite,
  the precheck holds (non-final outputs are injective codes of the absorbed prefix), and
  `tableOKWith (pure ∘ H) rows = true`. The semantics accepting exactly these rows is functional
  (`chainSem_functional`), which the guest's compiled code needs (it shares equal compressions,
  `B2C/ShareSound`'s `KeyHolds.unique`). The guest hashes only standard chains (every `BLAKE2S`
  site starts at the IV or continues a chain, with standard counters, including the runtime
  counters `baseMd`, `windowMd`, `vxMd`), so the semantics is complete for it once `D` holds the
  node's hashed strings.
* **The candidate set is the honest stack.** The honest word is `stackWord μ q₀`; a candidate
  agrees with it on `≥ thrOf ≥ 2^κ` columns of every lane, so its blocks are `q₀`'s
  (degree `< 2^κ`), so it is `q₀` (L8). If `q₀` failed `M3HoldsBlind` on `inputOf pi` the node
  would have no candidate and no children, which V_I accepts; it does not fail
  (`inputOf = publicInputOfDigest`: `ofWords lo hi = K.ofBits (lo + 2^32 hi)`).
* **`candidateRun`** re-runs the honest execution: an execution valid under a semantics of
  canonical rows is the halting Flock-blind run of its image (`haltingRunB_of_validB`, proved) and
  its rows are the semantics' rows (`blakeRows_of_validB`, proved); `imageOf (witnessOf …)` of the
  `gen°` stack is the execution's image (L4).
* **`sizesOf`** returns the honest sizes (`verifierLayout_injective`, admissible by the budget);
  `announced` and `stackRoot` read the honest stream's first ten scalars, `announce s ρ` and the
  root's scalars (L7); `stackShape` is `commitStack`'s shape, so the honest word is well shaped
  and `treeRootM H ht W` is the committed root.
* **The closure's fuel**: each distinct node is expanded once; `T.size ≤ fuel` suffices.
* **The outer checks**: the root's DA vector digests are honest (`T.Valid`), the bytecode part of
  the root's deferred claim is true (at a leaf `AtZero` constrains only the points; the batching's
  bytecode leg is honest); the matrix part is not checked.
* **The children's in-circuit verification**: the deferring verifier is V° plus the terminal
  `require`, closed by the hinted `matrixValue` with coefficient `1` (`Verifier.lean:1975`); the
  Flock-blind sumchecks derive one coefficient per round from the claim and check nothing
  (`sumcheckRoundPoly`), so V°'s Flock messages may be anything; only the slices are bound (ring
  switching), and they are the true slices of the stack's Flock region.
* **The batching** (`batchWith`) checks nothing per round; its final check is `bytecodeFinal =
  v·weight` (honest: the children's bytecode claims are true) and `matrixFinal = a·wA + b·wB`,
  solvable exactly when `(wA, wB) ≠ (0, 0)` (G2).

## 3. Decomposition

`H` total; `CM` a completeness model (L1). Line estimates in brackets.

| | lemma (statement) | carries over / new |
|---|---|---|
| L0 | `stdChain_chainRows`, `tableOK_chainRows`, `precheck_chainRows`, `chainInputs_finite`, `tableOKWith_chainRows`, `chainSem_functional`, `chainSem_step`, `chainSem_final`, `blakeRows_of_validB`, `haltingRunB_of_validB`, `intermediatesOf` | **done** (`E2E/Complete/Table.lean`) |
| L1 | **done** (`E2E/Complete/Model.lean`) `CompModel`: a functional `sem`, an answered `H : Bytes → Option Digest`, prefix cells `st`, with `st [] = ivCells`, canonical, and for `H x = some d` every whole block `i` of `x` checks from `st (prefixAt x i)` to `st (prefixAt x (i+1))` and the last block from `st (prefixAt x (nBlocks x))` to `digestScalars d`. Instances: `CompModel.deployed` (`absorbBlocks`), `CompModel.chain I H D` (L0, `H_D x = if x ∈ D then some (H x)`) | new [300] |
| L2 | **the guest's completeness over a model** (`GuestCompleteModel`): for every `CM`, `NodeRelWith CM.H s0 pc pr bc seed s w`, `Limits`, `CapsAgreeWith`, the budget ⇒ `∃ t, ValidExecutionB CM.sem guest (publicInputOf pi) t ∧ t.committedSizeB CM.sem ≤ 2^28 ∧ DecodeHonest t w` (`statementDigestWith CM.H seed s = some pi`); at `CompModel.deployed` it is `guest_complete` | redo, §4 [22–35k] |
| L3 | `constraintCompletenessB S` (`S` canonical): `ValidExecutionB S` ⇒ `SatisfiedByB ∧ AssignmentRepresentsB S`; `Trace.countB`, `committedSizeB`, `exists_admissible_witnessB` | parametrize `Arithmetization/Completeness/*` (6–7 files) [1.5–2.5k] |
| L4 | `gen°` (all 18 limbs into `F₀.slot`, `slots_gen°` unconditional, no R1CS), `stackOf°`, `m3HoldsBlind_stackOf°`, `paddingHonest_stackOf°` (no `padLimbs_compress`), `witnessOf_stackOf°` | `LeanIsa/Complete.lean` minus `blake2s_valid` [0.6–1k] |
| L5 | **done** (`Protocol/EndToEnd/Blind/Complete.lean`) `runI_blindProgram`: for `M3HoldsBlind` + `PaddingHonest` at admissible sizes and a valid rate, the honest strategy with the Flock-blind script (zero messages, true slices) wins every interactive run of `blindProgram` | `Complete/Assemble.lean` with `Phases°` (bus, table, public lemmas restated for `M3HoldsBlind`: their proofs never use `aux`; `follows_ringSwitch` unchanged) [0.8–1.2k] |
| L6 | `exists_prove_verifyBlindWith H` (**done**), and `verifyDeferredWith_honest`: the same proof is accepted by the deferring verifier with the honest fresh claims (open; design §5.1) | [0.6–1k] |
| L7 | **done** (`E2E/Complete/Stream.lean`, `nodeHead_prove`) the honest stream starts `announce s ρ ++ [root₀, root₁]`, root `treeRootM H ht (stackWord μ q)`; `announced`, `stackRoot`, `stackShape` on it | new (unfold `proveFrom` over `readSizes`, `commitStack`) [0.3–0.5k] |
| L8 | **done** (`E2E/Complete/Candidates.lean`, `Node.lean`'s `blindCandidates_stackWord`) `blindCandidates … (stackWord μ q₀) ⊆ {q₀}` | `enc_injective` on a subset of `≥ 2^κ` points, `eq_of_blockOf_eq` [0.3k] |
| L9 | E2E-5's `decodeAt`, T2 over any frame chooser (**done**: `Located/*B.lean` take the chooser, `End.decodeAt`, `guest_knowledge_model_at`, `GuestHypsM.open_stacked` at every chooser with `wOLB_spec_deployed`), `DecodeHonest` (open) | Located*B parametrized [0.5k]; honest frames [1–2k] |
| L10 | `honestIdeal` and `honestIdeal_ne_none_iff` | new [0.8–1.5k] |
| L11 | the batching with hinted values: `batchWith H s0 cs h = some (some defer)`, bytecode part true | sumcheck completeness of `batchRounds` [0.5–1k] |
| L12 | the node relation of the honest node, `NodeRelWith (some ∘ H)` (from L6, L11, `T.Valid`) | [0.3k] |
| L13 | **done modulo L2, L9 as hypotheses** (`E2E/Complete/Node.lean`) `nodeStep_honest`: an honest node's step returns its children's nodes (L0, L2, L4, L7, L8, L9, G3) | [0.6–1k] |
| L14 | **done** (`closure_accepts`, over any good set with a size) `closure_honest`: the closure over honest nodes accepts within `T.size` | [0.3k] |
| L15 | **done modulo L6** (`idealVerify_accepts`, `outerChecksWith_true`) the root: V° (L6) and `outerChecksWith` | [0.3k] |
| L16 | the budgeted run (`budgetedQuery`) equals the `Id` run when the count is within `budget` | naturality of `idealVerify` in the hash [0.4–0.6k] |
| L17 | the node's hashed strings `D` (the queries of `NodeRelWith`'s checks at `H`, logged) have `< 2^64` prefixes under `Limits` | reduced to a count on `nodeLog` (`NodeLog.lean`, `TreeLog.lean`; decision T6-2 of `e2e-security.md`); the count proved from `Limits` and `NodeRelWith` (`nodeLog_count_lt`, `Count/*.lean`, `l17-count.md`) |

Total ≈ 32–50k lines, of which L2 is two thirds. The design's 6–13k assumed the guest's
completeness would transfer from the deployed one; it does not (§4.1).

## 4. The guest's completeness under the table semantics (L2)

### 4.1 Decision: a model version, not a transfer

A transfer from the deployed completeness ("an execution valid under BLAKE2s is valid under any
semantics accepting its rows", `runB_of_runRows`) gives executions whose rows are compressions:
their standard chains end at `blake2sBytes x`, not `H x`, so the table check fails for every
`H ≠ blake2sBytes` on the hashed strings, and the children's proofs, made with `H`, are not the
ones a BLAKE2s execution verifies. Nor can the deployed proof be re-instantiated: it never takes a
row's existence as input but evaluates `compress` (`compressCells_iff.mpr`, `chainRun`,
`blake2s_default_iff`, `compress_of_hashPair`, `hon_sig`, `compress_seed`), and `blake2sBytes`
cannot be a chain of *any* fixed function agreeing with `H` on all strings (pigeonhole on
prefixes). So L2 is the deployed completeness **over a completeness model** (L1), the dual of
W2's `HashModel`: where W2 reads a digest off an answered hash (`HashModel.final`), completeness
*builds* the rows of an answered string (`CompModel.step`, `.final`), the intermediate cells
`st (prefixAt x i)`; the answered `H` makes the semantics accept only rows of the strings the
node's checks hash, so the guest hashes nothing else (the table check needs this), with no
invariant to carry.

### 4.2 Work, by layer (from the survey of `guest_complete`'s closure)

| layer | what | size |
|---|---|---|
| Memory | `Tree.Valid`, `Ev.Holds` reach `Atom.Holds` (`Core.lean:205`): `…B S` copies of `Memory/Eval`, `Placed`, `Regions`, `Tree`, `Discharge`, `Retemp`, `StaticSound`, `Memory.lean` (`CoreB` exists) | ≈7.3k, mechanical |
| B2C | `LHolds .blake`, `KeyHolds` 2/3 and `KeyHolds.unique` (by `Functional`), `BookOk`, `CplJust`, `ShareSound`, `Frame`, `FrameAll`, `Count`, `CplExec`, `CplSem`, `CplWalk*`, `CplRun`, `CplComp`, `CplSites`, `CplAll`, `B2`, `B2Final`, `Cpl`'s `KidsRun`; the generated checkers (`cplWin`, `shareWin`, `WinOk`, 1,254 modules) are `decide` facts and stay | ≈9k, mechanical |
| B1 hash sites | the backward halves over `CM` of every function computing a `BLAKE2S`: `holds_fsCompressT`/`holds_squeezeT` (`FsBlocks`), `compressCells_chainRun` sites (`Digest/*`, `Da/*`), `compress_of_hashPair` (`Whir/Cap`, `QueriesComplete`), `compress_final_iff`/`compress_two_iff`, `hmid` (`Sig/Hashing`), `compress_seed` (`VerifySub/CFront`), the `completeAt_of_rel_pure` sites; functions free of `BLAKE2S` by `relB_iff_rel_of_freeOn` | ≈6–12k |
| Main | `MainComplete` over `CM` (`B1/Main/MainBudget`, `HonestAll`, `CalleesAt`, `CalleesProved`, `AggComplete` with `s0` (pattern D), `ChildrenAt`, `HonestMain`), `CapsAgreeWith H` (`queriesOf` at `H`; `capAgrees_of_tree` for one tree's openings) | ≈2–4k |
| End | `CompletePiecesWithin` over `S`: `honest_of_main`, `guest_complete_within`, `committedSizeB`, the counts (`B2cCount` over `RunC` at `runB`) | ≈1k |
| Decode | `DecodeHonest` (L9) | ≈1–2k |

All new modules beside the deployed ones (decision W2-1's pattern); `Core`, `Logic`, `Exec`,
`CheckSound` untouched. Each copied layer recovers the deployed one at `blakeDeployed`
(`…B_deployed`), and `GuestCompleteModel` at `CompModel.deployed` re-derives `guest_complete`
(the analogue of `guest_knowledge_of_model`).

## 5. Order

1. ~~L0, L8, L7, L1~~ (done) — the V_I side's feasibility.
2. ~~L5~~ (done), L4, L6 — V° completeness with hinted values.
3. L10–L12 with L2 and L9's `DecodeHonest` as named hypotheses (`GuestCompleteModel`); L13–L15
   are proved over hypotheses of exactly that shape, so T6-det assembles from them.
4. L3, L16, L17, then L2 by layers (Memory, B2C in parallel; B1 hash sites by subtree as in
   `w2-guest-model.md` §4; Main; End), and L9.

Risks: L2's size (parallel agents as in W2); L9's honest frames (the coverage of the honest
tree's `BLAKE2S` atoms by the run's rows, which `BodyAtB (tableSem rows)` at the honest frame
needs — an invariant of the B2C copy); L17 if kept as a hypothesis.

### 5.1 L6's open half: the deferring verifier on V°'s proof

`deferredProgram c` is `verifyExecution (.claimed c)`: it differs from `blindProgram` at two
places only, the bytecode's value in the bus phase (`require (point = c.bytecodePoint)`, then
`c.bytecodeValue`) and the lincheck's end (`require` that `c`'s `alpha`, `zSkip`, points and
slices are the run's, then the terminal with `c.matrixValue`). With `c` read off V°'s run along
its Fiat–Shamir challenges (the bytecode's true value; `matrixValue := rLc − α²·eq·⟨skip, s⟩ −
α³·wCol[const]`, coefficient `1`), both `require`s pass and the two programs make the same moves,
so the honest proof is the same and the deferring verifier accepts it. The deployed compilation
lemma (`runProof_prove`) needs acceptance against *every* challenge, which `.claimed c` (one
transcript's values) does not have, so this needs a run along one challenge function:
`fsRun S fuel p cv h` (the interactive run at the challenges `proveFrom` squeezes), its `bind`
lemmas with `proveFrom`'s, `run_proveFrom_fs` (`run_proveFrom` with `fsRun`'s acceptance in place
of `AcceptsFrom`), and the two programs' agreement phase by phase (`bind` congruence; the
common prefixes literally equal). No new mathematics; ≈ 0.6–1k lines.

## 6. Status

**Proved** (no escapes; every lemma below depends only on `propext`, `Classical.choice`,
`Quot.sound`, pinned in `tests/LeanVMTests/E2E/CompleteTable.lean`):

| file | lines | content |
|---|---|---|
| `LeanVM/E2E/Complete/Table.lean` | 656 | L0: the honest table (`ChainRow`, `chainSem`, `Intermediates`, `intermediatesOf`); `stdChain_chainRows`, `tableOK_chainRows`, `precheck_chainRows`, `chainInputs_finite`, `tableOKWith_chainRows`, `chainSem_functional`, `chainSem_step`, `chainSem_final`; `runRows_eq_of_runB`, `blakeRows_of_validB`, `steps_unique`, `haltingRunB_of_validB` |
| `LeanVM/E2E/Complete/Model.lean` | 180 | L1: `CompModel`, `CompModel.deployed` (BLAKE2s, `absorbBlocks`), `CompModel.chain` (the honest table), `tableOKWith_of_validB`, `haltingRunB_of_validChain` |
| `LeanVM/E2E/Complete/Candidates.lean` | 78 | L8: `enc_eq_of_agreeOn`, `eq_of_mem_candidates_stackWord`, `eq_of_mem_candidates_deployed` |
| `LeanVM/E2E/Complete/Stream.lean` | 267 | L7: `readSizes_honest`, `announced_announce`, `proveFrom_readN_bind`, `prove_stream_head`, `nodeHead_prove` |
| `LeanVM/E2E/Complete/Node.lean` | 268 | L8's `blindCandidates_stackWord`, `sizesOf_verifierLayout`, `nodeStep_honest` (L13, the guest's table check and decoding as hypotheses), `closure_accepts` (L14), `outerChecksWith_true`, `idealVerify_accepts` (L15) |
| `LeanVM/Protocol/EndToEnd/Blind/Complete.lean` | 470 | L5: `replay`, `follows_replay`, `hFlockBlind`, `follows_hFlockBlind`, the bus/table/public phases from `M3HonestBlind`, `follows_verifyExecutionBlind`, `runI_blindProgram`, `exists_prove_verifyBlindWith` (V° accepts the honest proof for every `H`, no `WalkFaithful`) |
| `LeanVM/E2E/Complete/Interfaces.lean` | 181 | the interfaces L2 and L9 target: `queriesOfWith`, `NodeIsWith`, `BatchAgreesWith`, `CapsAgreeWith` (`capsAgreeWith_blake2s`: at BLAKE2s it is `End.CapsAgree`), `Frames`, `DecodeHonest fr t w`, `GuestCompleteModel` |
| `LeanVM/Arithmetization/CompletenessB/Count.lean` | 65 | `runCountB`, `Trace.countB`, `Trace.committedSizeB` (namespace `LeanVM.Semantics`), `committedSizeB_deployed` |
| `LeanVM/Arithmetization/CompletenessB/Rows.lean` | 145 | L3: `Canonical S`, `executeWithB_ne`, `blake2sBindings_of_execB`, `rowOf_sendsB`, `readAddrs_validB` |
| `LeanVM/Arithmetization/CompletenessB/Satisfied.lean` | 481 | L3: the skeleton witness under a canonical semantics, `skelWitness_satisfiedByB` |
| `LeanVM/Arithmetization/CompletenessB/Theorem.lean` | 299 | L3: `runRowsB`, `countB_eq_runRowsB`, `ImageOf`, `constraintCompletenessB_rows` |
| `LeanVM/Protocol/LeanIsa/CompleteB.lean` | 448 | L4: `SlotsOK`, `genFree`, `slotsOK_genFree`, `stackOfG`, `m3HonestBlind_stackOfG` (relation without Flock + honest padding), `witnessOf_stackOfG` |
| `LeanVM/E2E/Complete/Stack.lean` | 109 | L3 + L4: `exists_admissible_witnessB`, `exists_stack_of_validB` (admissible sizes, `M3HoldsBlind`, `PaddingHonest`, `candidateRun = some t`) |
| `LeanVM/E2E/Complete/FsRun.lean` | 341 | §5.1: `fsRun` (the run along the Fiat–Shamir challenges), `run_proveFrom_fs`, `runProof_of_fsRun`, `fsRun_bind`, `proveFrom_bind_of_fsRun`, `fsRun_of_acceptsFrom`, `FsSame` and its congruences |
| `LeanVM/E2E/Complete/Deferred.lean` | 361 | L6's deferring half: the bus and lincheck phases split at their `require`s (`verifyBusBalance_eq`, `verifyFlockLincheck_eq`, `…Blind_eq`), `AllRet`, `exists_deferred_honest` (the honest fresh claims `c`: bytecode value true, the same honest proof, the run returns), `verifyDeferredWith_honest` |
| `LeanVM/E2E/Complete/Prover.lean` | 227 | L10: `HonestTree`, `Entry`, `HonestOut`, `honestDefer` (the honest hints, `Hints.lean`), `NodeExec`, `freshFor` (accepted, bytecode true, caps agreeing), `honestStep`, `honestOut`, `idealOf` (words and the honest frames of each root), `honestIdeal`, `RootsInj` (E2E-4 on the prover's entries) |
| `LeanVM/E2E/Complete/Assemble.lean` | 399 | **T6-det**: `honestDefer_spec`, `honestStep_spec`, `nodeStep_out`, `GoodOut`, `honestOut_good`, `honestOut_root`, `idealVerify_complete` |
| `LeanVM/E2E/Complete/NonVacuity.lean` | 203 | L12 `nodeRel_honest`; node-level non-vacuity `honestStep_isSome` from `GuestCompleteModel` (L2), `NodeSupport` (L17 kept a hypothesis), `PowGood`; `honestOut_child`, `freshFor_spec` |
| `LeanVM/E2E/Complete/Hints.lean` | 323 | L11: `lead`, `roundPoly_lead`, `honestRounds`, `run_honestRounds` (the honest rounds close at the polynomial at the challenges), the transcript (`bStart`, `bEnd`, `mStart`, `mEnd`), `honestWeights` (G2's weights), `honestHints`, `batchWith_honestHints` (the batching accepts them, the bytecode part true, when the weights are not both zero) |
| `LeanVM/E2E/Complete/Caps.lean` | 325 | `heapLabel`, `climb_take_label`, `getD_path_label`, `nodeIsWith_openingAt`, `batchAgreesWith_openingAt` (one tree's openings below its leaf count agree), `QRange`, `queriesOfWith_proveFrom` (the query steps on an honest proof are honest openings) |
| `LeanVM/E2E/Complete/CapsRange.lean` | 494 | `NoCQ` and the phases before WHIR, `allRet_foldRounds`, `allRet_sampleQueriesAux`, `glue_folds`, `qRange_whirLevels`, `qRange_verifyExecution`, `qRange_deferredProgram` (the deferring verifier queries every tree below its leaf count), `queriesOfWith_deferred_honest` |
| `LeanVM/E2E/Natural.lean` | 255 | `rel_idealVerify` (V_I under a relation of two monads' computations closed under `pure`, `bind`), `IsMorphism`, `idealVerify_natural` |
| `LeanVM/E2E/Budget.lean` | 263 | L16: `Counted`, `queryCount`, `charge` (a monad morphism), `simHash` (a monad morphism), `simHash_budgetedQuery`, `run_idealVerify_budgetedQuery`, `run_idealVerify_budgetedQuery_of_le`, `hashImplOf` |
| `LeanVM/E2E/Complete/Tree.lean` | 369 | `HonestTree.AllNodes`, `Valid`, `WithinLimits` (L17's `NodeSupport` a field), `PowFound` (G1), `WeightsNonzero` (G2), `RootsInjAt` (G3); `honestDefer_some`, **`honestOut_isSome`**, **`idealVerify_complete'`**, `idealVerify_complete_budget` |

**T6-det as proved** (`Assemble.lean`):

```lean
theorem idealVerify_complete (H : Bytes → Digest) (T : HonestTree) {ρ pfuel fuel : ℕ}
    (hρ : validRate ρ) {o : HonestOut} (hI : honestOut H ρ pfuel T = some o)
    (hroots : RootsInj o.entries) (hfuel : T.size ≤ fuel)
    (hda : ∀ c ∈ T.claims.da,
      Da.toBytes c.2 = Id.run (Da.vectorDigestOfWith (fun x ↦ (pure (H x) : Id Digest)) c.1)) :
    o.stmt.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest (idealOf o) fuel o.stmt = true
```

It differs from §1.2 in shape only: the honest prover returns `some` exactly when every node
finds an execution (classical choice inside `honestStep`, so the theorem needs neither L2 nor
L9's `DecodeHonest` as hypotheses — they appear where they belong, in non-vacuity), and E2E-4 is
stated on the prover's entries.

**Non-vacuity and the combined form** (`Tree.lean`):

```lean
theorem honestOut_isSome (hL2 : GuestCompleteModel) (hρ : validRate ρ) :
    ∀ T : HonestTree, T.AllNodes (HonestTree.ValidAt H) → T.WithinLimits H ρ pfuel →
      T.PowFound H ρ pfuel → T.WeightsNonzero H ρ pfuel → ∃ o, honestOut H ρ pfuel T = some o

theorem idealVerify_complete' (hL2 : GuestCompleteModel) (T : HonestTree) {fuel : ℕ}
    (hρ : validRate ρ) (hv : T.Valid H) (hlim : T.WithinLimits H ρ pfuel)
    (hpow : T.PowFound H ρ pfuel) (hw : T.WeightsNonzero H ρ pfuel)
    (hroots : T.RootsInjAt H ρ pfuel) (hfuel : T.size ≤ fuel) :
    ∃ s ip, honestIdeal H ρ pfuel T = some (s, ip) ∧ s.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest ip fuel s = true
```

L2 (`GuestCompleteModel`, whose third conclusion is L9's `DecodeHonest`) is the one named
hypothesis besides the tree's validity (`Valid`: holders verify, the root's DA claims carry their
vector digests), the limits (`WithinLimits`: `Limits`, the budget, and L17's `NodeSupport`, kept a
field there) and the good events G1–G3 by name. The honest hints are now explicit
(`honestHints`): the bytecode sumcheck's honest rounds, zero matrix rounds with the final values
solved for, so G2 is a function of `H` alone; `freshFor` also asks its claims' query steps to
agree in the caps (`queriesOfWith_deferred_honest`), which the children's `CapsAgreeWith` needs.
The game's form (`idealVerify_complete_budget`) adds L16 (`run_idealVerify_budgetedQuery_of_le`).

L16 (`Budget.lean`), for any lawful `b` and any `impl` answering every hash query `x` with
`pure (H x)`:

```lean
simulateQ impl (((idealVerify (budgetedQuery budget) prog ip fuel s).run).run st) =
  pure (if queryCount H prog ip fuel s = 0 ∨ st.spent + queryCount H prog ip fuel s ≤ budget
    then (some (Id.run (idealVerify (fun x ↦ (pure (H x) : Id Digest)) prog ip fuel s)),
      { st with spent := st.spent + queryCount H prog ip fuel s })
    else (none, { st with spent := max st.spent budget }))
```

**Proved since**: L2 and L9's `DecodeHonest`, as `guestCompleteModel : GuestCompleteModel`
(`E2E/Complete/DecodeFinal.lean`): the executions (`guestCompleteModelExec`, `GuestModelAll.lean`)
from group B1's completeness over every model, `open_stacked` included (`Comp/Whir/Loc*`), and the
decoding by main's tree form (`Main/*T.lean`, `EndCompleteCT*.lean`): every tree carries the loads of
the words its decoder reads (`LoadsWords`, the callees' `…BST`/`…WCL` forms), the honest image reads
every instance's load equations and, off frames, 0 or the layout's words (`honestAtB_retemp_F`), so
the children's count (`decode_count`), statements (`decode_stmts`, `kidStmt_honest`) and proofs
(`d3HypO`, at the frame chooser `frOf` of the honest instances, told apart by their arguments:
`vsArgsAt_inj`, the cursor and `os_inj`) read back the honest ones. T6-det without L2 is
`idealVerify_complete_det`. L17 is reduced to a count on the node's log (`NodeLog.lean`,
`TreeLog.lean`, decision T6-2 of `e2e-security.md`), and the count is proved (`nodeLog_count_lt`,
`l17-count.md`): T6-det under the deployed limits and budget alone is
`idealVerify_complete_final` (`Count/Final.lean`).

**Open**: T6-prob (the good events' probabilities under the random oracle; note that the
node's execution, sizes and stack are still a classical choice in `honestStep`, which a
probability bound on G1 must replace by a choice that does not look at the grinds' answers).
