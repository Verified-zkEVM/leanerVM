# L17: the node's log count, from the deployed limits

Package L17 of [`t6-completeness.md`](t6-completeness.md) (§3), decision T6-2 of
[`e2e-security.md`](e2e-security.md) (§7). T6-det (`idealVerify_complete_det`,
`LeanVM/E2E/Complete/DecodeFinal.lean`) assumes, at every node, through `HonestTree.WithinLimits'`
(`TreeLog.lean`), the count

    (prefixesOf (nodeLog H s w)).length < 2 ^ 64.

This note plans its proof from what the tree's conditions already give, so that T6-det holds
under the deployed limits and budget alone.

## 1. The goal

```lean
theorem nodeLog_count_lt {H : Bytes → Digest} {s : NodeStatement} {w : NodeWitness}
    (hlim : End.Limits s w)
    (hrel : NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell
      B1.Main.daPadRow End.bytecode (seedOf H) s w) :
    (prefixesOf (nodeLog H s w)).length < 2 ^ 64
```

Both hypotheses are at hand at every node of a valid honest tree: `End.Limits` is a field of
`LimitsAt`, and `NodeRelWith (some ∘ H)` is `nodeRel_honest` (`NonVacuity.lean`, L12) from the
node's `ValidAt`, the children's `honestOut_child` and `honestDefer`, with no induction (the
children's outputs are given by `kidOuts … = some kos`). So:

* `HonestTree.LimitsBudgetAt H ρ pfuel` / `HonestTree.WithinLimitsBudget`: `LimitsAt'` without its
  count field (the deployed limits and the budget);
* `HonestTree.withinLimits'_of_budget (hρ) (hv : T.AllNodes (ValidAt H))
  (h : T.WithinLimitsBudget H ρ pfuel) : T.WithinLimits' H ρ pfuel`, node by node
  (`HonestTree.allNodes_and` and `allNodes_imp`);
* `idealVerify_complete_final`: `idealVerify_complete_det` with `hlim : T.WithinLimitsBudget H ρ
  pfuel` in place of `WithinLimits'`.

## 2. Why the count is small: only long strings count

`prefixesOf D` has one entry per whole non-final block of each string: `nBlocks x = (|x| − 1)/64`
(`Table.lean:140`). A string of at most 64 bytes has **none**. Every Fiat–Shamir step
(`absorbBlock`: a 32-byte state and a 32-byte block), every proof-of-work hash, every Merkle node
(`climb`: two 32-byte digests), every batching step (`observeWith`, `squeezeWith`), the child's
seed, the signer-set digest and every DA tree node is exactly 64 bytes. So the hint rounds,
the proof stream's length and the Merkle paths' heights do not matter: the strings with prefixes are

| where | string | blocks | bounded by |
|---|---|---|---|
| a statement's digest (node; each child twice: `childLog`, `childClaimsM`) | the leanXMSS / leanSPHINCS claim lists (64 bytes a claim), the DA list (64 a claim), the final string (96 + 24 per cell, padded) | `≤ n_x + n_s + n_d + cells + 3` | `Limits.coverage` (node), `Limits.lists`, `Limits.daRoots` (children); `Shaped` (`NodeRelWith`): `cells = 22 + 1 + 28 + 2` |
| a child's deferring verifier | the opened leaves, `8·width` bytes, hashed only when the leaf has the committed width (`openOne`) | per leaf `≤ (8·192 − 1)/64 = 23` | the program: only `commitStack` and `whirLevels` commit or query; widths `2^fold`, `3·2^fold`, `fold ≤ 6`; positions per level `≤ level.queries`, `Σ ≤ 368` (`queryTable`) |
| a held leanXMSS / leanSPHINCS signature | the tweakable hashes' inputs, fixed-size (signatures are `Fin`-indexed) | `≤ 384` resp. `≤ 686` queries (`verify_isTotalQueryBound`, `sphincsVerify_isTotalQueryBound`) × a constant | the claims' count `< 2^16` (`Limits.coverage`) |
| a held DA matrix | cells (2048 bytes), row digests (2048), the vector (`2^15 · 24` bytes) | `≤ 1024·64·31 + 1024·31 + 128·1024·31 + 12287 ≈ 2^22.6` | `OpensWith` (`NodeRelWith`): `rows ≤ 1024`, `|vector| = 2^15`; at most 16 DA claims (`Limits.daRoots`) |

At the deployed limits: node statement `< 2^17`; 16 children × (2 statements `< 2^18` + verifier
`368·23 = 8464`); signatures `< 2^16 · (384 + 686) · c`, `c ≤ 16`; one DA matrix `< 2^23`.
The total is below `2^38`, far below `2^64`.

**No hypothesis is missing.** `Limits.stream` and `Limits.stackLog` are not used: the program
bounds the child's leaves whatever its stream (a `require` rejects out-of-window layouts, and
`ladder` is `none` outside them). The count is not bounded by `Limits` alone: a direct DA holder's
rows and vector, and the deferred claims' cells, are bounded by `NodeRelWith` (`OpensWith`,
`Shaped`), which is why the hypothesis is `NodeRelWith`, available at every honest node. The
survey's 3–5 days for "counting inside the child verifier" assumed every hash counts; it does
not, and the phases before WHIR are already proved to neither commit nor query (`NoCQ`,
`CapsRange.lean`), so that part is about a day.

## 3. The framework (shared; L17-F, done first)

`LeanVM/E2E/Complete/Count/Basic.lean`:

* `prefixCount D := (prefixesOf D).length`; `prefixCount_nil`, `_cons`, `_append`, `_singleton`
  (`= nBlocks x`), `prefixCount_flatMap_le`, `nBlocks_le_of_length_le`
  (`|x| ≤ 64 (k + 1) → nBlocks x ≤ k`), `nBlocks_eq_zero_of_length_le` (`|x| ≤ 64`);
* `LogM`: `log_pure`, `log_bind`, `val_bind`, `log_map`, `log_hash`; `prefixCount_mapM_le`
  (`∀ a ∈ l, prefixCount (f a).log ≤ c → prefixCount (l.mapM f).log ≤ l.length * c`);
* `LogShort x` (every logged string at most 64 bytes, so `prefixCount x.log = 0`), closed under
  `pure`, `bind`, `map`, `mapM`; over a state (`LogShortS`), closed under `StateT`'s `bind`
  and `forIn` (for the batching);
* the schemes: `prefixCount_simulateQ_le`: for `oa : OracleComp (Bytes →ₒ β) α` with
  `IsTotalQueryBound oa n` and `AllQueriesSatisfy oa (fun t ↦ nBlocks t ≤ c)` (VCVio),
  `prefixCount (simulateQ (fun x ↦ f <$> LogM.hash H x) oa).log ≤ n * c`.

`LeanVM/E2E/Complete/Count/Prog.lean`, the cost predicate on the verifier language:

```lean
/-- Every commitment of `p` has width at most `W`, and `p` opens at most `n` leaves. -/
def LeafBound (W : ℕ) : Prog α → ℕ → Prop
  | .ret _, _ | .fail, _ => True
  | .read k, n | .sample k, n => ∀ x, LeafBound W (k x) n
  | .grind _ k, n => LeafBound W k n
  | .commit _ w k, n => w ≤ W ∧ LeafBound W k n
  | .query _ ps k, n => ps.length ≤ n ∧ ∀ rows, LeafBound W (k rows) (n - ps.length)
```

`LeafBound W p n` (the program before the count):

* `LeafBound.mono`, `LeafBound.bind` (`n₁ + n₂`), `LeafBound.bind_allRet` (through `AllRet`),
  `LeafBound.of_noCQ` (`NoCQ p → LeafBound W p n`), `LeafBound.bind_noCQ`;
* `leafBlocks W := (8 * W - 1) / 64`; **`prefixCount_run_le`**: `LeafBound W p n → (∀ r ∈ st.roots,
  r.2.2 ≤ W) → prefixCount (run (LogM.hash H) p st).log ≤ n * leafBlocks W` (by induction on `p`;
  `openAll` logs per position one leaf of the committed width and 64-byte nodes);
* `prefixCount_runProof_le`, `prefixCount_verifyDeferredWith_le` (the seed is 64 bytes);
* the deployed constants `whirLeafWidth := 192`, `whirLeaves := 368`.

## 4. The per-program bounds and the packages

Each package is one new file under `LeanVM/E2E/Complete/Count/`, importing only the framework
(and what it names), with a fixed interface, so all run in parallel. The constants named
`…Blocks` are the package's to define; the assembly uses only the `_le` caps.

**A. The child's deferring verifier** (`Count/Whir.lean`; ≈ 350 lines, 1 day). Imports
`Count/Prog.lean`, `CapsRange.lean` (`NoCQ`, `noCQ_*`, `AllRet`).

```lean
theorem leafBound_deferredProgram (c : FixedClaims) (bytecode : List K) (pi : Digest) :
    LeafBound whirLeafWidth (deferredProgram c bytecode pi) whirLeaves
```

Steps: `ladder_fold_le` (`l ∈ ladder μ r → l.fold ≤ 6`: `shape`'s first fold is `initialFold`,
`levelsFrom`'s are `min subsequentFold _`); `ladder_queries_sum_le` (`(cfg.map (·.queries)).sum ≤
368`, the sum being a `queryTable` entry's, all checked by `decide`);
`allRet_sampleQueriesAux_length` (`≤ remaining`); `leafBound_whirLevels` (by induction on the
levels, as `qRange_whirLevels`: cost `(levels.map (·.queries)).sum`, commitment width `3·2^fold`);
`leafBound_verifyExecution` (as `qRange_verifyExecution`: `readSizes`, the bus, the tables, the
public input, Flock and ring switching are `NoCQ`; `commitStack`'s width `2^fold ≤ 64`); the
`return true`.

**B1. leanXMSS verification** (`Count/Xmss.lean`; ≈ 150 lines, 0.5 day). Imports
`Count/Basic.lean`, `E2E/Reduction/VerifyBound.lean`.

```lean
def xmssVerifyBlocks : ℕ
theorem prefixCount_xmssVerifyWith_le (H : Bytes → Digest) (pk : LeanXmss.PublicKey)
    (msg : LeanXmss.Message) (σ : LeanXmss.Signature) :
    prefixCount (xmssVerifyWith (LogM.hash H) pk msg σ).log ≤ xmssVerifyBlocks
theorem xmssVerifyBlocks_le : xmssVerifyBlocks ≤ 2 ^ 20
```

Steps: `AllQueriesSatisfy (Concrete.verify pk msg σ) (fun t ↦ t.length ≤ L)` by the structure of
`VerifyBound.lean` (`tweakableHashInput`: 16 bytes, the tweak, a fixed-size payload; the leaf
hashes 58 chain ends), then `xmssVerifyWith_eq_simulateQ` and `prefixCount_simulateQ_le` with
`verify_isTotalQueryBound`.

**B2. leanSPHINCS verification** (`Count/Sphincs.lean`; ≈ 300 lines, 0.5–1 day). The same, with
`sphincsVerifyBlocks`, `prefixCount_sphincsVerifyWith_le`, `sphincsVerifyBlocks_le : ≤ 2 ^ 20`,
along `SphincsBound.lean`'s verification half (lines 41–255) and
`sphincsVerify_isTotalQueryBound`.

**C. A DA opening** (`Count/Da.lean`; ≈ 200 lines, 0.5 day). Imports `Count/Basic.lean`.

```lean
def daOpenBlocks : ℕ
theorem prefixCount_daLog_le (H : Bytes → Digest) (pc pr : LeanDa.Digest) (w : Da.Witness)
    (hr : w.rows.length ≤ LeanDa.maxRows) (hv : w.vector.length = 2 ^ LeanDa.logM) :
    prefixCount (daLog H pc pr w) ≤ daOpenBlocks
theorem daOpenBlocks_le : daOpenBlocks ≤ 2 ^ 30
```

Steps: `listCellDigestWith` hashes at most 256 symbols whatever the row (`listCell` is a
`drop`/`take`), 31 blocks; `rowDigestWith` 64 cells and 2048 bytes; `treeRootFuel` and
`treeLevelWith` are `LogShort`; the columns `128 · nPad r ≤ 128 · 1024` cells (padding cells
hash nothing); the vector `2^15 · 24` bytes. Rows of any length.

**D. Statements and the batching** (`Count/Stmt.lean`; ≈ 200 lines, 0.5 day). Imports
`Count/Basic.lean`.

```lean
def stmtBlocks (s : NodeStatement) : ℕ :=
  s.claims.xmss.length + s.claims.sphincs.length + s.claims.da.length + s.defer.cells.length + 3
theorem prefixCount_statementDigestWith_le (H : Bytes → Digest) (seed : Digest) (s : NodeStatement) :
    prefixCount (statementDigestWith (LogM.hash H) seed s).log ≤ stmtBlocks s
theorem prefixCount_childClaimsM_le (H : Bytes → Digest) (seed : Digest) (cs : List Child) :
    prefixCount (childClaimsM (LogM.hash H) seed cs).log ≤ (cs.map (stmtBlocks ·.statement)).sum
theorem prefixCount_batchWith (H : Bytes → Digest) (s0 : Digest) (cs : List ChildClaims)
    (h : BatchHints) : prefixCount (batchWith (LogM.hash H) s0 cs h).log = 0
```

The batching by `LogShortS` through `batchWith.go` (the proof of `rel_batchWith`, unary).

**E. Assembly** (`Count/Node.lean`, `Count/Final.lean`; ≈ 300 lines, 0.5 day; after A–D).
`prefixCount_nodeLog_le` (the sum of the parts, `holdersLog` over the direct holders,
`Forall₂` for the DA holders' shapes), `nodeLog_count_lt`, §1's tree statements and
`idealVerify_complete_final`; `Witness.lean`'s leaf under `WithinLimitsBudget`
(`idealVerify_complete_wTree` restated in a test); the axiom pins in `LeanVM.lean` and
`tests/LeanVMTests/Guest/`; decision T6-2 and §8 of `e2e-security.md`, the L17 row of
`t6-completeness.md`.

| package | file | lines | agent-days | depends on |
|---|---|---|---|---|
| F framework | `Count/Basic.lean`, `Count/Prog.lean` | 400 | 0.5 | — |
| A verifier (WHIR) | `Count/Whir.lean` | 350 | 1 | F (`Prog`) |
| B1 leanXMSS | `Count/Xmss.lean` | 150 | 0.5 | F (`Basic`) |
| B2 leanSPHINCS | `Count/Sphincs.lean` | 300 | 0.5–1 | F (`Basic`) |
| C DA | `Count/Da.lean` | 200 | 0.5 | F (`Basic`) |
| D statements, batching | `Count/Stmt.lean` | 200 | 0.5 | F (`Basic`) |
| E assembly | `Count/Node.lean`, `Count/Final.lean`, pins, docs | 300 | 0.5 | all |

About 1,900 lines and 4 agent-days; with A–D in parallel, about 1.5 days elapsed. A–D need
only the framework's interface (§3), so they can start against its statements while it is being
finished; E can be written against A–D's statements and checked when they land.

## 5. Edits to existing files

Only E edits existing files: `LeanVM.lean` (the new end theorem's axiom pin), a test under
`tests/LeanVMTests/Guest/` (the pins of `nodeLog_count_lt`, `idealVerify_complete_final`, and the
concrete leaf under the new limits), `docs/roadmap/e2e-security.md` (T6-2, §8),
`docs/roadmap/t6-completeness.md` (the L17 row). `TreeLog.lean`, `DecodeFinal.lean` and
`Witness.lean` are not changed: the new theorem is in a new file that imports them.

## 6. Status

**Done.** Every package is proved, with no escapes, and pinned at Lean's three axioms
(`LeanVM.lean`, `tests/LeanVMTests/Guest/CompCountWhir.lean`, `CompCountSig.lean`,
`CompCountNode.lean`):

| file | content |
|---|---|
| `Count/Basic.lean` | F: `prefixCount`, `LogM` lemmas, `LogShort`, `LogShortS`, `prefixCount_simulateQ_le` |
| `Count/Prog.lean` | F: `LeafBound`, `prefixCount_run_le`, `prefixCount_verifyDeferredWith_le`, `whirLeafWidth = 192`, `whirLeaves = 368` |
| `Count/Whir.lean` | A: `leafBound_deferredProgram` (368 is reached at stack size 28, rate 1) |
| `Count/Xmss.lean`, `Count/Sphincs.lean` | B: `xmssVerifyBlocks = 5376`, `sphincsVerifyBlocks = 10976` (queries of at most 960 and 1056 bytes) |
| `Count/Da.lean` | C: `daOpenBlocks = 6,138,880` |
| `Count/Stmt.lean` | D: `stmtBlocks`, `prefixCount_batchWith = 0` |
| `Count/Node.lean` | E: `prefixCount_nodeLog_le`, **`nodeLog_count_lt`** |
| `Count/Final.lean`, `Count/FinalWitness.lean` | E: `WithinLimitsBudget`, `withinLimits'_of_budget`, **`idealVerify_complete_final`**, the leaf (`idealVerify_complete_final_wTree`) |

The count at the deployed limits is below `2^16 + 56 + 16 (2^17 + 72 + 8464) + 2 · 2^36 +
16 · 2^30 + 16 (2^17 + 72) < 2^38`.
