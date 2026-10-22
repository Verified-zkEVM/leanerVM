# T6-prob: completeness of V_I with high probability over the random oracle

Package T6-prob of [`e2e-security.md`](e2e-security.md) (§4 T6, §7): remove T6-det's good events
G1–G3 (`PowFound`, `WeightsNonzero`, `RootsInjAt`, `LeanVM/E2E/Complete/Tree.lean`) by proving that
they hold with high probability when the hash is a random oracle. This note is the plan: what can
and cannot be bounded as stated (§1, with two fixes, decisions **E2E-8** and **T6-3** of
`e2e-security.md` §7), the model (§2), the H-oblivious prover (§3), the exact Lean statements
(§4), how each event is bounded (§5), the packages (§6) and the risks (§7).

Summary. The end theorem is a bound on an experiment run against the lazy oracle `Rom.loggedRO`:
a query-bounded *generator* outputs an honest tree, valid at every hash agreeing with its log;
the honest prover, restated as an oracle computation whose every choice is a function of answers
it received, proves it; except with probability

    completeError Q pfuel = Q · ((1 − 2^-17)^pfuel + Q/2^256)          -- G1, `powPot` (romComplete's)
                          + Q · (2^-192 + 4Q/2^256)                     -- G2, a doom potential on the matrices' weights

(`Q` the generator's and the prover's queries; `4Q/2^256` is `failBound batchSeedsAll Q`, the
batching's seeding having no common steps), the prover
outputs and V_I accepts its idealized proof at *every* hash agreeing with the oracle's log. G3
disappears: under E2E-8 (V_I reads words and frames by node) no event on roots is needed. At
`pfuel = 2^25` and `Q ≤ 2^64` the error is at most `6 · 2^-128 + 2^-192 ≤ 2^-124`.

## 1. Findings: what can be bounded as stated

### 1.1 A fixed tree is valid only for some hashes (formulation, T6-3)

The requested form "for every honest tree `T` valid and within the limits,
`Pr_H[V_I^H accepts honestIdeal H T] ≥ 1 − ε`" cannot be stated with `T` fixed: `T.Valid H`
(`Tree.lean`) is a property of `H`. Every node needs at least one claim (`Limits.nonempty`), every
leaf holds its claims directly, and a direct holder is valid only if a hash relation holds
(`xmssVerifyWith (some ∘ H)`, `sphincsVerifyWith`, `Witness.OpensWith` compare chain ends and
Merkle roots computed with `H` against values fixed in `T`). For a fixed `T` and a random `H` that
is an event of negligible probability (a fixed leanXMSS signature verifies only if a fresh answer
hits the key's 128-bit root), so "valid for every `H`" is vacuous and "valid at the random `H`" is
a conditioning. The signatures and DA openings of an honest tree are made *with* the oracle.

**Fix (T6-3 (a)):** quantify over trees produced by an oracle computation, a *generator*
`gen : OracleComp HashSpec (Option HonestTree)` with a total query bound, whose outputs are valid
(and within the limits) at every hash agreeing with the oracle's log of its run (`ValidGen`,
§4.5). The honest signers' key generation and signing, then the tree's assembly, is one; so is any
adversarial aggregator whose trees are valid — completeness holds for adaptively chosen valid
trees. The inhabitant (§4.6) signs one leanXMSS message and outputs the leaf holding it.

### 1.2 The classical choices are not oracle computations (question (b))

`honestStep` (`Prover.lean`) takes `e := Classical.choice h` for `h : Nonempty (NodeExec H pi w)`.
`NodeExec H pi w` depends on all of `H`: its strings `D` are a field (nothing ties them to the
node's checks), and `valid : ValidExecutionB (CompModel.chain I H).sem …` mentions `H` at every
string of `D`. For two hashes agreeing on the node's strings the two types are different terms,
and `Classical.choice` relates nothing across them. So the chosen sizes `e.sz` and stack `e.q` —
hence the stack root, the Fiat–Shamir chain of the node's proof and **the chaining values of its
grinds** — are an arbitrary function of the whole of `H`, including its answers at the grinds'
own inputs `H(base ‖ (n, 4))` and at the parent's batching challenges. `freshFor` (the children's
fresh claims, which the parent's batching absorbs) is a second such choice. Any probability bound
must hold for every choice function satisfying the specification, including one that steers into
failure: wherever `NodeExec` has many elements (sizes, the memory image's unconstrained cells), a
choice may pick the child execution whose fresh claims make the parent's matrix weights vanish
(G2), or a stack whose grinds fail (G1). No potential argument applies to a function of the whole
oracle.

**Fix (T6-3 (b)):** restate the prover as an oracle computation `honestProverComp`, every hash a
query, every choice a function of answers it already received, made from a *log* the computation
keeps itself:

* the node's execution, sizes, stack and frames from the answers on the strings the node's checks
  hash (`execOf L pi w`, `L` the log of `nodeLog`'s checks run with queries), chosen in
  `NodeExecOn (L.map Prod.fst) (fillLog L) pi w` — executions whose strings are exactly `L`'s —
  and transported to every hash agreeing with `L` (`NodeExec.transport`, **prototyped and built**:
  `LeanVM/E2E/Complete/Rom/Chooser.lean`, `chainSem_congr`: the honest table reads `H` only on
  `D`);
* the fresh claims read off V°'s run along the Fiat–Shamir challenges (`freshRun`, the run of
  `claimsProg`, V°'s prefix through the lincheck's reads, returning `freshOf` of what it read):
  the deferring verifier makes V°'s moves as long as its two `require`s pass (`Deferred.lean`,
  `FsSame`), so its queries on the honest proof are V°'s.

Its grinds are queried after these choices. They are not fresh by construction (an earlier query
— the generator's, another node's — may have hit a nonce input), and need not be: the
proof-of-work potential `powPot` of `Protocol/Compile/Rom/Complete.lean` pays, at the fresh
answer that creates a base, `(1 − 2^-17)^pfuel` plus `|ℓ|/2^256` for its nonce inputs already
being in the log. So **yes, the prover can be restated as an oracle computation; freshness of its
PoW queries is not needed, only that the computation is one.** `romComplete` is exactly this
argument for a single proof with a fixed strategy; T6-prob is its tree version with adaptive
strategies.

### 1.3 G1 as stated

`PowGood H pfuel pi` (`NonVacuity.lean`) quantifies over *every* chaining value: `∀ hist bits k
cv, … → findNonce H bits cv pfuel ≠ none`. It does not depend on the prover's choices, so it is
the one good event that survives 1.2: for a uniform function, a union bound over the `2^256`
bases gives `Pr[¬PowFound] ≤ 2^256 (1 − 2^-17)^pfuel` (the nonce inputs `u ‖ (n, 4)`, `n < 2^64`,
are distinct, `nonceInput_inj`). It is not used below (its bound needs a uniform *function*, and
the lazy oracle's run event is sharper); T6-prob replaces G1 by "no proof-of-work search of the
run exhausted `pfuel`".

### 1.4 G2 as stated

`WeightsNonzero` quantifies over the classical prover's `kidOuts`, so 1.2 applies. On the oracle
computation the event is boundable: the weights are
`wA = Σ_i (λ_i,1 · freshWeight(f_i, z) + λ_i,2 · eq(p_i, z))` (`Guest/Batch/Matrix.lean`), with
`λ` and the 28 coordinates of `z` squeezed after the children's cells are absorbed. Each sampled
variable enters `wA` affinely, and `wA` is not the zero function: `λ_0,2 = 1`, other lambdas `0`,
`z = p_0` give `eq(p_0, p_0) = 1` (characteristic 2: `p² + (1 + p)² = 1`). So the doom "`wA` is
not identically zero in the variables still to be sampled" holds at the start, and a challenge
breaks it only at one value (two values killing every completion would make the affine map zero):
an escape of `1/|E| = 2^-192` per challenge (`challengeOf` is a bijection of three 64-bit words
onto `E = GF(2^192)`). The certificate framework of the batching's soundness
(`Guest/Batch/RomSpec.lean`, `E2E/Batch.lean`'s `batchPot`) turns it into a potential.

### 1.5 G3 cannot be bounded as stated (precise obstruction; fix E2E-8)

`RootsInj o.entries` (two entries with one stack root are one entry, frames included) fails, for
whatever hash, in two situations that the specification of the prover allows and that no
probability bound can exclude:

1. **One stack, two witnesses.** Two nodes whose chosen executions share sizes and stack (so word
   and root) but whose witnesses differ (children with one statement and different proofs) carry
   different frames (`DecodeHonest fr t w` depends on `w`). Their entries differ with one root.
2. **One word, two sizes.** Two nodes whose stacks are one word at one stack height under
   different sizes (`stackShape` reads only `layout.stackLog`): one root, one word, but different
   executions `candidateRun s₁ q ≠ candidateRun s₂ q`; root-keyed frames serve one of them only.

Both are deterministic: for a choice function that realizes them whenever the guest admits such
executions, `RootsInj` fails with probability one. Excluding them needs an analysis of the whole
honest memory image (which executions are valid for which witnesses and sizes), the same
obstruction E2E-5 met for the decoder's first frame. Case 1 alone is harmless for acceptance (V_I
then follows the children of the entry it finds first, which are honest nodes; a representative
argument, §4.3); case 2 is not (the frames named for one execution decode the other).
Root collisions proper (two different words with one root) are a probabilistic event, `Q²/2^257`
given leaf/node length separation (stack leaves are `2^initialFold = 64` words, 256 bytes; nodes
64 bytes).

**Fix (E2E-8, a change to V_I, `e2e-security.md` §7):** an idealized proof gives words and frames
*by node* `ν = (pi, π)` (`IdealProof.words : List (Node × Word)`,
`IdealProof.frames : Node → Frames`); `nodeStep ν` reads `ip.word ν` and `ip.frames ν`, everything
else unchanged. Two honest subtrees with one node share `π`, hence sizes, rate and root; the
honest prover gives each node the word and frames of its *smallest* subtree, which pass at the
other (well shaped, same root, its stack the only candidate at the shared sizes and statement,
L8), and `nodeStep ν` returns that representative's children, honest nodes of strictly smaller
size. The closure then accepts by the existing measure argument (`closure_accepts`, with
`sz ν := ` the representative's size). **No good event on roots remains**, so G3 disappears
instead of being bounded. Soundness: any root-keyed idealized proof is a node-keyed one with the
same behaviour, so V_I accepts more and the soundness theorems get stronger; each word is still
checked against its own node's root; T1–T5 are per node. (Alternative 8a, not proposed: frames
keyed by root and sizes, words by root; it keeps a root-collision event with its Merkle lemma.)

## 2. The model: the lazy oracle `Rom.loggedRO`

The random oracle is `Rom.loggedRO` (`Protocol/ToVCVio/Rom/LoggedOracle.lean`): a lazily sampled
uniform `Digest` per fresh input, the ordered log as state, as in `game`. Reasons:

* `Bytes` is infinite: there is no uniform function on it, and a uniform function on a finite
  sub-domain is a different oracle from the game's;
* the three tools are lazy-oracle potentials, all present: `powPot`
  (`Compile/Rom/Complete.lean`, G1), the doom potential `pot`/`final_ineq` and the batching's
  `batchPot` with `startLog` (`Compile/Rom/Potential.lean`, `E2E/Batch.lean`, G2), the birthday
  potential (`Rom/Bounds.lean`, not needed under E2E-8); `prEvent_run_loggedRO_le_of_freshStepBelow`
  bounds any query-bounded computation, so the prover's adaptivity is free;
* the bridge from a run to a total hash exists: an outcome of a lazy run is the computation's value
  under every log extending the final one (`simulateQ_look_of_mem_support`), hence under every
  total hash agreeing with it (`simulateQ_id_of_look`), where T6-det applies;
* it composes with the game: `game` runs against the same oracle, and the generator may be the
  game's honest signers;
* `prEvent_romExperiment_eq_logExperiment` transfers to VCVio's `randomOracle` if wanted.

A uniform function would only add G1's ∀-cv union bound (§1.3), not needed.

V_I need not run inside the experiment: its acceptance is asked at every hash agreeing with the
log after the prover (`CompleteOK`), which T6-det gives deterministically. So V_I's queries are
not counted and V_I needs no total query bound; the form with V_I run lazily after the prover is a
corollary (its outcome is V_I at a hash extending that log).

## 3. The prover as an oracle computation

`honestProverComp ρ pfuel T : OracleComp HashSpec (Except ProverFail HonestOutN)`, bottom up, the
children first, then the node:

1. `seedOf` and the children's digests, `childClaimsWith` — by queries (`statementDigestWith`,
   `fiatShamirIvWith` are monad-generic);
2. the batching: `honestHintsM` (the bytecode's honest rounds, `honestRounds` with `roundCv` by
   queries; `lead` is a function of the round polynomial, unique), then `batchWith queryH`; if
   the matrix weights are both zero, `.error (.weights ccs)`;
3. the node's log `L`: `nodeLog`'s checks (`nodeLogWith`, monad-generic `…With`) run with queries
   recording `(x, answer)`;
4. `execOf L pi w` (§1.2); `none` gives `.error .stuck` (impossible on valid trees within the
   limits);
5. `proveM queryH (blindProgram …) (honestStrategyBlind guest e.sz ρ e.q) seed pfuel`
   (`Compile/Rom/Prover.lean`); `none` gives `.error (.grind P S seed)`;
6. the fresh claims `freshRunM` (the run of `claimsProg` along the challenges);
7. the output `HonestOutN`: statement, fresh claims, proof, and per node of the subtree its node,
   word, frames and subtree size.

As built: `honestOutN H ρ pfuel T` (`Rom/ProverN.lean`) is the deterministic prover with `execOf` and
`freshRun`; `honestProverM H` (`Rom/Comp.lean`) the same with the hash a parameter in any monad,
`honestProverComp := (honestProverM queryH …).run`, and its run at a total hash is `honestOutN H`
(`Rom/CompBridge.lean`). At every `H` this is the classical-shape prover with the choosers in place of
`Classical.choice`: T6-det's proofs go through with `NodeExec.transport` and the choosers' specs,
and E2E-8's representative argument removes `RootsInj`.

## 4. The Lean statements (a)

New modules under `LeanVM/E2E/Complete/Rom/` (names checked unique in `LeanVM/`), namespace
`LeanVM.E2E.Complete`.

### 4.1 E2E-8 (`LeanVM/E2E/Statement.lean`, edited)

```lean
abbrev Node : Type := Digest × Proof                      -- moved above `IdealProof`

structure IdealProof where
  proof : Proof
  words : List (Node × Word)                              -- was `List ((E × E) × Word)`
  frames : Node → String → List E → Option ℕ               -- was `E × E → …`

def IdealProof.word (ip : IdealProof) (ν : Node) : Option Word :=
  (ip.words.find? (·.1 = ν)).map (·.2)

-- `nodeStep ν`: `let some W := ip.word ν`, `decodeAt … (ip.frames ν) …`; unchanged otherwise.
```

### 4.2 The choosers (`Rom/Chooser.lean`; prototype built)

```lean
theorem chainSem_congr {D : List Bytes} (I : Intermediates D) {H H' : Bytes → Digest}
    (h : ∀ x ∈ D, H x = H' x) : chainSem I H = chainSem I H'                     -- done
noncomputable def NodeExec.transport (e : NodeExec H pi w) (h : ∀ x ∈ e.D, H x = H' x) :
    NodeExec H' pi w                                                              -- done
def fillLog (L : Log) (x : Bytes) : Digest := (look L x).getD 0
def NodeExecOn (D : List Bytes) (H : Bytes → Digest) (pi : Digest) (w : NodeWitness) : Type :=
  {e : NodeExec H pi w // e.D = D}
noncomputable def execOf (L : Log) (pi : Digest) (w : NodeWitness) :
    Option (NodeExecOn (L.map Prod.fst) (fillLog L) pi w)                         -- classical, on `L` only
theorem execOf_isSome (hL2 : GuestCompleteModel) … (hL : L = graph of H on nodeLog H s w)
    (hrel : NodeRelWith (some ∘ H) …) (hlim : End.Limits s w) (hcaps …) (hbud …) :
    (execOf L (digestOf H s) w).isSome                                            -- nodeExec_nonempty + nodeSupport_of_count + nodeLog_count_lt
def claimsProg (bc : List K) (pd : Digest) : Prog FixedClaims                   -- Rom/Fresh.lean
noncomputable def freshRun (H) (S) (fuel) (bc) (pd seed : Digest) : Option FixedClaims :=
  (fsRun H S fuel (claimsProg bc pd) seed []).map (·.1)
theorem exists_deferred_honest_run …  -- on V°'s honest proof, freshRun = some c with freshFor's properties
```

### 4.3 The deterministic core (`Rom/ProverN.lean`, `Rom/AssembleN.lean`, `Rom/NonVacuityN.lean`)

```lean
inductive ProverFail
  | grind (P : Prog Bool) (S : Strategy) (seed : Digest)   -- a proof-of-work search exhausted `pfuel`
  | weights (cs : List ChildClaims)                        -- an inner node's matrix weights both zero
  | stuck                                                  -- no execution / batching refused

structure HonestOutN where
  stmt : NodeStatement
  fresh : FixedClaims
  proof : Proof
  entries : List (E2E.Node × Word × Frames × ℕ)            -- node, word, frames, subtree size
  size : ℕ
  subs : List (E2E.Node × List E2E.Node × ℕ)

noncomputable def honestProverComp (ρ pfuel : ℕ) : HonestTree →
    OracleComp HashSpec (Except ProverFail HonestOutN)
noncomputable def honestOutN (H : Bytes → Digest) (ρ pfuel : ℕ) (T : HonestTree) :
    Except ProverFail HonestOutN :=
  simulateQ (fun x ↦ (pure (H x) : Id Digest)) (honestProverComp ρ pfuel T)
def idealOfN (o : HonestOutN) : IdealProof               -- entries by increasing size: `find?` meets the smallest

def HonestTree.WithinLimitsN (H : Bytes → Digest) (ρ pfuel : ℕ) (T : HonestTree) : Prop
  -- `LimitsBudgetAt` with `honestOutN`'s children: the deployed limits and budget, as today

/-- **T6-det without G3** (E2E-8, representatives). -/
theorem idealVerify_complete_N (H : Bytes → Digest) (T : HonestTree) {ρ pfuel fuel : ℕ}
    (hρ : validRate ρ) {o : HonestOutN} (hI : honestOutN H ρ pfuel T = .ok o)
    (hfuel : T.size ≤ fuel)
    (hda : ∀ c ∈ T.claims.da,
      Da.toBytes c.2 = Id.run (Da.vectorDigestOfWith (fun x ↦ (pure (H x) : Id Digest)) c.1)) :
    o.stmt.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest (idealOfN o) fuel o.stmt = true

/-- **The prover fails only at G1 or G2** on a valid tree within the limits. -/
theorem honestOutN_ne_stuck (H : Bytes → Digest) (T : HonestTree) (hρ : validRate ρ)
    (hv : T.Valid H) (hlim : T.WithinLimitsN H ρ pfuel) :
    honestOutN H ρ pfuel T ≠ .error .stuck
```

### 4.4 Bridges, tags and counts (`Rom/CompBridge.lean`, `Rom/CompCount.lean`)

```lean
theorem honestProverComp_look {ℓ : Log} {T : HonestTree} {r}
    (h : simulateQ (lookImpl ℓ) (honestProverComp ρ pfuel T) = some r) (Ht : Bytes → Digest)
    (hH : ∀ x u, look ℓ x = some u → Ht x = u) : honestOutN Ht ρ pfuel T = r  -- simulateQ_id_of_look
theorem grind_of_look (h : simulateQ (lookImpl ℓ) (honestProverComp ρ pfuel T) =
    some (.error (.grind P S seed))) :
    proveFromM (look ℓ) S pfuel P seed [] = some none ∧
      ∀ h b k, P.after h = some (.grind b k) → b = 17          -- movesOK_blindProgram
theorem weights_of_look (h : … = some (.error (.weights cs))) : WeightsVanish ℓ cs
  -- the batching's chain on `ℓ` (from `aggSeedD`, `startLog`) ends with `wA = wB = 0`
noncomputable def HonestTree.proverQueries (ρ pfuel : ℕ) : HonestTree → ℕ
theorem isTotalQueryBound_honestProverComp (T : HonestTree) :
    IsTotalQueryBound (honestProverComp ρ pfuel T) (T.proverQueries ρ pfuel)
theorem proverQueries_le (hshape : T.AllNodes ShapeOK) :
    T.proverQueries ρ pfuel ≤ T.size * nodeQueries pfuel
  -- nodeQueries pfuel = qChecks + leanVmCost · proverFactor costHeight pfuel + leanVmQueryBound + qBatch,
  -- proverFactor 26 pfuel = 2^27 + pfuel + 1; qChecks from ≤ 16 children (13216 each), < 2^16 direct
  -- signatures (≤ 384 / 686 each), ≤ 1 direct DA opening, the digests
```

### 4.5 The bounds and the end theorem (`Rom/Bounds.lean`, `E2E/Batch/Weights.lean`, `Rom/EndOf.lean`, `Rom/End.lean`)

```lean
-- G1 (romComplete's potential): a reachable outcome whose prover failed at a grind
theorem one_le_powPot_of_grind {z} (hz : z ∈ support (completeExp ρ pfuel gen))
    (hf : z.1 = some (T, .error (.grind P S seed))) : 1 ≤ powPot 17 pfuel z.2
-- G2 (a doom potential over every batching instance of the log)
noncomputable def weightsPot (ℓ : Log) : ℝ≥0∞
theorem weightsPot_nil : weightsPot [] = 0
theorem weightsPot_step (ℓ : Log) (t : Bytes) (ht : look ℓ t = none) :
    (∑ u, weightsPot (ℓ ++ [(t, u)])) / Fintype.card Digest ≤
      weightsPot ℓ + (2 : ℝ≥0∞)⁻¹ ^ 192 + failBound batchSeedsAll (ℓ.length + 1)
theorem one_le_weightsPot (h : WeightsVanish ℓ cs) (hs : ∀ c ∈ cs, ChildShaped End.bytecode c) :
    1 ≤ weightsPot ℓ

/-- **A valid-tree generator.** -/
def ValidGen (ρ pfuel N QP : ℕ) (gen : OracleComp HashSpec (Option HonestTree)) : Prop :=
  ∀ z ∈ support ((simulateQ loggedRO gen).run []), ∀ T, z.1 = some T →
    T.size ≤ N ∧ T.proverQueries ρ pfuel ≤ QP ∧
      ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) →
        T.Valid Ht ∧ T.WithinLimitsN Ht ρ pfuel

/-- **The completeness experiment**: the generator, then the honest prover, against one lazy oracle. -/
noncomputable def completeExp (ρ pfuel : ℕ) (gen : OracleComp HashSpec (Option HonestTree)) :
    ProbComp (Option (HonestTree × Except ProverFail HonestOutN) × Log) :=
  (simulateQ loggedRO (do
    match ← gen with
    | none => pure none
    | some T => pure (some (T, ← honestProverComp ρ pfuel T)))).run []

/-- The prover output, with the tree's claims, and V_I accepts at every hash agreeing with the log. -/
def CompleteOK (fuel : ℕ) (z : Option (HonestTree × Except ProverFail HonestOutN) × Log) : Prop :=
  ∀ T r, z.1 = some (T, r) → ∃ o, r = .ok o ∧ o.stmt.claims = T.claims ∧
    ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) →
      idealVerify (m := Id) (fun x ↦ (pure (Ht x) : Id Digest)) guest (idealOfN o) fuel o.stmt = true

noncomputable def completeError (Q pfuel : ℕ) : ℝ≥0∞ :=
  Q * (missProb 17 ^ pfuel + Q / 2 ^ 256) + Q * ((2 : ℝ≥0∞)⁻¹ ^ 192 + failBound batchSeedsAll (Q + 1))

/-- **T6-prob.** -/
theorem idealVerify_complete_rom {ρ pfuel N QG QP fuel : ℕ} (hρ : validRate ρ)
    (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : ValidGen ρ pfuel N QP gen) (hfuel : N ≤ fuel) :
    Pr{let z ← completeExp ρ pfuel gen}[¬ CompleteOK fuel z] ≤ completeError (QG + QP) pfuel
```

Proof: the potential `powPot 17 pfuel + weightsPot` with the step `missProb 17 ^ pfuel + Q/2^256 +
2^-192 + failBound` (`powPot_step`, `weightsPot_step`), `prEvent_run_loggedRO_le_of_freshStepBelow`
at `QG + QP`; on a reachable outcome with `¬ CompleteOK`, the prover's run at the final log is the
outcome (`simulateQ_look_of_mem_support`), and at every `Ht` agreeing with it
`honestOutN Ht = r` (`honestProverComp_look`); `ValidGen` gives `T.Valid Ht`, `WithinLimitsN Ht`;
if `r = .ok o`, `idealVerify_complete_N` contradicts `¬ CompleteOK`; `.stuck` is excluded
(`honestOutN_ne_stuck`); `.grind` gives `1 ≤ powPot` (`one_le_powPot_of_grind`), `.weights`
gives `1 ≤ weightsPot` (`weights_of_look`, `one_le_weightsPot`).

Corollaries (same file): V_I run lazily after the prover rejects with at most the same
probability (`idealVerify_complete_rom_run`); the tree-size form, `QP := N · nodeQueries pfuel`
under `ShapeOK` (`idealVerify_complete_rom_size`); the game's budgeted form, proved: V_I's query
count on the honest proof is at most `13,508 + fuel · 179,719,581` (`Rom/ViCost.lean`,
`queryCount_honest_le`), and V_I run as the game runs it, with `budgetedQuery budget`, rejects with
the same probability for every budget at least `N · viNodeBound` (`Rom/EndBudget.lean`,
`idealVerify_complete_rom_budget`; decision E2E-11 of `e2e-security.md`).

### 4.6 Numbers and the inhabitant (`Rom/End.lean`, `Rom/Gen.lean`)

```lean
theorem completeError_le (hQ : Q ≤ 2 ^ 64) : completeError Q (2 ^ 25) ≤ (2 : ℝ≥0∞)⁻¹ ^ 124
  -- missProb 17 ^ (2^17 · 256) ≤ 2^-256 (`missProb_pow_le`); then 2^-192 + 2^-128 + 2^-128 + 4 · 2^-128
noncomputable def xmssLeafGen : OracleComp HashSpec (Option HonestTree)
  -- honest leanXMSS key generation, one signature on the zero message, the leaf holding it directly
theorem validGen_xmssLeafGen (ρ pfuel : ℕ) : ValidGen ρ pfuel 1 (xmssLeafQueries pfuel) xmssLeafGen
theorem xmssLeaf_queries_le : xmssKeygenBound + xmssSignBound + xmssLeafQueries (2 ^ 25) ≤ 2 ^ 64
theorem idealVerify_complete_rom_xmssLeaf :
    Pr{let z ← completeExp 1 (2 ^ 25) xmssLeafGen}[¬ CompleteOK 1 z] ≤ (2 : ℝ≥0∞)⁻¹ ^ 124
```

A node costs the prover at most `nodeQueries pfuel = 45,507,690 + 26,420 · (2^27 + pfuel + 1)`
queries (`nodeQueries_eq`, `Rom/CompCount.lean`), about `2^42` at `pfuel = 2^25`: V°'s proof
(`proveM`) and the fresh claims' run (`freshRunM`) each cost the crude `leanVmCost · (2^27 +
pfuel + 1)` of `isTotalQueryBound_proveM`. So `Q ≤ 2^64` covers trees of about `2^21` nodes beside
a generator of `2^63` queries; for `Q ≤ 2^56` the error is below `2^-135`. The leaf instance's
generator makes `2^33 + 53,739,486` queries (`xmssLeafGen_queries_eq`).

Pins: `LeanVM.lean` prints the axioms of `idealVerify_complete_N`, `idealVerify_complete_rom`,
`idealVerify_complete_rom_run` and `idealVerify_complete_rom_xmssLeaf`; the tests
`tests/LeanVMTests/E2E/CompleteRom{N,M,Bridge,Tags,Count,Bounds,Gen}.lean` and
`tests/LeanVMTests/Guest/CompleteRomWeights.lean` pin the pieces at Lean's three axioms.

## 5. How each event is bounded (b)

| event | on the oracle computation | potential | per fresh query |
|---|---|---|---|
| G1: a grind exhausts `pfuel` | `.error (.grind …)`: some `proveFromM (look ℓ)` returned `some none` | `powPot 17 pfuel` (romComplete) | `(1 − 2^-17)^pfuel + |ℓ|/2^256` |
| G2: an inner node's weights vanish | `.error (.weights cs)`: the batching's chain on `ℓ` ends at `wA = wB = 0` | `weightsPot` (doom: `wA ≢ 0` in the unsampled variables) | `2^-192 + failBound` |
| G3 | none under E2E-8 (representatives) | — | — |

Why the prover's dependence on `H` is not a problem: every potential bounds an arbitrary
query-bounded oracle computation; the prover's choices may depend on any answer it received.
What was a problem is a dependence on answers it never asked for (1.2), which an oracle
computation cannot have. The PoW queries of a node come after its execution is fixed; whether they
are fresh is itself charged (`powPot`'s `|ℓ|/2^256`), so the generator and earlier nodes may query
anything.

## 6. Packages (c)

| | package | files | lines | depends on |
|---|---|---|---|---|
| P1 | **E2E-8**: `IdealProof` by node, `nodeStep`; re-plumb soundness (`Knowledge/Node.lean`, `Knowledge.lean`, `KnowledgeSub.lean`, `Vis/Knowledge.lean`, `Sanity.lean`) and T6-det (`Complete/Node.lean`, `Prover.lean`'s `idealOf`, `Assemble.lean`, `Witness.lean`), tests; statements unchanged except the type | edits | 300–700 | — |
| P2 | choosers and the chooser prover: `Rom/Chooser.lean` (prototype done), `Rom/ProverN.lean`, `Rom/AssembleN.lean` (representatives, `idealVerify_complete_N`), `Rom/NonVacuityN.lean` (`honestOutN_ne_stuck`, `WithinLimitsN`) | new | 2–3k | P1's types (develop against the 4.1 definitions) |
| P3a | monadic pieces: `honestHintsM`, `honestDeferM`, `nodeLogM` with answers, V° run with log; their `Id` runs; `proverQueries`, `nodeQueries`, `proverQueries_le` | new | 0.8–1.5k | — |
| P3b | `honestProverComp`, `honestProverComp_look`, `grind_of_look`, `weights_of_look`, `isTotalQueryBound_honestProverComp` | new | 0.6–1k | P2, P3a |
| P4 | G1: `one_le_powPot_of_grind` (from romComplete's `findNonceM_eq_some_none`, `proveFromM_eq_some_none`) | new | 0.2–0.4k | P3b |
| P5 | G2: `weightsProg` (the batching through the matrices' rounds, accepting when both weights vanish), its doom spec and certificate (`Spec` calculus as `RomSpec.lean`), `weightsPot` on `startLog`, `weightsPot_step`, `one_le_weightsPot`, `WeightsVanish` | new | 1.5–2.5k | — |
| P6 | assembly: `ValidGen`, `completeExp`, `CompleteOK`, `completeError`, `idealVerify_complete_rom` and corollaries, `completeError_le`, pins | new + `LeanVM.lean`, tests | 0.4–0.7k | all |
| P7 | inhabitant: `xmssLeafGen`, `validGen_xmssLeafGen` (lean_xmss correctness at every hash via the reductions' bridges to `xmssVerifyWith`; the leaf's limits and budget as `Witness.lean`'s) | new | 0.6–1.5k | `ValidGen`'s text (4.5), P2's `WithinLimitsN` for a leaf (no children) |

Total 7–11k lines. **In parallel now: P1, P5, P3a, P7, and P2's `Chooser.lean`/`ProverN.lean`**
(P2 against the definitions of 4.1; its `AssembleN.lean` builds once P1's `Statement.lean` lands).
Then P3b, then P4 and P6. Critical path P1 → P2 → P3b → P6; P5 is the longest independent one.

Edits to existing files: `Statement.lean` (E2E-8, a specification change); the re-plumbing of
P1 (forced by the type); `LeanVM.lean` and a new test file (pins); `e2e-security.md` §7 (E2E-8,
T6-3), §8 later; `t6-completeness.md` "Open" (a pointer here). Nothing else.

## 7. Risks (d)

1. **E2E-8 touches the soundness side** (decided by the user). Mechanical (`ip.word r`/`ip.frames r`: 39 lines in 8
   files, `r` replaced by the node in scope), but it rebuilds the E2E chain up to
   `Vis/Deployed.lean` and changes the type in every end theorem's statement (`game`'s adversary
   outputs an `IdealProof`). Fallback 8a (frames keyed by root and sizes)
   touches the same sites and adds a root-collision event.
2. **G2's certificate.** The doom predicate is functional ("some completion has `wA ≠ 0`"), the
   escape argument affine (one bad value); the work is the program and its specification in the
   `Spec` calculus, the batching's constant start (`startLog`), and identifying the honest
   batching's transcript as a run of `weightsProg` on the log (`E2E/Batch/With.lean`'s
   `RunsW`). `freshWeight` is a product of two multilinear extensions over disjoint halves of `z`
   (`Spec/Node.lean:251`), so `wA` is affine in each coordinate, as the escape bound needs.
3. **The fresh-claims chooser** needs the deferring verifier's queries on the honest proof to be
   V°'s at the log level (`FsSame` is at `Id`); fallback: compute the claims explicitly from V°'s
   run (`freshOf a.1 t zc u` of `Deferred.lean`) with a monadic `fsRun`.
4. **Query counts.** `proverQueries` needs counts of hash *calls* of the node's checks, which
   `Count/*.lean` does not give (it counts block prefixes); DA openings are the largest. Fallback:
   keep `T.proverQueries ≤ QP` a field of `ValidGen` and prove `proverQueries_le` for the leaf only.
5. **Limits stay on the prover's outputs** (`WithinLimitsN`, as `WithinLimitsBudget` today): a
   child's stack log must land in `[22, 28]` for whichever sizes `execOf` picks. Done (§8,
   recursion): `execOf` prefers sizes of at least 22 stacked variables; every node has such an
   execution, its memory zero-padded to `2^19` words when its committed size is below `2^21`, as
   leanVM's prover pads it (`guestCompleteModel_big`: the run, the bodies and D3's decoding
   transport to any extension of the honest memory, `PadHonest.lean`); and the stream cap holds of
   every accepted proof. So the limits are a condition on the tree alone (`LimitsT`), at any depth.
6. **The inhabitant's validity at every hash** goes through lean_xmss's correctness and the
   `Digest ≃ BitVec 256` bridges of `E2E/Reduction`; the leaf's budget must be the kernel-evaluated
   one of `Witness.lean` (`End.work` reads only shapes). Fallback: a leanSPHINCS leaf
   (`Sphincs.Completeness.correct`, every fixed hash).
7. **Build memory**: `Rom/*` import `Complete/Prover.lean`'s closure only; keep each module under
   3.5 GB, the Batch certificate modules away from the guest families.

## 8. Status

Built (no escapes; pins at Lean's three axioms):

| file | content |
|---|---|
| `Rom/Chooser.lean` | `chainSem_congr`, `NodeExec.transport`, `logOf`, `fillLog`, `NodeExecOn`, `execOf`, `nodeExec_nodeLog`, `execOf_isSome` |
| `Rom/Fresh.lean` | `claimsProg`, `freshRun`, `exists_deferred_honest_run` |
| `Rom/ProverN.lean` | `ProverFail`, `EntryN`, `HonestOutN`, `honestDeferN`, `proveNode`, `honestStepN`, `honestOutN`, `WithinLimitsN` |
| `Rom/NonVacuityN.lean` | `honestOutN_claims`, `honestOutN_child`, `honestDeferN_ne_stuck`, **`honestOutN_ne_stuck`** |
| `Rom/AssembleN.lean` | `repOf`, `idealOfN`, `EntryStep`, `honestOutN_good`, **`idealVerify_complete_N`** (T6-det, no G3) |
| `Rom/Comp.lean` | `honestProverM`, `honestProverComp` |
| `Rom/EndOf.lean` | `genProve`, `completeExp`, `CompleteOK`, `RomPieces`, `ValidGenOf`, **`idealVerify_complete_rom_of`**, `completeRunVI`, `prEvent_reject_le_not_completeOK` |
| P3a `Rom/MonadicM.lean`, `Rom/CountM.lean` | monadic pieces with `Id` bridges, hash-call counts |
| P4 `Rom/Bounds.lean` | `completeError`, `completeError_le`, `one_le_powPot_of_proveFromM`, `prEvent_le_completeError` |
| P5 `Guest/Batch/Weights*.lean`, `E2E/Batch/Weights.lean` | `WeightsVanish`, `weightsPot`, `weightsPot_step`, `one_le_weightsPot` |
| P7 `Rom/Gen.lean` | `xmssLeafGen`, `xmssLeafGen_spec`, `xmssLeaf_limits` |

| A `Rom/CompBridge.lean` | `simulateQ_honestProverM`, `honestProverM_id`, `honestProverComp_at`, `honestProverComp_lookImpl`, `honestProverComp_look` |
| B `Rom/CompTags.lean` | `honestProverM_grind`, `honestProverM_weights`, `honestOutN_weights_shaped` |
| C `Rom/CompCount.lean`, `Rom/Valid.lean` | `HonestTree.proverQueries`, `isTotalQueryBound_honestProverComp`, `ShapeOK`, `nodeQueries_eq`, `proverQueries_le`, `ValidGen`, `validGen_xmssLeafGen` |
| `Rom/End.lean` | `romPieces`, **`idealVerify_complete_rom`**, **`idealVerify_complete_rom_run`**, `xmssLeaf_queries_le`, **`idealVerify_complete_rom_xmssLeaf`** |

**T6-prob as proved** (`Rom/End.lean`, pinned in `LeanVM.lean`):

```lean
theorem idealVerify_complete_rom {ρ pfuel N QG QP fuel : ℕ} (hρ : validRate ρ)
    (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : ValidGen ρ pfuel N QP gen) (hfuel : N ≤ fuel) :
    Pr{let z ← completeExp ρ pfuel gen}[¬ CompleteOK fuel z] ≤ completeError (QG + QP) pfuel
```

`completeError Q pfuel = Q · ((1 − 2^-17)^pfuel + Q/2^256) + Q · (2^-192 + 4(Q + 1)/2^256)`. No
good event is a hypothesis: G1 and G2 are bounded (`powPot`, `weightsPot`), G3 is removed by
E2E-8. `CompleteOK` asks V_I's acceptance at every hash agreeing with the oracle's final log; with
V_I run lazily after the prover the same bound holds (`idealVerify_complete_rom_run`).

**Recursion** (the limits on the tree, any depth; a two-level inhabitant):

| file | content |
|---|---|
| `Rom/StreamCap.lean` | `deferredStream_le` (an accepted proof's stream has at most 1696 words), `honestOutN_stream_le` |
| `Rom/Pad.lean` | `padImage`, `runB_of_ext`, `exists_padded`, `exists_stack_total`, **`nodeExec_nodeLog_big`** (a leaf has an execution of at least 22 stacked variables) |
| `Rom/Chooser.lean` (edited) | `execOf` takes an execution of at least 22 stacked variables when there is one |
| `Rom/LimitsT.lean` | `LimitsT`, `KidsLeaves`, `withinLimitsN_of_T`, `ValidGenT`, **`idealVerify_complete_rom_T`** |
| `Rom/RootBudget{A,B,C,D,E,F,}.lean` | the deployed budget at a node with one child (`budget_rootWork`), evaluated piece by piece |
| `Rom/RootGen.lean` | `xmssRootGen` (a root over the leanXMSS leaf), `validGenT_xmssRootGen`, **`idealVerify_complete_rom_xmssRoot`** (`2^-124`) |
| `PadHonest.lean`, `HonestBodiesPad.lean`, `DecodePad.lean` | `MemExt` (an extension of the honest memory, its zero padding) and the transports; the honest bodies and D3 on it (`d3HypO_ext`) |
| `GuestModelBig.lean` | **`guestCompleteModel_big`**: L2 with an execution of committed size above `2^21` |
| `Rom/PadRec.lean` | every node has a padded execution (`nodeExec_nodeLog_bigG`), every child's stack log in `[22, 28]` (`honestOutN_stackLog`), `ValidGenR`, **`idealVerify_complete_rom_rec`** (any depth) |

Completeness through recursion is `Main.complete_recursive` (`LeanVM/E2E/Main.lean`).

Decisions: E2E-8 decided by the user, T6-3 recorded (`e2e-security.md` §7).
