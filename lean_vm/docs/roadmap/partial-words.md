# Partial-word V_I (decision E2E-10, decided by the user)

Design note for [`e2e-security.md`](e2e-security.md) (§2 V_I, §4 T4/T6/T7′, §5, §7). It changes
V_I, the trusted statement. The user answered yes to all seven questions below; the design is
implemented as described (§6), and recorded as decision E2E-10 in `e2e-security.md` §7.

## Questions for the user (yes/no; all answered yes)

1. **Representation.** Should a partial word be the row function plus *holes*, `hole k j : Option
   Digest` for node `j` of level `k` (`k = 0` a single leaf), with its root computed top-down and a
   hole's digest standing for its subtree? (Recommended: yes. A lazy prover that skipped a subtree
   knows only that subtree's digest, so holes must be possible at inner nodes.)
2. **Missing columns are errors.** Should a column under a hole count as a *disagreement* (an
   error) in the candidates V_I follows, with level 0's Johnson threshold `thr` unchanged?
   (Recommended: yes. Counting it as an agreement (an erasure) is also sound, but its lists grow
   with the holes: from a fraction `√ρ` of holes on, every stack is a candidate, and V_I rejects
   provers the deployed verifier accepts after about `2^23` attempts at rate `1/16`; §2.3.)
3. **A word with a hole needs a candidate.** Should V_I reject a node whose word has a hole and no
   candidate satisfying the relation without Flock, and keep accepting, as today, a full word
   with none? (Recommended: yes. With errors this rule is needed for soundness (§2.2: otherwise
   `Pr[Breaks] ≈ 1`). Keeping today's rule for full words makes the new V_I accept a superset of
   today's proofs.)
4. **No cap on holes.** Should V_I accept any number of holes? (Recommended: yes. Soundness needs
   no cap, and V_I's list stays at most `listMax ≤ 2^18`, §2.4.)
5. **T7′.** Should T7′ get a second form whose one knowledge hypothesis is `KnownStacks`: each
   reached node's partial word has at least `thr` present columns, each the encoding of one stack
   satisfying the full relation? It would replace `WordsCover` and `CandidatesAux`, and
   `TablesPrecheck` would apply to that one stack only. (Recommended: yes. Today's T7′ stays,
   restated with full words.)
6. **§5.** Should §5 state the bridge's knowledge assumption as KA-pw (§4.2), the deployed proof
   system's knowledge soundness with the straight-line Merkle-trace extractor at its own Johnson
   radius? (Recommended: yes.)
7. **In place.** Should V_I change in place, with `IdealProof.words` holding partial words and
   every end theorem keeping its name and bound, rather than a second V_I beside today's?
   (Recommended: yes. A parallel V_I would duplicate T4, T5, W-vis and the headline.)

Summary of the answers they lead to: soundness holds with an unchanged bound (λ₁, the `30q²`
term and every closed form are unchanged); completeness is untouched (the honest prover gives full
words); T7′ gains a form whose hypotheses all lazy provers meet, so the bridge's knowledge
assumption becomes the proof system's own knowledge soundness instead of today's "knows the full
committed word", which lazy provers falsify.

## 1. The change to `IdealProof` and `nodeStep`

### 1.1 Representation and root

```lean
structure PWord where
  word : Word                      -- the rows (read only where no hole covers them)
  hole : ℕ → ℕ → Option Digest      -- node j of level k (leaves at level 0) given as a digest

def PWord.full (W : Word) : PWord := ⟨W, fun _ _ ↦ none⟩
def PWord.Present (P : PWord) (ht p : ℕ) : Prop := ∀ k ≤ ht, P.hole k (p / 2 ^ k) = none
def PWord.Full (P : PWord) (ht : ℕ) : Prop := ∀ p < 2 ^ ht, P.Present ht p

def pNodeM (H : Bytes → m Digest) (P : PWord) : ℕ → ℕ → m Digest
  | 0, j     => match P.hole 0 j with
                | some d => pure d | none => H ((P.word j).flatMap kBytes)
  | k + 1, j => match P.hole (k + 1) j with
                | some d => pure d
                | none => do H (digestBytes (← pNodeM P k (2*j)) ++ digestBytes (← pNodeM P k (2*j+1)))
def pTreeRootM (H) (ht : ℕ) (P : PWord) : m Digest := pNodeM H P ht 0
```

The leaf and node hashes are `leafHashesM`/`parentsM`'s (`Protocol/Compile/Rom/Prover.lean:49-73`),
so a full word has the deployed root: `pTreeRootM_full : pTreeRootM (Id) H ht (full W) = treeRoot H
ht W`. Holes outside the tree, or nested under another hole, are ignored. Rows under
a hole are not read, but `WellShaped w P.word` stays on every row (the prover pads with zeros),
so that line of `nodeStep` does not change.

Other representations considered: an inductive tree (`leaf | node | hole`) needs a shape
predicate and its own position lookup, for no gain; an optional row per leaf with only leaf
digests cannot express a skipped subtree, whose leaf digests the lazy prover never computed.

### 1.2 Candidates, radius, and the rule on empty lists

```lean
def SAgrees μ R ht P q S := ∀ v ∈ S, P.Present ht v ∧ ∀ u, laneOf P.word u v = enc (μ-6) R (blockOf q u) v
def SCandidates μ R A ht P : Set (Column μ) := {q | ∃ S, A ≤ S.card ∧ SAgrees μ R ht P q S}
def blindCandidatesS prog s ρ ht pi P := {q | q ∈ SCandidates (leanIsaμ prog s) ρ (thrOf ..) ht P ∧ M3HoldsBlind .. q}
```

- **Radius.** It is level 0's Johnson threshold `thr = ⌈(√ρ₋ + η)n⌉`, as today. A hole column
  counts as a disagreement (an error). Equivalently, V_I list-decodes the word at the Johnson
  radius with the holes filled by anything that matches no codeword. On a full word
  `SCandidates = Candidates` (`sCandidates_full`).
- **Which candidates V_I follows.** All of them, as today: every member of `blindCandidatesS`
  runs, passes the table check, and its decoded children are queued.
- **New rule.** If `blindCandidatesS … P = ∅` and `¬ P.Full ht`, V_I rejects the node. A full
  word with no candidate is still accepted with no children, as today.

The new `nodeStep` (`LeanVM/E2E/Statement.lean`) differs from the previous one in three lines:

```lean
  let some P := ip.word ν | pure none                       -- was: a Word
  if ¬ WellShaped w P.word then return none
  let root ← pTreeRootM H ht P                              -- was: treeRootM H ht W
  if digestScalars root ≠ r then return none
  if (blindCandidatesS prog s ρ ht pi P) = ∅ ∧ ¬ P.Full ht then return none   -- new
  if h : (blindCandidatesS prog s ρ ht pi P).Finite then …  -- unchanged loop
```

`IdealProof.words : List (Node × PWord)` and `IdealProof.word : Node → Option PWord`
(`Statement.lean:174-187`); `frames`, the closure, `outerChecksWith` and `idealVerify` are
unchanged.

**Superset.** For every total hash `H`, the new V_I accepts a proof whose words are `PWord.full`
iff today's V_I accepts the same proof with plain words (`pTreeRootM_full`,
`blindCandidatesS_full`, `full_full`). So every proof today's V_I accepts is accepted, and the
soundness theorems cover strictly more proofs.

## 2. Soundness

### 2.1 Where T4 uses the full word

T4's induction (`Knowledge.lean:244-362`, `heldDirect_of_node`) needs, at each checked node, one
candidate in V_I's list that satisfies `M3HoldsBlind`. V_I has checked that candidate (its run,
its table, its children). Today that candidate is T1's extracted stack. The full word enters at:

| place | what it uses |
| --- | --- |
| `Statement.lean:110`, `:205-209` | `blindCandidates` on a `Word`; `nodeStep` reads the word and computes `treeRootM` |
| `Knowledge/Node.lean:198-205` | `nodeStep_some` exposes `W`, `WellShaped`, `treeRootM H ht W = some root` |
| `Knowledge/Word.lean:258-276` | `openOne_of_treeRootM`, `extract_eq_of_treeRootM`: every row of a tree the log answers has an accepted opening, so `Rom.extract` equals `W` on **every** row |
| `Knowledge/Word.lean:340-347`, `:463-465` | `candidates_congr`: T1's candidate of the extracted word is a candidate of `W`, because the two words are equal on every column |
| `Knowledge.lean:270-278`, `KnowledgeSub.lean:91`, `Vis/Knowledge.lean:257` | the call sites (`treeRootM_mono` at the sub-log) |
| `Rel.lean:48-50`, `:127-129`; `Natural.lean:98-112` | `rel_treeRootM`, `treeRootM_mono`, `rel_nodeStep` |

Nothing else reads the word: T1 (`blind_knowledge_cache'`) is about the word extracted from the
log, not V_I's; W6, E5 and T3 read the decoded witness and the log.

### 2.2 The argument with partial words

At a checked node with partial word `P`, one of two cases holds.

- **`P.Full ht`** (every row present). T1 gives an extracted stack `q` in `Candidates(extract)`.
  Every present row has an accepted opening through the partial tree's answered queries: the
  queries on the path are exactly the ones `pTreeRootM` makes, and the holes are the siblings.
  So `Rom.extract = P.word` on every present row (`extract_eq_of_pTreeRootM`, via
  `climb_of_pNodeM` and `climb_append`, `Knowledge/Word.lean`), and `q ∈ SCandidates P`. This is today's
  proof, with three lemmas generalized.
- **`P` has a hole.** By the new rule V_I's list has a member `q` satisfying `M3HoldsBlind`. V_I
  checked it. T1 is not needed.

In both cases the rest is unchanged. The sizes are admissible by `sizesOf`. `q`'s execution is
valid under its table's oracle model (C5). T2 at the frames gives `NodeRelWith` for a decoded
statement of digest `pi`, which is the node's statement (`statement_eq_of_digest`). The children
are queued and of smaller rank (T3). The children need V°'s acceptance only for the full-word
case below them, and they still get it from `verifyDeferredWith`.

T4 needs only *some* checked candidate, not T1's in particular. The decoded statement is fixed by
its digest, so whichever valid execution V_I checked holds the node's claims.

**The rule is needed (counterexample to errors without it).** In the random-oracle game:
1. Take a statement `s` with a claim of an honest key on an unrequested message.
2. Build a stack `q*` satisfying `M3HoldsBlind` on its digest whose `BLAKE2S` rows are fake, so
   that the guest's signature check passes on garbage. V° is Flock-blind, so the honest V° prover
   proves `q*`.
3. Commit `enc(q*)` in full, and give V_I the word with a hole over a subtree of more than
   `n − thr` columns, with that subtree's true digest, so the root matches.

Then `q*` has fewer than `thr` present agreements. Any other stack agrees with `enc(q*)` on fewer
than `2^κ ≤ thr` columns (`eq_of_enc_agree`). So the list is empty, `nodeStep` returns `some []`
without the rule, V_I accepts, and `Forged` holds with probability about 1. The headline would be
false.

**Erasures (holes as agreements) are also sound,** with no rule: T1's `q` agrees with the
extracted word on `S`, `|S| ≥ thr`, and with `P` on `S`'s present columns, so it is a candidate
when holes count as agreements. They are not
proposed, for the bridge's sake (§2.3).

### 2.3 Lists, radius, deployed parameters

- **Finiteness** of V_I's list never used Johnson: `Column μ` is finite (`Set.toFinite`, as in
  `Sanity.lean:425`).
- **Errors (proposed).** For any filling `W′` of the holes, `SCandidates P ⊆ Candidates W′`. So
  `|list| ≤ listMax ≤ 2^18` (`candidates_ncard_le`, `Params/Deployed.lean` `shapeOK`), whatever
  the holes.
- **Uniqueness.** Suppose every present column is the encoding of a stack `q` and at least `thr`
  columns are present. Then the list is `{q}` (`eq_of_mem_sCandidates_deployed`,
  `Complete/Candidates.lean`): a second
  member agrees with `enc(q)` on at least `thr ≥ 2^κ` columns, and two encodings of degree below
  `2^κ` that agree there are equal.
- **Erasures (not proposed).** A list with `e` hole columns is the punctured code's list at
  agreement `thr − e`. It stays Johnson-bounded only while `e ≲ ηn/(1 − √ρ/2)`, and the deployed
  `η = e_cert/2^22 ≤ 2^-12`. For an exact word it is unique only while `e ≤ thr − 2^κ ≈ (√ρ − ρ)n`.
  From `e ≥ thr ≈ √ρ·n` on, it is every stack, including stacks with fake `BLAKE2S` rows (they
  exist for every statement with a claim), so V_I^{BLAKE2s} rejects.

A prover that cannot open a fraction `δ` of level-0 columns passes the deployed query phase with
probability about `(1 − δ)^{t₀}`. The level-0 query counts are `t₀ = 222–225, 111–112, 75, 56` at
`R = 1, 2, 3, 4` (`Verifier.lean:182`). Per attempt:

| `R` | at the Johnson radius `δ = 1 − √ρ` | at `δ = √ρ − ρ` (erasures stop being unique) | at `δ = √ρ` (erasures: every stack) |
| --- | --- | --- | --- |
| 1 | `2^-111.5` | `2^-74.7` | beyond Johnson |
| 2 | `2^-112` | `2^-46.5` | beyond Johnson |
| 3 | `2^-112.5` | `2^-28.1` | `2^-47.2` |
| 4 | `2^-112` | `2^-16.8` | `2^-23.2` |

With erasures, the lazy provers the bridge must cover would stop at the third column, which is
cheap at `R = 3, 4`. With errors, they stop at the first column, the protocol's own soundness
(about `2^-112` per attempt, then the proof of work).

### 2.4 Which lemmas change; the bound

- **T1, W6, E5, T3, T5, W-vis's events, `AggBad`, every error term: unchanged.** λ₁ and the
  headline's `30q²/2^256` do not change. V_I's queries on a partial tree are at most those on the
  full tree, so `viCost` is unaffected.
- **Changed** (sizes in §5): `Knowledge/Word.lean`, where the node lemma becomes
  `exists_blindCandidatesS` with the two cases and the three Merkle lemmas are generalized;
  `Knowledge/Node.lean` `nodeStep_some`, one more branch; the three call sites; `Natural.lean`
  and `Rel.lean`, which get `rel_pNodeM` (an induction on the level) and `pTreeRootM_mono`.
- **Optional, not proposed.** If V_I also rejected *full* words with an empty list, T1 would
  leave T4 altogether and κ_V°'s `2^-128` could leave the bound. λ₁ would gain at most half a
  bit: `126.17 → 126.64` with leanXMSS keys only, nothing visible at `2^20 + 2^20` keys. The
  superset property would be lost, and V_I's soundness would no longer exercise V°'s.

## 3. Completeness (T6-det, T6-prob)

The honest prover gives full words, `PWord.full (stackWord μ q)`. `nodeStep_honest`
(`Complete/Node.lean:115-175`) takes three rewrites: `pTreeRootM_full`, `blindCandidatesS_full`,
and the new rule's branch, which is skipped by `full_full`. The honest proofs' `words`
(`Complete/Prover.lean:220`, `Complete/Rom/AssembleN.lean:59`) wrap their words in `PWord.full`.
The statements reading `ip.word … = some e.2.1` (`Assemble.lean:169, 242, 256, 313`,
`AssembleN.lean:66, 97`) read `some (PWord.full e.2.1)`. Nothing else changes:
- G1/G2 and `completeError` are unchanged;
- the query count of the full partial tree is the deployed tree's, in a different order, and
  T6 asks acceptance in `Id` at every hash agreeing with the log;
- E2E-4 and E2E-8 are untouched.

## 4. The bridge

### 4.1 T7′ restated

Today (`Sanity.lean:476-500`, `idealVerify_blake2s`) the hypotheses on the reached nodes are
`WordsCover` (a full word with the stack root), `CandidatesAux`, `TablesPrecheck` and
`FuelBounds`. `WordsCover` is false for a prover that left a subtree uncomputed (an arbitrary
digest at an inner node): no full word has that root unless a BLAKE2s preimage is found.

With partial words:

- **Today's T7′ carries over verbatim**, with `ip.word ν = some (PWord.full W)`: a full word
  is never rejected by the new rule.
- **T7″ (new, `idealVerify_blake2s_known`)**:
  - Hypotheses: `verifyAggregate guest s ip.proof`, `KnownStacks`, `StacksPrecheck` and
    `FuelBounds` ⇒ V_I^{BLAKE2s} accepts.
  - `KnownStacks ip root`: every reached `ν` with head `hd` has `P`, `q` with
    `ip.word ν = some P`, `WellShaped hd.width P.word` and `pTreeRoot blake2s hd.height P` the
    node's root. Moreover `M3Holds (leanIsaInstance F₀ guest hd.sizes) (inputOf ν.1) q` holds,
    every present column of `P` is `stackWord q`'s, and at least `thr` columns are present.
  - `StacksPrecheck`: `Precheck` of that `q`'s run's rows.

| today's hypothesis | with partial words (T7″) |
| --- | --- |
| `WordsCover` | **replaced** by `KnownStacks`. The tree part is met by any prover from its own partial tree, and a prover can turn a wrong present column into a level-0 hole (its leaf digest). The content left is "at least `thr` columns encode one stack satisfying the relation". |
| `CandidatesAux` | **disappears**: the list is `{q}` (`eq_of_mem_sCandidates`), and `q` satisfies `aux` by `M3Holds`. Non-emptiness, which the new rule asks for, comes with it (`mem_sCandidates_of_exact`). |
| `TablesPrecheck` | **weakens** to the one stack's rows: two active non-final rows of a deployed-valid execution with distinct inputs and equal outputs are a BLAKE2s compression collision. That is collision resistance, falsifiable from the extractor's output. |
| `FuelBounds` | **unchanged**: the closure's size, i.e. no cycle of nodes, which is a hash fixed point under BLAKE2s. |

### 4.2 The knowledge assumption (for §5)

§5 states the deployed conclusion as a conjecture. The route by which the random-oracle theorem
supports it is: an extractor turns a deployed adversary `A` into an idealized one
`A′ = (A, E_A)`; T7″ makes V_I^{BLAKE2s} accept `A′`'s output; and the random-oracle heuristic
is applied to `A′`. Today that route needs "`A` knows every reached full word", which a lazy `A`
falsifies at no cost. With partial words it needs:

> **KA-pw (straight-line extraction of partial words, BLAKE2s).** Let `A` be an adversary of the
> deployed game whose BLAKE2s compression calls are observable (§5 (d)'s convention), with trace
> `τ_A`. Let `E_A` be the following deterministic extractor:
> - It runs V_I's closure with BLAKE2s.
> - At each reached node `ν` with stack root `r_ν`, it reads the partial word `Ext(τ_A, r_ν)`
>   off the trace: the row of every leaf whose path to `r_ν` the trace answers, and a hole at
>   every maximal subtree whose digest the trace does not invert (`Rom.extract` with holes).
> - If some stack `q_ν` satisfying `M3Holds` on `ν`'s input agrees with that word on at least
>   `thr` present columns (list decoding to the Johnson radius, then the relation check), it
>   replaces the present columns that disagree with `enc(q_ν)` by level-0 holes.
> - It names no frames.
>
> Assumption: except with probability `ε_KA(q_A) ≈ q_A · 2^-128` (the proof system's designed
> knowledge error: the level-0 query phase at the Johnson radius, `≈ 2^-112` per attempt, then
> its proof of work), whenever `verifyAggregate` accepts `A`'s output, such a `q_ν` exists at
> every node `E_A` reaches.

KA-pw, collision resistance of BLAKE2s compression (`StacksPrecheck`) and acyclicity
(`FuelBounds`) are the hypotheses of T7″ for `A′`.

**How standard it is.** KA-pw is knowledge soundness of the deployed proof system (WHIR at the
Johnson radius plus Flock, Fiat–Shamir with BLAKE2s), with the BCS straight-line extractor that
reads the Merkle trees off the prover's hash trace. Its random-oracle analogue is a theorem: T1
proves the same extraction with `M3HoldsBlind` and error κ_V°. The Flock part (`aux`) has no
analogue there (V° is Flock-blind), and it is the deployed Flock check's soundness. Given the
trace, KA-pw can be checked: extract, list-decode, check `M3Holds`. Every lazy prover meets it up
to the protocol's own soundness level (§2.3 table, first column). The full-word assumption it
replaces cannot be met.

## 5. Packages

| package | files | lines | content |
| --- | --- | --- | --- |
| PW1 statement | new `E2E/PartialWord.lean`; `E2E/Statement.lean` | ≈ 150 | `PWord`, `pNodeM`, `pTreeRootM`, `Present`, `Full`, `SAgrees`, `SCandidates`, `blindCandidatesS`; `IdealProof.words`, `nodeStep` (§1.2); `pTreeRootM_full`, `sCandidates_full` |
| PW2 relational | `E2E/Natural.lean`, `E2E/Rel.lean` | ≈ 80 | `rel_pNodeM`, `rel_pTreeRootM`, `rel_nodeStep`, `pTreeRootM_mono`; `Bridge.lean` follows via `rel_idealVerify` |
| PW3 T4 | `Knowledge/Word.lean`, `Knowledge/Node.lean`, `Knowledge.lean`, `KnowledgeSub.lean`, `Vis/Knowledge.lean` | ≈ 350 | `climb_append`, `climb_of_pNodeM`, `extract_eq_of_pTreeRootM`; `exists_blindCandidatesS` (two cases); `nodeStep_some`'s new branch; call sites |
| PW4 T6 | `Complete/Node.lean`, `Complete/Prover.lean`, `Complete/Rom/AssembleN.lean`, `Complete/Assemble.lean` | ≈ 120 | `PWord.full` wrapping, three rewrites in `nodeStep_honest` |
| PW5 T7′/T7″ | `Sanity.lean` | ≈ 350 | today's T7′ with `PWord.full`; `KnownStacks`, `StacksPrecheck`, `idealVerify_blake2s_known` from `eq_of_mem_sCandidates_deployed`, `mem_sCandidates_of_exact` |
| PW6 docs, tests, pins | `e2e-security.md` §2, §4 T7′, §5, §7, §8; `docs/roadmap/README.md`; `tests/LeanVMTests/E2E/Sanity.lean`; `LeanVM.lean` (pin T7″) | ≈ 150 | |

Total about 1.2k lines (estimate); the implementation came to about 700 (§6).

**Order.** PW1 → PW2 → {PW3, PW4, PW5} in parallel (disjoint files) → PW6. The end theorems'
names, statements and bounds do not change, so T5, `NoForgery*`, `Deployed*`, `Headline` and
the `Vis/*` family only rebuild.

**Rebuild.** `Statement.lean` sits below about 370 modules: every E2E module, plus the Guest
completeness modules that import `E2E/Complete/Table`. None of the generated kernel-checked
families is among them. A full `lake build` with `scripts/ci-build.py` is still the gate.

**Risks.**
1. `nodeStep_some`'s unfolding proof (`split at h` chain) is brittle under the new `if`. It is
   mechanical but must be redone, along with Sanity's `nodeStep_eq_some` and T6's
   `nodeStep_honest`.
2. `rel_nodeStep`/`rel_closure` in two monads: `pNodeM`'s match on a hole must be related by
   cases on `P.hole k j`. It is small.
3. The classical `= ∅` test in the trusted statement is harmless: V_I is already classical, as in
   `Finite` and `ν ∈ done`.
4. Nothing probabilistic changes, so the risk to the bound is nil. The only theorem-level novelty
   is the holed case of T4, which is shorter than today's.

## 6. Implementation (done)

- **PW1** `LeanVM/E2E/PartialWord.lean` (new): `PWord`, `PWord.full`, `Present`, `Full`,
  `pNodeM`, `pTreeRootM`, `pTreeRootM_full`, `SAgrees`, `SCandidates`, `sCandidates_full`,
  `mem_sCandidates_of_candidates`. `LeanVM/E2E/Statement.lean`: `blindCandidatesS`,
  `blindCandidatesS_full`, `IdealProof.words : List (Node × PWord)`, `nodeStep` (§1.2).
- **PW2** `Natural.lean` (`rel_pNodeM`, `rel_pTreeRootM`), `Rel.lean` (`pTreeRootM_mono`),
  `Engine.lean` (`closed_pNodeM`; `closed_nodeStep`, `closed_closure` no longer need a lawful
  monad).
- **PW3** `Knowledge/Word.lean` (`climb_append`, `climb_of_pNodeM`, `extract_eq_of_pTreeRootM`,
  `mem_blindCandidates_of_extractedBlind` at a full partial word, `exists_blindCandidatesS`),
  `Knowledge/Node.lean` (`nodeStep_some` exposes the full-or-candidate fact), the call sites in
  `Knowledge.lean`, `KnowledgeSub.lean`, `Vis/Knowledge.lean`.
- **PW4** `Complete/Node.lean` (`nodeStep_honest` at `PWord.full`), `Complete/Prover.lean`,
  `Complete/Assemble.lean`, `Complete/Rom/AssembleN.lean` (honest words wrapped in `PWord.full`).
- **PW5** `Complete/Candidates.lean` (`eq_of_mem_sCandidates_exact`,
  `eq_of_mem_sCandidates_deployed`, `mem_sCandidates_of_exact`); `Sanity.lean` (`nodeStep_eq_some`
  on partial words; `WordsCover` asks full words, `CandidatesAux`/`TablesPrecheck` read the strict
  candidates; T7″: `Head.config`, `KnownAt`, `KnownStacks`, `StacksPrecheck`,
  `step_of_reached_known`, `idealVerify_blake2s_known`).
- **PW6** this note, `e2e-security.md` (§2, §4 T7′, §5 KA-pw, §7 E2E-10, §8), the pin of
  `idealVerify_blake2s_known` in `LeanVM.lean`, tests (`tests/LeanVMTests/E2E/PartialWord.lean`,
  `Sanity.lean`, `Knowledge.lean`).

Every end theorem (T4, T5, W-vis, the headline and the sharp headline, T6-det, T6-prob, T7′)
keeps its name, statement and bound.

## 7. Decision text

Recorded as **E2E-10** in `e2e-security.md` §7.
