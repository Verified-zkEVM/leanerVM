Closes the four **structural** obligations in `OracleReduction/LiftContext/Reduction.lean`, plus the
completeness transport that sits on top of them.

Measured against `main`: that file carries **10 `sorry` occurrences across 8 declarations**. This PR
closes **4 of the 8** (10 → 5 occurrences). The 4 that remain are exactly the `Verifier.*` soundness
theorems, which are deliberately out of scope — see *Scope* below.

This is **not** "closes #676". Please read the scope section before merging.

The design question behind the largest change is raised separately in the #676 thread; if you'd
rather the interface took a different shape, that discussion should probably settle before this is
reviewed in detail.

---

## The finding this PR is really about

`Verifier.StateFunction.liftContext` was **not provable as typed**. The `sorry` was a symptom, not
unfinished work.

`StateFunction.toFun_empty` is a biconditional, and both directions are genuinely consumed:
`Composition/Sequential/Append/StateFunction.lean` uses `.mp` once (line 318) and `.mpr` four times
(324, 430, 521, 648), and `Security/RoundByRound.lean` uses `.mpr` once. But
`Statement.Lens.IsSound` supplies only `proj_sound : ∉ outerLangIn → ∉ innerLangIn`. The converse
doesn't exist anywhere in the API at the **language** level — `Context.Lens.IsComplete.proj_complete`
has the right shape but lives at the **relation** level (`Set (Stmt × Wit)`) and cannot discharge a
`Set Stmt` obligation.

The two conditions turn out not to be two hypotheses but **one equation**:

```lean
theorem Statement.Lens.eq_preimage_of_projSound_of_isComplete :
    outerLangIn = lens.proj ⁻¹' innerLangIn
```

`proj_sound` is one containment; the missing datum is the other; `toFun_empty` is that equation read
pointwise (`mem_iff_proj_mem`). Hence a new language-level class, mirroring the existing
relation-level one, passed as an instance argument.

**The alternative is deliberately not taken.** Weakening `toFun_empty` from `↔` to `→` removes the
`sorry` immediately, but breaks the already-landed append state function and weakens the
state-function notion for every protocol in the library — converting a faithful encoding of
Chiesa–Yogev Definition 31.1.1 into something weaker while leaving every downstream theorem name
unchanged.

---

## What changed, split by what needs your decision

**Interface changes (need a maintainer call) — `LiftContext/Lens.lean`**

| Item | What it is |
|---|---|
| `class Statement.Lens.IsComplete` | the missing language-level containment |
| `[lensComplete : …]` on `Verifier.StateFunction.liftContext` | new instance argument |
| 5 instances | incl. `instIsCompletePreimage`, the terminal one: every complete pair factors through the preimage language |
| `isSound_not_implies_isComplete`, `isComplete_not_implies_isSound`, `isSound_not_implies_isComplete_nonvacuously` | both separation directions, plus a witness where soundness is discharged against a genuine out-of-language statement rather than an empty quantifier |
| `preimage_subset_of_projSound` | isolates the single classical step (a contraposition out of a negated statement) so the layer's classical content stays auditable |

**Pure proof contributions (no interface change; statements unchanged)**

| Obligation | Note |
|---|---|
| `Extractor.RoundByRound.liftContext` | applies `E.extractMid`/`E.extractOut` and routes the statement through the lens; ships `liftContext_extractMid`/`_extractOut` pinning that it does |
| `StateFunction.toFun_full` | consumes `lensSound.lift_sound` |
| `Reduction.liftContext_runWithLog` | consumes `Prover.liftContext_runWithLog` |
| `Reduction.liftContext_completeness` | statement unchanged, no added hypothesis, no import change |

**One new general lemma, `Reduction.simulateQ_optionT_map`.** A pure post-map passes straight through
any simulation: `simulateQ impl (f <$> oa) = Option.map f <$> simulateQ impl oa`, for an arbitrary
target monad — naturality of the monad morphism `simulateQ impl` in the value. It's needed twice
(`liftContext_runWithLog` is the `WriterT` instance, `liftContext_completeness` the `StateT` one), so
the with-log lemma is now a one-line corollary. Net new API across both proofs is this single
declaration, and it is choice-free (`[propext, Quot.sound]`).

Two obstructions it resolves, neither visible from the statement:

1. **The lift starts trapped inside the simulation.** `liftContext_run` exhibits the lifted run as a
   pure post-map, but `completeness` evaluates its predicate on `(simulateQ pImpl _).run' s`, so the
   two probability events don't share a base computation until that post-map is commuted out.
2. **`compatContext` is stated about the wrong computation.** It's defined against
   `support (R.run …)` — the *unsimulated* reduction — while `probEvent_mono` supplies membership in
   the support of the simulated, state-threaded, `OptionT`-wrapped one. The bridge is that
   simulating can only shrink the support (`support_simulateQ_run'_subset`), since every `QueryImpl`
   answer already lies in the query's own range.

---

## Disclosed limitation of the instance set

All five instances are structural families (identity, input-only, output-only, the preimage/terminal
one) plus the separation witnesses. **None is a lens taken from `ArkLib/ProofSystem/`.**

I'd rather state why than leave it implicit: `Statement.Lens.IsSound` appears in no ArkLib source
file other than its own definition in `Lens.lean` — it has **zero instances**, is taken as an
instance argument at several sites, and is produced by no protocol. There is no protocol-level
precedent at the language level to mirror. At the *relation* level the picture differs
(`Sumcheck/Spec/SingleRound.lean` has a proved `proj_complete`; `Binius/FRIBinius` has one stubbed),
which is itself the point: the relation level is populated and the language level never was.

So the honest status is that the class is **inhabitable across structural families and demonstrably
non-redundant**, but has **not** been exercised on a real protocol. If you want that first, it's a
larger piece of work than this PR.

---

## Scope

- **In:** the non-probabilistic half of `LiftContext/Reduction.lean`, plus `liftContext_completeness`.
- **Out:** `liftContext_soundness`, `liftContext_knowledgeSoundness`, `liftContext_rbr_soundness`,
  `liftContext_rbr_knowledgeSoundness`, and all of `Security/Implications.lean`.
- **Why:** the excluded theorems are probability-statement-bearing, and #913 is actively retiring the
  PMF surface they're written over. Proving them now would invite rework.

The honest claim is: **this closes the structural half of #676; the soundness half remains open and
is gated behind the probability migration.**

**One excluded theorem does change, and it is a hypothesis change.** Three of the four
(`liftContext_soundness`, `liftContext_knowledgeSoundness`, `liftContext_rbr_knowledgeSoundness`) are
untouched. `liftContext_rbr_soundness` gains exactly one instance binder,
`[lensComplete : lens.IsComplete outerLangIn innerLangIn]`, because constructing the lifted state
function now requires it; its proof body and its `sorry` are unchanged. That's a strengthened
hypothesis on an out-of-scope theorem, and it's the one place this PR makes a downstream statement
weaker. If you'd prefer that theorem keep its current signature, the alternative is a separate
constructor taking the completeness datum explicitly — happy to do it that way.

**Interaction with #913.** I checked rather than assumed: #913 modifies this file only by deleting
six lines of dead scaffolding from `liftContext_rbr_knowledgeSoundness` (an out-of-scope theorem), and
it does **not** alter `structure StateFunction` or `toFun_empty` — so the argument above survives it.
The completeness proof here consumes VCVio's probability API directly, which is the target of that
migration rather than the surface being retired. Expect one trivial textual conflict in that
out-of-scope theorem depending on merge order; happy to rebase either way.

---

## Verification

| Check | Result |
|---|---|
| Declaration set preserved | **0 removed**, 42 added |
| `sorry` / `admit` / `stop` / `native_decide` in the four bodies | 0 |
| `Security/RoundByRound.lean` diff | **empty** — `structure StateFunction` untouched |
| `Security/Implications.lean` diff | **empty** |
| `#print axioms`, **every one of the 42 added declarations** (41 addressable; 1 is `private`) | **zero `sorryAx`** |
| of those 41: axiom-free / choice-free / using `Classical.choice` | **17 / 35 / 6** |
| `Extractor.RoundByRound.liftContext`, `simulateQ_optionT_map`, `run_simulateQ_writerT_optionT_map` | `[propext, Quot.sound]` — choice-free |
| `preimage_subset_of_projSound` | `[propext, Classical.choice, Quot.sound]` — the one deliberately classical step, isolated so it stays auditable |
| Substitution-body mutation fixtures (kept local, not submitted) | 4 harnesses, **21/21** mutants rejected, **7/7** controls still elaborating |
| Independent check of the pullback characterisation | brute-force enumeration over all 4 projections × 4 outer × 4 inner languages on `Bool`: **0 disagreements / 64** |

**What I could not check.** My development tree is pinned to **v4.31**, so the content above is
verified green there, not at v4.34. The module syntax (`module`, `public import`,
`@[expose] public section`) is taken from the current `main` file layout, and the `simp` → `simp only`
tightenings already on `main` are preserved rather than reverted. **CI here is the acceptance gate,
not my local build** — if it finds a v4.34-only breakage I'll fix it in this PR.

One note, since 4.34 makes unfolding export-controlled: every lemma these proofs rewrite with is a
*theorem*, so `simp only` consumes its statement and never its body, and the module system can't
change whether they fire. The one step discharging a defeq by computation rather than a named lemma
is the trailing `rfl` in `OptionT.probEvent_eq_of_run_map_eq _ _ _ _ rfl` — the first place to look
if 4.34 disagrees.
