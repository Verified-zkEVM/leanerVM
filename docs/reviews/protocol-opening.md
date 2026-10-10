# Review: the opening phase

> An archive of the review of commit `54e1802` of the branch `feat/protocol-opening` ("the
> opening phase"), against its base `2c4573d`, the head of draft pull request #77 (batching by
> powers), which is not under review except as the base the commit consumes: names, paths and
> line numbers are those of `54e1802`. No pull request was open for the branch at the time of the
> review. What is accepted from it is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of the
> pull request that met it.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. the stated reason for not consuming `Component.batch` is false | met: the phase is rebuilt as `Component.batch` followed by a new zero-round component whose verifier asks the stack one question and checks the answer (`Component.queryCheck`), composed as `Component.batchQuery` at the slot's `draw E` with its completeness, its security at `(k − 1)/|F|` from `batchSecurity`, and its refutation `batchQuery_not_rbr`, in `ToArkLib/QueryCheck.lean`; the state after the challenge is that the batched claim holds (`Opening.BatchedHolds`); `ToArkLib/SampleQuery.lean` and the phase's own count are gone and `sampleProver_run_support` is private again; the check and verdict of an appended guarded form are two lemmas of `ToArkLib/Component.lean`. The refutation of an added check rejecting `λ = 0` is dropped: on the composition it would need a lemma on the appended prover's runs, and acceptance test 20 is met by the verifier itself, whose batching draws `λ` with no check |
| 2. "the bound is attained" is not shown: the duplicated claim has one bad challenge, the bound is three | met: the review's pool (`tightStmt`), accepted at `1`, `y` and `y + 1` and rejected at `y² + 1` and `0`; the copies stay for the unit-weights refutation; the test docstring and the status say "a pool of four claims is accepted at three challenges" |
| 3. no refutation exercises the weighted half of the pool | met: `columnsOnly_not_rbr` on `flocky`, a true column claim and a false weighted claim on the zero stack, the column-only combination accepted at every challenge, through `columns_holds` stated over an abstract instance |
| 4. `leanVmPhases` sits in a hole whose *Needs* omit the phases it needs, and no blueprint ask is recorded | met: the status asks, through a `docs(protocol)` pull request, for a hole of its own, "the oracle protocol", needing every phase, and for the two generic components to be listed |
| 5. public surface and placement | met: `pool_holds_iff` and `simulateQ_askInput` are private, the prover lemma went with `SampleQuery.lean`, and the status names the public names the tests and the halves' bodies need |
| 6. hygiene and documentation | met: docstrings on `length_poolList` and `accepts_iff`; `ClaimWeights` a plain import; the block comment's `(h₁ h₂)` named as the bus phase's side conditions; the unparsable sentences went with `SampleQuery.lean`; the test file rewritten; the Python verifier cited; the review listed in `docs/README.md`; the pull request number and the classification in the pull request |
| the observations | no change needed |

Reviewed with the `adversarial-review` skill in three passes. The expectation was formed first,
before any Lean was read: from the blueprint (the intro, *For zkVM engineers*, the conventions
*The oracle*, *Claim pool order*, *Errors*, *Load-bearing checks*, *Trusted surface*, *Unproved
targets*, *Generic code*, *Holes*, *Extractors*, *Module system* and *The wall*, the spine's
*What the spine fixes*, the holes-table row "opening phase", Layer 4's batching paragraph,
Layer 10, Layer 11's `whirOpen` paragraph, acceptance tests 20, 24, 31, 32, 33 and 35, the
interfaces list, decision 19) and from the specification at `a386121f`
(`doc/leanvm/body/08-end-to-end-protocol.tex:94-101`, Definition 3.13 at
`03-proving-primitives.tex:112-118`, Annex B's Protocol and Theorem `thm:rbr` at
`b-polynomial-commitment-scheme.tex:108-122, 141-151, 229-230`); then the Rust
(`crates/pcs/src/stack_open.rs:1-58, 152-325, 473-549`, `crates/lean_vm/src/cpu/mod.rs:604-814`,
`crates/lean_vm/src/pcs.rs:128-173`) and the Python (`python-verifier/verifier.py:186-188, 286-311,
515-522, 1350-1413`), each read with `git show a386121f:<path>` since the sibling checkout is past
the pin. Every changed file was read in full, with the base modules it consumes
(`Spine/{Instance,Seams,Errors,Phase,Compose}.lean`, `ToArkLib/{Component,SampleChallenge,Batch,
InnerProduct,Schedule}.lean`, `ToCompPoly/PowerBatching.lean`, `ClaimWeights.lean`, `Field.lean`,
the visibility pattern of `PublicInput.lean`) and the archived review of batching by powers.
Lean was run twice, serially, with `lake env lean` on two scratch files: the first printed the
kernel axioms, checked that `draw E ++ₚ !p[]` and both of its instance families are the slot's by
`rfl`, and ran the tight-bound guards of finding 2 against the built test module; the second
typechecked `Component.batch` appended with a zero-round component at the opening's slot (finding
1). `audit-lean.sh`, `check-imports.sh`, `check-layers.sh` and `check-docs.py` pass; the built
`.olean`s postdate every source file of the commit, so the test file's guards passed when it was
built. `lake test` and `./scripts/validate.sh` were not run (the machine is memory-limited).
Nothing was edited but this file.

Target classification: the commit names #12 and the hole, not a target. The pull request, once
open, is to say that the work feeds T4 through the oracle protocol (the last of the five phases
the master theorems are conditional on), in both directions (`openingComplete`,
`openingSecurity`), that it is Category A (the Lean is the standard) with one transcribed fact,
the order in which the pooled claims take the powers of `λ`, pinned by a `#guard`, and that
`leanVmPhases` is not built.

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological. `openingPhase` is `Component.sampleQuery` at the
slot's `draw E` (`Opening.lean:164-165`): the verifier draws `ρ`, asks the stack once at
`Weight.batch` of the pool's weights and checks the answer against `powerBatch` of the pool's
values. Its state function is the blueprint's ("every pooled claim holds" before `λ`, "the
batched claim holds" after), its relations are inhabited and non-trivial (`honestStmt_flock`,
`badStmt_not_flock`), its error is the slot's closed form, earned by `card_false_batch_le`
(`Opening.lean:181-199`), and it computes (`tests/…/Opening.lean:191-193`, kernel axioms
`propext`, `Classical.choice`, `Quot.sound`). The order of the powers, the weights and the target
match the specification, the Rust verifier and the Python verifier. What is wrong is in the
account of the work: the reason given for departing from the blueprint's "Needs Layer 4's
`batch`" is refuted by a probe (finding 1), and "the bound is attained" is not what the test
shows (finding 2). One refutation is missing (finding 3) and one blueprint ask is unrecorded
(finding 4); the rest is surface and hygiene.

## Findings, most severe first

### Should fix

**1. The stated reason for not consuming `Component.batch` is false.** *Blueprint fit; status
page.* `protocol-status.md:232-236` says the phase uses batching by powers' algebra rather than
`Component.batch` because "a zero-round query after `batch` has the schedule `draw E ++ₚ !p[]`,
which is not the slot's `draw E`". It is the slot's: probed,

```lean
example : (draw E ++ₚ !p[] : ProtocolSpec 1) = draw E := rfl
example : (msgAppend (instOracleInterfaceDraw E)
    (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i)) :
      ∀ i, OracleInterface ((draw E).Message i)) = instOracleInterfaceDraw E := rfl
example : (chalAppend (instSampleableTypeDraw E)
    (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i)) :
      ∀ i, SampleableType ((draw E).Challenge i)) = instSampleableTypeDraw E := rfl
```

all compile, and so does the component-level form, at an abstract instance:

```lean
def batchThenStep : Phase.Def I (I.Stmt × FlockOut I) Unit openingSpec :=
  (Component.batch (W := Unit) (TheOracle I) E (fun s j ↦ (Opening.pool I s.2 j).value)
    (fun s ρ v ↦ (s, ρ, v))).append (Phase.passThrough I fun _ ↦ ())
```

with `Component.Security.mono _ (S₁.append S₂)` typechecking at `openingError I` for `S₁` a
`batchSecurity`-shaped security and `S₂` the zero-round step's (the pointwise inequality between
`errAppend` and `openingError`, left open in the probe, is the obvious one at the one challenge).
The archived review of batching by powers had already found the schedule to be `draw E` by `rfl`
(`docs/reviews/protocol-batch.md`, first observation); the instances, which it left unprobed, are
too. The failure: the one departure from Layer 10's *Needs* rests on a claim that is not true, and
the phase re-derives the count `batchSecurity` already proves (`Opening.card_badQuery_le`) and
adds a second one-challenge component beside `sampleChallenge`. What the probe does not supply is
a zero-round component whose verifier queries the oracle and checks the batched claim (the
pass-through above does not query), with its completeness, its security at the empty error and
an intermediate relation "the batched claim holds of the stack". Fix, one of:
- build the phase as `Component.batch` followed by such a zero-round query component, so that
  `batchSecurity` is consumed as the holes table's *Needs* has it, the status then recording the
  new generic component instead of `SampleQuery`; or
- keep `sampleQuery` and replace the sentence with the real trade (one component and no
  intermediate relation, against two components, an intermediate relation and an append; the
  count is `card_false_batch_le` either way).

**2. "The bound is attained" is not shown.** *Tests; status page; commit message.* The test
docstring (`tests/LeanerVMTests/Protocol/Opening.lean:16-17`), the status
(`protocol-status.md:245-246`) and the commit message say the bound is attained by `dupStmt`. The
toy's pool has `J = 4` claims, so the slot's bound is `J − 1 = 3` bad challenges; `dupStmt`'s
difference polynomial is `1 + λ` (two copies off by one, two true claims), with exactly one root,
`λ = 1`. The guards show that a bad challenge exists, which is weaker. A pool attaining the bound
exists on the same claims: four claims on one column and point, off by the coefficients of
`(λ + 1)(λ + y)(λ + y + 1) = λ³ + (y² + y + 1)·λ + (y² + y)`. Probed against the built test module,
every guard passes:

```lean
/-- The claim on column `c` at `(z)` with its value off by `d`. -/
def offBy (c : toy.ColumnId) (z d : E) : ColumnClaim toy :=
  ⟨c, #v[z], (trueClaim c z).value + d⟩

/-- Four claims whose differences are the coefficients of `(λ + 1)(λ + y)(λ + y + 1)`: three
bad challenges, the slot's `J − 1`. -/
def tightStmt : K × FlockOut toy :=
  stmtOf (offBy ⟨0, 0⟩ y (y * y + y)) (offBy ⟨0, 0⟩ y (y * y + y + 1)) (offBy ⟨0, 0⟩ y 0)
    (offBy ⟨0, 0⟩ y 1)

#guard ¬ ∀ c ∈ tightStmt.2.columns.toList, c.Holds honest
#guard Opening.accepts toy tightStmt.2 1 (answer tightStmt 1)
#guard Opening.accepts toy tightStmt.2 y (answer tightStmt y)
#guard Opening.accepts toy tightStmt.2 (y + 1) (answer tightStmt (y + 1))
#guard !Opening.accepts toy tightStmt.2 ρ₂ (answer tightStmt ρ₂)
```

Fix: add the guards above (a polynomial of degree three has no more roots, so the three accepted
challenges are all of them), keep `dupStmt` for the unit-weights refutation, and reword the test
docstring and the status line ("the bound is attained: a pool of four claims is accepted at
three challenges").

**3. No refutation exercises the weighted half of the pool.** *Load-bearing checks.* Every
refutation runs on the toy (`tests/…/Opening.lean:286-387`), which has no Flock region, so
`FlockOut.weighted` is empty there: a verifier that batches the column claims alone and drops the
Flock phase's weighted claims is identical to `openingPhase` on every statement the tests use.
Layer 9 lists "the weighted claim and the limb claims entering the pool" among the checks that
each come with a refutation, and the opening is where the weighted claim enters the batch. The
failure: the omission that loses Flock's whole contribution to the relation is the one weakening
no test can catch. Fix: a fourth refutation on `flocky` (`tests/…/Opening.lean:147-161`), which
already pools one weighted and one column claim. On the constant-one stack of height `2^8`,
`flockyPool`'s column claim (value `1` at `ys`) holds and its weighted claim
(`⟨eqWeight ys, y⟩`, answer `1`) fails, so the statement is outside the Flock seam; the verifier
whose question and check batch `s.2.columns.toList.map (Opening.columnWeighted flocky)` alone
accepts it at every challenge, and `Component.sampleQuery_not_rbr` gives no error below one.
Following the pitfall recorded in `tests/README.md`, prove "a pool whose column claims all hold
is accepted by the column-only batch at every challenge" once over an abstract instance, give the
variant's question and check as named definitions, and instantiate at `flocky`.

**4. `leanVmPhases` sits in a hole whose *Needs* omit the phases it needs, and no blueprint ask
is recorded.** *Holes; status page.* The holes table's row "opening phase" produces
`leanVmPhases` and needs "the spine; batching by powers; tables and stacking"
(`protocol-blueprint.md:592`), but `leanVmPhases` needs the bus phase, the table sumcheck, the
Flock phase and the deployed public-input phase. The commit is right to leave it a block comment
(`Opening.lean:218-228`, convention *Unproved targets*), and the status says so
(`protocol-status.md:224-231`); but the hole can never be built from the prerequisites its row
names, and the status records no ask, unlike the GKR's (`protocol-status.md:186-189`). Fix: add to
the status the ask, for a `docs(protocol)` pull request, that `leanVmPhases` and the protocol-level
test move to a hole of their own ("the oracle protocol", needing every phase), or that the
opening's row lists those phases among its *Needs*.

### Nits

**5. Public surface and placement.** *Interfaces; module structure.* The hole's interfaces are
`openingPhase`, `openingComplete`, `openingSecurity` (and `leanVmPhases`); the commit adds 37
public declarations besides: 19 in `Opening`, 16 in `ToArkLib/SampleQuery.lean`, 2 in
`ToArkLib/WeightBatch.lean`, and `sampleProver_run_support` made public. Most are needed public
(the exposed bodies of `pool`, `openingComplete` and `openingSecurity` name `length_poolList`,
`check_of_flock` and `card_badQuery_le`; the tests name the pool, weight, value, question and
their lemmas; the generic module is upstream material). Proof-only helpers that could be
`private`, as `PublicInput.lean` does for its own:
- `Opening.pool_holds_iff` (`Opening.lean:134`), used only in two proofs;
- `Component.simulateQ_askInput` (`SampleQuery.lean:73-79`), used only in
  `queryVerifier_verify`'s proof;
- `Component.exists_mem_support_sampleProver_run` (`SampleQuery.lean:120-131`), a lemma about
  `sampleProver`, used only in `sampleQuery_not_complete`'s proof. If kept public, its home is
  `ToArkLib/SampleChallenge.lean` beside `sampleProver_run_support`, the definition it is about.

The status's opening bullet may say which public names, beyond the hole's, the tests and the
generic module need, as the deployed public-input bullet does (`protocol-status.md:148-150`).

**6. Hygiene and documentation.**
- `Opening.lean:72` (`length_poolList`) and `:99` (`accepts_iff`): no docstring
  (`CONTRIBUTING.md:114`).
- `Opening.lean:13`: `public import LeanerVM.Protocol.ClaimWeights` appears to be needed only by
  proofs (`ColumnClaim.holds_iff_weighted` is named in no statement or exposed body); a plain
  `import` would do. Not probed.
- `Opening.lean:222`: the block comment's `(h₂ : …)` elides the hypothesis; name it (decision
  30's "a table with a constraint is on the bus", and the fit of the pull and count leaves the
  status adds), or write `(h₁ h₂)` as the blueprint does.
- `SampleQuery.lean:30-32` and `:246-248`: "a statement with no witness at which every challenge
  passes the check into the output relation" does not parse; "a statement outside the input
  relation, every challenge passing the check and landing in the output relation" does.
- `tests/…/Opening.lean:227-228`: two blank lines before the section header.
- `protocol-status.md:218-222`: "as both deployed sources do" cites the Rust alone; add
  `python-verifier/verifier.py:1409-1413` ("it leads the batch, taking the first power").
- `protocol-status.md:29, 52`: `#PRNUM` to fill when the pull request opens.
- `docs/README.md` lists each review; this file is to be listed.
- The pull request body: the classification above, and the corrected wording of findings 1 and 2
  (the commit message repeats both).

### Observations, no change needed

- **Fidelity of the order, the weights and the target.** The specification gives claim `j` the
  power `λ^{j−1}`, "the ring-switched claim first and the pooled column claims after"
  (`08-end-to-end-protocol.tex:98`); the Rust verifier takes `powers(vs.sample(), n_rs +
  point_claims.len())` split at `n_rs` (`stack_open.rs:518-519`, `powers` from `x^0`), the target
  `Σ g·verify_finish(…) + Σ g·claim.value()` (`:521-527`) and the weight
  `rs_part·sel_eq + Σ g·stack_claim_eq_at` (`:530-546`); the Python pools
  `[ringswitch, *claims]` under `powers(transcript.sample(), len(claims))` (`verifier.py:1361,
  1413`, `powers` from `1` at `:186-188`). `poolList` is `weighted ++ columns`
  (`Opening.lean:69-70`), `value` is `powerBatch`, zero-based, and `Weight.batch`'s evaluator is
  `Σ_j ρ^j·W̃_j(r)`: the three agree, and the `#guard` on `flocky`
  (`tests/…/Opening.lean:173-174`) pins the order against the swapped one.
- **The column claim's weight.** `eqWeight (I.layout.extend c.col c.point)` is the Rust's
  `stack_claim_eq_at` (`stack_open.rs:294-325`) for both claim kinds, provided the layout lifts a
  committed column's point to `(point, sel bits)` and a BLAKE2S value column's to
  `(slot bits, point, sel bits)` (`cpu/mod.rs:790-814`, `verifier.py:295-297`): the opening
  takes every column claim through the layout's lift, and routing the eighteen limb columns to
  strided slots of `q_flock` is the adaptor's to prove of `leanIsaInstance`.
- **The count of checks.** The deployed opening makes one acceptance equation (WHIR against the
  combined target); its other conditions are caller invariants it asserts (`stack_open.rs:485-500`:
  the `q_flock` alignment and range, at least one ring-switched claim, the suffix lengths, every
  claim inside the cube) and the shape of the 64 `s_hat_v` (`:506-511`), which the Lean carries by
  types (vector lengths, the layout into `Vector E μ`, the Flock slot's `say (Vector E 64)`) or,
  for "at least one ring-switched claim", rightly does not require (the toy has no region). The
  Lean's one equation is the deployed one. The six ring-switching challenges come before `λ` in
  both (the end of the Flock slot; `stack_open.rs:513`).
- **The error.** Annex B charges the level-0 batch `(J_0 − 1)·L_0/|E|`
  (`b-polynomial-commitment-scheme.tex:143, 230`), which is the slot's `(J − 1)/|E|` with the
  unique oracle of the ideal model. The slot's error is load-bearing against two variants the
  tests do not need: positive powers (`ρ = 0` becomes a bad challenge for every false pool, so a
  pool with `J − 1` other roots has `J`) and accepting at `ρ = 0`.
- **Pooled values.** The opening pools no value of its own: every value comes from the Flock
  seam's statement, bound before `ρ`, so acceptance test 31's concern has no object here.
- **`leanVmPhases` as a block comment** follows *Unproved targets*, and the status row
  ("without `leanVmPhases`") and bullet are honest about it; finding 4 is about the blueprint's
  row, not the call.
- **Acceptance tests.** 20: `openingComplete` holds at every `ρ`, `0` included, and the verifier
  that rejects `ρ = 0` is refuted (`rejectsZero_not_complete`). 24: `keepExtractor`, and
  `security` is a compiled `def` at `E`. 32: the three refuted variants have no error below one at
  any extractor, and the slot's error is `overE (J − 1)`. 33: one challenge and one question. 35:
  the opening is the only phase typed `Phase.Def`.
- **Generic code.** `SampleQuery.lean` and `WeightBatch.lean` carry no protocol vocabulary
  (grepped; "opening" appears once, as a generic example), say they are ArkLib candidates, and
  live in `ToArkLib/` by their objects (`OracleVerifier`, `Weight`), `WeightBatch` importing the
  CompPoly candidate `PowerBatching` as ArkLib imports CompPoly.
- **The honest-pool guards** evaluate `Opening.accepts` on the oracle's answer computed in the
  test (`answer`, `tests/…/Opening.lean:71-72`), which is the guarded check of `openingPhase` by
  `queryVerifier_verify` and `innerProductOracle_answer`; a mis-wiring of `openingPhase` itself
  would break `openingComplete`'s proof first.

## Answers to the questions put to the review

- **Is `openingSecurity` earned, with a non-vacuous state function?** Yes. The state function is
  `queryStateFunction` at `Seam.flock` and `Seam.done`: the Flock seam before `ρ`, the check on
  the stack's answer after it (`SampleQuery.lean:184-196`). The bad challenges are those at which a
  statement outside the Flock seam passes the check (`badQuery`); `card_badQuery_le` bounds them
  by the roots of `powerBatch answers − powerBatch values`, nonzero since some claim is false
  (`Opening.lean:191-199`). `Seam.flock → Seam.done` are the spine's seams for the slot. No
  hypothesis; inhabited and non-trivial relations.
- **Could a weaker verifier satisfy the same theorems?** None found. The variants that satisfy
  both theorems are those that permute the powers, which is the transcribed fact the `#guard`
  pins. Missing refutation: finding 3.
- **Do the refutations refute the right weakenings, with inhabited hypotheses?** Yes for the
  three on the toy and the extra-check one: each is a closed theorem over a concrete statement
  (`badStmt`, `dupStmt`, `honestStmt`) proved outside or on the seam.
- **The λ-power order and the column-to-weighted conversion.** Faithful to the specification, the
  Rust and the Python (observations).
- **`leanVmPhases` as a block comment.** The right call; finding 4.
- **The departure from "Needs Layer 4's `batch`".** Not justified as written: finding 1.
- **Generic code rules, public surface.** Generic and well placed; surface in finding 5.
- **Does the security compute?** Yes: `openingSecurity` is `Security.mono` (inlined) over
  `sampleQuerySecurity`, no real number argument, `keepExtractor`, and the test's `security` is a
  compiled `def`.
- **Hygiene.** No Lean comment cites the roadmap; no Lean line exceeds 100 columns; findings 6.
- **The test file.** Every guard and example tests what its comment says, except "the bound is
  attained" (finding 2); "every stack is accepted" on the empty pool is tested on one stack, which
  the zero weight makes enough.

## Pass A: the statements

`openingPhase` is a computable `Def` with no error in it; `openingComplete` asks nothing beyond
the Flock seam; `openingSecurity` is at the slot's `openingError I`, raised from
`sampleQuerySecurity` at `(J − 1)/Nat.card E` by an equality. The generic `sampleQuery_complete`,
`sampleQuery_rbr`, `sampleQuery_not_rbr` and `sampleQuery_not_complete` mirror
`sampleChallenge`'s with the check moved after the challenge and onto the oracle's answer; their
hypotheses are the escape condition and its negation. `Weight.pair_batch` is linearity of the
pairing; `Weight.batch`'s evaluator carries its proof. Non-vacuity: `honestStmt_flock`,
`badStmt_not_flock`, `dupStmt_not_flock` and the guards. Load-bearing checks: three refutations
of the check and one of an added check; the fourth owed is finding 3.

## Pass B: fidelity at `a386121f`

One Category-B fact: the order of the powers. Source and Lean agree on it, on the zero-based
powers, on the target and on the combined weight; the count of acceptance equations is one on
both sides; the deployed caller invariants are types or absent by design (observations). No
deviation is declared, and none was found.

## Pass C: hygiene

The module docstrings carry the specification paragraph with path, lines and pin, the Rust lines
for the order, and how the module was written ("from the specification; the Rust verifier was
read afterwards for the order of the powers"). Declaration docstrings are one or two lines. The
rest is findings 5 and 6.

## Kernel axioms

`openingSecurity`, `openingComplete`, `Component.sampleQuery_not_rbr`,
`Component.sampleQuery_not_complete` and `Weight.pair_batch`: `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`.

## What could not be checked

The pull request's description, not yet open. Whether a zero-round query component plus
`Component.batch` is smaller in total than `SampleQuery` (finding 1): the component was not
written. Whether `ClaimWeights` can be a plain import (finding 6). That `leanIsaInstance`'s layout
routes the limb columns to strided slots (the adaptor, not built). The whole `lake test` and
`./scripts/validate.sh`, not run on the memory-limited machine.
