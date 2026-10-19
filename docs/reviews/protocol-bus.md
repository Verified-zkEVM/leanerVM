# Review: the bus phase, definition and completeness

> An archive of the review of one commit on the branch `feat/protocol-bus`, `3b1db0c`, against
> its base `feat/protocol-fingerprint-collision` (#78, reviewed separately and not re-reviewed
> here). Names, paths and line numbers are those of `3b1db0c`. What is accepted from it is text of
> the [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of
> the pull request that met it.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. no test pins the check `R_c ≠ 0`, and its refutation is not recorded as owed | met: `roots_unchecked_no_stateFunction` in the bus tests, the section retitled; the status records that the refutation is at the step's relations, a phase-level one not attempted |
| 2. the public lines and the Flock predicate ride as a rider on no variable, which the grand-product module does not document and no test exercises | met: the grand-product module's riders paragraph says what a rider on no variable is, a grand-product test fails both relations with one, a bus test evaluates the lines rider on the spine's toy, and the status names the frame that would replace it |
| 3. audit surface: one dead theorem, one dead case, proof-only lemmas public | met: `cast_lowPoint` deleted, the six lemmas private, `Source.tuple`'s docstring says no definition reads the count case, and the status names what the security half consumes |
| 4. the status page and the stacking module's docstring are short of the new work | met: the pull request number, the axiom sentence, the wording, one bullet for the fits, the owed blueprint edit and the adaptor's obligation in the status; the stacking module's list |
| 5. Layer 6's test list is met only in part, and the status page does not say so | met in part: the round and challenge counts guarded at `busToy`; the run by parts recorded in the tests and the status, no by-hand run of the grand-product argument on the bus's leaves |
| 6. citation ranges and one ambiguous sentence in the module docstring | met |

Reviewed with the `adversarial-review` skill in three passes. Order of reading: the specification
first (`doc/leanvm/body/05-arithmetization.tex` §5.1–§5.5 at lines 6-160, and
`06-bus-interactions.tex` §6.2, "The count product", line 78), then the pinned Rust
(`crates/lean_vm/src/leaf.rs` whole, `gkr.rs:236-430`, `cpu/layout.rs:328-427`,
`witness.rs:67-79`, `constraints.rs:241-262`), all with `git show a386121f:…` from the object
store of `/home/scaraven/Documents/leanEthereum/leanVM`, whose working tree is past the pin; then
the blueprint's spine (`What the spine fixes` and its Lean sketch), the conventions table, the
holes table, Layers 5 to 7, decisions 3, 17, 18, 21, 30, 31, acceptance tests 2, 3, 5, 6, 17, 18,
28 and the Interfaces list; then the Lean. Every changed file was read in full from the branch
with `git show`, with the consumers' and producers' sides: `Spine/Instance.lean`,
`Spine/Seams.lean`, `Spine/Errors.lean` (the bus slot), `ToArkLib/GrandProduct.lean` (the
relations and `gkr`), the header and `gkrSecurity` of `ToArkLib/GrandProductSecurity.lean`,
`ToArkLib/SendChecked.lean`'s refutation, `Stack.lean`'s `stack_eval_ambient_one`, and the
grand-product tests. `audit-lean.sh`, `check-layers.sh`, `check-imports.sh` and `check-docs.py`
pass (run on the worktree, whose `Bus.lean`, `Stacking.lean` and bus test are identical to the
branch's). Two Lean processes were run, one at a time under the shared `flock`, peak 3.1 GB: the
branch's `tests/LeanerVMTests/Protocol/Bus.lean` (36 s, every `#guard` and `example` passes, no
warning) and a probe (below, 60 s) printing the axioms and checking the two implications the
security half needs. Nothing in the repository was edited.

Target classification: no pull request exists yet and the commit message does not classify the
work. When it opens, the description should say: artifact, the bus phase of the oracle protocol
(the verifier's schedule, its one check and its output `BusOut`), the stacking identity at a point
(specification §5.4, equation (2)) and the bus phase's perfect completeness from `Seam.commit` to
`Seam.bus`; the completeness direction only, knowledge soundness to follow; Category A for the
relations and the verifier, written from §5.2–§5.4, with the leaf layout, its tie order, the count
blocks and the message order Category B, transcribed from `leaf.rs` and `gkr.rs` at the pin;
contribution to T4 through `piop_perfectCompleteness` (the `bus` field of `Phases.Complete`).

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological, the phase is at the slot's type and schedule, and it
is faithful to the deployed verifier: the blocks per side, their order and tie order, the count
blocks with their `α = 0`, `β = 0` leaves, the pad `1`, the trees' common depth, the one root
shared by push and pull, the check `R_c ≠ 0`, the boundary values' order, the totals and the forms'
coefficients all match `leaf.rs` at `a386121f` (Pass B's table). `leaf_decomposition` is equation
(2) of §5.4 against a leaf extension `Source.leafEval` defined independently, as the verifier
writes it, and `sum_forms_eq_total_iff` says what its name says. The intermediate relations are the
right ones for the security half at `busError I`: the probe proves that the roots' check with
`Gkr.relIn` gives `afterChallenge`, and that `Seam.bus` of the output, whatever values were sent,
gives `Gkr.relOut`; with `card_sideProduct_collision_le` at `N = 2 ^ μ_bus` (push by `μBus`'s
definition, pull by `Conditions.pull_fits`) the step from `Seam.commit` to `afterChallenge` costs
`4·2^{μ_bus}/|E|` and nothing else, since the other four conjuncts of `afterChallenge` do not
depend on `(α, β)`. The two added side conditions are necessary, not convenience (Pass A). The
carrier of the public lines and the Flock predicate through the grand-product argument, a rider on
no variable, is sound and honest about what it does, but it is a use of riders the generic module
does not state, and no test exercises it (finding 2). Every finding is Low: the one check of the
verifier is pinned by no test (finding 1), and the rest is audit surface, documentation and test
coverage against Layer 6's list.

## Findings, most severe first

### Low

**1. No test pins the check `R_c ≠ 0`, and its refutation is not recorded as owed.** *Load-bearing
checks; acceptance test 3; test quality.* `Bus.rootsStep` (`Bus.lean:752-757`) checks
`decide (r.2 ≠ 0)`. The test section titled "The zero-count mutation"
(`tests/…/Protocol/Bus.lean:207-223`) evaluates `rootsHonest` and applies its own
`decide (_ ≠ 0)` (`:223`, likewise `:171`); it never reaches the step's check. A mutation of
`rootsStep` to `fun _ _ ↦ true`, or to a check of `r.1`, passes every test, and `busComplete`
still holds (a weaker verifier keeps perfect completeness). The convention requires each check
of a phase to come with a refutation of the verifier without it, listed in the phase's pull
request, and acceptance test 3 names its witness ("the bus phase without the check has no
knowledge soundness (the zero-count mutation)"); the status page's Layer 6 entry neither
supplies it nor says the security half owes it, so the section title reads as if test 3 were
met. The cheap witness exists now, at the step's own relations: with the check removed,
`zeroCount` is outside `afterChallenge` (its counts fail) while the honest roots carry it into
`Gkr.relIn` (the products are the roots, and the riders are zero since the constraint, the lines
and the absent Flock region hold), so `Component.sendChecked_no_stateFunction`
(`ToArkLib/SendChecked.lean:192`) refutes any knowledge state function. Fix: add that refutation
to the bus tests (the step with `fun _ _ ↦ true` in place of the check, on `busToy` and
`zeroCount`), retitle the section to say what it shows, and record in the status page that the
phase-level refutation, at the seams `Seam.commit` and `Seam.bus`, is owed by `busSecurity`'s pull
request.

**2. The public lines and the Flock predicate ride as a rider on no variable, which the
grand-product module does not document and no test exercises.** *Design choice 1; the *Generic
code* convention.* `Bus.linesRider` (`Bus.lean:536-539`) is the one-cell table
`#v[if I.PublicLinesHold input q ∧ I.aux q then 0 else 1]`, appended to the constraint riders
(`:549-552`), so that `Gkr.relIn` and `Gkr.relOut`, which mention only leaves and riders, carry the
two conjuncts of `Seam.commit` the bus does not touch through to `Seam.bus`.

It is sound: `gkrSecurity` is proved for every rider list, a rider's variable count is a
`Fin (μ + 1)` so `0` is admitted, and a rider on no variable restricted to the coordinates drawn so
far is its one value, which no challenge moves: it never escapes and adds nothing to `gkrError`
(the knowledge state is false throughout when a line fails, and `Seam.bus` is false at the end).
It is honest about what it does: the module docstring (`:54-59`) and the status page say it, and
`ridersZero_iff` and `riders_vanish_iff` state the reading exactly. Three weaknesses: (a) it is a
use of riders outside the purpose `ToArkLib/GrandProduct.lean:50-53` states ("They are for a
protocol that reuses `ζ` as a zerocheck point"), so a reader of the generic module does not learn
that a rider on no variable is a side condition carried unchanged, and a later edit of the
generic riders (say, to require `τ ≥ 1`, or to batch riders by a challenge) would break the bus
phase's soundness argument without touching its file; (b) no executable test exercises it, since
`busToy` has no public line and no Flock region (`nLines := 0`, `flock := none`), so its rider is
`0` on every stack, and the spine's toy, which has a line, appears only to type `busComplete`;
(c) it does not generalise: the table sumcheck must also carry the lines and the Flock predicate
from `Seam.bus` to `Seam.table`, and a sumcheck has no riders, so Layer 7 will need another
carrier. The cleaner carrier is a generic frame for front components (a predicate of the part of
the statement the component keeps and of the oracles it hands on, conjoined to both relations of
a `Complete` and a `Security`), which both phases would use; it needs a lemma that `gkr`'s output
keeps its input's data, which the riders' trick avoids. Fix, at least: one sentence in
`GrandProduct.lean`'s riders paragraph, in generic words ("a rider on no variable is a condition
on the data and the oracles, carried unchanged to the output relation"), with a grand-product test
that a nonzero rider on no variable fails `relOut` at every point; a bus test on the spine's toy
with a stack failing its public line, `¬ Gkr.RidersZero`; and a status line saying that the frame
would replace the rider when Layer 7 needs it.

**3. Audit surface: one dead theorem, one dead case, proof-only lemmas public.** *Audit
surface; the Interfaces list.* `Bus.lean` has about 75 public declarations against the hole's
six names. (a) `Bus.cast_lowPoint` (`:809-812`) has no use anywhere on the branch (`git grep`).
(b) `Source.tuple`'s count case (`:116`, "the count cell followed by zeros") is read by nothing:
`Source.leaf` gives a count block its cell directly (`:122`), and `sideTuples` ranges over push
and pull blocks only; the docstring presents it as part of the model. (c) Lemmas used only inside
other proofs: `κ_le_of_mem` (`:256`), `leafCount_push` (`:230`), `sideTuples_eq` (`:448`),
`Source.evalMle_leaf` (`:422`), `lowAt_eq` (`:789`), `src_mem` (`:972`). Those referenced from an
exposed definition (`Conditions.fits`, `Conditions.τmax_le`,
`Conditions.κ_le_of_boundaryColumn`, `sorted_antitone`, `honestValues_getElem` in
`valuesComplete`) must stay public, and so must what a security half in another module needs
(`afterChallenge`, `prod_pushLeaves`, `prod_pullLeaves`, `prod_countLeaves_ne_zero_iff`,
`ridersZero_iff`, `riders_vanish_iff`, `sum_forms_eq_total_iff`, `lowPoint_point`, and the
lemmas that bound the sides' tuple counts). Fix: delete `cast_lowPoint`; make the six
proof-only lemmas private; give `Source.tuple` the docstring "the tuple of a push or pull block"
and either drop the count case behind a separate function on the two tuple sources or say it is
unused; record in the status page the public names the security half consumes, since the
blueprint's Interfaces list names only `busPhase` and `leaf_decomposition`.

**4. The status page and the stacking module's docstring are short of the new work.**
*Documentation.* `docs/roadmap/protocol-status.md`: (a) `:32`, the placeholder `PRB` for the
pull request number; (b) `:36-39`, the `#print axioms` sentence does not list the bus phase's
results (verified here, kernel axioms only: `busComplete`, `leaf_decomposition`,
`Bus.sum_forms_eq_total_iff`, `Bus.prod_countLeaves_ne_zero_iff`, `Bus.ridersZero_iff`,
`Blocks.prod_stackAt`); (c) `:254-255`, "needs this pull request and #78" refers to itself in a
durable page; (d) the fit of the pull and count sides is now stated twice, by the spine
revision's bullet (`:100-102`) and by the new sub-bullet (`:227-229`): one home; (e) nothing says
the blueprint is owed a `docs(protocol)` edit for Layer 6 (the signature `busPhase I h` with
`Bus.Conditions`, `Phase.FrontDef`, `countLeaves I q` without challenges, `leaf_decomposition`
per side with `h` and `k`) and for the Interfaces list (`Bus.Conditions`, `Blocks.prod_stackAt`,
`Blocks.total_eq_sum`), as the fingerprint's entry says for its own hole; (f) nothing says the
adaptor owes `Bus.Conditions` of `leanIsaInstance` at admissible sizes, which `leanVmPhases`
needs: the deployed verifier asserts the fits (`leaf.rs:130-134`, a panic on a public layout) and
rejects a point shorter than `τ_max` (`constraints.rs:251-253`, `Error::Truncated`), so the
compiled verifier's admissibility check must imply them. `ToCompPoly/Stacking.lean:23-30`: the
module docstring's list of contents does not mention the product of a stack's cells
(`prod_stackAt`, `total_eq_sum`). Fix: fill (a) when the pull request opens; add the six names
to (b); reword (c) as "needs the bus phase's definition (#…) and #78"; fold (d) into one bullet;
add (e) and (f) to the Layer 6 entry; add one bullet to the stacking module's list.

**5. Layer 6's test list is met only in part, and the status page does not say so.** *The
*Holes* convention; Layer 6's tests.* The blueprint asks for "the whole phase on the toy
instance's honest stack" and "the message and challenge counts of test 17"; the convention asks
that a `Def` land "with its `Complete` and an honest run on the toy instance". The bus tests run
the phase by pieces on `busToy`: the roots (`:163-171`), the leaves at a point (`:175-178`) and
the last step with each leaf claim set to the true extension (`:182-205`), skipping the
grand-product argument on the bus's own leaf stacks; the spine's toy only types `busComplete`
(`:237-251`), and no guard counts the phase's rounds or challenges at `busToy` (the spine's tests
do it for the spine's toy, `tests/…/Spine.lean:128-129`). Perfect completeness is proved, so this
is evidence that the definitions run, not of correctness. Fix: guards on `busRounds busToy` and
`Fintype.card (busSpec busToy).ChallengeIdx`, and either a by-hand run of `gkr 3 2` on
`busToy`'s three leaf stacks in the style of `tests/…/GrandProduct.lean` (combined claim,
descendants' check, combination challenges, the claims at `ζ` the last step consumes) or a status
line saying the honest run is by parts and why.

**6. Citation ranges and one ambiguous sentence in the module docstring.** *Fidelity citations.*
`Bus.lean:22`: `05-arithmetization.tex:16-119` starts at §5.1's domain separators (line 16;
§5.2 starts at 18) and stops before §5.4's end (123: "There is one such equation per side…").
`:74`: the decomposition `leaf.rs:389-454` stops before the pad's mass, `Ok(acc + (F192::ONE +
sel_sum))` at `:459-460`, which is the term `Bus.total` subtracts. `:29-31`: "ties in the order of
`sources` (boundary blocks first, then each table's flushes, then the count columns)" reads as one
list, while the count columns are a side of their own. Fix: cite `:18-123` and `:384-461`, and say
"per push or pull side, its boundary blocks then each table's flushes; on the count side, each
table's count columns".

### Observations

- **The two added side conditions are necessary.** `pull_fits` cannot be dropped: `stackAt`
  truncates, so on an instance whose pull side has more than `2 ^ μ_bus` leaves the verifier would
  compare the push product with the product of a prefix of the pull leaves, and a stack whose push
  multiset is that prefix passes with certainty while `Balanced` (a permutation of lists of
  different lengths) is false. `count_fits` likewise: a truncated count stack drops counts, and a
  zero count past the cut passes. `pull_fits` is weaker than the deployed assertion
  `push.mu == pull.mu` (`leaf.rs:130-133`), so it admits more instances; `count_fits` is exactly
  `count.mu ≤ push.mu` (`:134`). On any instance whose relation is inhabited, `pull_fits` follows
  from `Balanced`; as a hypothesis on the instance it is still the right form.
- **Sign conventions.** The Lean writes the leaf `β − π_α(t)` and the forms' terms `−w·eq(α, i)`,
  correct in any characteristic, where the Rust adds (`leaf.rs:246`, `:420`); the pad's weight
  `1 + Σ_b eq(sel_b, ζ_{≥κ_b})` is the characteristic-two form, as in §5.4 and
  `stack_eval_ambient_one`. In `E` they agree.
- **Forms as lists.** A flush block contributes seventeen terms, one per coordinate whether its
  polynomial is `0` or not, and the same column appears in several terms; the Rust's `BusForm` is
  a dense form per table, zero coordinates absent and products merged (`leaf.rs:304-328`). The
  values agree at every point, so the table sumcheck's check is the same number; the compiled
  verifier evaluates more terms, which Layer 12 may want to normalise. No transcript effect.
- **A name collision from the spine.** `I.pushLeaves` is `M3Instance.pushLeaves`, the number of
  push leaves (`Spine/Instance.lean:261`), and `pushLeaves I α β q` is this module's leaf stack,
  the blueprint's name; `leafCount_push` equates the count with the first. A later spine touch
  could rename the count `pushLeafCount`.
- **Silent filter.** `constraintRiders` drops the constraints of a table taller than `μ_bus`
  (`:532-534`, `else []`); harmless, since `Conditions.constrained` excludes such a table and
  `ridersZero_iff` takes the conditions.
- **The challenges reach the count side.** `Bus.leaves` passes the real `(α, β)` to the count
  side, `countLeaves` passes `0, 0`, and `Source.leaf` ignores both for a count block: the same
  table. The deployed count tree is at `α = 0`, `β = 0` (`leaf.rs:606-622`, `:674`, `:698`), whose
  leaf `0 + 1·c` is the count; the Lean's leaf is the count directly.
- **Bytecode claim.** `BusVerify.bytecode_claims` (`leaf.rs:927`), the stacked bytecode
  polynomial at `(ζ_{<κ_bc}, α)`, is not modelled; the native verifier computes it and checks
  nothing with it, and the blueprint's *Boundaries* assigns it to recursion (`settleFixedClaims`).
  The `known` coordinates evaluate each public column at `ζ_{<κ}`, which is what
  `decompose_verify` does (`leaf.rs:453`).

## Pass A: the statements

Read against §5.2–§5.4 and the spine's seams before the proofs.

- **`Bus.Source`, `Bus.sources`, `Bus.sorted`, `Bus.blocks`, `Bus.sideLeaves`** (`:93-174`): a
  side's blocks, stacked by a stable merge sort on `κ` descending, padded with `1` on `μ_bus`.
  `sorted_antitone` makes the layout aligned by `Blocks.descending`, so a smallest-first sort
  does not compile.
- **`Bus.Conditions`** (`:178-186`): `1 ≤ I.d` and "a table with a constraint has
  `τ_j ≤ μ_bus`" are the blueprint's two hypotheses (decision 30); `pull_fits` and `count_fits`
  are new, necessary (Observations), recorded in the status page, and anticipated by the spine's
  `μBus` docstring ("the bus phase assumes it of the instance"). `τ_max ≤ μ_bus` is derived
  (`Conditions.τmax_le`), with every boundary column's `κ ≤ μ_bus`. Inhabited on `busToy` and on
  the spine's toy (`tests/…:125-129`, `:243-247`).
- **`leaf_decomposition`** (`:772-780`): for every side `k`, `Ṽ_k(ζ)` is
  `Σ_b eq(sel_b, ζ_{≥κ_b})·leafEval_b(ζ_{<κ_b}) + (1 + Σ_b eq(sel_b, ζ_{≥κ_b}))`, with
  `leafEval` (`:334-342`) defined as the verifier writes it: `β − Σ_i eq(α, i)·c̃_i` where `c̃_i`
  is a boundary coordinate's extension (a constant, a known column's, a committed column's read
  off the stack) or the extension of a flush polynomial's values on the rows (the virtual table,
  not the polynomial of the columns' extensions, which differ at degree 2), and the column's
  extension for a count block. This is §5.4's equation (2) per side. Substitution test: with
  `leafEval` replaced by `evalMle (Vector.ofFn leaf)` it would be the stacking identity alone; as
  stated it adds the extension's linearity, which `Source.evalMle_leaf` proves case by case, so it
  pins the verifier's formula. The kernel guard (`tests/…:175-178`) checks it on all three sides
  at a point off the cube.
- **`prod_pushLeaves`, `prod_pullLeaves`, `prod_countLeaves_ne_zero_iff`** (`:495-522`): the
  products of the push and pull stacks are `sideProduct α β` of the instance's tuple lists (the
  pad is `1`, `Blocks.prod_stackAt`; the blocks are the tuples in another order,
  `sideTuples_perm`), and the count product is nonzero exactly when `CountsNonzero`. These are
  Theorem 5.1's inputs and §6.2's "all counts are nonzero exactly when their product is".
- **`ridersZero_iff`, `riders_vanish_iff`** (`:588-629`): the riders are zero exactly when
  `ConstraintsVanish ∧ PublicLinesHold ∧ aux`, and their extensions vanish at `ζ_{<τ}` exactly when
  every constraint of a table that fits does and the lines and Flock predicate hold. Under the
  conditions, no constraint is lost to `constraintRiders`' filter.
- **`Bus.busOut`, `Bus.total`, `Bus.forms`** (`:701-729`): the verifier's last step. `total` is
  `v_s − (Σ_b w_b·boundaryValue_b + (1 + Σ_b w_b))`, `rem_s` of §5.4; `forms` per sumcheck table
  is the flushes' terms `(w·β, 1)`, `(−w·eq(α, i), P_i)` and the count columns' `(w, X_c)`, §5.4's
  `B^s_j` with §6.2's count side. Row polynomials within `I.d` by type (test 28): `1` of degree
  0, the flush polynomials by `flushes_degree`, `X_c` by `one_le_d`.
- **`sum_forms_eq_total_iff`** (`:978-997`): with the boundary values the true extensions,
  `Σ_j Form.eval (forms k j) = total k ↔ Ṽ_k(ζ) = v`. Both directions, no other hypothesis; the
  name says what it states. The guard at `tests/…:198-202` shows a wrong leaf claim breaks the
  equation.
- **`afterChallenge`** (`:1005-1009`): the products agree at `(α, β)`, the counts are nonzero, the
  constraints vanish, the lines and the Flock predicate hold; the blueprint's state after
  `(α, β)` word for word, asking the products to agree, not the multisets.
- **`busPhase`, `busComplete`** (`:1070-1083`): a `Phase.FrontDef` at `busSpec I` (the type
  `Phases.bus` has) and a `Phase.Complete` from `Seam.commit` to `Seam.bus` (the type
  `Phases.Complete.bus` has), composed from the four parts' completeness. The input relation is
  inhabited (`#guard M3Holds busToy () honest`), and `Seam.bus` is not trivial (its column
  claims and form equations are evaluated at `tests/…:192-196`).
- **The relations for the security half** (design choice 2). Checked by the probe: (a) for a
  message `(R, R_c)` with `R_c ≠ 0`, `Gkr.relIn` of `(x, ![R, R, R_c])` gives `afterChallenge` of
  `x` (the shared root makes the products agree; the count root is the count product; the riders
  give the rest); (b) for every boundary message `vals`, `Seam.bus` of `busOut h ℓ vals` gives
  `Gkr.relOut` of `ℓ` (the column claims make `vals` the true values, then
  `sum_forms_eq_total_iff` gives each leaf claim, and the zerocheck conjunct with the lines and
  the Flock predicate gives the riders through `lowPoint_point`). With (a), the roots' message is
  sound at error 0; with (b), the values' message is; the grand-product argument is
  `gkrSecurity 3 μ_bus` at `gkrError E (1/Nat.card E)`, the slot's `gkrError E (overE 1)` by
  `overE_one`; and the challenge `(α, β)` takes `Seam.commit` to `afterChallenge` only on a
  collision of the two products when `Balanced` alone fails (any other failing conjunct is
  independent of the challenge), counted by `card_sideProduct_collision_le` at
  `N = 2 ^ μ_bus`. That is `busError I` exactly: `4·2^{μ_bus}/|E|` on `(α, β)`, `gkrError` on the
  grand product's challenges, nothing else.
- **`Blocks.prod_stackAt`, `Blocks.total_eq_sum`** (`ToCompPoly/Stacking.lean:89-92`,
  `:393-410`): the product of a stack's `2 ^ μ` cells is the product of the blocks' cells times
  `pad ^ (2 ^ μ − total)`, under the fit; the total is the sum of the heights. General, any ring,
  any pad; no protocol vocabulary; in `ToCompPoly/` by its objects. Its helper is private.
- **Coverage.** §5.2's product check, §5.3's three batched trees, §5.4's layout, decomposition,
  boundary values and remainders, §6.2's count product: all present. The completeness direction
  only; knowledge soundness is the next hole, as the status page says.

## Pass B: fidelity

Category A for the verdict and relations (written from the specification, as the module says);
Category B for the leaf layout, the count tree and the message order, read in the Rust before the
Lean. Pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`.

| Item | Specification | Rust | Lean |
| --- | --- | --- | --- |
| blocks per side | one per flush rule and one per boundary set (§5.4) | push: state, memory seed, bytecode seed, then per table its `fb.push`; pull the same with the final state and finalizations (`cpu/layout.rs:353-411`) | `sideSources`: `I.boundary` of that side in order, then per table its flushes of that side in order |
| count blocks | every count column (§6.2, line 78) | per table its `count_columns`, one `Col` each; finalize counts not in it (`cpu/layout.rs:412-414`) | `countSources`: per table `I.counts j` |
| layout | largest first, aligned (§5.4) | `stack_offsets`: `κ` descending, ties by input index (`witness.rs:67-79`) | stable `mergeSort` on `κ` descending (`:146-147`); tie guarded (`tests/…:140-141`) |
| depth | every tree padded to the deepest (§5.3) | push's `log2_ceil(max(placed, 1))`, no floor (`leaf.rs:149-156`); count tree at push's `μ` (`:679`, `:881`); `push.mu == pull.mu`, `count.mu ≤ push.mu` asserted (`:130-134`) | `μBus = clog 2 pushLeaves`; pull and count fit by `Conditions` |
| leaf | `β − Σ_i eq(α, i)·c_i(z)` | `β + Σ_i w_i·c_i(z)`, `w = eq(α⃗, ·)` (`leaf.rs:227-246`) | `β − fingerprint α t` |
| count leaf | the count | `α⃗ = 0`, `β = 0`: `1·c_0` (`leaf.rs:606-622`) | the count cell |
| pad | `1` (§5.3, §5.4) | `F192::ONE`, implicit past the blocks (`leaf.rs:223`) | `stackAt … 1` |
| roots | one product per side; the count product sent (§6.2) | `FirstTwoShared`: the shared root, then the count root (`gkr.rs:364-367`) | `say (E × E)`, statement `![R, R, R_c]` |
| check | the count product is nonzero | `count_root == 0` → `ZeroCount` (`leaf.rs:884-889`) | `decide (r.2 ≠ 0)` |
| boundary values | each committed multilinear at `ζ_{<κ_b}` (§5.4) | sides `[push, pull, count]`, blocks in input order, coordinates in order, deduplicated by `(col, point)` (`leaf.rs:403-457`, `:466-471`) | `I.boundaryColumns` (push then pull, first occurrence); point `ζ_{<κ}` |
| totals | `rem_s`: `Ṽ_s(ζ)` less the boundary contributions and the pad term | `framework + values[s]`, the framework including `1 + Σ_b sel_b` (`leaf.rs:459-460`, `:924`) | `v − (Σ_b w_b·boundaryValue_b + (1 + Σ_b w_b))` |
| forms | `B^s_j = Σ_b eq(sel_b, ζ_{≥τ_j})(β − Σ_i eq(α, i)·c_{b,i})` | `constant += eq_hi·β`, `coeffs += eq_hi·w_i` per coordinate term (`leaf.rs:416-422`, `:367-382`) | `(w·β, 1)` and `(−w·eq(α, i), P_i)`; count: `(w, X_c)` |
| zerocheck point | `ζ_{<τ_j}` (§5.5) | `zeta[..τ]`; a point shorter than `τ_max` rejected (`constraints.rs:250-253`) | `point = ζ_{<τ_max}`; `Conditions.constrained` |

Counts. Checks of `verify_balance`: one of its own (the count root) and the grand product's layer
checks, delegated; the Lean, one (`rootsStep`) and `gkr`'s. Messages: two roots, then one value
per distinct committed boundary column (five for leanISA: `mem_0, mem_1, mem_2, cntfin_mem` at
`ζ_{<κ_mem}`, then `cntfin_bc`, given the instance's boundary order); the Lean, `say (E × E)` and
`say (Vector E I.busClaims)`. Challenges before the grand product: five squeezes against one
joint draw, the spine's choice. Outputs: `BusVerify`'s point, forms, totals and claims are
`BusOut`'s (decision 21; the point cut to `τ_max`), its `count_root` is only checked, its
`bytecode_claims` is not modelled (Observations). No block, leaf, coefficient or check is present
on one side and absent on the other. Deviations: the pull side's fit as `≤` where the Rust asserts
`=`, and the short-point rejection as a hypothesis; both admit more instances and are recorded
(finding 4f asks for the adaptor's obligation).

## Pass C: hygiene and policy

- **Comments.** Docstrings are one or two lines, self-contained, and cite no roadmap, layer,
  hole or acceptance test (`grep` over both files); the module docstring carries the design, the
  citations, the pin and the authoring note (Category A, Rust-informed for the layout). No line
  over 100 columns.
- **Surface.** Finding 3. Names: `Bus.point`, `Bus.total`, `Bus.weight`, `Bus.src`, `Bus.Data` are
  short and generic inside `Bus`; `Bus.total` sits beside `Blocks.total`, distinguished by dot
  notation. Harmless.
- **To-folder rule.** `Blocks.prod_stackAt` and `Blocks.total_eq_sum` are generic (any
  commutative ring, any pad), worded generically, private helper; right folder by their objects.
  The module's list of contents is behind (finding 4).
- **Aggregates.** `LeanerVM.Protocol.Bus` and `LeanerVMTests.Protocol.Bus` appear once each, in
  order. The test file is a plain file, so its `#guard`s run compiled code.
- **Tests: what they catch.** Caught by a guard: the tie order reversed (`:140-141`); a `0` pad
  (the count side, two leaves on four, `:165`); a count column dropped (`:117`, `:143`); a wrong
  boundary column or point (`:195-196`); a flush form missing its `β` term (`:192-193`, `:205`); a
  wrong leaf claim (`:198-202`). Caught by the proofs: a smallest-first sort (`Blocks.descending`),
  a rider dropped or the lines' rider made constant (`valuesComplete` needs both), the roots'
  vector reordered, a count leaf depending on `β`, a wrong value order (`coordValue_eq`).
  Surviving: the check `R_c ≠ 0` removed or weakened (finding 1); anything in `Source.tuple`'s
  count case (finding 3); since `busToy` has one boundary column, the order of several values is
  pinned only by the proof. The "pad" guard (`:228-229`) builds its own `0`-padded stack and
  documents the reading rather than testing the definition.
- **Status page.** The deviations listed match the code; what is missing is finding 4.

## Probe

Run with `flock /tmp/claude-1000/leanerVM-lean.lock lake env lean`, from the worktree, whose
`Bus.lean` and `Stacking.lean` are the branch's.

```lean
import LeanerVM.Protocol.Bus
open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Bus CompPoly CMlPolynomialEval

#print axioms LeanerVM.Protocol.busComplete                       -- each: [propext,
#print axioms LeanerVM.Protocol.leaf_decomposition                --   Classical.choice,
#print axioms LeanerVM.Protocol.Bus.sum_forms_eq_total_iff        --   Quot.sound]
#print axioms LeanerVM.Protocol.Bus.prod_countLeaves_ne_zero_iff
#print axioms LeanerVM.Protocol.Bus.ridersZero_iff
#print axioms LeanerVM.Protocol.Blocks.prod_stackAt

-- The roots' check and the grand product's input relation give `afterChallenge`.
example {I : M3Instance} (h : Conditions I) (x : Data I) (o : ∀ i, TheOracle I i) (r : E × E)
    (hr : r.2 ≠ 0)
    (hin : ((((x, ![r.1, r.1, r.2]) : Data I × (Fin 3 → E)), o), ()) ∈
      Gkr.relIn 3 I.μBus (leaves I) (riders I)) :
    (((x, o), ()) : (Data I × ∀ i, TheOracle I i) × Unit) ∈ afterChallenge I := by
  obtain ⟨hz, hroots⟩ := hin
  obtain ⟨hc, hl, ha⟩ := (ridersZero_iff h x o).mp hz
  have h0 := hroots 0
  have h1 := hroots 1
  have h2 := hroots 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  refine ⟨?_, ?_, hc, hl, ha⟩
  · show (∏ i : Fin (2 ^ I.μBus), (leaves I x o 0)[i]) = ∏ i : Fin (2 ^ I.μBus), (leaves I x o 1)[i]
    rw [← h0, ← h1]
  · exact (prod_countLeaves_ne_zero_iff h x.2.1 x.2.2 (theStack o)).mp (h2 ▸ hr)

-- `Seam.bus` of the output gives the grand product's output relation, whatever values were sent.
example {I : M3Instance} (h : Conditions I) (ℓ : Gkr.LayerStmt (Data I) E 3 I.μBus)
    (o : ∀ i, TheOracle I i) (vals : Vector E I.busClaims)
    (hout : (((ℓ.1.1, busOut h ℓ vals), o), ()) ∈ Seam.bus I) :
    ((ℓ, o), ()) ∈ Gkr.relOut 3 I.μBus (leaves I) (riders I) := by
  obtain ⟨hz, hforms, hcols, hl, ha⟩ := hout
  have hvals : ∀ i : Fin I.busClaims, vals[i] =
      eval₂Mle (I.column (theStack o) I.boundaryColumns[i]).values (algebraMap K E)
        (columnPoint h ℓ.2.1 i) := by
    intro i
    refine (hcols ⟨I.boundaryColumns[i], columnPoint h ℓ.2.1 i, vals[i]⟩ ?_).symm
    show _ ∈ (Vector.ofFn _).toList
    rw [Vector.toList_ofFn]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  refine ⟨fun k ↦ (sum_forms_eq_total_iff h k _ _ _ _ _ _ hvals).mp (hforms k), ?_⟩
  refine (riders_vanish_iff ℓ.1 o ℓ.2.1).mpr ⟨fun j hj C hC ↦ ?_, hl, ha⟩
  have hst : I.SumcheckTable j := Or.inl (List.ne_nil_of_mem hC)
  have := hz ⟨j, hst⟩ C hC
  rw [show (busOut h ℓ vals).point = point h ℓ.2.1 from rfl, lowPoint_point] at this
  exact this
```

Both examples compile; every printed result has the kernel's three axioms and no `sorryAx`.
