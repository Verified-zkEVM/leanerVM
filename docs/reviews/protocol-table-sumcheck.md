# Review: the table sumcheck phase, definition and completeness

> An archive of the review of one commit, `d08eac2` of the branch `feat/protocol-table-sumcheck`,
> against its base `7ed6942` (`feat/protocol-batch`, batching by powers, pull request #77): names,
> paths and line numbers are that commit's. No pull request was open for the branch at the time
> of the review. What is accepted from it is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of the
> pull request that met it.

**Disposition**:

| Finding | Disposition | Commit |
| --- | --- | --- |
| 1. the honest run is on the two-table instance, not on the toy | met: a one-round run on the toy, a form on each side | `a257206` |
| 2. `lowPoint` is the generic `lowCoords`, defined twice | met in part: the proof reads it through `getElem_lowCoords`; redefining the spine's `lowPoint` would break the bus phase's open branch (#79), whose proofs unfold it by name, so the status records it as owed after that merge | `a257206` |
| 3. the test's guards recompute the honest run | met: each run computed once, in one guard (5.5 min to 1.3 min) | `a257206` |
| 4. hygiene | met: no acceptance-test numbers, `constraints.rs:271-273`, a private import, `finalClaims_holds_iff` on the context, the review listed | `a257206` |
| the observation on the security half and `I.d ≤ 2` | met in the stacked pull request of the knowledge soundness | — |
| the observation on the refutation of the final check at the table seam | met in the same, from `Component.sendChecked_no_stateFunction` | — |

Reviewed with the `adversarial-review` skill in three passes: the statements against the
blueprint's Layer 7, the conventions *Table sumcheck*, *Sumcheck variants*, *Load-bearing checks*,
*Generic code*, *Holes*, *Seams* and *Claim pool order*, the holes table's Layer 7 rows and
acceptance tests 7, 9, 16, 28 and 30, read before the proofs; the expectation for the phase formed
from the specification at the pin (`doc/leanvm/body/05-arithmetization.tex` §5.5, lines 125-155;
`03-proving-primitives.tex`, Fact 3, Definition 2 and "Two savings on a round message") before the
Rust (`crates/lean_vm/src/cpu/mod.rs:361-441, 656-667, 711-779`,
`crates/lean_vm/src/constraints.rs:1-60, 74-82, 243-291`, with `python-verifier/verifier.py:600-620,
1386-1394` as the cross-check), all read in the pinned checkout at `a386121f`; and hygiene. Every
changed file was read in full, with the base's `ToArkLib/Sumcheck.lean`, `ToArkLib/Batch.lean`,
`ToCompPoly/PowerBatching.lean`, `Spine/Instance.lean`, `Spine/Seams.lean`, `Spine/Errors.lean`,
`Spine/Phase.lean`, `ToArkLib/Component.lean` (`Complete`, `Front`, `Security.mono`) and
`Spine/Toy.lean`. Lean was run serially: `lake build LeanerVM.Protocol.Spine.Toy` (the one module
the worktree had not built, 5 s); `lake env lean` on a scratch file printing the kernel axioms of
the fifteen public results and the toy's sizes; `lake env lean -Dprofiler=true` on the test file
(every `#guard` passes; the timings are under finding 3); and `lake env lean` on a scratch file
with the probes reported below, among them the security half of the phase built to the slot's
error. The repository scripts `audit-lean.sh`, `check-imports.sh`, `check-layers.sh` and
`check-docs.py` pass. Nothing was edited but this file; the uncommitted edit of the test file that
the worktree held at the end of the review is the author's session's, made during the review
(finding 3), and the review reads the commit.

Target classification: the commit message names the hole and its direction ("definition and
completeness"); the pull request, once open, is to say that the work feeds T4 through the table
sumcheck phase (Layer 7) in the completeness direction, that its knowledge soundness is the next
hole, that the phase is Category A (the Lean is the standard, written from §5.5) with the order of
the powers, the shared side powers, the weights and the order of the values and of the output
claims checked against the Rust, and that completeness and the coming knowledge soundness both
take `I.d ≤ 2` (the observation below).

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological, and the phase is §5.5's. The summand is `F` with
the point read by the formula: table `t` weighs its rows by `eq(ζ_{<τ_t}, ·)` below its log-height
and by the padding `X_k` above it (`tableWeights`, `TableSumcheck.lean:159-160`; `prodWeight`
makes `(1 − z)(1 − ζ) + zζ` of a low coordinate and `z` of a high one, and in characteristic two
the first is the deployed `1 + ζ + z`, probed), and owes its constraints at `ξ` to their position,
numbered table by table (`constraintPos`, `position_val`), and the three sides' forms at the
shared `ξ^{B+s}` (`rowValue`, `:152-155`). The sum over the cube is the true values batched
(`sum_tableSummand`), the true values are the claimed ones exactly under the bus seam's two
claims (`trueValues_eq_claimed_iff`), so under the seam the sum is the derived target
(`tableSummand_target`), which the batch step never sends (`claimed`, `batchStep`). The summand
has degree three in each variable when `I.d ≤ 2` (`tableSummand_degree`), the hypothesis the
cubic slot needs and the leanISA instance meets (`d = 2`). The output carries the bus claims
forward and then one claim per column at the final point's low coordinates (`tableOut`,
`finalClaim`), the deployed `chi[..tau]` in the deployed order. Completeness is inhabited on the
toy and on the two-table instance as plain `def`s, and its kernel axioms are the standard three.
The knowledge-soundness half is provable at `tableError I` with these definitions: the probe
built `Phase.Security I (tableSumcheck I).toDef (Seam.bus I) (Seam.table I) (tableError I)` in
twenty-five lines from the three generic halves. The variable order and the shared powers are
pinned by guards that fail under the alternative. What remains is a convention's letter (the
toy's run), one duplicated definition, the test file's cost, and hygiene.

## Findings, most severe first

No finding is above low.

### Low

**1. The honest run is on the two-table instance, not on the toy.** *Convention: Holes.* "A
`Def` lands with its `Complete` and an honest run on the toy instance." The run
(`tests/LeanerVMTests/Protocol/TableSumcheck.lean:191-222`) is on `twoTab`; the toy gets the slot's
inhabitant (`:348-350`) and the completeness `def` (`:353-355`), no run. The toy (probed) has one
table of log-height 1 with a constraint, a flush and a count column: `τ_max = 1`, `B = 1`, three
columns, no bus claims; `twoTab` has two tables of heights 2 and 1 with constraints only and
hand-written forms, which is the shape the Layer 7 test list asks for and the only one that shows
the back-loading. The toy's run would add one thing the two-table run lacks: a table whose count
and flush sides are non-empty, so a form on the pull or count side. Either add the toy's one-round
run (forms hand-written as `busOutOn` does, one on each side), or record in the status, under the
phase's bullet, that the two-table instance stands in for the toy and why. The pull request says
which.

**2. `M3Instance.lowPoint` is the generic `lowCoords`, defined twice.** *Convention: Generic
code.* `Spine/Seams.lean:113-114` and `ToCompPoly/Multilinear.lean:543-544` are the same term
(`Vector.cast (min_eq_left h) (p.take k)`; `I.lowPoint p j = lowCoords (I.τ_le_τmax j) p` is
`rfl`, probed). `weightedCubeSum_table` (`TableSumcheck.lean:314-319`) then unfolds `lowPoint` by
hand (`M3Instance.lowPoint, Vector.getElem_cast, Vector.getElem_take`) where `getElem_lowCoords`
is the lemma. Fix: define `lowPoint p j := lowCoords (I.τ_le_τmax j) p` in `Seams.lean` (no
consumer changes, the term is the same) and rewrite with `getElem_lowCoords`; a one-line commit
on the spine's file, said so in the pull request.

**3. The test's guards recompute the honest run.** *Cost.* The file takes 327 s of
interpretation (profiled at a 1.5 s threshold): thirteen `#guard`s of 14 to 31 s each, every
other command under a second. `#guard` interprets its term and shares nothing between commands,
so every guard that mentions `s2`, `vals`, `b2` or `p1'` re-interprets the whole chain
`q0 → s1 → q1 → s2 → vals` (two interpolations at four nodes of cube sums in `E`). Three guards
pay for the chain and read none of it: `:216` (the final point), `:219` and `:221` (the claims'
points and values), which need the challenges and the columns' extensions only. State them on a
statement whose challenges are written down, `(x, (#v[c0, c1], _))` with
`vals := (tableSummand twoTab).values ctx #v[c1, c0]`, and they cost under a second. Group the
guards that need one chain into one `#guard` with `∧` (`:214, :277, :280, :281` on the honest
chain; `:265, :271` on the repaired one), so each chain runs once. About half the five minutes;
the trade is one failure message per group. *While this review ran, the worktree received an
uncommitted edit of the test file from the author's session (not reviewed: a `Run` structure
computed by `let` inside one `#guard` per chain, two chains in all), which is this grouping; what
is left of the finding is to commit it and to profile once more.*

**4. Hygiene.** *CONTRIBUTING; the comment rule.*
- `tests:20, 29, 32, 34`: the module docstring cites acceptance tests 7, 16, 9 and 30. Comments
  never cite the roadmap (*Generic code*, last sentence); name the property ("the target",
  "the variable order", "the shared bus powers", "the sumcheck's tables") and drop the numbers.
- `tests:19`: `constraints.rs:274-277` for the weights; the loop is `:271-273` (`eq_k` at 271,
  `weights[t] *=` at 273); 274-277 are closing braces and `let mut acc`. `:173-174` paraphrases
  the same lines rightly.
- `IndividualDegree.lean:12`: `public import CompPoly.Multivariate.MvPolyEquiv.Eval` is used by
  proofs only (`eval₂_equiv`, `totalDegree_equiv`); the statement of `cmvPolynomial_eval₂` needs
  `CPoly.CMvPolynomial`, `totalDegree` and `eval₂` of `CompPoly.Multivariate.Basic`. Plain
  `import`, with a public import of `Basic` if it is not already transitive.
- `TableSumcheck.lean:481`: `finalClaims_holds_iff` takes `x : Data I`, which nothing reads (the
  values depend on the oracle alone: equal for any two `x`, by `rfl`, probed); it builds the
  context. Either state it on `table I (theStack o)` or say in the docstring that the data is a
  dummy. The security half will have an `s` to hand, so it is harmless there.
- `docs/README.md:30-66` lists each review; this file is to be listed.

### Observations

- **The security half is provable at the slot's error, and takes `I.d ≤ 2`.** The following
  compiles against the branch (probed, with the two hypotheses proved, not assumed): the batch's
  values fixed before the challenge are `trueValues I s (theStack o)`; a statement off the bus
  seam whose output is in `Sumcheck.relIn … (side I)` meets the side condition, so it fails the
  seam's first two clauses, so `trueValues ≠ claimed` (`trueValues_eq_claimed_iff`), and the
  combined claim is `powerBatch trueValues ρ` (`sum_tableSummand`); the final's hypothesis reads
  the table seam at `tableOut`: the final claims hold, so the values are the tables'
  (`finalClaims_holds_iff`), and the carried claims, the lines and the Flock predicate are the
  side condition. The errors compose to `tableError I` once `(B + 3 − 1) / Nat.card E` is
  `overE (B + 2)` and `3 / Nat.card E` is `overE 3`, by `Nat.card_eq_fintype_card` and `rfl`:

  ```lean
  noncomputable example (I : M3Instance) (hd : I.d ≤ 2) :
      Phase.Security I (tableSumcheck I).toDef (Seam.bus I) (Seam.table I) (tableError I) :=
    have hb := Component.batchSecurity (TheOracle I) E (claimed I) (start I)
        (relIn := Seam.bus I)
        (relOut := Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I))
        (fun s o ↦ ⟨trueValues I s (theStack o), fun w ρ hin hout ↦ by
          cases w
          obtain ⟨h1, h2⟩ := hout
          have h1' : powerBatch (claimed I s) ρ = powerBatch (trueValues I s (theStack o)) ρ := by
            rw [← sum_tableSummand I (s, ρ) o]; exact h1
          refine ⟨fun h ↦ hin ?_, h1'⟩
          have := (trueValues_eq_claimed_iff I s (theStack o)).mp h
          simp only [Seam.bus, Seam.of, Set.mem_ofPred_eq]
          exact ⟨this.1, this.2, h2⟩⟩)
    have hf := Sumcheck.finalSecurity (tableSummand I) Sumcheck.unitWeights nodes (side I)
        (tableOut I) (relOut' := Seam.table I) (fun s o w v hout ↦ by
          cases w
          simp only [Seam.table, Seam.of, Set.mem_ofPred_eq, tableOut, Vector.toList_append,
            List.mem_append] at hout
          refine ⟨(finalClaims_holds_iff I s.1 o _ _).mp fun c hc ↦ hout.1 c (Or.inr hc),
            fun c hc ↦ hout.1 c (Or.inl hc), hout.2⟩)
    tableError_eq I ▸ (hb.append (Sumcheck.roundsSecurity (tableSummand I)
      Sumcheck.unitWeights nodes (side I) (tableSummand_degree I hd) nodes_injective)).append hf
  ```

  The hypothesis `I.d ≤ 2` is load-bearing for the error, not a convenience: `roundsSecurity`
  needs the summand of degree at most three in each variable, and with a summand of higher degree
  a cubic message disagreeing with the true round polynomial could agree with it at more than
  three challenges, so `3 / |E|` per round would be false. The pull request names it beside the
  bus phase's `1 ≤ I.d` (acceptance test 28).
- **The refutation of the final check at the table seam.** The base's
  `final_unchecked_no_stateFunction` is stated at `finalOut` and `relOut V side`
  (`Sumcheck.lean:455-466`), not at an output map; the phase's own refutation, at `tableOut` and
  `Seam.table`, comes from `Component.sendChecked_no_stateFunction` directly, with the security
  half, the round check's refutation being the base's and the batch having no check. The
  convention asks the pull request to list them.
- `tableSummand_target` takes the whole bus seam though only its first two clauses matter;
  `trueValues_eq_claimed_iff` is the sharp form, and the blueprint states the target under the
  seam. No change needed.
- The test's target `T` is nonzero, so `weightedSum = T` is not a cancellation: `ξ = y² + y + 1`
  is nonzero (`ξ = 0` would give `y³ = 1`, against `y³ = y + 1`), and the one non-empty total is
  `y² + 1`. A `#guard T ≠ 0` would pin it.
- `repeatHigh`'s second argument `(_ : k ≤ n)` is unused in the body; it fixes `n`. Harmless.

## Answers to the questions put to the review

- **Vacuity and strength.** `tableSumcheckComplete` is `Component.Complete`: a guarded form and
  perfect completeness from every state of the shared oracle (`Component.lean:129-134`), inhabited
  on the toy (`d = 2`, `τ_max = 1`) and on `twoTab` (heights 2 and 1), both `def`s without
  `noncomputable`; its one hypothesis is needed (above). `sum_tableSummand` names
  `powerBatch (trueValues …) ξ`, an object defined apart from the sumcheck (each constraint's
  extension at `ζ_{<τ_t}`, each side's forms summed at `ζ`), and is pinned on `twoTab` by
  `tests:187-189`; `trueValues_eq_claimed_iff` is an `iff` whose right side is the seam's two
  clauses verbatim; `tableSummand_target` follows from the two and is the blueprint's statement;
  `tableSummand_degree` is `IndividualDegreeLE` at `3`, the existence per point and coordinate of
  a cubic agreeing with the restriction, built from `prodWeight` at one and the row value at two
  (`cmvPolynomial_eval₂` under `constraints_degree` and the forms' bound by type);
  `finalClaims_holds_iff` is an `iff` between the claims holding of the stack and the values being
  the tables' extensions, used in both directions (completeness and the probe); `tableOut_mem_table`
  is the completeness step and nothing more; `position_val` is the numbering `Σ_{t' < t} n_{t'} + i`
  through Mathlib's `finSigmaFinEquiv`, pinned by `tests:113-118`. The generic lemmas are
  identities over any commutative ring with no vacuous hypothesis (`weightedCubeSum_lowCoords`
  needs weights `(0, 1)` from `k` on, which `tableWeights` supplies).
- **Fidelity.** Formula: §5.5's `F`, with `eq` as the multilinear weight of the low coordinates and
  the padding as that of the high ones; `constraints.rs:271-273` accumulates the same weights. The
  powers: constraint `i` of table `t` at `o_t + i` with `o_t = Σ_{t' < t} n_{t'}` (`xi_offsets`,
  `constraints.rs:74-82`; `position_val`); side `s` at `B + s` with `B = Σ_t n_t` (`xi_form_base`,
  `cpu/mod.rs:413-416`; `rowValue`), shared by the tables, and the target
  `Σ_s ξ^{B+s} · totals_s` derived (`cpu/mod.rs:735`; `claimed`, `tableSummand_target`). The
  weights `prodWeight (tableWeights ζ t) r` are `∏_{m < τ_t} (1 + ζ_m + r_m) · ∏_{m ≥ τ_t} r_m`
  (`tests:175-176`). The final point `r = challenges reversed` is coordinate order, the first
  challenge the highest coordinate (`constraints.rs:264-269`: `m = n − 1 − j`, `chi[m] = rk`;
  `verifier.py:609`: `point = reversed(challenges)`), and each table's claim is at `chi[..tau]`
  (`constraints.rs:286`; `lowPoint r t`). The output: bus claims then constraint claims
  (`finish_claims`, `cpu/mod.rs:656-667`; `verifier.py:1395`; `tableOut`). The sides' index `s`
  is the bus phase's, used consistently for forms and totals.
- **Knowledge soundness.** Provable, at `tableError I`, with `I.d ≤ 2` (the observation). No
  definition blocks it: the batch's values are fixed before `ξ`; the side condition is inside
  both relations so a challenge cannot make it true; the output map reads the statement and the
  values only, so the table seam determines the values sent.
- **Generic code.** The three `ToCompPoly` additions carry no protocol vocabulary (grepped for
  layer, hole, blueprint, roadmap, acceptance, leanVM, slot, protocol, bus, GKR: none beyond
  "sumcheck" in `IndividualDegree.lean:24`, a pre-existing sentence about what a sumcheck needs of
  a summand, which is mathematics); `weightedCubeSum_lowCoords`'s `(0, 1)` is a hypothesis, not a
  pad value chosen; `repeatHigh`, `lowCoords`, `prodWeight` are general. Proof helpers of
  `TableSumcheck.lean` are private (eight); the public surface is the definitions the phase is
  made of, the five results the security half consumes (`sum_tableSummand`,
  `trueValues_eq_claimed_iff`, `tableSummand_degree`, `nodes_injective`, `finalClaims_holds_iff`),
  `side`, and the three position helpers (`onSumcheck`, `sum_onSumcheck`, `sumcheckTable_of_lt`,
  `sigmaOnSumcheck`), which the exposed bodies of `position` and `sigmaOnSumcheck` need public.
- **Tests.** The Layer 7 list is met in full (the target on heights 2 and 1; a violated constraint
  caught, and by the final check against a prover that repairs each round from the wire's derived
  coefficient; the reversed order; the taller column group), and acceptance test 9 besides (the
  per-table powers). The mutations exercise the conditions doing the work: the first round's
  check against the derived target (`:250`), the final check (`:271, :281`), the padding and
  `eq` under the reversed point (`:280-281`), the sharing of the side powers (`:302`). Missing
  only the toy's run (finding 1); the cost is finding 3.
- **Hygiene.** Finding 4. No line over 100 columns in any changed file; the module docstring of
  `TableSumcheck.lean` cites the specification and the Rust with the pin and says the order of
  checking (specification first); docstrings are one to two lines; the header of each generic
  module names its library.

## Pass A: the statements

Read before the proofs, from the blueprint and §5.5. Besides the answers above:

- `Data I` is the statement after the batch step, `(I.Stmt × BusOut I) × E`; the formula reads
  `ζ` off it (`x.1.2.point`) and `ξ` (`x.2`), as Layer 4's design intends (the formula reads the
  public data and the point).
- `table I q k` is the column lifted to `E` and read on `τ_max` variables as the same in every
  slice of the high coordinates (`repeatHigh`); its extension at `z` is the column's at the low
  coordinates (`evalMle_repeatHigh`). With the padding in the formula, this is §5.5's
  `(…)(X_{<τ_j}) · ∏_{k ≥ τ_j} X_k` exactly, and the padded coordinates contribute `1` to the sum
  (`weightedCubeSum_lowCoords`), the "copying lift" acceptance test 7 contrasts with the lift
  that keeps the sum.
- The side condition `side` is the seam's last three clauses; it rides through the sumcheck
  unchanged (`family … inv`), which is what lets the batch's security see the first two clauses
  fail.
- Substitution test: a different final check of the same shape leaves `Seam.table` and
  `finalClaims_holds_iff` unchanged and `tableOut_mem_table`'s use in `finalComplete`
  unprovable; a different batching map (per-table powers) makes `tableSummand_target`'s right
  side not the verifier's target (`tests:302`). The seams specify, the checks follow.
- `nodes = ![0, 1, y, y + 1]` is the honest prover's choice and reaches no verifier
  (`nodes_injective` is its one obligation).

## Pass B: fidelity at `a386121f`

Run from the specification, then the Rust, before the Lean's checks. The phase is Category A.

- **The specification** (`05-arithmetization.tex:125-155`): the constraints' zerocheck at the
  recycled point `ζ_{<τ_j}` (equation `eq:cons`), the bus claims per side (`eq:bus`), the
  back-loaded batch with `ξ^{o_j+i−1}` and `ξ^{B+s−1}`, `F` with `eq(ζ_{<τ_j}, X_{<τ_j})` and
  `∏_{k ≥ τ_j} X_k`, the target `Σ_s ξ^{B+s−1} rem_s` computed by the verifier, degree `d + 1 = 3`,
  rounds binding `X_{τmax−1}` first, one claim per column at `χ_{<τ_j}`. All of it is in the Lean
  (zero-based powers).
- **`constraints.rs:243-291`, `verify`.** Eight behaviours: `zeta.len() < n` rejects (`:251-253`;
  by type in the Lean, `point : Vector E I.τmax`); per round, four coefficients read with `c_1`
  derived (`:267`; the wire, Layer 12, the oracle protocol checking each round), the challenge at
  `chi[m]` (`:268-269`), the next claim (`:270`), the weights (`:271-273`); finally `n_cols` values
  per table (`:280`), `acc = Σ_t weights[t] · eval_t(pows, evals)` (`:282`), `acc ≠ claim` rejects
  (`:288-290`), the claims `chi[..tau]` (`:283-286`). The Lean: `Sumcheck.rounds` at degree `3`,
  `Sumcheck.final` with `finalCheck` on `formula`, `tableOut`. Two deployed checks, two modelled;
  the `eval` of an `Air` (`cpu/mod.rs:376-391`) is `Σ_i pows[off_t + i] C_i + Σ_s ξ^{B+s} B^s_t`,
  which is `rowValue`.
- **`cpu/mod.rs:726-743`.** `ξ` drawn after the bus (`:726`), `form_pows` the three powers from
  `xi_form_base` (`:727`, `:413-421`), the target derived (`:735`), `constraints::verify` at
  `bus.point` (`:736-743`). The slot's `draw ++ₚ rounds ++ₚ say` and `batchStep` are that order.
- **`cpu/mod.rs:656-667`, `finish_claims`.** Bus claims, then `constraint_claims` (`:428-441`:
  table by table, column by column, at `chi`), then the public-input claims. `tableOut` appends
  the final claims to the carried bus claims; the public-input claims are the next phase's.
- **Python** (`verifier.py:600-620, 1389-1395`): `n_constraints + 3` powers, the last three shared;
  `target = dot(form_powers, bus.totals)`; `point = reversed(challenges)`; `weights[t] *=
  equality if height > variable else challenge`; `claims = [*bus.claims, *table_sumcheck_claims]`.
  Agrees with the Rust and the Lean on every point checked.
- **Deviations declared.** None in the docstrings. The `eq` factor is written
  `(1 − ζ)(1 − r) + ζ r` (any characteristic) and said to be `1 + ζ + r` in characteristic two;
  probed over `E`.
- **Citations.** `TableSumcheck.lean:21-22, 58-59`: `05-arithmetization.tex:125-155` (§5.5 starts
  at 125), `cpu/mod.rs:404-441` (the docstring of `xi_form_base` through `constraint_claims`),
  `cpu/mod.rs:726-743`, `constraints.rs:243-291`: all at the pin, all what they are said to be.
  The test's `constraints.rs:274-277` is off by three (finding 4).

## Pass C: hygiene

The three generic modules are generic as *Generic code* asks; their new docstrings are one to
three lines and name what each lemma is for without a protocol word; imports are explicit, with
one that could be private (finding 4). `TableSumcheck.lean` has the module shape, Mathlib-style
section headers, docstrings on every public declaration, no proof narration, no roadmap
reference, no line over 100 columns, eight private helpers. The test file's module docstring is
the one place the roadmap is cited (finding 4); its guards are commented by what they pin. The
aggregate imports carry the two new modules once each.

## Kernel axioms

`tableSumcheckComplete`, `sum_tableSummand`, `tableSummand_target`, `tableSummand_degree`,
`trueValues_eq_claimed_iff`, `finalClaims_holds_iff`, `tableOut_mem_table`, `position_val`,
`nodes_injective`, `evalMle_repeatHigh`, `weightedCubeSum_lowCoords`,
`weightedCubeSum_one_prodWeight`, `DegreeLEAt.prodWeight`, `DegreeLEAt.cmvPolynomial_eval₂`,
`DegreeLEAt.mvPolynomial_eval₂`: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## What was checked and found sound

The formula against §5.5 and against `Air::eval`; the powers' numbering, the shared side powers
and the derived target against `xi_offsets`, `xi_form_base` and `cpu/mod.rs:735`; the weights
against `constraints.rs:271-273` and the Python; the variable order and the claims' points
against `constraints.rs:264-287` and `verifier.py:609`; the output order against
`finish_claims`; the `eq` factor in characteristic two; the two relations the phase sits between
and the side condition; completeness inhabited on two instances; the security half built to the
slot's error; the degree hypothesis necessary; the test's target nonzero; the guards for the
order, the repaired prover, the per-table powers and the column group; the generic modules free of
protocol vocabulary; the aggregate imports; the scripts; the kernel axioms.

## What could not be checked

The pull request's description, not yet open, and the status page's bullet, not yet written. The
whole `lake test` and `./scripts/validate.sh`, not run on the memory-limited machine; the test
module was elaborated once with the profiler and every `#guard` passed.
