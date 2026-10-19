# Review: batching by powers, and the GKR's combiner as a batching

> An archive of the review of three commits of the branch `feat/protocol-batch`, `59fef66` (the
> files of contributor pull request #43, carried unchanged), `ea85403` (`ToArkLib/Batch.lean`)
> and `9e53765` (the GKR's combiner becomes `Component.batch`), against their base `5618097`, the
> head of draft pull request #70: names, paths and line numbers are those of `9e53765`. No pull
> request was open for the branch at the time of the review. What is accepted from it is text of
> the [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of
> the pull request that met it.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. `batchSecurity` asks for a subsingleton witness and decidable equality that a different quantifier order does not need | met in `3f235c4`: the review's statement, the true values chosen before the witness, with `[Finite F]` only; `lambdaSecurity` and the test supply it; the module docstring says why the order matters, and a test guards it (two witnesses collide at two challenges between them) |
| 2. the carried files' public surface: three declarations superseded or unused, one name beside `Component.batchComplete` | met in `0f18da2`, a commit after `59fef66` with #43's co-author trailers: the ArkLib module's uniform-sample bound and its test are gone, `uniform_false_batch_fraction_le` is gone, `batch_complete` is `sumCube_hadamard_batchWeight_of_forall`, and the cross-library sentence is gone |
| 3. the GKR spells its one batching three ways | met in `3f235c4`: `combineCheck` combines by `powerBatch`, its two proofs take one `mul_comm` step, and the module docstring writes one order; the summand stays |
| 4. hygiene and documentation | met: the long lines wrapped; `noO` and `truth` gone, the comment says "the combined claim"; this review listed in `docs/README.md`; the status row's number and the pull request body's classification and the note on #43 filled when the pull request opens |
| the observation on the opening phase as a consumer | no change needed: the opening phase is Layer 10's; its pool meets the hypothesis with the weighted pairings, as the review says |
| the observation on the status's "either side" | met: the sentence says what each side would cost |

Reviewed with the `adversarial-review` skill in three passes: the statements against the
blueprint's Layer 4 section ("The batching's state function is 'some claim is false'; escape needs
the batching polynomial, of degree `< k`, to vanish at the challenge"), its holes-table row, the
Layer 5 GKR and Layer 10 opening sections, the ledger row "Batching by powers", the conventions
*Holes*, *Extractors*, *Generic code*, *Load-bearing checks* and *Claim pool order*, and
acceptance tests 24 and 32, read before the proofs; the expectation for the powers formed from the
specification at the pin (`05-arithmetization.tex:91-93`, §5.5 `:145`;
`08-end-to-end-protocol.tex:98-99`) before the Rust (`crates/primitives/src/field/mod.rs:51-61`,
`crates/pcs/src/stack_open.rs:400-401, 518-544`, `crates/lean_vm/src/gkr.rs:369-423`,
`crates/primitives/src/multilinear.rs:243-247`, each fetched from GitHub at `a386121f`); and
hygiene. Every changed file was read in full, with the
base's `SampleChallenge.lean`, `Component.lean`, `Schedule.lean`, `Spine/Errors.lean`,
`Spine/Seams.lean` and the GKR's tests. Lean was run five times, serially, with `lake env lean`:
two scratch files (the kernel axioms and the probes below) and the three test files
`Protocol/Batch.lean`, `Protocol/PowerBatching.lean` and `Protocol/GrandProductSecurity.lean`
(exit 0, every `#guard` passes; `Protocol/GrandProduct.lean`'s build output postdates the
refactor). `audit-lean.sh`, `check-imports.sh`, `check-layers.sh` and `check-docs.py` pass. The
carried files are byte-identical to #43's head `ad3f297` (blob hashes compared through the GitHub
API), and `59fef66` keeps #43's author and both co-author trailers. Nothing was edited but this
file.

Target classification: the commits name the hole and #12. The pull request, once open, is to say
that the work feeds T4 through the GKR (Layer 5) and, later, the table sumcheck and the opening
(Layers 7 and 10), in both directions (`batchComplete`, `batchSecurity`), that the component is
Category A (the Lean is the standard) while the zero-based powers are a transcribed fact pinned by
tests, and that #43 is superseded by this branch with its author credited.

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological, and the GKR's statements and errors did not move.
`batch` is `sampleChallenge` with no check and the map `out s ρ (powerBatch (value s) ρ)`
(`Batch.lean:43-45`); `batchSecurity` (`:58-93`) charges `(k − 1)/|F|` on the challenge, the
blueprint's error, under a hypothesis that is the escape condition in the consumer's relations:
from outside the input relation, every challenge that lands in the output relation makes the
combined claim equal the combination of values `a` chosen before the challenge, `a` not the
claimed values. The hypothesis cannot let `a` depend on the challenge, handles `k = 0` and
`k = 1` correctly (error zero, and the hypothesis then forces that no challenge lands), and is met
by the GKR's combiner (`GrandProductSecurity.lean:247-256`) and, algebraically, by the opening's
pool through `pairing_batchWeight`. It needs a subsingleton witness only because `a` is chosen
after the witness; chosen before, the same bound holds for every witness type (finding 1, probed).
The zero-based powers are the specification's (`λ^{s−1}` for `s` from 1) and the Rust's
(`powers` starts at `x^0`; `poly_eval` is Horner constant first), and `lambdaStep` is
definitionally the base's combiner (probed by `rfl`). The rest is surface and hygiene.

## Findings, most severe first

### Low

**1. `batchSecurity` asks for a subsingleton witness and decidable equality that a different
quantifier order does not need.** *Generic code.* The hypothesis is
`∀ s o w, ((s, o), w) ∉ relIn → ∃ a, ∀ ρ, …` (`Batch.lean:62-64`), so `a` may depend on the
witness, and the instance `[Subsingleton W]` (`:56`) is what keeps the bad challenges of different
witnesses from adding up. That instance is necessary for this order: two witnesses whose true
values against claimed `(0, 0)` are `(1, −1)` and `(2, −1)` give two bad challenges over
`ZMod 5` (`ρ = 1, 2`), above `k − 1 = 1` (probed as a `#guard`). Choosing `a` before the witness
removes it, and `[DecidableEq F]`, which the proof never uses past `classical`, with it; the
proof also loses its case splits on `Nonempty W` and on the input relation. The following
compiles against the branch with only `[Finite F]` (probed):

```lean
def batchSecurity
    (h : ∀ s o, ∃ a : Fin k → F, ∀ w ρ, ((s, o), w) ∉ relIn →
      ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut →
        a ≠ value s ∧ powerBatch (value s) ρ = powerBatch a ρ) :
    Security (batch O F value out) relIn relOut
      (drawError F (((k - 1 : ℕ) : ℝ≥0) / (Nat.card F : ℝ≥0))) :=
  sampleChallengeSecurity O F _ _ (k - 1) fun s o _ ↦ by
    have := Fintype.ofFinite F
    classical
    rw [natCard_subtype_eq_card_filter]
    obtain ⟨a, ha⟩ := h s o
    by_cases hgood : ∃ ρ w, ((s, o), w) ∉ relIn ∧
        ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut
    · obtain ⟨ρ₀, w₀, hin₀, hρ₀⟩ := hgood
      refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans
        (card_false_batch_le (value s) a (Function.ne_iff.mp (ha w₀ ρ₀ hin₀ hρ₀).1.symm))
      obtain ⟨w', hw', hout⟩ := (Finset.mem_filter.mp hρ).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ha w' ρ hw' hout).2⟩
    · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ρ - ⟨w', hw', hout⟩
      exact hgood ⟨ρ, w', hw', hout⟩
```

For a subsingleton witness the two hypotheses are equivalent, so both consumers supply it as
easily (`fun s o ↦ ⟨a, fun _ l hs hl ↦ …⟩` in `lambdaSecurity`; `fun _ _ ↦ ⟨v₃, fun _ _ hs hρ ↦ …⟩`
in the test). The failure today: a consumer whose witness carries data the claims do not depend
on cannot use `batchSecurity`, though the bound holds for it. Fix: the statement above, the
module docstring's "the extractor that keeps a witness that carries no information" becoming
"the extractor that keeps the witness", and the `#guard` above in the tests as the reason the
order matters.

**2. The carried files' public surface: three declarations superseded or unused, one name beside
`Component.batchComplete`.** *Interfaces; public surface.* With `batchSecurity` built:
- `ToArkLib/PowerBatching.lean` (`probEvent_uniform_false_batch_le`, `:29-39`) is the uniform-sample
  bound `batchSecurity` now obtains through `sampleChallengeSecurity`; only its own test reads it,
  and its docstring (`:16-19`, "this is not a knowledge-soundness or transcript theorem") describes
  the gap `Batch.lean` fills.
- `ToCompPoly/PowerBatching.lean:145-152`, `uniform_false_batch_fraction_le`, is
  `card_false_batch_le` divided by `|F|` in `ℚ`; nothing reads it.
- `:76-82`, `batch_complete`, is `pairing_batchWeight` followed by `simp_rw`; nothing reads it, and
  `LeanerVM.Protocol.batch_complete` and `LeanerVM.Protocol.Component.batchComplete` are two
  unrelated statements one underscore apart.
- `:30-31` of the same file's docstring points a CompPoly candidate at an ArkLib-candidate
  module, which an upstream CompPoly would not have.

`singleton_batch_ne` and `empty_powerBatch` are read only by tests and cheap; they may stay. Fix,
in a commit after `59fef66` so the credit stays in its history (repeating the co-author trailers):
delete the `ToArkLib` module and `uniform_false_batch_fraction_le` with their test lines, or keep
the module and say for which upstream consumer; delete or rename `batch_complete`
(`sumCube_hadamard_batchWeight_of_forall`); drop the cross-library sentence.

**3. The GKR spells its one batching three ways.** *Hygiene.* After the refactor `lambdaNext`
combines by `powerBatch`, `Σ value_t · λ^t` (`GrandProduct.lean:273-274`), while the verifier's
second use of the same combiner, `combineCheck`, writes `Σ λ^t · ∏ …` (`:356-358`), as do
`summand` (`:150-151`), `summand_boolVec` (`:293`) and the table in `partialSum_summand_zero`'s
proof (`:310`, which now needs a `mul_comm` step), and the module docstring writes both orders in
one bullet (`:30-33`). The values agree in a commutative ring, so no `#guard` changed meaning; but
the combination the deployed verifier computes twice with one `poly_eval` (`gkr.rs:376, 384, 411`)
is two definitions here. Fix: `combineCheck` as
`decide (s.2.2 = powerBatch (fun t ↦ ∏ c : Fin (2 ^ ρ), (ch t)[c]) s.1.2)`, and one order in the
docstring; the summand may stay as it is.

**4. Hygiene and documentation.**
- `GrandProductSecurity.lean:237`: 103 columns.
- `protocol-status.md:178`: 146 columns, the edited paragraph not rewrapped.
- `protocol-status.md:28`: the row names "the pull request stacked on #70"; fill the number when
  it opens.
- `tests/LeanerVMTests/Protocol/Batch.lean:27`: `noO` is unused, and the comment at `:44` says
  "the verifier's verdict" while the guard evaluates `powerBatch` alone; either run `batch3`'s
  verifier through `Component.sampleVerifier_verify` on `(v₃, noO)` or say "the combined claim";
  `truth` (`:48`) ignores its argument.
- `docs/README.md` lists each review; this file is to be listed.
- The pull request body: the classification above, and that #43 (still open) is superseded.

### Observations

- **The opening phase can consume `batch`, with one piece Layer 10 supplies.** Its pool meets the
  hypothesis with `a j = ⟨W_j, q⟩`, fixed by the oracle before `λ`: the output relation
  "`⟨W_λ, q⟩ = C_λ`" with `W_λ = batchWeight W λ` is, by `pairing_batchWeight`, the collision
  `powerBatch a λ = powerBatch c λ`, and `ColumnClaim.holds_iff_weighted` makes "some pooled claim
  is false" `a ≠ c`. The slot goes from `Seam.flock` to `Seam.done` with the statement `Unit` and
  the verifier queries the stack after `λ`, so the phase is `batch` followed by a zero-round
  query step; the schedule `draw E ++ₚ !p[]` is `draw E` by `rfl` (probed: ArkLib's
  `Fin.vappend_zero` is `rfl`), while the instance arguments of the appended `Component.Def` were
  not probed. The pool must be ordered with the ring-switched claims first to meet the deployed
  powers (`stack_open.rs:400-401, 518-519`; §8.5 "the ring-switched claim first"), which `batch`
  leaves to `value`, rightly. The error is written with `Nat.card F` and the slot's with
  `overE`'s `Fintype.card E`; `Security.mono` bridges them, as for the GKR.
- **The status's "on either side".** `protocol-status.md:173-176` keeps the base's reason for the
  statement maps: "a relabelling pass-through on either side would put a `!p[]` into the schedule
  and break the definitional equality with `stepSpec`". On the output side the schedule does not
  change (the probe above); whether the instance arguments or the error would break there was not
  probed. The design choice stands either way, since a relabelling step would add an `append`, a
  security and a `mono`; the sentence may say "on the input side" or name what breaks.

## Answers to the questions put to the review

- **Is the hypothesis the right abstraction?** Yes. The state function is `sampleChallenge`'s, the
  input relation before the challenge and the output relation at the mapped statement after it
  (`SampleChallenge.lean:150-159`); the blueprint's "some claim is false" is the consumer's input
  relation, and the hypothesis is its escape condition. Stating it on the consumer's relations,
  rather than fixing them from a function of true values, is what lets a relation carry conjuncts
  the batching does not touch: the GKR's riders are discharged as "no challenge lands"
  (`lambdaSecurity`, through `mem_rel_lambdaNext`, `:232-241`). The test inhabits it over `E`
  (`tests:64-68`).
- **Is it satisfiable by the consumers?** The GKR's combiner: yes, built. The table sumcheck's `ξ`
  (`tableSpec = draw E ++ₚ …`, `k = B + 3` claims at error `B + 2`, `Spine/Errors.lean:158-171`):
  yes in shape (not built), its claimed values (zeros and the sides' totals) being in the
  statement and its true values functions of the stack. The opening's pool: yes, see the first
  observation.
- **Does it hide a case?** `k = 0`: no `a` differs from the empty family, so the hypothesis says no
  challenge lands, and the error is zero, which is right. `k = 1`: error zero; a false singleton
  never collides (`singleton_batch_ne`). A witness type that is not a subsingleton: excluded by the
  instance, and necessary for the current order (finding 1). An `a` depending on the challenge:
  impossible, `∃ a` precedes `∀ ρ`; `a` may depend on the oracle, which is the opening's case.
- **The deployed powers.** `powers(x, n)` is `[x^0, …, x^{n−1}]` (`field/mod.rs:51-61`), taken by
  the opener at `stack_open.rs:400-401` and the verifier at `:518-519`, the ring-switched claims
  first, the target `Σ g · value` (`:521-526`) and the weight with the same powers (`:531-544`,
  which `evalMle_batchWeight` and `pairing_batchWeight` mirror). The GKR's combiner is
  `poly_eval(values, λ)` (`gkr.rs:376`), Horner with the constant first (`multilinear.rs:243-247`),
  so `Σ_s value_s λ^s`, and its checks `poly_eval(products, λ)` (`:384, 411`). `powerBatch`'s
  zero-based convention matches all three.
- **Did the refactor change the GKR's statements or errors?** No. `lambdaStep` is definitionally
  `sampleChallenge O F (fun _ ↦ true) (fun s l ↦ lambdaNext nside m (inp s) l)` (probed by `rfl`);
  the types of `lambdaComplete`, `lambdaSecurity`, `gkrComplete` and `gkrSecurity` are untouched;
  `partialSum_summand_zero` (`:304`) is restated with `powerBatch`, the same proposition up to
  commutativity.
- **The order of powers and the `#guard`s.** `Σ_s value_s · λ^s` now, `Σ_s λ^s · value_s` before:
  the same element of a commutative ring, and the specification's and the Rust's order of the
  powers. The GKR tests' guards evaluate the same values; the one that spells the powers,
  `claim0 = vals 0 + lam * vals 1 + lam * lam * vals 2` (`tests/…/GrandProduct.lean:224`), pins
  them. The security test compiles here; the definition test's build output postdates the
  refactor.
- **Stale references to `card_filter_powerSum_eq_le`.** None outside the archived reviews
  (`docs/reviews/protocol-gkr-security.md:15, 125, 219`, `protocol-gkr-security-second.md:320`),
  which record their commits; the status names its removal (`:177`); `SumcheckRound.lean`'s
  docstring dropped it.

## Pass A: the statements

- `batch` (`Batch.lean:43-45`) is a computable `Def` with no error in it (*Holes*); `batchComplete`
  (`:49-54`) asks exactly that the input relation be carried to the output relation at every
  challenge, which is needed. `batchSecurity`'s error is a closed form of `k` and `|F|`
  (acceptance test 32) and its extractor is the base's `keepExtractor`; `batchSecurity3` is a
  plain `def` in a compiled test (acceptance test 24).
- The hypothesis doing the work is `a ≠ value s` with `a` fixed before the challenge; its negative
  is the guard that equal families collide at every challenge (`tests/…/Batch.lean:76-77`).
  The order `∃ a, ∀ ρ` is load-bearing: with `a` chosen after `ρ`, every landing challenge has
  such an `a` once `k ≥ 2` (add `(ρ, −1, 0, …)` to the claimed values, whose combination at `ρ` is
  zero), so the hypothesis would hold of every relation; the order written is the right one.
- The carried statements: `card_false_batch_le` (at most `J − 1` collisions, truncated
  subtraction making the empty and singleton cases zero), `natDegree_batchDifference_le`,
  `pairing_batchWeight` and `evalMle_batchWeight` (linearity, the opening's need) are right and
  non-vacuous (their tests over `ZMod 5` and `E`).
- Load-bearing checks: the batching makes no check, so no refutation is owed.

## Pass B: fidelity at `a386121f`

Run from the specification, then the Rust. The component is Category A; the zero-based powers are
transcribed.

- Specification: the GKR's combiner `Σ_{s=1}^{nside} λ^{s−1} Ṽ^s` (`05-arithmetization.tex:91-93`);
  the table batch `ξ^{o_j+i−1}`, `ξ^{B+s−1}` (`:145`); the opening "Claim `j` takes the weight
  `λ^{j−1}`, the ring-switched claim first", `W_λ = Σ_j λ^{j−1} W_j`, `C_λ = Σ_j λ^{j−1} c_j`,
  "drawn after every claim value is bound" (`08-end-to-end-protocol.tex:98-99`). All zero-based in
  the exponent, the values bound before the challenge: `powerBatch`, `batchWeight` and the
  hypothesis's `a` fixed before `ρ`.
- Rust: four places, all zero-based (the answers above): `powers`, the opener's and verifier's
  split, the verifier's target and lifted weight, the GKR's `poly_eval`.
- Errors: the specification charges `nside + B` for `ξ` (`05-arithmetization.tex:155`), one more
  than the degree; the Lean's `k − 1` is the degree bound, already recorded as such in
  `Spine/Errors.lean`'s docstring.
- Deviations declared: none in `To*/`, which rightly cites no specification (*Generic code*).

## Pass C: hygiene

`Batch.lean` and the two carried modules are generic: no slot, pad value, point or protocol
vocabulary (grepped for layer, hole, decision, acceptance, ledger, blueprint, leanVM, GKR,
opening, Flock, WHIR, bus, slot, phase: none), each with a header naming its candidate library,
imports public only where exposed definitions need them. The refactor's added comments carry no
bookkeeping. Docstrings are one to three lines; the module docstrings carry the design. The
carried files keep their derived-source notice and leanth citation. The rest is findings 2 to 4.

## Kernel axioms

`Component.batchSecurity`, `Component.batchComplete`, `Gkr.lambdaSecurity` and `gkrSecurity`:
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`. `card_false_batch_le` and the
uniform-sample lemma `sample_rbr` uses are in `batchSecurity`'s closure; the carried
`probEvent_uniform_false_batch_le` and the pairing lemmas were not printed.

## What could not be checked

The pull request's description, not yet open. Whether the instance arguments of a `Component.Def`
appended with a zero-round step on the right agree with the slot's, which the opening phase will
meet. The whole `lake test` and `./scripts/validate.sh`, not run on the memory-limited machine.
