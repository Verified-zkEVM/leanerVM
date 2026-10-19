# Tests

Lean tests live here and are run by `lake test`, which builds the `LeanerVMTests` library: every
test is a `#guard` (compiled evaluation) or an `example` (kernel check) that fails the build.
`Main.lean` imports the `LeanerVMTests.lean` aggregate, which imports every test module and
checks the production public module graph; `scripts/validate.sh` elaborates it with warnings as
errors. There is no test executable: at the former CompPoly pin a binary linking the `BF64`
module was killed at startup evaluating its eager `Fintype BF64` instance (finding P3 in
[`docs/roadmap/leanisa-status.md`](../docs/roadmap/leanisa-status.md)). At `572f9973` that
instance is proof-only; whether the tests can again be an executable is unchecked.
`scripts/check-imports.sh` rejects missing, stale, or duplicate test imports. The aggregate and
`Main.lean` are plain files because `LeanerVM.lean` is one (see `CONTRIBUTING.md`); a test
module may be a `module` or plain, and a plain one can decide `E` arithmetic in the kernel,
which a `module` cannot.

As executable definitions arrive, add focused unit, differential, and mutation tests here.
Put their modules under `tests/LeanerVMTests/` and import each one from `LeanerVMTests.lean`.
Tests must not be imported by the production `LeanerVM/` library.

In a `module` test file, a `#guard` needs a `meta import` of the module it evaluates, and
core's `DecidableEq` instances for `Vector` and `Array` are not exposed, so neither `decide` nor
the kernel can reduce an equality of vectors there (finding L1): state such checks on the word
lists through `Vector.toList_inj`, and give production predicates over vectors a `Decidable`
instance that compares lists, as `CompressCells` does in `LeanerVM/Semantics/Blake2s.lean`.

A kernel check of an equality on a structure over `K` or `E` goes through that structure's
`DecidableEq` instance, and a *derived* instance decides its later fields under `h ▸` for the
earlier ones, which makes the kernel compare two field values symbolically instead of
evaluating them (finding E5): `decide +kernel` on `⟨g * 1, 1⟩ = ⟨g ^ 1, 1⟩` never returns
under a derived instance. Production structures that kernel proofs compare carry a
hand-written `decidable_of_iff` instance (`Regs`), and an `E` equality is decided only against
a word in `E.ofLimbs` form, as `tests/LeanerVMTests/Semantics/Execution.lean` does.

Pitfalls met while building the proof system (`LeanerVM/Protocol/`):

- A structure that holds a real number (an error bound) makes every definition built from it
  `noncomputable`, and so does a real number or a `Fintype E` instance passed as an argument;
  keep the reduction, the verifier and the extractor in computable definitions and the error
  in types: state a security at its exact error, counting with `Nat.card` under `[Finite F]`,
  raise it with `Component.Security.mono`, which is inlined before compilation, and check an
  extractor by a `def` without `noncomputable`.
- `simp` does not rewrite inside instance arguments carried by a structure's type: state a
  phase's lemmas on its literal prover and verifier, not on the bundle's projections.
- A `Decidable` instance written `by unfold …; infer_instance` can elaborate and never return
  when a `#guard` evaluates it; write it `inferInstanceAs (Decidable …)`. Read a compile's exit
  status: a kill hidden behind a pipe into `head` looks like success.
- A binder whose type is a membership in `Finset.univ : Finset E` makes a linter enumerate the
  field ("maximum recursion depth"); state counting bounds over an abstract `[Fintype α]`.
- Under a section's `[CommRing R]`, a `def` taking `[Zero R]` is rejected by Mathlib's
  overlapping-instances linter, which `warningAsError` makes an error; use the ring's zero.
- `#guard v = w` finds no `Decidable` instance when the vectors' length is a computed size;
  compare `.toList`. A `#guard` whose proposition has a numeral of `E` next to an operation
  (`y ^ 2 + 1`) finds none either; name such values as definitions.
- An instance `∀ i, OracleInterface ((p₁ ++ₚ p₂).Message i)` for concrete schedules `p₁`, `p₂`
  is never found by instance search, even with the parts' instances at hand: ArkLib's instance
  is applied by name (`msgAppend`, `chalAppend` in `ToArkLib/Schedule.lean`). A recursive
  schedule gets a recursive instance the same way.
- `exact le_of_eq (Finset.sum_eq_zero fun i _ ↦ …)` against a right side that is not `0` fails
  with "type of `i` is not known": the lambda is elaborated before the unification that would
  fail anyway. Write `(Finset.sum_eq_zero fun (i : T) _ ↦ …).le.trans zero_le` with the index
  type spelled out.
- Since CompPoly `572f9973` a numeral in `K` has its characteristic-two value (`(2 : K) = 0`):
  write an encoded word as `K.ofBits n`.
- A `Decidable` instance for `∀ r ∈ l, …` over a list of tables over `E` can be found through
  `Fintype` on the tables, which is noncomputable for `K`, and the `#guard` fails to compile;
  give `List.decidableBAll _ _` by name.
- A `#guard` on a subtype value built by hand with its proof (a polynomial with its degree
  bound, `⟨q.val + C 1, …⟩`) never returned; build test values with the definitions under test.
- `draw C ++ₚ draws C k` has `1 + k` rounds and `draws C (k + 1)` has `k + 1`, which are not
  the same type for a variable `k`; so `draws` nests its new challenge last, and a component
  drawing `k` challenges one at a time recurses on a prefix (`Gkr.interpPrefix`) and folds its
  last step into the last challenge (`Gkr.interpolate`).
- A `Finset.filter` in a statement under `open scoped Classical in` takes the classical instance
  only where no other applies: a lemma stated without `[DecidableEq F]` in scope and used where
  it is in scope fails with "synthesized type class instance is not definitionally equal". Keep
  the instances in scope the same at the statement and at the use, or compare the filters
  through `Finset.card_le_card` and `Finset.mem_filter`, which ignore the instance.
- A recursion whose branch must reduce a `match` on its index (the last step of
  `Gkr.layerStepsSecurity` uses one tracker, the others another) splits the index as
  `0`, `1`, `k + 2`: a `match` on a variable `k` inside the branch does not reduce, and the two
  sides of `Component.Security.append` must agree definitionally.
- A closed statement over `E` in a definitional comparison is an evaluation of the trees: a
  hypothesis such as `s.2.2 ≠ Φ.claim (ctxOf …) …` at `s := (s0.1, (s0.2.1, trueClaim + 1))`,
  with `s0` and `trueClaim` the hand run's values, sends the unifier, or the kernel, through
  `s0` and never returns (the round refutation hit the recursion limit, the descendants' one a
  kernel timeout). The same proof on a symbolic statement, `(x, (cv, Φ.claim ((x, noO), ()) 0
  cv + 1))` with `x` and `cv` variables, is one unfolding, since nothing closed can be
  evaluated. State a refutation over variables and keep the hand run's values for the honest
  runs; never `simp`, `show` or `change` between two spellings of a claim over `E`.
- Handing a transcript to a guarded check in a refutation
  (`Verifier.GuardedForm.probEvent_pos_of_check` on `fullOf c msg`) can exceed the default
  recursion depth when the statement has three public lines, the unifier unfolding the count of
  sent lines to match the message: a local `set_option maxRecDepth 1000 in` on that one example
  is enough (`zeroTop` in `tests/LeanerVMTests/Protocol/PublicInput.lean`). `simpa` on a
  hypothesis that mixes `E` arithmetic with a structure literal can hit the same limit; name the
  lemmas in a `simp only`.

- On the toy instance, an `abbrev`, unifying a term the library built with one the test
  elaborates afresh can time out at `whnf` where the same unification at an abstract instance is
  immediate: a column claim's weighted claim written as `⟨eqWeight …, c.value⟩` against
  `Opening.columnWeighted toy c`, the stack's question `⟨0, W⟩` against the library's, or a
  variant verifier's steps given as lambdas mentioning the pool to
  `Component.batchQuery_not_rbr`. Use the library's named terms and its lemmas stated over an
  abstract instance (`Opening.columnWeighted_holds_iff`, `Opening.answer_weight_iff`), prove a
  fact once over an abstract instance and instantiate it (`unit_holds_of_copies` in
  `tests/LeanerVMTests/Protocol/Opening.lean`), and define a variant verifier's steps over an
  abstract instance.
- A component appended with a zero-round one has the schedule `draw F ++ₚ !p[]`, which is
  `draw F` by `rfl`, instances included, but instance search does not find the appended
  instances for statements about it; give the composition the type at `draw F` by an
  abbreviation (`Component.batchQuery`), and pin `ChallengeIdx.sumEquiv`'s schedules by name.

Implementation-validation tests should run identical versioned workloads through the Lean
reference and a pinned Rust leanVM revision, comparing decoding, state transitions, outputs,
traces, encodings, and rejection behavior as each surface becomes available. Optimized native,
Rust FFI, CUDA, and future compiled paths use the same fixtures. These tests establish observed
agreement, not a formal theorem about the foreign implementation.

The initial target suite should cover all six opcodes, write-once conflicts, invalid generator-
power addresses, branch state, BLAKE2s counter/finalization metadata, public-input encoding, and
prover-supplied cells. Guest-level fixtures should separately cover XMSS epoch groups, SPHINCS
`(key, message)` claims, overlaps, conflicting messages, omitted coverage, child mappings, and
deferred-claim rejection. Bind vectors to the revision in
[`docs/leanvm-target.md`](../docs/leanvm-target.md).

The executable ISA checker and its proved contracts are documented in
[`docs/leanisa-checker.md`](../docs/leanisa-checker.md). The optional
`python3 scripts/test-rust-contracts.py /path/to/leanVM` lane runs the maintained Rust fixtures
in `tests/rust/` and validates their actual exports in Lean. It requires the pinned source
commit and an offline Cargo cache; the ordinary Lean gate does not depend on a Rust checkout.
