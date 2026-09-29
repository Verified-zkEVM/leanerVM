# Review: the public-input phase (hole P5)

Reviewed on 2026-09-29 against branch `worktree-proof-system-hole-impl`, whose HEAD is `main`
at `5cb7da6`. The work is **staged and not committed** (`git diff --cached`: six files, 904
insertions, 55 deletions), so `git diff main...HEAD` is empty. Read-only, with the repository's
`adversarial-review` skill. The repository was not modified; this file is the only one created.

Sources read:

- leanVM at the pin `a386121f84292f6fa663aaa3e570c15bc0240ea2` (confirmed by `rev-parse`):
  `doc/leanvm/body/02`, `03`, `04`, `06`, `08`; `doc/leanvm/preamble/theorems.tex`;
  `crates/lean_vm/src/cpu/mod.rs:600-682` and `:711-779`;
  `crates/primitives/src/multilinear.rs:39-48`; `python-verifier/verifier.py:1397-1402`.
- ArkLib `dca90385`: `OracleReduction/Basic.lean` (`OracleVerifier`, `toVerifier`,
  `materializeOutput`), `Security/RoundByRound.lean` (`Extractor.RoundByRound`,
  `KnowledgeStateFunction`, `rbrKnowledgeSoundnessWorstCaseWith`), `Security/Basic.lean`
  (`perfectCompleteness`, `perfectCompleteness_of_run_support`),
  `Security/CoordinateWiseSpecialSoundness/Guarded.lean` (`IsGuardedWith`, `GuardedForm`).
- CompPoly `3468b38c` and VCVio `f9dc47d9`, for the cited declarations only.
- Every changed Lean file in full, and in full what they are stated over: `Spine/Instance`,
  `Seams`, `Phase`, `Compose`, `Toy`; `ToArkLib/Component`, `PassThrough`, `SendOracle`,
  `Oracles`; `Protocol/Field`; `Parameters/Field`; `tests/LeanerVMTests/Protocol/Spine.lean`.
- For intent: `AGENTS.md`, `CONTRIBUTING.md`, the blueprint (Pinned conventions, Layer 8,
  Layer 10, the acceptance tests), the status file, `docs/reviews/protocol-spine.md`.

The blueprint's Layer 8 text and the status file were edited by the author in this same
change. Their agreement with the code was therefore given no weight. The authority used for
what the phase must do is the specification tex at the pin.

**Method.** This is Category A work. The expectation of the phase (schedule, messages, check,
pooled claims, error, honest prover) was written down from the tex before the Lean file was
opened, and the Rust was opened last, only to check what the documents say about it.

Mechanical checks, all run by the reviewer on the staged tree:

| Check | Result |
| --- | --- |
| `./scripts/audit-lean.sh` | passed |
| `./scripts/check-repository.sh` | passed |
| `./scripts/check-imports.sh` | passed |
| `./scripts/check-layers.sh` | passed |
| `python3 ./scripts/check-docs.py` | passed |
| `lake build LeanerVM.Protocol.PublicInput` | exit 0, 3159 jobs (replayed) |
| `lean -E warning` on `PublicInput.lean` | exit 0, no warning, 15.5 s, 1.74 GB |
| `lean -E warning` on the test file | exit 0, no warning, 22.8 s, 3.05 GB |
| `lean -E warning` on `tests/.../Spine.lean` (baseline) | exit 0, 13.2 s, 3.15 GB |
| `./scripts/validate.sh` | exit 0; 3234 jobs; 2983 declarations audited |

The full gate was run because status finding E13 reports a `#guard` that behaved differently
in the full test build than alone, so a standalone compile does not settle it. The axiom audit
reports no unexpected axiom. The author's claim that `validate.sh` is green is confirmed.

The test file costs what the spine's test file costs (the memory is the imports), so no
`#guard` is expensive.

`#print axioms` reports `propext`, `Classical.choice`, `Quot.sound` only, and no `sorryAx`,
for: `publicInputSecurity`, `publicInputComplete`, `publicInput_rbr`, `publicInput_complete`,
`publicInputStateFunction`, `publicInputGuarded`, `publicInputVerifier_toVerifier_verify`,
`bad_challenge_unique`, `line_challenge_unique`, `eval₂Mle_linePoint`, `lineClaim_holds_iff`,
`publicInputOut_of_check`, `pooled_mem_pub`, `honestValues_eq_expectedValues`,
`publicInputPhase`, `publicInputExtractor`, `publicInputVerifier`, `publicInputProver`. No
admitted ArkLib theorem is in the closure.

## Disposition

| Finding | Disposition |
| --- | --- |
| B1 (medium): the two checks are not equivalent at a fixed challenge | Met: the false sentence is gone from the blueprint's Layer 8 and from the status file, and status finding F18 states what holds (the equations per limb imply the equation on the words, not conversely; the two checks accept the same stacks; each has at most one bad challenge, not the same one) and that the pinned verifiers' soundness is a lemma Layer 12 owes. The module docstring says the same. The counterexample is a test (`badLimbs`, `rStar`, `wordsEquation` in `tests/LeanerVMTests/Protocol/PublicInput.lean`). |
| C1 (low): fragile proofs, declared the template for three more phases | Met: `LeanerVM/Protocol/ToArkLib/GuardedVerdict.lean` holds the two facts both proofs start from, for every guarded verifier (`Verifier.GuardedForm.of_probEvent_pos`, `Reduction.mem_support_run_of_guarded`). The phase's proofs use explicit `simp only` lists and restate no whole goal; the prover's run is unfolded with ArkLib's `processRound` lemmas. The status file names the verdict lemma and the shared lemmas as the pattern, not the proofs. |
| A1 (low): `publicInputOut` drops a claim on a short list | Met by H1: the only output is `PublicInput.pooled`, which does not read the message. |
| A2 (low): `sent` is fixed by no statement and no test | Met by one change to the spine, which the user allowed where justified: `PublicLine.sent : Bool` in `LeanerVM/Protocol/Spine/Instance.lean`, declared with the line, so the phase takes no parameter and the instance is where the protocol and the compiled verifier read it (status decision 15). Tested on three lines in the shape of the memory limbs (`threeLimbs`, `badTopLimb`) and on an instance that sends nothing (`noneSent`). A count above the number of lines can no longer be written. |
| C2 (low): ten unprefixed public names in `LeanerVM.Protocol` | Met: `namespace PublicInput`; outside it only `publicInputPhase`, `publicInputComplete`, `publicInputSecurity`. |
| B2 (low): Schwartz-Zippel cited as Lemma 5.2; it is Lemma 3.8 | Met: Lemma 3.8 in the status file (finding F18, the survey record). |
| C3 (low): the module docstring has no pin and no provenance | Met: the docstring cites the tex lines at the pin, says the module was written from the specification and the Rust read afterwards, and says what the pinned verifier checks instead. |
| B3 (low): six slips in the changed documents | Met: the status file was rewritten on `main`'s text after the merge with Layer 1, so the findings run E10 to E18 with none missing; finding E12 names the declarations as they are; `Execution.lean:642`; `08-end-to-end-protocol.tex:27-33`; the snapshot is dated 2026-09-29; the blueprint cites the row *Claim pool order* of the pinned conventions. |
| A3 (observation): several tests restate definitions | Met: the restating tests are removed; tests 1, 2, 3 and 5 of *Tests to add* are added (test 3 as the instance that sends nothing; test 4 is moot after H1). |
| A4 (observation): the message type is wider than two scalars | Kept: the message is a `List E` whose length the check fixes, so that one phase serves every instance; a wrong length is rejected (tested). |
| C4 (observation): generic lemmas kept in the phase module | Met: the counting bound is `LeanerVM/Protocol/ToVCVio/UniformSample.lean`. The line identity stays in the phase module, a point chosen by the protocol being no upstream material, and is derived from Layer 1's `evalMle_append_boolVec`; the helper that duplicated `evalMle_boolVec` is gone. |
| H1 to H6: audit-surface compressions | All taken. H1: one output, `pooled`; the claims are pooled at the lines' values, which are the values sent whenever the check passes. H2: the prover sends `expectedValues`. H3: five lemmas private. H4: `pubWitMid` inlined. H5: `Verifier.GuardedForm.of_probEvent_pos`, used by the phase and by the pass-through and send-oracle components. H6: `keepOracles` and `OracleVerifier.materializeOutput_of_keepOracles` in `LeanerVM/Protocol/ToArkLib/KeepOracles.lean`, used by the phase and the pass-through. |

The names below are those reviewed. The branch has since put the phase's declarations in the
namespace `PublicInput` (`publicInputVerifier` is `PublicInput.verifier`, and so on), removed the
parameter `sent`, and been merged with Layer 1 (#59).

## Verdict in one paragraph

No theorem statement is wrong, none is vacuous, and the phase is the specification's: one
challenge, the prover's values, a per-limb check that rejects, three claims pooled in the
roadmap's order at the point `(r, 0, …, 0)`, error `1/|E|` whatever the number of lines. Both
halves are proved on the kernel's three axioms and the full gate passes. The defects are
elsewhere. One is in the documents changed with the code: they assert that the
specification's check and the Rust's are equivalent once the scalars are evaluations of
`K`-valued columns, which is false and was checked false by computation (B1); the sentence
replaced a correct one. The others are about cost, which is what the user asked about: the
module exposes 35 public declarations where 23 suffice, carries two definitions of the output
and two of the sent values, and its three hardest proofs rest on the normal form `simp`
happens to leave, while the status file names them the template for three more phases (C1).
All of it is cheap to fix now, before P1, P3 and P7 copy it.

## Pass A: specification

### What was tested, and what breaks a wrong phase

The tautology test was run against five wrong verifiers. Each breaks a stated theorem, so the
statements specify the phase rather than restate it.

| Wrong verifier | What breaks | Evidence |
| --- | --- | --- |
| (i) checks nothing | knowledge soundness | computed, below |
| (ii) pools no claim | knowledge soundness | computed, below |
| (iii) another point or value | completeness | computed, below |
| (iv) pools only the sent values | knowledge soundness | the test file, `:155-161` |
| (v) accepts any list | knowledge soundness | same as (i) |

Computed on the toy at statement `1`, with `badLine` the stack whose column 2 is `[1, 1]`:

- (i), (v): `badLine` is outside `Seam.table` (`PublicLinesHold` is `false`). At the sampled
  challenge `y` the prover sends its column's true evaluation. The check rejects it (`false`),
  and the output pooled at the sent value is inside `Seam.pub` (`true`). Without the check the
  bad event has probability one, so `toFun_full` forces a state that `publicInput_rbr` cannot
  bound. The check is load-bearing.
- (ii): the output with no pooled claim is inside `Seam.pub` for every stack, `badLine`
  included (`true`), with the same consequence.
- (iii): on the honest stack the claim at the wrong value `y` is false (`false`) and the claim
  at the line's value holds (`true`), so a wrong value breaks completeness. A wrong point is
  separated by the test file's `:48-52`, on a table of two variables.

### The knowledge state function

`PublicInput.lean:387-434`. Each round's predicate is the right one and none is trivial.

- Round 0 is `Seam.table`: true of `honest`, false of `badLine`.
- Round 1 is `Seam.pub` of `pooled` at the challenge. It is not trivially false: on `badLine`
  at `r = 0` every pooled claim holds (computed `true`), and at `r = y` it does not
  (`false`). So the bad event is inhabited, the bound `1/|E|` is attained, and the error
  cannot be lowered to zero.
- Round 2 is the check together with `Seam.pub` of the output.

`toFun_empty` ties round 0 to the input relation, `toFun_full` ties round 2 to the verifier's
verdict, so the state function is not free to be chosen conveniently.

### The error bound

`publicInput_rbr` (`:464-487`) proves `Pr[…] ≤ ↑(1 / |E|)` in `ℝ≥0∞`, in the form of ArkLib's
`rbrKnowledgeSoundnessWorstCaseWith` (`RoundByRound.lean:553-568`): every fixed prefix, the
fresh challenge only, the event quantified over the intermediate witness. It is proved for
every instance and every `sent`, so it is independent of the number of lines as claimed.
Nothing is proved only of the toy that is claimed in general.

### Degenerate parameters

All are covered by the general theorems; each was also computed on the toy.

| Case | Behaviour | Verdict |
| --- | --- | --- |
| `sent = 0` | the prover sends `[]`; the line is still pooled | sound, complete |
| `sent` above the number of lines | as `sent` = the number of lines | sound, complete |
| no public line | both seams coincide; no bad challenge | sound, complete |
| duplicate lines | a claim is pooled twice | sound, complete |
| a line with cells `0, 0` | its value is `0` at every challenge | sound, complete |

### Hypotheses are satisfiable

`Seam.table toy` is inhabited by the honest stack at statement `1` with no received claim
(`Spine.lean:59` and `aux := True`). `publicInputSecurity toy 1` typechecks (test `:212`).

### A1 (low). `publicInputOut` silently drops a claim on a short list

`PublicInput.lean:145-147`. The sent values are paired with the lines by `List.zipWith`, which
stops at the shorter list.

Concrete failure, computed: `(publicInputOut toy 1 stmt1 y []).2.columns.length` is `0`. The
one public line's claim is gone, and the output is inside `Seam.pub` for every stack. Only the
check stands in the way (`publicInputCheck toy 1 stmt1 y []` is `false`).

No theorem is affected: every theorem reaches `publicInputOut` behind the check. The hazard is
for the consumer. The blueprint (`:963-964`) says the check and `publicInputOut` "are
computable definitions, and Layer 12 reads those". A compiled verifier that calls
`publicInputOut` on a list decoded apart from the one it checked pools nothing for a line and
accepts a stack that violates it.

Fix: H1 below. The verifier pools `pooled`, which does not take the sent values and cannot
drop a claim. The two verdicts are equal for every list of sent values (proved in the
prototype), so nothing observable changes.

### A2 (low). `sent` is fixed by no statement and no test

`PublicInput.lean:124-125`. `publicInputSecurity I sent` and `publicInputComplete I sent` hold
for every `sent`. The parameter is therefore irrelevant to security and shapes the transcript
only. It is a parameter of the phase, not of the instance, and "for leanISA `sent` is `2`"
(`:30`) is prose.

Concrete failure: the adaptor builds `Phases` with `publicInputPhase I 3`, or `0`. Every
theorem still holds and every test still passes. The transcript now carries three scalars, or
none, where both pinned verifiers read two (`cpu/mod.rs:747-749`, `verifier.py:1399`). The
error surfaces in Layer 12, far from its cause.

The mechanism is safe for every instance, and faithful for leanISA provided the lines are
listed `mem_0, mem_1, mem_2`. What is missing is the binding.

Also missing: acceptance test 10 (`protocol-blueprint.md:1201-1203`) names as its witness "the
Layer 8 mutation with a nonzero `mem_2` at cell 0 and the third claim dropped". The test file
has a two-line toy with one value sent, a second line with cells `(1, 1)`, and a mutation of
cell 1 (`:132-161`). leanISA's shape, three lines with `sent = 2` and a third line with cells
`(0, 0)`, is exercised nowhere.

Fix: add the test in leanISA's shape (Tests to add, 1). Then either record `sent` with the
lines, as a field of the instance, or have the adaptor define it once next to `publicLines`
with a guard.

### A3 (observation). Several tests restate definitions

`tests/LeanerVMTests/Protocol/PublicInput.lean`. These pass for any definition that unfolds to
itself and would not fail if the definition were wrong:

- `:125-128` re-invokes `publicInputOut_of_check` at the toy;
- `:166-176`, `:179-187` are `rfl` on the phase's fields;
- `:192-209` are `Iff.rfl` on the three rounds of the state function.

They pin the shape against an accidental edit, which has some value, but they are not
evidence of meaning. The `#guard`s are. `:100` repeats `:77`.

The seam-level bad event is not guarded: the file shows that the check passes at `r = 0` on
`badLine` (`:96`) and not that the pooled claim then holds of it.

### A4 (observation). The message type is wider than two scalars

`PublicInput.lean:87`. The prover's message is a `List E` of any length; the specification's
is two scalars. The length is enforced by the check alone. Layer 12 must serialize exactly
`sent` scalars with no length prefix, which the type does not say.

### Pass A, clean

The schedule, the check equation and the claims match the expectation written from the tex.
Completeness and knowledge soundness are both stated and both proved. The extractor is a
computable definition. No hypothesis is stronger than the seam it comes from. The trust
closure is clean and the layer rule holds.

## Pass B: fidelity

### The enumeration

The expectation from `08-end-to-end-protocol.tex:27-33` and `:80-85`, against the Lean:

| Item | Specification | Lean | Match |
| --- | --- | --- | --- |
| challenges | one, `r_m ∈ E`, first | one, `E`, round 0 | yes |
| prover messages | `c_0, c_1` | a list of `sent` values | yes at `sent = 2` |
| check equations | two, `ℓ ∈ {0, 1}` | `sent` | yes at `sent = 2` |
| the equation | `(1 + r)·m⁰_ℓ + r·m¹_ℓ` | `lineValue`, `:108-109` | yes |
| claims pooled | three | one per line | yes at three lines |
| top limb | value `0`, no scalar | computed, `0` on cells `0, 0` | yes |
| point | `(r_m, 0, …, 0)` | `linePoint`, `:51` | yes |
| error | `1/|E|` | `publicInputError`, `:100` | yes |

No check of the specification is omitted and none is added.

**The point and the bit order.** `(r, 0, …, 0)` is the line through cells 0 and 1 only if
coordinate 0 is the low bit of the cell index. That is proved, not assumed:
`eval₂Mle_linePoint` (`:71-80`) is a theorem about CompPoly's `eval₂Mle`, for every `n ≥ 1`,
and the test file's `:48-52` separates the two orders on a table of two variables. It agrees
with the specification ("bits low first", `08:9`), with `Column`'s convention
(`Protocol/Field.lean:64`), and with both pinned verifiers (`cpu/mod.rs:676`, `point[0] = r`).
The toy has log-height 1, where the two orders coincide, so the phase's own tests on the toy
could not detect a wrong order; the theorem and the two-variable guard do.

**`1 + r` and `1 - r`.** The check is written with `1 + r` as the specification writes it; the
line identity is proved with `1 - r`; they are joined by `CharTwo.sub_eq_add` (`:198`,
`:211`). Correct in characteristic two, and named.

**The pool order.** The roadmap's order is bus claims, then table claims, then the three
public-input claims (`protocol-blueprint.md:318`). The Lean pools the received claims, then
the lines in the order of `I.publicLines` (`:121-122`, `:145-147`). `finish_claims`
(`cpu/mod.rs:656-667`) and `bind_pi_claim` (`:674-682`, order `MEM_LO, MEM_HI, MEM_TOP`) agree,
and the citation is exact.

**The honest prover.** The Lean's evaluates its own columns (`:133-136`). The pinned prover
computes the two values from the public words (`cpu/mod.rs:611-613`). On the input seam the
two are equal. See H2.

### B1 (medium). The two checks are not equivalent at a fixed challenge

`docs/roadmap/protocol-blueprint.md:968-971`, and `docs/roadmap/protocol-status.md:358-365`
(finding F17). Both say of the specification's per-limb check and the Rust's combined check
`c_0 + Y·c_1 = interp(pi_0, pi_1, r)`:

> The per-limb equations imply the combined one. The converse fails on the scalars alone,
> which range over `E`, and holds once the scalars are evaluations of `K`-valued columns,
> since `1, Y` are independent over `K`.

The last clause is false. The scalars are evaluations at a point of `E`, so they are in `E`
even when the columns are `K`-valued, and `u_0 + Y·u_1 = 0` does not give `u_0 = u_1 = 0` for
`u_ℓ ∈ E`. Independence of `1, Y` over `K` applies to the cells, not to the values at `r`.

Concrete failure, checked by computation. Public words zero; `mem_0 = [0, 1]` and
`mem_1 = [1, 0]`, all cells in `K`, so the stack violates the public input in both low limbs.
The true evaluations are `c_0 = r` and `c_1 = 1 + r`. At the challenge `r* = y / (1 + y)`,
which is neither `0` nor `1`:

| Check | Result |
| --- | --- |
| the Rust's, `c_0 + y·c_1 = 0` | `true`: accepts |
| the specification's, `c_0 = 0` | `false`: rejects |
| the specification's, `c_1 = 0` | `false`: rejects |

What is true: each check has at most one bad challenge for a given bad stack, and they are
not the same one. The text before this change said exactly that ("They are not the same
challenge by challenge (each has at most one bad `r`, not the same one)", visible in
`git diff --cached`). The edit replaced a correct sentence by an incorrect one.

Why it matters. The documents assign the reconciliation to Layer 12. On transcripts the Lean
check is strictly stronger: for any `t ≠ 0` the Rust accepts `(c_0 + y·t, c_1 + t)` and the
Lean rejects it. Both pinned verifiers use the combined check (`cpu/mod.rs:752-755`,
`verifier.py:1400`). So `publicInputSecurity` is a theorem about the specification's verifier,
and the deployed verifier, which accepts more, needs its own argument. A Layer 12 author who
believes the quoted sentence will expect "Rust accepts iff Lean accepts" to be provable. It is
not.

The conclusion the documents draw, that both checks give the error `1/|E|`, is true. It was
checked on paper, not in Lean: with `A, B ∈ E` the two-limb differences at cells 0 and 1, the
combined equation is `A + r·(A + B) = 0`, of degree one in `r`, and `A = 0` exactly when both
limbs agree.

Fix: in both places restore the earlier sentence, and state the consequence: the phase proves
the specification's verifier; the pinned verifiers accept strictly more transcripts; their
knowledge soundness at `1/|E|` is a separate lemma owed by Layer 12. Pin the fact with a test
(Tests to add, 5).

### B2 (low). Schwartz-Zippel is cited as Lemma 5.2; at the pin it is Lemma 3.8

`docs/roadmap/protocol-status.md:388`: "error `1/|E|` by Lemma 5.2's degree-one argument".

§8.2 cites `Lemma~\ref{lem:sz}` (`08:33`), which is `03-proving-primitives.tex:51`.
`preamble/theorems.tex:4-15` numbers every environment on one counter within the section, and
`lem:sz` is the eighth in section 3: Lemma 3.8. The count is cross-checked by `def:ipcs`, the
thirteenth, which the spine cites correctly as Definition 3.13.

Lemma 5.2 is `lem:gp`, "a product identity is a multiset identity", and the same documents use
"Lemma 5.2" for it (`protocol-status.md:242`, `protocol-blueprint.md:299`, `:842`, `:863`).

Concrete failure: a reader who follows the citation finds the grand-product lemma, which has
no degree-one argument. Fix: "Lemma 3.8 (Schwartz-Zippel)".

### B3 (low). Six slips in the changed documents

- `protocol-status.md:355`: the environment finding after E13 is numbered E17. E14, E15 and
  E16 do not exist.
- `protocol-status.md:346-351` (E12) names `(publicInputVerifier I)` and
  `(publicInputPhase I)`. Both take `I sent`; the text is left from the first build.
- `protocol-status.md:389`: `Prover.run_of_verifier_first` is at `Execution.lean:642`, not
  `:641`.
- `protocol-status.md:387`: the range `08-end-to-end-protocol.tex:27-35` runs into the next
  subsection; §8.2 is `:27-33`.
- `protocol-status.md:5`: "checked on 2026-09-28", in a file whose decision 15 and findings
  E17 and F17 are dated 2026-09-29.
- `protocol-blueprint.md:958`: "the pool order of Layer 10". Layer 10's section (`:1009-1056`)
  states no order; the row "Claim pool order" of Pinned conventions (`:318`) does.

### Citations checked and found exact

`cpu/mod.rs:745-755` (the challenge, the two scalars, the combined check);
`cpu/mod.rs:656-667` (`finish_claims`); VCVio `simulateQ_optionT_bind_run` `:49` and
`simulateQ_optionT_failure` `:214`; VCVio `probEvent_uniformSample` `:225`; ArkLib
`Fin.induction_two` `:93`, `Reduction.support_run_pure_verifier` `:343`,
`Reduction.run_of_prover_first` `:663`, `perfectCompleteness_of_run_support` `:193`,
`KnowledgeStateFunction` `:164`, `rbrKnowledgeSoundnessWorstCaseWith` `:553`, `GuardedForm`
`:112`; CompPoly `evalMleStep` `:467`, `evalMleLayer_get` `:482`, `evalMle_succ` `:512`.
`evalMle_append_boolVec` does not exist in the tree; the documents say "once Layer 1 lands",
which is accurate.

### Pass B, clean

Nothing historical is carried: no Poseidon, no KoalaBear, no LogUp. The fields are `K` and `E`
of `Parameters/Field.lean`. The Lean matches neither verifier line for line, and its check is
the specification's rather than the Rust's, which is the right sign for Category A work.

## Pass C: hygiene

The two Lean files are clean on the convention the user named. A search for roadmap
bookkeeping (layer, hole, `P5`, acceptance test, decision, ledger, finding, target ids)
finds nothing in either file. No line exceeds 100 characters. Docstrings are one to three
lines; the three longer ones record durable constraints (`:97-99`, `:373-375`, `:454-456`).
The header comment, `module`, the imports, the module docstring, the namespace and the
`public section` are in the order `CONTRIBUTING.md` asks. `Mathlib.Algebra.CharP.Two` is a
plain `import`, correctly. Section headings are Mathlib-style. There is no dead code.

### C1 (low). Fragile proofs, declared the template for three more phases

`protocol-status.md:117-125` says of this module: "Its proofs are the template for P1, P3 and
P7". Three of them depend on facts that no statement fixes.

**`publicInput_run_support`, `PublicInput.lean:333-349`.** An unscoped `simp … at hx` (`:336`)
is followed by `obtain ⟨r, -, hx⟩ := hx`, then `split at hx`, then a second unscoped
`simp at hx` (`:341`) followed by `subst hx`. Read with `lean_goal`, the hypothesis after
`:336` is

```text
∃ i ∈ support (liftM (liftM (query ⟨⟨0, h0⟩, ()⟩))),
  x ∈ support (Option.elimM (liftM (if publicInputCheck … = true then … else failure).run).run
    (pure none) fun x ↦ Option.map … <$> x.getM.run)
```

The next four tactics need exactly that shape: one existential over the support, one `if`.
Moreover the check inside it is stated at
`Transcript.concat (honestValues …) (Transcript.concat i default) 0`, not at `r`, so
`absurd hcheck hneg` (`:349`) closes only because that term reduces to `r` by unfolding
`Transcript.concat`.

**`publicInputVerifier_toVerifier_verify`, `:280-305`.** `hq₀` is closed by `rfl` through
`simulateQ`, `simOracle2` and `liftM`; the goal is restated whole by `change` (`:299-304`).
`queryValues` (`:237`) builds its query by `by change Unit; exact ()`.

**`publicInputStateFunction.toFun_full`, `:409-434`.** Twenty-six lines, two `change`s, two
unscoped `simp … at hy`. It is the third and fourth copy of one argument: the same block is
`SendOracle.lean:162-173` and `PassThrough.lean:121-126`.

What was verified is the dependence, by reading the goals. That these break at the next pin
is a prediction; it could not be tested without moving the pins. The status file plans that
move (`:129-131`: Lean 4.34, ArkLib 246 commits ahead). Each of these proofs will then need
repair, in this module and in every copy.

Fix:

1. H5: one lemma in `ToArkLib` for every guarded verifier. Prototyped and proved; `toFun_full`
   becomes two lines here and can in the two spine components.
2. H6: one shared embedding for "the output oracles are the input oracles", with its lemma.
   Prototyped; it applies to this verifier and to the pass-through by `rfl`.
3. For completeness, a lemma on the run of a guarded verifier after a verifier-first
   schedule, stated once in `ToArkLib`. The survey record (`protocol-status.md:371-376`) says
   `ToArkLib/VerifierFirst.lean` was deleted in the rebuild with its one consumer; this is
   the place for its successor. Not prototyped.
4. Replace the unscoped `simp … at` by `simp only` with the lemma list `simp?` reports.

### C2 (low). Ten unprefixed public names in `LeanerVM.Protocol`

`linePoint`, `lineValue`, `claimAt`, `lineClaim`, `pooled`, `expectedValues`, `honestValues`,
`queryValues`, `line_challenge_unique`, `bad_challenge_unique` sit directly in
`LeanerVM.Protocol`. The spine prefixes its top-level names (`commitSpec`, `commitDef`) or
namespaces them (`Component.*`, `Phase.*`, `Seam.*`, `Toy.*`). The phase's own prefix is also
split: `pubSpec` and `pubWitMid` against `publicInput…`.

Concrete failure: the opening phase, written on this template, defines its own `pooled`,
`honestValues` or `queryValues` in the same namespace, and the declaration is rejected as
already declared. The rename then lands in this module, after it has consumers.

Fix: keep `publicInputPhase`, `publicInputComplete`, `publicInputSecurity` at top level, as
the blueprint's interface names them, and move the rest into `namespace PublicInput`.

### C3 (low). The module docstring has no pin and no provenance

`PublicInput.lean:14-39` cites "Specification §8.2" with no file and no revision.
`CONTRIBUTING.md:119-121` asks that claims be bound to an exact revision, and
`Parameters/Field.lean:16-19` shows the form. The spine's files omit it too, so this is
partly inherited.

Two statements are missing that a reviewer needs:

- how the module was written. `Instance.lean:39` says "Written from the specification;
  nothing here transcribes Rust". This module says nothing, and the survey record
  (`protocol-status.md:377`) shows `cpu/mod.rs:745-755` was read during the rebuild;
- that the check is the specification's and that both pinned verifiers check one combined
  equation instead. `AGENTS.md` asks a theorem to say whether it describes deployed
  behaviour. This one does not describe it, and only the roadmap says so.

Fix: three lines in the module docstring: the tex file, its lines and the pin; "written from
the specification; the Rust was read afterwards"; "the pinned verifiers check one combined
equation over `E` (`cpu/mod.rs:752-755`), which accepts more transcripts".

### C4 (observation). Generic lemmas kept in the phase module

`evalMle_of_forall_eq_zero` (`:54-66`, the extension at the zero point is cell 0) and
`card_filter_le_one` (`:457-460`) are facts about CompPoly and about `Finset`, not about the
protocol. The convention "Generic code" (`protocol-blueprint.md:323`) places such material
under `ToCompPoly/`. The author's stated reason, "a special point chosen by the protocol is
not upstream material", covers `linePoint` and not these two. Both are private, so the cost is
small. The note on the universe of `emptySpec` (`:373-375`) is its fourth copy, after
`Component.lean:96-97`, `PassThrough.lean:101-102` and `SendOracle.lean:131-132`.

## Audit surface

### Every declaration of `LeanerVM/Protocol/PublicInput.lean`

Classes: **L** load-bearing (in the statement of a top-level result, or consumed by later
work); **S** supporting; **P** proof help.

| # | Line | Declaration | Visibility | Class | Proposal |
| --- | --- | --- | --- | --- | --- |
| 1 | 51 | `linePoint` | public | L | keep |
| 2 | 54 | `evalMle_of_forall_eq_zero` | private | P | keep |
| 3 | 71 | `eval₂Mle_linePoint` | public | S | keep |
| 4 | 87 | `pubSpec` | public | L | keep |
| 5 | 89 | instance, `OracleInterface` | public | L | keep |
| 6 | 93 | instance, `SampleableType` | public | L | keep |
| 7 | 100 | `publicInputError` | public | L | keep |
| 8 | 108 | `lineValue` | public | L | keep |
| 9 | 112 | `claimAt` | public | S | delete, H1 |
| 10 | 116 | `lineClaim` | public | L | keep |
| 11 | 121 | `pooled` | public | L | keep |
| 12 | 128 | `expectedValues` | public | L | keep |
| 13 | 133 | `honestValues` | public | L | delete, H2 |
| 14 | 139 | `publicInputCheck` | public | L | keep |
| 15 | 145 | `publicInputOut` | public | L | delete, H1 |
| 16 | 150 | `publicInputOut_of_check` | public | S | delete, H1 |
| 17 | 161 | `lineClaim_holds_iff` | public | P | private, H3 |
| 18 | 172 | `line_challenge_unique` | public | P | private, H3 |
| 19 | 193 | `honestValues_eq_expectedValues` | public | P | delete, H2 |
| 20 | 203 | `pooled_mem_pub` | public | P | private, H3 |
| 21 | 217 | `publicInputProver` | public | L | keep |
| 22 | 235 | `queryValues` | public | P | keep |
| 23 | 241 | `publicInputVerifier` | public | L | keep |
| 24 | 255 | `publicInputPhase` | public | L | keep |
| 25 | 265 | `publicInput_materializeOutput` | public | P | private, H3 |
| 26 | 273 | `publicInputVerifier_toVerifier_verify` | public | S | keep |
| 27 | 308 | `publicInputGuarded` | public | L | keep |
| 28 | 316 | `publicInputCheck_honestValues` | public | P | delete, H2 |
| 29 | 323 | `publicInput_run_support` | private | P | keep |
| 30 | 353 | `publicInput_complete` | public | S | keep |
| 31 | 362 | `publicInputComplete` | public | L | keep |
| 32 | 371 | `pubWitMid` | public | S | delete, H4 |
| 33 | 376 | `publicInputExtractor` | public | L | keep |
| 34 | 387 | `publicInputStateFunction` | public | L | keep |
| 35 | 438 | `bad_challenge_unique` | public | P | private, H3 |
| 36 | 457 | `card_filter_le_one` | private | P | keep |
| 37 | 464 | `publicInput_rbr` | public | S | keep |
| 38 | 490 | `publicInputSecurity` | public | L | keep |

### The count

| | Before | After H1 to H5 | With H6 |
| --- | --- | --- | --- |
| declarations | 38 | 31 | 30 |
| public | 35 | 23 | 23 |
| private | 3 | 8 | 7 |
| definitions and top-level statements a human must read | 23 | 19 | 19 |

The arithmetic: seven public declarations are deleted (three by H1, three by H2, one by H4)
and five are made private by H3, so `35 - 7 - 5 = 23` public and `3 + 5 = 8` private. H6
then replaces one of the private lemmas, `publicInput_materializeOutput`, by the shared one.

H5 and H6 add two public declarations to `ToArkLib`, each shared by every component, and none
to this module.

The column "After H1 to H5" is not an estimate. The compressed module was written as a
`module` and compiled with `-E warning`: exit 0, no warning. Its `publicInputSecurity` and
`publicInputComplete` have the same type as the reviewed ones: the same schedule, the same
relations, the same error. The prototype dropped the docstrings, so its length is not
comparable and no saving in lines is claimed. H6 was compiled separately, against the
verifier as it is written, and not inside that module.

### The compressions

**H1. One output. Delete `claimAt`, `publicInputOut`, `publicInputOut_of_check`.**

The edit: in `publicInputVerifier`, in `publicInputProver.output`, in `publicInputGuarded.out`
and in round 2 of the state function, write `pooled I s r` for `publicInputOut I sent s r cs`.
Define `lineClaim` directly as `⟨l.col, linePoint (I.κ l.col) r, lineValue I r l⟩`.
`toFun_next` becomes `exact h.2`.

The verdict is unchanged. Proved in the prototype, for every list `cs`:

```lean
(if publicInputCheck I sent s r cs then pure (publicInputOut I sent s r cs) else failure) =
  (if publicInputCheck I sent s r cs then pure (pooled I s r) else failure)
```

It removes A1, and the module stops carrying two definitions of the pool joined by a lemma.

Cost, which the user should weigh. Decision 15 (`protocol-status.md:218-224`) records that
"the claims are pooled at the sent values", on the user's instruction. H1 keeps everything
that instruction names as the transcript: the challenge, the prover's values, the check that
rejects. It changes which of two equal values is written in the output. If the instruction
meant the output's text and not only the transcript, H1 is declined and A1 is met instead by a
guard theorem. The test file's `:113-128` would be rewritten over `pooled`.

**H2. One list of sent values. Delete `honestValues`, `honestValues_eq_expectedValues`,
`publicInputCheck_honestValues`.**

The edit: the prover sends `expectedValues I sent st.2.1.1.1 st.1`. The check on it holds
with no hypothesis, by `decide_eq_true rfl`.

The honest prover then reads nothing of the stack, which is what the phase needs: the values
are functions of the public words and the challenge. The specification says what the values
claim, not how they are computed.

Cost: the tests that model "a prover that sends its true evaluations" through `honestValues`
on a bad stack (`:84-96`, `:105-106`, `:122`, `:150-161`) evaluate the column directly. The
`Decidable` instance they need is already in the file.

**H3. Five lemmas private: `lineClaim_holds_iff`, `line_challenge_unique`,
`pooled_mem_pub`, `publicInput_materializeOutput`, `bad_challenge_unique`.**

None is used outside the module or by the tests.

Three others cannot be private, and this was learned from the compiler, not assumed:
`publicInput_complete`, `publicInput_rbr` and `publicInputVerifier_toVerifier_verify` are
referenced from the bodies of exposed definitions, and Lean rejects that ("a private
declaration … exists but would need to be public to access here").

Cost: the status file names `bad_challenge_unique` in the P5 row (`:69`) and in the review
budget (`:110-114`); both would name `publicInput_rbr` instead.

**H4. Delete `pubWitMid`; write `fun _ ↦ Unit` in place.** `PassThrough.lean:104` already
does. Cost: none.

**H5. One lemma for `toFun_full`, in `ToArkLib`.**

```lean
theorem guarded_of_probEvent_pos (G : V.GuardedForm) (init) (impl) (stmt) (tr)
    (P : StmtOut → Prop)
    (h : Pr[P | OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] > 0) :
    G.check stmt tr = true ∧ P (G.out stmt tr)
```

Proved in the prototype on the three standard axioms. `publicInputStateFunction.toFun_full`
becomes `guarded_of_probEvent_pos (publicInputGuarded I sent) init impl stmt tr _ h`, in place
of twenty-six lines. Its use in `sendStateFunction` and `passThroughStateFunction` was not
prototyped.

**H6. One embedding for "the oracles are kept", in `ToArkLib`.**

`keepOracles : OracleOutputEmbedding OStmt pSpec.Message OStmt`, and
`materializeOutput_keepOracles`. Proved (it depends on `Quot.sound` alone), and checked to
apply by `rfl` both to `publicInputVerifier` and to `Component.passThroughVerifier` as they
are written. It replaces the record at `PublicInput.lean:248-251` and
`PassThrough.lean:48-51`, and the lemmas at `PublicInput.lean:265-269` and
`PassThrough.lean:61-65`. Every later phase keeps the stack and would use it.

### Considered and not proposed

- Removing `sent`. It restores the first build, in which the prover sends nothing, and the
  phase then no longer has the specification's transcript.
- Making `eval₂Mle_linePoint` private. It is the statement that gives `linePoint` its
  meaning, and the one place the bit order is proved.
- Inlining `queryValues` into the verifier. Not attempted: the verdict's proof names it.

### What downstream work has to understand

- **The opening phase** sees `PubOut` and `Seam.pub` only. Nothing of this module reaches it.
- **The adaptor** must choose `sent` and the order of the lines. That is new, and A2 is the
  cost of leaving it unrecorded.
- **The compiled verifier** reads `pubSpec`, `publicInputCheck` and the output. After H1 the
  output does not depend on the message, and the verifier reads two functions of which one
  cannot be misused.

No new public definition duplicates a spine definition. The duplication is in the proofs
(H5, H6).

## Tests to add

1. (A2) Acceptance test 10 in leanISA's shape: three lines, `sent = 2`, a third line with
   cells `(0, 0)`; a stack with a nonzero cell 0 in the third column passes the check and
   fails the third claim, and the pool without the third claim accepts it.
2. (A3) On `badLine` at `r = 0` every pooled claim holds, and at `r = y` one does not: the
   bad event at the level of the seam, and the evidence that the bound is attained.
3. (A2) `sent = 0`, and `sent` above the number of lines.
4. (A1, if H1 is declined) a theorem that when the check passes the output holds as many
   claims as were received plus one per line.
5. (B1) At `r* = y / (1 + y)`, with `c_0 = r*` and `c_1 = 1 + r*`: the combined equation
   holds and the per-limb check rejects. It keeps the false sentence from returning.

## Not checked

- That the pinned verifiers' combined check is knowledge sound at `1/|E|`: argued on paper
  under B1, not proved in Lean.
- That the proofs of C1 break at the next pin. Only their dependence on the `simp` normal
  form and on unfolding `Transcript.concat` was verified.
- H5 applied to the two spine components, and the completeness-side lemma of C1 (3).
- `queryValues` inlined.
- The trackers on GitHub (issue #12, the hole comment). The work is uncommitted and has no
  pull request; no network access was used.
- ArkLib's own proofs. Only the definitions the statements use were read.
