# Review: the deployed check of the public-input phase (pull request #72)

> An archive of the review of one commit: names, paths and line numbers are that commit's.
> What is accepted from it goes into the code and the status page; this file records what was
> found and why.

Reviewed on 2026-10-05 against branch `feat/protocol-deployed-public-input` at `eb32a66`, whose
base is `main` at `577c50e`. The diff is thirteen commits: four files, 1009 insertions, 18
deletions. With the repository's `adversarial-review` skill. Lean was run: the production
module and the two test modules that import it were built, the kernel axioms of the six new
public results printed, and the three repository scripts run. The findings were applied on the
branch (see the disposition at the end).

Sources read:

- Both changed Lean files in full: `LeanerVM/Protocol/PublicInput.lean` (992 lines) and
  `tests/LeanerVMTests/Protocol/PublicInput.lean` (1121 lines); the unchanged definitions they
  are stated over: `Spine/Seams.lean` (`table`, `pub`, `ColumnClaim.Holds`), `Spine/Instance.lean`
  (`PublicLine`, `PublicLinesHold`, `aux`), `Spine/Errors.lean` (`pubSpec`, `pubError`, `overE`),
  `Parameters/Field.lean` (`E`, `y`, `E.ofLimbs`, `ofLimbs_eq`, `limb_ofLimbs`).
- leanVM at the pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`, read from the commit object
  (the sibling checkout is at `7f80c641` and has moved; see *Context* below):
  `crates/lean_vm/src/cpu/mod.rs:130-145`, `:604-620`, `:656-684`, `:711-760`;
  `crates/primitives/src/multilinear.rs:39-48`; `crates/primitives/src/field/gf2_64x3.rs:1-50`;
  `python-verifier/verifier.py:216-219`, `:240-245`, `:281-283`, `:1396-1402`;
  `crates/rec_aggregation/guests/aggregate.py:1672-1689`;
  `doc/leanvm/body/08-end-to-end-protocol.tex:27-33`, `:80-85`.
- ArkLib `7653a901`: `Security/RoundByRound.lean:165-190` (`KnowledgeStateFunction`),
  `:555-571` (`rbrKnowledgeSoundnessWorstCaseWith`).
- For intent: the blueprint (Layer 8, decisions 22 and 31, the convention *Load-bearing checks*),
  the status page, `docs/leanvm-target.md` (the discrepancy *the public-input check*), the
  pull request body, and the review of the specification phase
  ([public-input-phase.md](public-input-phase.md)).

**Method.** `checkWords` is Category B, so the Rust, the Python and the recursion guest were
read first and an expectation of the equation, the words' limb order, the message and the pool
written down before the Lean definition was checked against it. The phase, its state function
and the theorems are Category A: the expectation was formed from §8.2 at the pin and from the
blueprint's Layer 8 before the Lean was read, and the specification pass asked of each theorem
whether its hypotheses are inhabited, what it would still say if `checkWords` had another shape,
and whether the bound is attained.

## Specification pass: nothing wrong or vacuous

Every new theorem's hypotheses are inhabited by a test, and every statement names an object
defined without the verifier:

- `checkWords_of_check`: `check` accepts `good` on the toy and `expectedValues` on `twoLimbs`
  and `wordsTwo`, where `checkWords` then accepts them too; the converse fails at `rStar` and at
  the message `[y, 1]`, both pinned by guards.
- `accepts_two_challenges`: its two acceptance hypotheses hold of the memory `(1, 1, 0)` at `y`
  and at `y² + 1` (`acceptsAt`), and one challenge is not enough (`(0, 1, 0)` accepted at
  `r = 1`). The theorem is about `E`-arithmetic alone: replacing `checkWords` by another
  Boolean would leave it unchanged, which is the right direction for the substitution test,
  since `bad_challenge_unique_words` is where the check's shape enters. The independence of
  `1` and `y` over `K` is used only to read the limbs back (`pair_challenge_unique`), and the
  mutant `y ↦ 1` is refuted at error one.
- `deployedPublicInputComplete`: `Seam.table` is inhabited on the deployed shape
  (`stmtHonestWords_table`); the honest message passes at `0`, `1`, `y` and `y² + 1`.
- `deployedPublicInputSecurity`: the bound `1/|E|` is the slot's and is attained on `oneBadLimb`
  at `r = 1`, so it cannot be lowered; the state after the challenge is an existential over
  the message, which is the only honest reading when the message is no function of the
  statement and the challenge (the guard at `[y, 1]` shows the check does not decide the pool).

Both halves are present and the pull request classifies the work as T4, proof-system side, with
the Lean phase as the boundary and the Rust and Python left to the transcription and the
differential run. That matches `AGENTS.md`.

One observation, no failure scenario: the sources pool the top limb at the constant `0` and
the phase pools the value computed from the statement. Decision 22 asks that the relation of a
variant to the deployed one be a theorem; here it is a guard on one instance (`threeLimbs`),
and the general statement, that the two pools agree when every unsent line has cells `(0, 0)`,
is left to the adaptor, which is the first consumer that needs it. Recorded, not fixed.

## Fidelity pass: the counts matched

| Artifact | Pinned source | Lean | Match |
| --- | --- | --- | --- |
| The challenge, then the message | `cpu/mod.rs:745` samples `r_pi`, `:747-749` read two scalars; `verifier.py:1398-1399` | `pubSpec`: `V_to_P` then `P_to_V`; `verifierWith` rejects a message of another length than the sent count | yes |
| The equation | `cpu/mod.rs:752-754`: `pi_limbs[0] + Y·pi_limbs[1] = interp(pi[0], pi[1], r)`, with `interp(lo, hi, t) = lo + t·(lo + hi)` (`multilinear.rs:39-41`); `verifier.py:1400`: `poly_eval([c₀, c₁, 0], Y)`, Horner constant first, against `multilinear_eval([h₀, h₁], [r]) = h₀·(1 + r) + h₁·r`; `aggregate.py:1680-1683` | `c₀ + y·c₁ = (1 + r)·w₀ + r·w₁`; `lo + t·(lo + hi) = (1 + t)·lo + t·hi` in characteristic two | yes |
| `Y` | `gf2_64x3.rs:44`: `(0, 1, 0)`, the root of `y³ + y + 1` | `Parameters.y`, `y_pow_three` | yes |
| The words | `l.pi[0]` is `mem[g⁰]`, its `c0` limb the cell of `mem_0`, its `c1` the cell of `mem_1`; `c2` rejected at `cpu/mod.rs:141-142` | `w₀ = E.ofLimbs l₀.cell0 l₁.cell0 0`, `w₁ = E.ofLimbs l₀.cell1 l₁.cell1 0` | yes, with the adaptor to list `mem_0` then `mem_1` |
| The honest message | `cpu/mod.rs:611-613`: `interp_k(pi[0].cℓ, pi[1].cℓ, r) = ofK lo + r·ofK(lo + hi)` | `expectedValues`: `(1 + r)·ofK cell0 + r·ofK cell1` | yes |
| The pool | `cpu/mod.rs:746`, `:674-682`: `[c₀, c₁, F192::ZERO]` on `mem_0, mem_1, mem_2` at `(r, 0, …, 0)` | `pooledFrom`: `c₀`, `c₁`, then `lineValue r l₂` for the unsent line | declared; equal where the unsent line is `(0, 0)`, which the public words give; the constant is refuted at error one on `topOne` |

One equation on each side; two scalars read on each side; three claims pooled on each side.
The citation `cpu/mod.rs:752-755` in the module and the status page covers the check at
`:752-754` and its closing brace; `docs/leanvm-target.md` says `:750-755`. Both find it; neither
was changed.

**Context, not a finding.** The sibling leanVM checkout at `7f80c641` no longer has this
check: §8.2 there says the prover sends nothing and `verifier.py` computes the three claims
itself. The pull request is bound to the pin, where the message and the check exist, and the
drift workflow is where that movement is reported. When the pin moves, `deployedPublicInputPhase`
becomes the phase of a verifier that no longer runs, and the specification phase's design, which
decision 31 already rejects for pooling computed values, becomes the deployed one.

## Hygiene pass

Two findings, both low, both applied:

1. `deployed_complete` was a verbatim copy of `complete` with `deployedGuarded` for `guarded`
   and `accepts_checkWords_of_check` for `accepts_check_iff`: twenty-two lines a reader had to
   diff to confirm they were the same. Now one private `complete_with`, over the check, proves
   completeness of every verifier of the phase's shape whose check accepts the specification's
   values, and both public theorems are one line. Their statements are unchanged.
2. The docstring of `bad_challenge_unique_words` narrated its case split, which the module
   docstring already carries; the docstring of `accepts_two_challenges` ended on a sentence the
   tests pin. Both trimmed.

Observations, left as they are:

- `rbr` and `deployed_rbr` share twelve lines of scaffolding around a six-line core. A generic
  lemma would need the transcript shape of ArkLib's event stated once more; the saving is small
  and the core is what a reader looks for.
- `guarded` and `deployedGuarded` could be inlined into the four phase structures, two public
  definitions fewer; `guarded` is on `main` and the pair reads better than one of them.
- `bad_challenge_unique_words` is ninety lines; the case of two sent lines could be its own
  lemma taking the filtered list as a hypothesis.

Clean: the three repository scripts; the aggregate imports (no module added); the layer DAG
(no import changed); naming; module shape; the docstring of the module and of the tests moved
with the code; the status page's *owes* entry names every deviation from the blueprint's
signatures and what the adaptor is to prove.

## Disposition

| Finding | Disposition | Commit |
| --- | --- | --- |
| One completeness proof for both verifiers | met | `549a6b4` |
| Two docstrings trimmed | met | `549a6b4` |
| The pools' agreement as a theorem | recorded, for the adaptor | — |

The test file passes unmodified against the edited module; the kernel axioms of `complete`,
`deployed_complete`, `publicInputComplete`, `deployedPublicInputComplete` and
`deployedPublicInputSecurity` are the kernel's three.
