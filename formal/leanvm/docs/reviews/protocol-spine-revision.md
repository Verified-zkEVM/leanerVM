# Review: the spine at the slots' schedules and errors (pull request #65)

> An archive of the review of one commit: names, paths and line numbers are that commit's.
> What is accepted from it goes into the code, the status page and the blueprint; this file
> records what was found and why.

Reviewed on 2026-10-02 against branch `feat/protocol-revision` at `7b6b234`, whose base is
`feat/protocol-wall-field` at `a4fa81b` (pull request #64). The diff is one commit: 22 files,
2348 insertions, 543 deletions. Read-only, with the repository's `adversarial-review` skill; the
repository was not modified and no Lean was run (the machine is memory limited and nothing below
needed a probe: every finding is a reading of the sources). This file is the only one created.

Sources read:

- Every changed Lean file in full, and the unchanged files they are stated over:
  `Protocol/Field.lean`, `ToArkLib/{GuardedVerdict,KeepOracles,Oracles,InnerProduct}.lean`.
- leanVM at the pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`, fetched from GitHub:
  `crates/lean_vm/src/gkr.rs:247-430`, `leaf.rs:100-170`, `:389-470`, `:864-935`,
  `constraints.rs:240-300`, `cpu/mod.rs:361-390`, `:705-785`, `cpu/layout.rs:350-418`,
  `hash_flock.rs:255-300`, `pcs.rs` (grep), `tables.rs:307-320`,
  `crates/fiat_shamir/src/transcript.rs:280-312`, `crates/flock/src/hash.rs:983-1010`,
  `zerocheck.rs:350-430`, `lincheck.rs:1137-1216`; `python-verifier/verifier.py:406-460`,
  `:635-640`, `:1092-1420`; `doc/leanvm/body/05-arithmetization.tex` (grep),
  `08-end-to-end-protocol.tex:1-140`.
- ArkLib `7653a901` (`.lake/packages/Arklib`): `Security/RoundByRound.lean:424-640`,
  `Security/Implications.lean:180-235`.
- Pull requests #62 (the grand-product argument) and #66 (the strided reader and the pool from
  values sent), for the names they declare or consume.
- For intent: the blueprint (*Pinned conventions*, *The spine*, Layers 5 to 10, *Decisions*),
  the status page, `AGENTS.md`, `CONTRIBUTING.md`.

**Method.** The schedules are Category B (transcribed from the deployed verifiers), so the Rust
and the Python were read first and an expectation of each slot written down before the Lean's
`Spine/Errors.lean` was checked against it. The errors are the blueprint's numbers; each was
checked against the degree it charges where the degree can be read off the source (the
fingerprint, the GKR's rounds and combiners, the table batching, the public line, the Flock
skip and lincheck), and the ring-switching errors were taken as the blueprint's, owed with its
proof. The specification pass and the fidelity pass were run separately: the specification pass
asked of each theorem whether it is non-vacuous and what it would still say if the slot's
numbers were different.

## Verdict

No theorem is wrong or vacuous, and the master theorems say what the blueprint asks: the two
master theorems are stated for every bundle at the slots' errors, the extracted stack is the
committed message on every transcript, and `piopError_le` is non-vacuous (the toy meets its
hypotheses). The schedules match the deployed verifiers at every slot but one message of the
Flock slot, and the citations behind two slots are wrong. The schedule combinators and the
grand-product argument's schedule are written at `E` inside a leanVM module, which the generic
grand-product argument of pull request #62 cannot consume; this is the largest finding. The
public surface of the whole proof system is 510 declarations, of which about 70 can be hidden or
deleted without changing a statement, and about 40 more with one design change.

## Findings

Ranked most severe first. Each names the pass that found it.

### 1. The Flock slot sends a third value the deployed verifiers derive (fidelity)

`Spine/Errors.lean:508-509` has `say (Vector E 3)` after the zerocheck rounds, and the module
docstring (`:42-43`) says "the three values `v_a, v_b, v_c`". Both deployed verifiers read two
and derive the third: `crates/flock/src/zerocheck.rs:421-422` reads `final_a_eval`,
`final_b_eval`; `python-verifier/verifier.py:1148-1149` reads `v_a, v_b` and sets
`v_c = running + v_a * v_b`. The blueprint's Layer 9 schedule says "two values; one challenge"
(`162 + 2·k_batch` scalars) and lists `v_c = R_zc + v_a·v_b` among the derived encodings that
are "not checks". The module docstring's rule for derived values ("the oracle protocol sends
every coefficient of a round polynomial …") covers round polynomials only, and the pull request's
*Where this differs from the blueprint* does not list this message.

Concrete consequence: the Flock phase (Layer 9) built against this slot must make its verifier
check `v_c = R + v_a·v_b` and the compiled verifier (Layer 12) must prove one more decoding
lemma, for a value that is a definition, not a claim a prover can fail. Either send two values
(`say (Vector E 2)`; `flockRoundsOf` and `flockErrorOf` are unchanged, the test counts too), or
keep three and extend the docstring's rule and the blueprint's Layer 9 to say so. The first is
recommended.

### 2. The schedule combinators and the grand-product schedule are not generic (under-abstraction)

`Spine/Errors.lean:83-408` defines `say`, `draw`, `draws`, `roundSpec`, `roundsSpec`,
`stepSpec`, `stepsSpec`, `oddSpec`, `gkrSpec`, their instances and their errors (`sayError`,
`drawError`, `drawsError`, `roundsError`, `stepError`, `stepsError`, `oddError`, `gkrError`).
Every one of them is written at `E` (`draw E`, `overE`), in a leanVM module, although nothing in
them is leanVM's: a sumcheck round of degree `d` over a field, a layer of a grand-product
argument of radix `2^ρ` at depth `m`, the error `d/|F|` per round. The blueprint's hole table
assigns `gkrError` to the spine and `gkr` to `ToArkLib/GrandProduct.lean`, a generic module.

Concrete consequence: pull request #62's `gkr nside μ leaves : Component.Def … O Unit …` is
generic over `F` and builds its schedule from its own combinators (`SumcheckRound.pSpec F d :
ProtocolSpec 2`, `childrenSpec F nside ρ`, `sampleSpec := ⟨!v[.V_to_P], !v[C]⟩`, a
`passThrough` prefix of zero rounds). It cannot import `Spine/Errors.lean` without becoming
leanVM-specific, and the bus phase (Layer 6) needs its schedule to *be* `gkrSpec 3 I.μBus`
definitionally to fill the slot `busSpec I`: two constructions of the same schedule are not
definitionally equal (`!p[] ++ₚ s` against `s`, `⟨!v[.V_to_P], !v[C]⟩` against
`⟨fun _ ↦ .V_to_P, !v[C]⟩`), and ArkLib has no transport of a verifier along a schedule equality.

Recommended shape: a `ToArkLib/Schedule.lean` with the combinators over
`(C : Type) [SampleableType C]` and errors taking the unit error as a parameter (`ε : ℝ≥0`,
instantiated at `overE 1`), with their sum lemmas as the API; #62 consumes them; `Spine/Errors.lean`
keeps `overE`, the six slots, `piopSpec`, `piopError` and `piopError_le`. The same move settles
the collision between #62's `sampleSpec` literal and #65's `draw`.

### 3. `Verifier.not_rbr` cannot refute a check that later challenges follow (under-abstraction)

`ToArkLib/Refutation.lean:108-131`. The theorem requires `hlater : ∀ j, i.1 < j → pSpec.dir j =
.P_to_V` and reaches the state function at round `i + 1` through acceptance
(`exists_toFun_take`, which walks `toFun_next` over prover rounds only). The generic fact is the
step the proof calls `hall`: if after every challenge `c` some witness makes the state function
true at `i + 1` while it is false for every witness at `i`, then `1 ≤ ε i`. That statement needs
neither `hlater` nor `hacc`, and it is what a refutation of a check in the middle of a phase
needs.

Concrete consequence: the load-bearing-checks convention asks for a refutation of every check.
The grand-product argument's layer check (`gkr.rs:395-397`, `:412-414`) is followed by that
layer's combination challenges and the next layer's combiner; the Flock zerocheck's terminal
identity is followed by the lincheck's `α`. For both, `hlater` is false and `not_rbr` does not
apply; only the last check of a phase can be refuted with it. Split the theorem: the certain-escape
lemma (generic) and the acceptance corollary under `hlater` (the public-input phase's case).

### 4. Three citations point at the wrong source (documentation)

- `Spine/Instance.lean:266-267` (`μBus`): "stacked largest first at aligned offsets with no floor
  on the depth; the three trees share it (`layout.rs:354-415`)". At the pin there is no
  `crates/lean_vm/src/layout.rs`; `cpu/layout.rs:354-415` is the bus block wiring (the state,
  memory and bytecode blocks, then each table's flushes and count blocks). The depth
  `μ = ⌈log2 Σ 2^κ_b⌉` with no floor is `leaf.rs:149-156`; that the three trees share it is not a
  layout fact but two assertions and one assignment, `leaf.rs:123-146` (`push.mu == pull.mu`,
  `count.mu <= push.mu`) and `leaf.rs:876-880` (`count_lay.mu = push_lay.mu`). See finding 8 for
  what that means for the instance.
- `Spine/Errors.lean:40` (Flock): `hash_flock.rs` holds no verifier (it re-exports
  `flock::hash`, `hash_flock.rs:44-46`); the reads are `crates/flock/src/hash.rs:983-1010`,
  `zerocheck.rs:350-430` and `lincheck.rs:1137-1216`. The six ring-switching challenges are
  outside the cited Python range: `verifier.py:1314-1347` (`ring_switch`), and in the Rust they
  are drawn inside the stacked opener, not the Flock reduction (`pcs.rs:128`,
  `cpu/mod.rs:767-768`). The pull request body repeats the range.
- `Spine/Errors.lean:36` (the table sumcheck): `cpu/mod.rs:726-735` is `ξ` and the derived
  target only; the rounds (`next_round_poly(4, …)`, one challenge each) and the one value per
  committed column of every table are `constraints.rs:243-291`.

### 5. The table error sharpens the specification without saying so (documentation)

`Spine/Errors.lean:50-52` and `tableError` charge `B + 2` on `ξ`; the specification charges
`nside + B = B + 3` for the `ξ`-batching (`05-arithmetization.tex:155`). The Lean is right (the
batch is a polynomial of degree `B + 2` in `ξ`, `B + 3` terms) and matches the blueprint, but a
reader checking the docstring against §5.5 sees a mismatch. One clause ("the degree of the batch,
one less than the specification's count of powers") settles it.

### 6. Stale sentence in `Stack.lean` (documentation)

`Protocol/Stack.lean:23-24`: "`Blocks.layout` packages the reader, the lift of a point and that
identity as a `Layout`". After this pull request a `Layout` is the lift and one law; the reader
is derived (`Layout.read`), and `Blocks.layout` (`:124-126`) sets `extend` only. The pull
request body says so ("built from the lift alone"); the docstring does not.

### 7. Small documentation slips

- `Spine/Instance.lean:29`: "Three quantities are read off an instance" introduces four kinds
  (`τmax`, `B`, `μBus`, and the claim counts).
- The blueprint's hole table assigns `flockError_le` (a bound `(4·kBatch + 163 + 2^32)/|E|`) to
  Layer 9; this pull request's `sum_flockErrorOf` gives the exact sum
  `(4k + 302 + 2^31 + 2^15)/|E|`, which is stronger. The row and Layer 9's signature are owed an
  update when the blueprint is next edited; the pull request body's deviations list could name
  it.
- The pull request body names no target of `AGENTS.md`'s map. The work is the spine of the proof
  system; one clause saying it feeds T4 through the blueprint's picture would meet the
  requirement.

### 8. The depth of the pull and count trees is an assertion, not a consequence (observation)

`M3Instance.μBus` is `Nat.clog 2 I.pushLeaves`; `busSpec` and `busError` are stated at it for
every instance. The Rust refuses to run when the pull tree is deeper or the count tree is deeper
than the push tree (`leaf.rs:123-146`), and `prove_product_triple` asserts every lane fits
`2^μ` (`gkr.rs:266-268`). For an abstract instance whose pull side has more leaves than
`2^μBus` the slot describes a protocol the deployed verifier never runs. Not a defect of this
pull request (the instance is trusted data), but decision 30's side conditions of the bus phase
should include "pull and count leaves fit in `2^μBus`" beside `1 ≤ I.d`, or `μBus` should be the
maximum of the three. The `μBus` docstring should say the sharing is enforced, not derived.

### 9. Two smaller under-abstractions (observation)

- `ToVCVio/UniformSample.lean` exposes the `c = 1` case only. The bus phase's `(α, β)` bound
  and the grand-product argument's layer bounds need `c/|α|` from a cardinality bound; VCVio's
  `prEvent_uniformSample_le_div_iff` gives it, and the local file could expose that form beside
  the subsingleton one so no phase restates the coercion.
- `FlockRegion.height : S.τ col.1 = 8 + kBatch` bakes 256-bit blocks into the abstract instance.
  It is the blueprint's choice (decision 25) and is recorded here only.

## What is clean

- **Specification.** `piopError_le` is non-vacuous (the toy has `μBus = 1`, `τmax = 1`, `B = 1`,
  no region, `poolSize = 4`); `piopExtractedStack_eq` holds for every bundle and transcript;
  `piop_perfectCompleteness` and `piop_rbrKnowledgeSoundness` are conditional on the phases only
  and state `rbrKnowledgeSoundnessWorstCaseWith` for the named extractor and state function; the
  existential form is labelled a soundness statement only. Every refutation lemma carries an
  example on a two-round schedule. The master theorems typecheck on the toy with the built
  public-input phase in its slot. The Compose docstring's claim that only
  `rbrKnowledgeSoundness_implies_knowledgeSoundness` is admitted at the pin is right: it is
  `Implications.lean:193-198` (`sorry`), and the two worst-case-to-average implications it
  needs (`RoundByRound.lean:609-640`) are proved.
- **Fidelity of the schedules**, slot by slot, against the Rust and the Python at the pin:
  - the bus: `(α, β)` as one draw (five scalars on the wire, `leaf.rs:876-882`), the two roots
    (`gkr.rs:384-391`, `FirstTwoShared`), the grand-product argument, the boundary values as one
    message. The flat sequence of the grand-product argument is the Rust's: combiner, then per
    layer the rounds, the descendants (twelve scalars, tree by tree), the combination
    challenges and the next combiner; one binary layer first when `μ` is odd; a last combiner
    read by nothing (`gkr.rs:393-430`). Depths `m + 2i` from `m = μ mod 2` match
    `round_count = mu - layer`. Five coefficients per radix-four round, one derived on the wire
    (`transcript.rs:289-309`, `next_round_poly(5, …)`).
  - the table sumcheck: `ξ`, `τmax` cubic rounds (four coefficients, `c₁` derived), one value
    per committed column of every table in table order (`constraints.rs:250-291`,
    `cpu/mod.rs:361-390`).
  - the public input: `r`, then one message (`cpu/mod.rs:745-749`, `verifier.py:1398-1400`).
  - Flock: the `k + 1` sampled coordinates (`hash.rs:983-990` with `equality_tail`,
    `verifier.py:1139`: `log_n − 6 − 7` with `log_n = 14 + k`), 64 values, `z_skip`, `8 + k`
    quadratic rounds, two values (finding 1), `α`, 8 rounds, 64 values, six challenges.
  - the opening: `λ` (`verifier.py:1361`).
  - Errors per challenge against the degrees: `4·2^μ` (Theorem 5.1), `nside − 1 = 2` per
    combiner, `2^ρ` per round, `1` per combination challenge, `B + 2` (finding 5), `3` per cubic
    round, `1` on the line, `127` on `z_skip` (a 128-point interpolant), `2` per quadratic round,
    `3` on `α` (four terms), `J − 1` on `λ`. The ring-switching values are the blueprint's.
  - The claim counts: `boundaryColumns` follows `decompose_formula`'s order (blocks in slice
    order, coordinates in order, a `(column, point)` opened once across the sides,
    `leaf.rs:389-470`); `tableColumns` is one per column of each sumcheck table; the pool is
    the column claims plus one ring-switched claim, so `openingError` charges `poolSize − 1`.
- **Hygiene.** Module docstrings are short and carry the pin; declaration docstrings are one or
  two lines; the layer check, the aggregate imports and the audit are green by inspection
  (`LeanerVM.lean` lists the four new modules once). `docs/dependencies.md` and
  `tests/README.md` moved with the code.

## The audit surface of the whole proof system

Counted on this branch over `LeanerVM/Protocol/` (30 files): 532 declarations, 510 public.
This pull request adds 137 public ones (`Spine/Errors.lean` 111, `ToArkLib/Refutation.lean` 10,
`ToArkLib/ExtractIn.lean` 9, `ToArkLib/FrontVerifier.lean` 7). The largest file is
`Spine/Errors.lean`: 40 of its declarations are named instances for the message interfaces and
challenge samplers of each appended schedule, 19 are sum lemmas.

Reductions that change no statement, in this pull request's files:

| Where | What | Count |
| --- | --- | --- |
| `Spine/Errors.lean` | `private` for the sum lemmas used only by `piopError_le`'s proof (`sum_sayError` … `sum_flockError_le`, `nat_mul_overE`); keep `overE_add`, `overE_mono` as the API; delete `overE_zero` (unreferenced) | 18 |
| `Spine/Compose.lean` | `private` for `zero_lt_piopRounds`, `piopExtractor_readsFirst` | 2 |
| `ToArkLib/ExtractIn.lean` | `private` for `foldToOne`, `foldMid_succ`, `append_extractMid_zero_heq` | 3 |
| `ToArkLib/Refutation.lean` | `private` for `take_succ_eq_concat`, `not_toFun_of_val_eq_zero`, `run_of_guarded`, `mem_support_simulateQ_run'_of_forall`; #66 uses `not_rbr`, `not_rbr_zero`, `probEvent_pos_of_check`, `not_perfectCompleteness_of_reject'` only | 4 |
| `ToArkLib/FrontVerifier.lean` | `private` for `toVerifier_verify` (used by `toVerifier_verify_of_check` and an example) | 1 |
| `Spine/Phase.lean` | delete `Phase.Guarded` (mentioned in the docstring, used nowhere) | 1 |
| `Protocol/Field.lean` | delete `instOracleInterfaceE`, `instOracleInterfaceListE`: dead since `say` and `pubSpec` carry their own `instDefault`; the blueprint's Layer 0 row names them | 2 |
| `ToArkLib/InnerProduct.lean` | delete `innerProductInterface`: `Field.lean`'s `innerProductOracle` restates it on `Column` instead of using it (#64's file, seen from the whole) | 1 |
| `Protocol/PublicInput.lean` | delete the alias `PublicInput.pSpec` (use `pubSpec`); `verifier_verify` is unreferenced and #66 deletes it | 1 |

Thirty-three declarations, without touching a proof. The `To*` files keep their reusable helper
lemmas public by the repository's rule, so none of `Multilinear.lean`'s or `Stacking.lean`'s
unreferenced lemmas is listed; three of them are unreferenced and not obviously reusable
(`cubeIndex_mod`, `boolVec_onesIndex`, `lagrangeBasis_zero_index`) and could go.

One design change: a bundle `Schedule n` (a `ProtocolSpec n` with its two instance families and
its error) with an append on bundles would replace the 40 named instances of `Spine/Errors.lean`
by two generic instance declarations and make each slot one definition; the nine-deep
`msgAppend` chains of `flockSpecOf` (`:513-525`) are the reviewer-drowning case. It is also the
natural home for finding 2's generic combinators. Not verified to compile; ArkLib's appended
instances are not found on concrete schedules (`docs/dependencies.md`), which a bundle sidesteps
by matching on a projection. Together with finding 2 this moves about 45 declarations out of
the leanVM surface into an upstream candidate.

Outside this pull request, the status page already assigns to #66: `BlockClaims.lean` (8
declarations) and its test, `Padding.prodVars` with its two lemmas, `bytecodeSlotColumn` and
`bytecodeColumn_slot`, `slice_bytecodeColumn`, `unstack_eval`, `stack_eval_ambient_zero`,
`stackColumn_eval`, `stackColumn_eval_ambient`, `evalMle_lagrangeBasis`. `KnowledgeAppend.lean`
(25 public) is a verbatim port deleted at the pin bump and was not counted against the design.

## Disposition

Applied on 2026-10-02 on the same branch, unstaged until the author takes them; `lake build
LeanerVM`, the twelve protocol test modules and the four repository scripts pass locally (the
full gate is CI's).

| Finding | Disposition |
| --- | --- |
| 1. third Flock value | Met: `flockSpecOf` sends `say (Vector E 2)`, the docstrings say `v_c` is derived by both verifiers; the round and challenge counts are unchanged, as the tests check. |
| 2. generic combinators | Met: `ToArkLib/Schedule.lean` (new) holds `say`, `draw`, `draws`, `roundSpec`, `roundsSpec`, `stepSpec`, `stepsSpec`, `oddSpec`, `gkrSpec` over any challenge type `C`, their instances, their errors from a unit `u` and the sum lemmas; `Spine/Errors.lean` keeps `overE` and the six slots and instantiates at `E` and `overE 1`. Pull request #62 consumes them on its rebase. |
| 3. `not_rbr` core lemma | Met: `Verifier.not_rbr_of_escape` is the certain-escape lemma; `Verifier.not_rbr` is derived from it under `hlater`. |
| 4. citations | Met in `Spine/Errors.lean` and `Spine/Instance.lean`; the pull request body's source line is drafted below. |
| 5. table error clause | Met (`Spine/Errors.lean`'s module docstring). |
| 6. `Stack.lean` sentence | Met. |
| 7. small slips | "Four kinds of quantity" met. The blueprint owes: Layer 9's schedule ("two values") and its `flockError_le` row, which `sum_flockErrorOf` subsumes; the Layer 0 row's `instOracleInterfaceE`, `instOracleInterfaceListE` and the interfaces listing's `Phase.Guarded`, all deleted; drafted below for the status page. The target clause is in the pull request body draft. |
| 8. tree depth assertion | Recorded in the `μBus` docstring; the side condition for decision 30 is drafted below. |
| 9. observations | Recorded only. |
| audit surface, 33 declarations | 22 hidden or deleted: the seven slot sum lemmas of `Spine/Errors.lean` private and `overE_zero` deleted; `zero_lt_piopRounds`, `piopExtractor_readsFirst`; `foldToOne`, `foldMid_succ`, `append_extractMid_zero_heq`; `take_succ_eq_concat`, `not_toFun_of_val_eq_zero`, `run_of_guarded`, `mem_support_simulateQ_run'_of_forall`; `toVerifier_verify`; `Phase.Guarded`; `instOracleInterfaceE`, `instOracleInterfaceListE` with their `#synth` guards; `innerProductInterface`. The ten generic sum lemmas moved to `ToArkLib/Schedule.lean`, where they are the API. Kept public on purpose: `nat_mul_overE` (the conversion from the unit to `overE`) and `exists_toFun_take` (a generic fact). Left to #66, which rewrites the file: `PublicInput.pSpec`. |
| audit surface, schedule bundle | Not taken: a design change the review did not verify. |

## Drafts for the trackers

Not posted; the author posts them.

**Pull request #65, body.** In *The slots' schedules and errors*, replace "the three values
`v_a, v_b, v_c`" by "the two values `v_a, v_b` (the third, `v_c`, both deployed verifiers
derive)". Replace the sources line by: "Sources: `leaf.rs:864-935`, `gkr.rs:247-430`,
`cpu/mod.rs:711-779`, `constraints.rs:243-291`, `crates/flock/src/hash.rs:983-1010`,
`zerocheck.rs:350-430`, `lincheck.rs:1137-1216`, `verifier.py:1135-1347`, §5, §8.2, §8.5,
Annex C." Add a paragraph before *The component interface*:

> **Generic schedules** (`ToArkLib/Schedule.lean`, new). One message, one challenge, `k`
> challenges, a sumcheck round of degree `d`, `m` rounds, a layer of a grand-product argument of
> radix `2^ρ` at depth `m`, `k` layers of radix four, the binary layer and the whole argument
> (`gkrSpec`), over any challenge type, each with its instances and its error from a unit `u`
> (`gkrError C u nside μ`, `sum_gkrError_le`). `Spine/Errors.lean` instantiates them at `E`.
> `Verifier.not_rbr_of_escape` (`ToArkLib/Refutation.lean`) is the certain-escape lemma behind
> `not_rbr`, for checks that later challenges follow.

In *Where this differs from the blueprint*, add: "the schedule combinators and `gkrSpec`,
`gkrError` are generic, in `ToArkLib/Schedule.lean`; the Flock slot sends two values after the
zerocheck, as the deployed verifiers read, so the spine's `sum_flockErrorOf` is the exact sum
Layer 9's `flockError_le` only bounds; `instOracleInterfaceE`, `instOracleInterfaceListE`
(Layer 0) and `Phase.Guarded` are deleted as unused." Add at the end of the first paragraph:
"The spine advances no target of `AGENTS.md`'s map by itself; it is what the base theorems (T4)
are stated through."

**Status page, *What the built work owes the blueprint*** (by the third pull request of the
stack, which records the revisions): the lines above, and: "the bus phase's side conditions
(decision 30) gain 'the pull and count leaves fit in `2^μBus`', which the deployed verifier
asserts (`leaf.rs:123-146`) and an instance does not guarantee"; "a `Schedule` bundle (a spec
with its two instance families and its error) would replace the named instances of
`Spine/Errors.lean`; not tried".
