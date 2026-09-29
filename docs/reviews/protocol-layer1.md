# Review: the proof system's Layer 1 (PR #59)

Reviewed on 2026-09-29 against branch `feat/protocol-layer-1` at `8bc9bbd` (fourteen commits
over `main` at `5cb7da6`), read-only, with the repository's `adversarial-review` skill. The three
passes were run by three agents with no knowledge of the branch's history and none of each
other: the fidelity pass read the pinned leanVM sources and wrote down what it expected before
it opened a Lean file, and the specification pass did not open `crates/` or the Python
verifier. Sources: leanVM at the pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`
(`doc/leanvm/body/04`, `05`, `06`, `08`; `crates/lean_vm/src/{witness.rs,leaf.rs,cpu/layout.rs,
cpu/mod.rs}`, `crates/pcs/src/stack_open.rs`, `crates/primitives/src/{multilinear.rs,
field/mod.rs}`, `python-verifier/verifier.py`), CompPoly `3468b38c`
(`Multilinear/Basic.lean`), and the spine on `main` (`LeanerVM/Protocol/Spine/{Instance,Seams,
Toy}.lean`). Every changed Lean file was read in full; the blueprint, the status file, the
catalog and the pull request body were read for intent.

Validation of the reviewed commit passed: `./scripts/validate.sh` (exit 0; the axiom audit
reports 3153 declarations and no unexpected axiom), and CI on the same commit. `#print axioms`
on fourteen theorems of the layer gives `propext`, `Classical.choice`, `Quot.sound` only.

Findings are confirmed against `8bc9bbd`. The paths in the findings are the reviewed commit's;
the disposition names where things are after the fixes, which also moved modules (the generic
half was made generic in the same change, status finding E17).

## Disposition

| Finding | Disposition |
| --- | --- |
| A1 (medium): `BlockClaim.isValid_iff_pairing` cannot be used by the phase named as its consumer | Met: `LeanerVM/Protocol/ClaimWeights.lean` states the step over an abstract instance, `ColumnClaim.holds_iff_weighted`, from `Weight.pair_eq_sumCube` and `eqWeight` (the equality kernel as a `Weight`, its evaluator proved by `evalMle_lagrangeBasis`); tested on the toy instance, whose layout knows nothing of aligned blocks. The three claims are reworded: `BlockClaim` is the aligned-block form, usable where a `Blocks` is known. |
| A2 (low): `Blocks.layout` does not have the type of `M3Instance.layout` | Met: `Layout.comap` renames a layout's columns along a map that keeps heights; `Blocks` is sizes only, so no structure update of values is involved; the test puts the aligned layout of three blocks of height 2 in the layout field of the toy instance, and `M3Holds` decides on it as on the toy. |
| A3 (low): `bytecodeColumn_slot` restates the definition and does not pin the bit order | Met: `bytecodeColumn_answer_boolVec`, the oracle's answer at the cube point of an instruction index and a slot, for every program; it fails on the opposite layout, which `bytecodeColumn_slot` does not. |
| A4 (low): a mutation guard that passes for an unrelated reason | Met: the guard now evaluates the stack at block 1's point with reversed selector bits. |
| A5 (low): back-loaded padding tested at one new variable only | Met: `tests/LeanerVMTests/Protocol/Padding.lean` lifts by two variables, where the all-ones slice differs from the others, and adds the copied table, whose sum is zero in characteristic two. |
| A6 (low): load-bearing statements whose only test cites the theorem | Met: the pairing is evaluated on a table that is no honest stack at a point outside `K`; the native bytecode evaluator off the cube; the selector weights of a full layout and of one with a gap. |
| B1 (medium): the order of equal-size blocks is fixed by leanVM, left open by this layer, and stated backwards in the roadmap | Met in the documentation: the blueprint's convention *Stacks*, its contract table and Layer 3 give the pinned order and cite `witness.rs:67-101` and `cpu/layout.rs:13-49`; status findings S15 and F17. No Lean change: `Blocks` takes the order as given, and the instance (I2) supplies it. |
| B2 (low): the claims docstrings describe one weight construction where the source has two | Met: `BlockClaims.lean` says strided and ring-switched claims exist and are not `BlockClaim`s, and cites `stack_open.rs:73-98`. |
| B3 (low): "equation (5.4)" does not exist | Met: "§5.4, equation (2)" in `Stack.lean`, the blueprint and the status file; status finding S16. |
| B4 (low): a citation that is a comment cut mid-sentence | Met with B2. |
| D1 (high): the wall is not enforced by the script the blueprint names | Met in the documentation: the blueprint's convention *The wall* and acceptance test 25 say the rule is checked by review and list the exceptions, `FixedColumns.lean` and the compiled verifier included. Open: the rule in `scripts/check-layers.sh`, a repository policy change, left to the maintainer. |
| D2 to D4, D9 (medium): the status file says things false of the branch | Met: the commit citations are said to be on the sibling branch; #59 is a draft; seven pull requests are open beside it; four are consolidated, not five. |
| D5 to D7 (medium): names and consumers the branch renamed in one place and left in others | Met: `ETable`, `sumCube_prod_vars`, `stack_eval_pad`; the spine needs Layer 0 only; the hole table consumes L1. |
| D8, D10 to D16 (low) | Met, except the two left to the maintainer below: D8 (the reserved finding numbers), D10 and D11 (the catalog), D12 (the citation ranges), D13 (acceptance test 13), D15 (`docs/architecture.md` describes the `To*` folders), D16. D14 and D17 are edits on GitHub. |
| C1: per-file copyright and author headers in two modules | Open: the maintainer's decision. Kept as their author wrote them. |
| C2 to C9: hygiene | Met where a change was due: no pointer to a roadmap document and no history in a docstring; `FixedColumns.lean` imports what it uses; `Blocks.stack_eval` against `eval_stack` renamed apart (`stackColumn_eval`, `stackColumn_eval_ambient`); one public `evalMle_replicate` for three lemmas; section headers; lines within 100 characters; the test docstrings. Not changed: the blanket `@[expose] public section`, which is `main`'s convention. |

## Verdict in one paragraph

No theorem in scope is false, vacuous or of the wrong strength against the specification, every
hypothesis has an inhabitant under `tests/`, and every Lean object is the leanVM object: the
evaluation order, the offsets and selectors, the padding term, the index column and the
bytecode table agree numerically with the pinned Python verifier on the same inputs. The
defects were at the two ends. Towards the consumers, the layer offered `BlockClaim` to a phase
that cannot form one and a layout of a type no instance has (A1, A2); towards the sources, the
roadmap this layer will be built on states the order of equal-size blocks backwards (B1), which
no theorem here can notice and the compiled verifier would. Both are cheap now and expensive
after the adaptor and the opening phase are written.

## Pass A: specification

### A1 (medium). `BlockClaim.isValid_iff_pairing` has no call site in its claimed consumer

`ToCompPoly/Claims.lean:92-98`, with the docstring at `:41`, the status file and the pull
request body naming the opening phase as the consumer. The opening phase is written over an
abstract `I : M3Instance`, whose layout is an opaque `Layout`; a `BlockClaim B S` needs a
`Blocks` in scope, so the phase cannot form one from a `ColumnClaim I`. And the theorem's right
side is a cube sum of a pointwise product, while the spine's `WeightedClaim.Holds` is
`Weight.pair`; nothing related the two, and the equality is not `rfl`.

Concrete failure. The opening phase needs, for every `c : ColumnClaim I`,
`c.Holds q ↔ WeightedClaim.Holds q ⟨the equality weight at I.layout.extend c.col c.point,
c.value⟩`. It could not get it from `isValid_iff_pairing`.

### A2 (low). `Blocks.layout` does not have the type of `M3Instance.layout`

`Stack.lean:90-94`. `Blocks.layout : Layout μ (Fin B.n) B.size`, and an instance needs
`Layout μ (Σ j, Fin (width j)) (fun c ↦ τ c.1)`. After sorting largest first, the size of the
block a column lands on equals the column's log-height only propositionally, and neither the
spine nor the branch had a way to rename the columns of a layout.

Concrete failure. `layout := B.layout hμ` does not typecheck in `leanIsaInstance`. The tests
avoided the question by comparing cell lists against `Toy.layout`.

### A3 (low). `bytecodeColumn_slot` restates the definition

`FixedColumns.lean:77-80`. The definition (`cubeSplit.symm`) and the statement (`cubeIndex`)
follow one convention, so the theorem cannot disagree with a wrong layout: with the opposite
layout, slot bits low, the same proof script proves the same statement. What pinned the bit
order was `bytecodeColumn_eval` and `#guard`s on programs of at most two instructions, so "the
opcode of instruction `z` is `P(z, 1, 1, 0, 0)`" (§8.1) was not a theorem for a program in
general.

### A4 to A6 (low). Tests

A4: `tests/.../Stacking.lean:72-76` compared block 1 at `13` with block 0 at `(13, 0)`, two
unrelated numbers; the inequality holds with any selector bits. A5: back-loaded padding was
tested with one new variable, where the all-ones index, index 1 and the top-bit index coincide,
and the reading the roadmap excludes (copying the table) had no test. A6: the pairing theorems,
the native bytecode evaluator off the cube and the sum of the selector weights had as only test
an `example` applying the theorem.

### Observations

- The reading law holds for any high index in place of the selector. What pins the selector to
  `offset >> size` is `unstack_getElem` and `unstack_stackAt` with `pow_size_dvd_offset`, not
  `unstack_eval₂`.
- `Stack.lean` said the padding term "vanishes exactly when the blocks fill the stack". Only
  "if" is proved, and pointwise the converse is false: on the fixture at `ζ = (0, 9, 11)` the
  weights sum to one. Reworded.
- `bytecodeColumn_eval` is a double sum. The bus phase's known columns are per slot and will
  want `answer (bytecodeColumn prog) (z ++ w) = Σ_s eq(w, s) · answer (bytecodeSlotColumn prog
  s) z`, which follows from `evalMle_split` and `slice_bytecodeColumn` and is not stated. Open.

## Pass B: fidelity

The pin was confirmed from the checkout's `HEAD`. B0 is clean: binary fields, BLAKE2s, six
tables, one bus. B6 is clean: the branch claims no correspondence with the Rust.

### B1 (medium). The order of equal-size blocks

`ToCompPoly/Stacking.lean:53-61` asks only that the sizes do not increase. leanVM sorts by size
and breaks ties by column index (`witness.rs:67-79`, `.then(a.cmp(&b))`; `verifier.py:305-311`),
and the column index puts the six shared columns first, `MEM_LO = 0` to `QFLOCK = 5`, then the
tables' columns (`cpu/layout.rs:13-49`). The specification gives no rule for ties
(`04-committing-the-witness.tex:6`), and §8.5 lists the table columns first in prose. The
blueprint followed the prose and cited `witness.rs:85-101`, which is `placements_of` and lists
no column.

Concrete consequence. Whenever a table's log-height equals `log_mem` the two orders give
different offsets and selectors: with sizes `[4, 4, 4, 4, 2, 5, 4, 4]` in the pinned order
`MEM_LO` sits at offset 32 and the table columns at 96 and 112; in the roadmap's order the table
columns sit at 32 and 48 and `MEM_LO` at 64. An adaptor built on the roadmap's order satisfies
every theorem of this layer, and the compiled verifier rejects every proof the Rust produces.

### B2 to B4 (low)

B2: `Claims.lean` said the pinned sources "use the same selector-weight construction" and that
only unshifted claims exist; the eighteen BLAKE2S limb columns are read by strided claims on the
same stack (`stack_open.rs:84-97`, `cpu/mod.rs:790-814`), which a `BlockClaim` cannot express.
B3: the specification is an `article` with no `\numberwithin`; its equations are (1) to (4),
the leaf decomposition is (2). B4: `stack_open.rs:8-12` is a module comment cut before its last
line; the interface is `StackClaim` at `73-98`.

### The comparison

There are no constraints or flags in scope. Column groups: `bytecode_columns` returns 8 columns
and `entry` is a `Vector K 8`; 16 slots on both sides.

| Artifact | Source consulted | Matched | Absent in the Lean |
| --- | --- | --- | --- |
| Evaluation order | `multilinear.rs:109-114, 271-277, 309-326`; `verifier.py:233-245`; CompPoly `Basic.lean:410-411, 467-500` | coordinate `k` is bit `k`; one table at one point gives one value in both, and the reversed point another, equal in both | none |
| Offsets and selectors | `witness.rs:67-79`; `verifier.py:295-315`; `stack_open.rs:294-304` | prefix sums `[0, 4, 6]` for sizes 2, 1, 0; the lifted points; the selector weights | the filter of virtual columns, the tie rule, the permutation to input order (B1) |
| Stack height | `witness.rs:97`; `leaf.rs:153`; §4.1 | any `μ` the blocks fit in; the generality is needed, since the count tree is lifted to the push tree's depth and the Rust floors the witness stack at 15 | the height itself, the instance's to define |
| Padding | `05-arithmetization.tex:106-109`; `leaf.rs:459-460`; `verifier.py:589` | the one-padded stack at a point equals the covered part plus `1 + Σ sel` | none |
| Index column | `field/mod.rs:102-113`; `verifier.py:271-278` | `g = 2`; the closed form equals the table's evaluation | none |
| Bytecode table | `leaf.rs:585-604`; `cpu/layout.rs:229-309`; §8.1 | all 128 cells of an eight-instruction program; the evaluation at a seven-coordinate point; the last index encoded like any other | none |
| Block claim weight | `stack_open.rs:73-98, 294-325`; `verifier.py:514-522` | the point claim | strided and ring-switched claims, the batching (B2) |

Declared deviations, and whether their licence holds: the pad-one term written `1 + Σ` and the
index column's factor written `1 + z(1 + a)`, both by characteristic two over `E`, yes; the
geometric table for any ring element, yes; the pad as a parameter, yes, zero and one being the
two leanVM values.

### Observations

- The fixtures of `tests/LeanerVMTests/Protocol/FixedColumns.lean` use instructions whose
  operands are all `1`, which cannot detect a permutation of the operand slots. A table derived
  from the pinned source with all six opcodes, both non-cell `DEREF` modes and the compiler's
  padding instruction (`Op::Set { o: 0, k: 0 }`, `lean_compiler/src/lib.rs:162`) would. Open.
- The Rust was not executed; agreement with it is by reading, and with the Python verifier by
  running it.

## Pass C: hygiene and documentation

### D1 (high). The wall is not enforced by the script the blueprint names

`protocol-blueprint.md`, convention *The wall* and acceptance test 25, named
`scripts/check-layers.sh` as the witness that no module above the adaptor imports
`LeanerVM.Arithmetization`. The script checks `Parameters`, `Semantics`, `Arithmetization` and
`Applications` for reverse edges and has no rule for `Protocol`:
`LeanerVM/Protocol/FixedColumns.lean` imports `LeanerVM.Arithmetization.Bytecode` and passes,
and so would a phase. By search the wall holds today.

### D2 to D17

The status file said each cherry-picked commit cites its pull request (true of the sibling
branch only), called a draft "in review", counted three open pull requests where eight are
open, and "five" consolidated where four are. The blueprint kept `ETable`, `sumCube_prod_vars`
and an ordering sentence that made the spine depend on Layer 1; the catalog kept
`stack_eval_pad`, listed as next port candidates things already proposed in open pull requests,
and named leanth as the source of a composition proof that was ported from ArkLib #615. Three
citation ranges stopped short of, or ran past, what they cite: §8.1's range ended before the
sentence that gives the bit order (line 25). `docs/architecture.md` did not know the `To*`
folders.

### C1 to C9

Compactly, at the reviewed commit: two modules carry a per-file copyright and authors header,
which `CONTRIBUTING.md` asks to leave to the repository history (C1); two docstrings pointed at
a roadmap document and two narrated history (C2); `PowerColumn.lean` imported a module it did
not use and `FixedColumns.lean` relied on that import (C3); `Blocks.stack_eval` and
`Blocks.eval_stack` were two statements told apart by word order (C4); seven lines over 100
characters (C5); three lemmas about constant tables where one would do, two of them private
(C6); three modules without section headers (C7); a statement about any ring of characteristic
two outside the generic half, and the tests of a generic table in a leanVM test file (C8); one
stale test docstring (C9). The five gate scripts pass.

## Left to the maintainer

- The rule for the wall in `scripts/check-layers.sh`, with its allowlist and its test in
  `scripts/test-policy-checks.py` (D1).
- The per-file headers of `ToCompPoly/AmbientStacking.lean` and `BlockClaims.lean` (C1).
- Replacing the history of #59 by that of `feat/protocol-layer-1-credited`, which needs a force
  push.
- On GitHub: the L1 line and the open pull request table of the dashboard #12 (D17), and the
  note to the author of #39 and #43 that `Blocks` no longer carries values.

## Not checked

- The Rust was not run. The leanth line citations were checked against a local checkout of the
  private repository, not by this repository's readers.
- `DEREF` in cell mode was read, not evaluated, in the bytecode comparison.
- The fixes were made after the review and have not themselves been reviewed adversarially;
  they were validated by `./scripts/validate.sh` and by the tests named in the disposition.
