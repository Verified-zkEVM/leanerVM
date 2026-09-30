
## D. The top limb of the public input, along the whole chain

The sibling dossier `code-pubinput.md` §D traced the limb through the phase, the spine and the
deployed verifiers; this section does not repeat it and adds the two ends of the chain and the
anchors. Its facts used here: the oracle protocol's theorems hold for every instance, so a
leanISA instance with two lines is as good an `M3Instance` as one with three (§D.1); the
deployed verifiers pool the third claim at `0` with no scalar (`cpu/mod.rs:746, 756`,
`bind_pi_claim` `:674-682`; `verifier.py:1399-1401`; §D.3).

**The type.** `PublicInput` is four lanes of `K`, and the two words are built with a literal
zero top limb (`Memory.lean:101-110`, probe `Shapes`, output lines 69-78):

```lean
structure PublicInput where
  lanes : Fin 4 → K
def PublicInput.word0 (p : PublicInput) : E := E.ofLimbs (p.lanes 0) (p.lanes 1) 0
def PublicInput.word1 (p : PublicInput) : E := E.ofLimbs (p.lanes 2) (p.lanes 3) 0
```

A public input with a nonzero top limb cannot be written; the probe proves
`p.word0.limb 2 = 0` and `p.word1.limb 2 = 0` for every `p` by `simp` (`Shapes.lean:45-49`,
exit 0). The specification agrees, "two 192-bit words (with top limb 0)"
(`08-end-to-end-protocol.tex:29`), the Rust rejects a third limb (`cpu/mod.rs:141-143`) and the
Python's `Digest` has none (`verifier.py:223`).

**What `SatisfiedBy` says of cells 0 and 1.** `word0_eq : (imageOf w.data).2.read (gpow 0) =
some input.word0` and `word1_eq` (`Statement.lean:338-340`): the *whole* `E`-word of the image
at index 0 is `input.word0`, top limb included; and `public_input_eq` (`:315`), which no
component reads. **What `ValidExecution` says**: `HasPublicBoundary input t` has the same two
equations on `t.image` (`Execution.lean:108-110`), whole words again.

**What the instance says.** Three lines (`:834-836`): `mem_0` with cells `(word0.limb 0,
word1.limb 0)`, `mem_1` with `(word0.limb 1, word1.limb 1)`, `mem_2` with `(0, 0)`.
`PublicLinesHold` on them is exactly the six limb equalities, from which
`E.ofLimbs mem_0[i] mem_1[i] mem_2[i] = input.word_i` follows (probe `Shapes.lean:57-63`,
the second `example`).

**If the instance omitted the third line.** `M3Holds` would say nothing of `mem_2[0]`,
`mem_2[1]`; the master theorems hold unchanged; the theorem left without a proof is
**`satisfiedBy_witnessOf`**, for *every* possible `witnessOf`, not only the natural one:

- the natural `witnessOf` writes the image's word 0 as `E.ofLimbs mem_0[0] mem_1[0] mem_2[0]`;
  with `mem_2[0] ≠ 0` it is not `input.word0`, whatever `input` (probe `Shapes.lean:51-55`:
  `E.ofLimbs a b c ≠ p.word0` when `c ≠ 0`, by comparing limb 2);
- a `witnessOf` that zeroed the limb when building the data and the block would break
  `mem_balanced` for any program that reads cell 0 (the reading row's pulled tuple carries
  `mem_2[0]` from `q`, the built seed carries `0`);
- and no `witnessOf` at all can serve when no satisfying witness exists: take the program
  whose first instruction is `SET_CONSTANT [g^0, y²]` (`Instr.setConstant 1 (E.ofLimbs 0 0 1)`;
  at `fp = 1` the operand `g^0` names cell 0) followed by a jump to the sentinel and the fill
  blocks. Its constraints are satisfiable only with cell 0 = `y²`, whose low limbs are `0, 0`:
  a stack with `mem_0[0] = mem_1[0] = 0`, `mem_2[0] = 1` satisfies the constraints, the
  balances, the counts and the two remaining lines at `input = ⟨![0, 0, l₂, l₃]⟩`, so it is
  in the two-line `M3Holds`; but `SatisfiedBy prog input w` demands `word0_eq` with
  `input.word0 = E.ofLimbs 0 0 0 ≠ y²`, and `ValidExecution` demands the same of `t.image`, so
  neither has an inhabitant. (An inference from the definitions: `execute` of `SET_CONSTANT`
  requires `[o] = k`, `Step.lean`; the honest stack of that program is not built as a probe.)

**If `SatisfiedBy` were weakened instead** (its two word conjuncts restricted to limbs 0
and 1), `satisfiedBy_witnessOf` would close with two lines, and the theorem left without a
proof would be **`constraintSoundness`**: it must produce `∃ t, AssignmentRepresents w t ∧
ValidExecution prog input t`, `AssignmentRepresents` fixes `t.image` to `imageOf w.data`
(`Statement.lean:355-362`, `assignmentRepresents_image`), and `HasPublicBoundary` then demands
the whole word (`Execution.lean:110`). For the program above no `t` exists, so the theorem is
false. **If `HasPublicBoundary` were weakened too**, nothing on the chain would object, and the
anchor would be the specification alone; the top limb would then be constrained only where a
guest reads it (T3). **The anchor** is therefore the pair `PublicInput.word0`,
`PublicInput.word1` with their literal `0` (`Memory.lean:107-110`), consumed verbatim by
`HasPublicBoundary` and by `SatisfiedBy`; the requirement of the owner's note ("a missing,
weak or wrong verifier check must leave knowledge soundness or completeness unprovable") is
met one level down from the oracle protocol, in the adaptor's theorem, and the acceptance
test that claims it (test 10, `:1293-1295`) should name that theorem, as `code-pubinput.md`
G.3 also asks.
