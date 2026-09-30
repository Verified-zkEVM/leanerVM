
## H. Negative results, what was not done, and what contradicts the brief

**Checked and found consistent** (no finding):

- `M3Holds`'s five clauses against `SatisfiedBy`'s thirteen conjuncts: every conjunct has a
  source (A.4); no conjunct of `SatisfiedBy` is delivered by nothing once the caps hypothesis,
  the boundary lemma, the count derivation and the Flock consequence lemma are in place.
- `w.Constraints` is asserts and lookups only (Clean `93c9d1ef`, `Operations.lean:687-688`,
  probe `Shapes` output 154-159); leanISA emits no lookup and only `JUMP` asserts; so
  `toM3_constraints_iff` is provable in principle.
- The degree bound `d = 2`: every flush coordinate of the six tables read (`Tables/*.lean`
  `main`) is of degree at most two (`JUMP`'s successor `b·v_pc + b·(g·pc) + g·pc`,
  `Jump.lean:199-201`; `DEREF`'s store `fbar·v3 + f_pc·(g²·pc) + f_fp·fp`, `Deref.lean:203-206`;
  `MUL_NATIVE`'s twelve products, `MulNative.lean:168-173`; the pushes' `g · count`).
- The state boundary as constants only (`Coord.committed` needs `τ = κ = 0`, impossible for a
  real column), as `layout.rs:354-358`; the memory and bytecode blocks' committed coordinates
  are columns of tables whose `τ` equals the block's `κ` by construction (E.4).
- `Caps` is derivable from `Admissible` plus the construction of `witnessOf` (A.4 row 5), and
  `Sizes.ofWitness w = some s` from `SatisfiedBy` (A.6).
- The chain names one `prog` and one `input` throughout (B.2); no theorem lets the prover
  choose either.
- The top limb is anchored (section D), agreeing with `code-pubinput.md` §D.
- `Refinement` accepts a `Type 1` target witness (probe `Transport`); the pointwise
  composition of T4 typechecks (examples 3-4); `Extractor.Straightline.map` cannot serve
  (probe `UniverseFail`).
- The axioms of every arithmetization declaration the chain will use (`assumptions_of_
  blake2sRowsValid`, `memRowOf_bindings`, `bytecodeRowOf_bindings`, `bytecodeRowOf_decodes`,
  `verifier_pull_eval`, `verifier_push_eval`, `rowAt_toElements`, `decode_eq_some_iff`,
  `assignmentRepresents_image`, the six tables, the two blocks, the verifier) and of the two
  master theorems, `bytecodeColumn_eval`, `idxColumn_eval`: the kernel's three (probe `Shapes`,
  output 168-187); `map_option_valid`: two.

**Not done, and how it would be verified.**

- The injectivity of `prog ↦ (prog.logSize, bytecodeColumn prog)` (B.2 item 1): inferred from
  `entry_injective` and `bytecodeColumn_slot`; a probe proving it was not written.
- The counterexample program of section D (`SET_CONSTANT [g^0, y²]`): its two-line stack was
  not built; the load-bearing fact, `E.ofLimbs a b c ≠ p.word0` for `c ≠ 0`, is proved
  (probe `Shapes`).
- The count of admissible size vectors (B.3, about `2^34`) is a hand estimate from the caps
  and the stacking window; the exact count depends on the layout's `μ`, which Layer 3 defines.
- Whether CompPoly's `toCMvPolynomial` is still `noncomputable` at the new pin `572f9973` was
  not checked (the review's object is the old pin).
- No probe was re-run after the upgrade; the two probes with numerals other than `0`, `1`
  need `K.ofBits` before a re-run (header).
- The claim that a run of a halting program visits distinct states (note 18) is an argument
  from determinism of `step`, not a Lean proof.

**Contradicts the brief.**

- The leanVM checkout `/home/scaraven/Documents/leanEthereum/leanVM` is **no longer at the
  pin**: on 2026-09-30 its `HEAD` is `248da0719e94ec253af47c930908f087a7be02a1` and the crate
  tree has changed (`crates/leanvm`, `crates/leanvm_core`; no `crates/lean_vm`). The brief
  (§3, §8) and the coordinator's message say it is unchanged at `a386121f`. This task did not
  move it (no `git checkout`, `pull`, `reset` or `switch` was run here; the shell history of
  this task holds only `git rev-parse`, `git status`, `git log`, `git show`, `git cat-file`,
  `git merge-base`). Every Rust citation of this dossier was read from the working tree on
  2026-09-29 when `HEAD` was `a386121f` (verified then), and the ones in sections C-F were
  re-verified on 2026-09-30 with `git show a386121f:<path>` from the object store (the
  commit is present: `git cat-file -t a386121f` = `commit`). Other agents citing the working
  tree after the move would cite the wrong revision.
