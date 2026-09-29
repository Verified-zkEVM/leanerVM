# Dossier: the spine as built (task `code-spine`)

Reviewed: leanerVM `main` at `b435631` (the checkout is on the branch
`docs/protocol-blueprint-review`, created from it; its tracked sources are those of `main`).
Libraries at the pins: ArkLib `dca90385`, CompPoly `3468b38c`, VCVio `f9dc47d9`. leanVM at
`a386121f`.

**Status of this file: in progress.** Sections are added in the order D, C, F, B, E, A; a
section that is not there yet is not written yet.

## 0. Summary

(Provisional; rewritten when the dossier is complete.)

Read in full: `LeanerVM/Protocol/Spine/{Instance,Seams,Phase,Compose,Toy}.lean`,
`LeanerVM/Protocol/ToArkLib/{Oracles,Component,PassThrough,SendOracle,Refinement,GuardedVerdict,KeepOracles}.lean`,
the statements of `KnowledgeAppend.lean`, `LeanerVM/Protocol/Field.lean`,
`LeanerVM/Protocol/PublicInput.lean`, `tests/LeanerVMTests/Protocol/Spine.lean`, the blueprint's
headline, conventions, spine section, Layers 3 to 13, acceptance tests and interface list, the
earlier review `docs/reviews/protocol-spine.md`, the ArkLib definitions the statements unfold
to, and the specification's §4, §5, §6, §8 and Definition 3.13.

Conclusions so far:

1. No theorem of the spine is wrong for what it states, and `M3Holds` is a sound and
   non-vacuous definition on every case probed, including the multiplicity cases the
   repository's tests lack.
2. The master theorems are composition theorems. Their hypotheses are satisfiable, for every
   instance, by phases that check nothing, because the error a phase declares is unconstrained
   (machine-checked: `Phases.Security toy` inhabited at error 1).
3. The composed extractor's output is not the stack as soon as a phase has a round; the
   repository's `rfl` test covers zero-round phases only.
4. A layout can alias columns and empty the relation; the reading law determines `read` from
   `extend`.
