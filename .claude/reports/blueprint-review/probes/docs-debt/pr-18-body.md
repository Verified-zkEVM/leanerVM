## Motivation

The private repository `Verified-zkEVM/leanth` (pull request #16, branch `leanth-project` at `23929f8c`) holds an ~80k-line, sorry-free formalization of the pre-leanISA leanVM ("leanVM-a") by Aristotle (Harmonic), Stefano Rocca and Elias Judin. The proof-system roadmap (#12) did not mention it. Because the repository is private, issues and the blueprint cannot cite it; this draft carries the reusable part into leanerVM so that they can cite this repository instead. It stacks on #15 (base `feat/protocol-roadmap`) and should be retargeted to `main` once #15 merges.

## What is added

- **`docs/roadmap/leanth-reuse.md`**, the catalog: provenance and the credit convention for derived material; the leanVM-a to leanVM-b delta that decides reusability (characteristic 2, Clean relation, grand product instead of logup, one table sumcheck, binary WHIR, BLAKE2s chain, ArkLib instead of an in-house `PMF` framework, little-endian indexing); per-layer tables of the leanth declarations cited as `module:line`, each with a verdict (copy, port, pattern, drop), its roadmap target and an effort size; the lessons the survey binds on the roadmap; the port log; and the ArkLib upstream candidates per ledger item (A1, A2, A3, A6, A7, A8).
- **Layer 1, generic half**, ported: `LeanerVM/Protocol/Multilinear.lean` (`sumCube`, `hadamard`, `eqTable` with the partition of unity `sumCube_eqTable`, `cubeIndex`/`cubeSplit`/`sum_cube_split`, `lagrangeBasis_cubeIndex`, `boolVec`, `slice`, `evalMle_split`, the selection identity `evalMle_append_boolVec`, `prodVars`, `padHigh` with `sumCube_padHigh` and `evalMle_padHigh`) and `LeanerVM/Protocol/Stacking.lean` (`Blocks` largest first, `offset`, alignment `pow_size_dvd_offset` from the descending order, window lemmas, `stackAt` with a pad value, `selector`, `stack_eval`). Tests: `#guard`s over `K` on a two-variable table and on blocks of heights 4, 2, 1, offsets and selectors decided in the kernel, mutations.
- Pointers from the blueprint (dependencies section, Layer 1 file list), the status file (coverage row, ledger note, pending decision 3, survey record), the docs index and the agent guide.

## Sources and revisions

leanth `leanth-project` at `23929f8c` (Apache-2.0), read in eight clusters with every load-bearing declaration's statement and proof; the maintainer's audit branch `scaraven/leanth-project-audit` and explore branch `scaraven/proof-system-explore` as secondary sources. Every derived module carries the "Derived from" line and every commit the three `Co-authored-by` trailers. Category A throughout: nothing transcribes a leanVM source; the proofs of the ported statements are new, on CompPoly's `evalMle` and `lagrangeBasis`.

## Design notes

- The catalog cites `module:line` at the pinned commit so an issue can name a port source without the private tree; no source is copied (AGENTS.md: port reviewed ideas, do not copy historical trees). A verbatim reference snapshot of the reusable files was deliberately not added; say so if you want one as a separate commit.
- `Stacking.lean` is the generic stacking (any commutative ring); the blueprint's `Stack.lean` (`Column` blocks over `K`, `stack_eval_pad`, `idxColumn`, `bytecodeColumn`) stays open. The blueprint's Layer 1 file list now names both.
- Two findings recorded for the roadmap rather than applied: leanth charges the recycled zerocheck point once for the whole constraint family, so the blueprint's per-constraint `τ_max/|E|` over-estimates (status, pending decision 3); ArkLib at `dca90385` has no `ProofSystem/Whir/` directory, confirming ledger A7.

## Layer ownership of new public definitions

`Protocol` (generic): `sumCube`, `hadamard`, `eqTable`, `lagrangeBasis_getElem_nat`, `evalMle_eq_sum`, `eval_eq_sum_eqTable`, `evalMle_replicate_one`, `evalMle_replicate_zero`, `evalMle_cast`, `sumCube_eqTable`, `cubeIndex`, `cubeIndex_div`, `cubeIndex_mod`, `testBit_cubeIndex`, `cubeSplit`, `sum_cube_split`, `lowVec`, `highVec`, `lagrangeBasis_cubeIndex`, `boolVec`, `fin_eq_iff_testBit`, `lagrangeBasis_boolVec`, `evalMle_boolVec`, `slice`, `evalMle_split`, `evalMle_append_boolVec`, `onesIndex`, `prodVars`, `sumCube_prodVars`, `lagrangeBasis_onesIndex`, `evalMle_prodVars`, `padHigh`, `sumCube_padHigh`, `evalMle_padHigh`; `Blocks` with `offset`, `total`, `offsetNat_mono`, `offset_add_pow_le_offset`, `offset_add_pow_le_total`, `pow_size_dvd_offset`, `InWindow`, `stackAt`, `size_le`, `selector`, `slice_stackAt`, `stack_eval`.

## Validation

```sh
./scripts/validate.sh
lake build LeanerVM.Protocol.Multilinear LeanerVM.Protocol.Stacking LeanerVMTests.Protocol.Multilinear LeanerVMTests.Protocol.Stacking
```

All gates pass. `#print axioms` on `stack_eval`, `evalMle_padHigh`, `sumCube_eqTable`, `evalMle_append_boolVec`: `propext, Classical.choice, Quot.sound`.

## Deployed behavior or repair

Neither: generic algebra with no source to be faithful to.

## Linked issues

Dashboard #12 (Layer 1); stacks on #15; the catalog's upstream table is the input for the ArkLib issues drafted in the status file.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
