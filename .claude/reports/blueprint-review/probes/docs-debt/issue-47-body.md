Tracks #12. Hole **I2**, the adaptor: blueprint Layer 3 restated over the spine. This is the only place the proof system meets leanISA (convention *The wall*).

**Produces** (`LeanerVM/Protocol/M3.lean`, plain file):
- `Sizes`, `Sizes.ofWitness`, `Sizes.Admissible`, `admissible_iff_caps`.
- `leanIsaInstance prog s : M3Instance` (`Ensemble.toM3` of the eight tables with leanISA's separators and directions from `channelSep`/`channelDir`; the stack layout of `witness.rs:85-101` and the leaf layout of `leaf.rs:53-156`, every offset a `decide`), with `leanIsaInstance_degree` (≤ 2), `leanIsaInstance_flush_degree`, `leanIsaInstance_fits`.
- `stackOf : EnsembleWitness (leanIsaEnsemble prog) → Column μ`, `witnessOf : Column μ → EnsembleWitness (leanIsaEnsemble prog)` (total and computable: rebuilds the tables from the columns, the interactions from the components, the image from the memory columns, the program from `prog`).
- `satisfiedBy_witnessOf : M3Holds (leanIsaInstance prog s) input q → SatisfiedBy prog input (witnessOf prog s q)`, `m3Holds_stackOf : SatisfiedBy prog input w → M3Holds … (stackOf w hs)`, `witnessOf_stackOf : witnessOf (stackOf w) = w` on the committed fields.

**Consumes:** the spine (`M3Instance`, `M3Holds`), I1 (`Ensemble.toM3`, Clean #466 or its local copy), leanISA Layers 5–8 (`leanIsaEnsemble`, `SatisfiedBy`, `BalancedPair`, `Caps`, `imageOf`), #38's `unstack`, #40's ambient evaluation.

**Tests:** a witness with one row per table stacked and read back (`witnessOf_stackOf` by `decide +kernel` on the columns); `#guard witnessOf (stackOf w) = w` (acceptance test 24); `Sizes.Admissible` rejects `logMem = 15` and `τ_BLAKE2S = 2`.

**Pending decisions:** 6 (witness type), 8 (which of `SatisfiedBy`'s 13 conjuncts are `M3Holds` clauses and which are adaptor work; the three fixed-column conjuncts are proposed as `M3Instance` coordinate tags), 9 (balance: `BalancedPair` now, Clean #464 later).

**Claim** by assigning yourself.
