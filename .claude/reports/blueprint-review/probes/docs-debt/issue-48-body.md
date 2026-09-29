Tracks #12. Holes **P1** (definition and completeness) and **P2** (round-by-round knowledge soundness): the bus phase, blueprint Layer 6, over an abstract `I : M3Instance`.

**Produces** (`LeanerVM/Protocol/Bus.lean`, module):
- P1: `pushLeaves`, `pullLeaves`, `countLeaves` (the leaf tables of §5.4 from `q`, padded with 1), `busPhase I (G : Gkr.Def) : Phase.Def I Unit (BusOut I) (busSpec I) (M3Holds I) (Seam.bus I)` (verifier: `(α, β)`, one root `R` and the count root `R_c` (finding F3), the batched GKR over the three trees, the leaf decomposition with the public parts computed by the verifier, the pooled boundary claims, `R_c ≠ 0`), `busError`, `leaf_decomposition` (specification (5.4), from #40's `stack_eval_ambient_one` and #41's `idxColumn_eval`/`bytecodeColumn_eval`), and `Phase.Security.complete`.
- P2: `Phase.Security.rbr` with `busError` = `4·2^μ_bus/|E|` on `(α, β)` plus `gkrError 3 μ_bus`, plus the zerocheck charge: `Seam.bus` carries `∀ j i, C̃_{j,i}(ζ_{<τ_j}) = 0`, and the escape "some constraint violated on the cube, extension zero at ζ" is charged coordinate by coordinate as ζ is drawn, `1/|E|` per coordinate per constraint (decision 3, settled).

**Consumes:** the spine (`Seam.bus`, `busSpec`, `BusOut`), G5's `Gkr.Def` (P2 also needs G6's `Gkr.Security` and G4's `sideProduct_collision`), #40, #41.

**Tests:** `leaf_decomposition` in the kernel on a layout with two blocks; the whole phase run on the toy instance's honest `q`; the zero-count mutation rejected (acceptance test 3); the pad-0 mutation rejected (test 2).

**Claim** by assigning yourself; P1 and P2 are separate pull requests.
