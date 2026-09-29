Tracks #12 (roadmap revision 2, section *The spine* of `docs/roadmap/protocol-blueprint.md`). Hole **S**. This is the trunk every other hole plugs into; it lands first, after #18 (Layer 1's generic half) is on `main`.

**Produces** (`LeanerVM/Protocol/Spine/{Instance,Seams,Phase,Compose}.lean`, modules; `tests/LeanerVMTests/Protocol/Spine.lean`):
- `M3Instance` (the polynomial view of an arithmetization: log-heights, widths, constraint polynomials of degree ≤ 2, flush tuples with side and separator, count columns, boundary blocks as tagged 16-coordinate tuples, the stack layout as `Blocks`, `μ`, the fit proof, the caps) and `M3Holds I input q`, `M3Rel I` on `q : Column I.μ`.
- The seam types and relations `BusOut`, `TableOut`, `PubOut`, `FlockOut`, `Pool`; `Seam.bus`, `Seam.table`, `Seam.pub`, `Seam.flock`, `Seam.pool`. `Seam.bus` carries the reused-zerocheck clause `∀ j i, C̃_{j,i}(ζ_{<τ_j}) = 0` (blueprint decision 3, now a convention).
- The message schedules `commitSpec`, `busSpec`, `tableSpec`, `pubSpec`, `flockSpec`, `openSpec` (Category B: `cpu/mod.rs:711-779`).
- The hole interfaces `Phase.Def`, `Phase.Security`, `Sumcheck.Def/Security`, `Gkr.Def/Security`, `Batch.Def/Security`, `KnowledgeAppend` (ledger A2, ArkLib #615's shape).
- `Phases I`, `Phases.Security`, `leanVmPiop`, `leanVmVerifier`, `leanVmProver`, `piopError`, `piop_perfectCompleteness (P) (S : P.Security)` and `piop_rbrKnowledgeSoundness (A : KnowledgeAppend) (P) (S)`.
- The adaptor's generic half: `Refinement` (a witness map with `map_valid`) and `knowledgeSound_of_refinement` (post-compose ArkLib's straight-line extractor).
- The toy instance (one table, width 2, one constraint, one push/pull pair, one boundary block), an honest `q` and a mutated `q`.

**Consumes:** Layer 0 (`Column`, `evalOracle`), Layer 1's generic half (`Blocks`, `unstack` from #18 and #38), ArkLib `OracleReduction`, `append`, `perfectCompleteness`, `rbrKnowledgeSoundnessWorstCase`, `Verifier.GuardedForm`.

**Acceptance:** blueprint acceptance tests 24–27 (computable extractor, the wall, seams as the contract, honest toy instance); the import rule in `scripts/check-layers.sh` (no module above the adaptor imports `LeanerVM.Arithmetization`); `./scripts/validate.sh`; the axiom audit; the status file rewritten whole and the dashboard ticked.

**Pending decisions it depends on** (status file, decisions 2 and 6–11): witness type at the boundary, generic instance, conjunct placement, balance, security notion, statement shape, extractor discipline. Settle them on this issue before the PR opens.

**Claim** by assigning yourself and commenting; slices go through `[Intention]` issues as usual.
