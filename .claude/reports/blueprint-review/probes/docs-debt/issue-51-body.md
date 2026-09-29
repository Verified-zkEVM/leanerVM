Tracks #12 and #3. Hole **P6**: the Flock and ring-switching phase, blueprint Layer 9, as the `Phase.Def`/`Phase.Security` pair at the flock seam.

**Produces** (`LeanerVM/Protocol/Flock.lean`, module): the seam-side objects this roadmap owns: `FlockOut I` (the pool with the ring-switched weighted claim, `Weight`/`WeightedClaim` shape of Definition 3.13), `Seam.flock`, `flockSpec I`, `limbColumns : Column μ → Fin 18 → Column (τ_5)` (the BLAKE2s value limbs read from the `q_flock` region), the error bound shape `flockError_le : Σ flockError ≤ (4·k_batch + 163)/|E| + 2^32/|E|`, and the statement that the phase's `Phase.Def` and `Phase.Security` are #3's witness obligation (F3–F5, F8 there).

**Consumes:** the spine (`Seam.pub`, `Seam.flock`, `Pool`); the inhabitant comes from #3 (the BLAKE2s circuit, zerocheck, lincheck, ring switching).

**Tests:** typechecking only here; the instance's tests belong to #3.

**Upstream watch:** ArkLib #383 (ring switching, Binary Basefold, additive NTT, completeness and rbr knowledge soundness of the FRI-Binius family) and ArkLib #893 (Binius/ring-switching roadmap, ledger A9).

**Claim** by assigning yourself (coordinate with #3).
