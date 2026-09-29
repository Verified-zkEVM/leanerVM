Tracks #12. Hole **P5**: the public-input phase, blueprint Layer 8, over an abstract `I : M3Instance`. Small; both halves in one pull request.

**Produces** (`LeanerVM/Protocol/PublicInput.lean`, module): `publicInputPhase I input : Phase.Def I (TableOut I) (PubOut I) pubSpec (Seam.table I) (Seam.pub I)` (the verifier draws `r_m`, forms `(1 + r_m)·word_ℓ + r_m·word'_ℓ` for the two limbs, and pools three claims on `mem_0, mem_1, mem_2` at `(r_m, 0, …, 0)`, the third with value 0; §8.2, acceptance test 10) and its `Phase.Security` with error `2/|E|`.

**Consumes:** the spine only (`Seam.table`, `Seam.pub`, `pubSpec`, the memory block's committed-column tags of `I`).

**Tests:** a wrong `c_0` rejected; the mutation with a nonzero `mem_2` at cell 0 and the third claim dropped accepted by a verifier that skips it and rejected by this one (acceptance test 10).

**Claim** by assigning yourself.
