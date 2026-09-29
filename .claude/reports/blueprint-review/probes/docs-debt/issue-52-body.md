Tracks #12. Holes **P7** (definition and completeness) and **P8** (round-by-round knowledge soundness): the claim pool and the opening sumcheck, blueprint Layer 10's phase half, over an abstract `I : M3Instance`.

**Produces** (`LeanerVM/Protocol/Opening.lean`, module):
- P7: `Weight μ` (cube values plus an evaluator that agrees with them, Definition 3.13), `WeightedClaim`, `Claim.toWeighted` (a `BlockClaim` of #38 as `eq((ζ, sel), ·)`), the pool order (bus claims, per-table column claims, the three public-input limb claims, the ring-switched claim taking the low powers of `λ`: findings F8 and `finish_claims`), `openingPhase I (B : Batch.Def) (S : Sumcheck.Def) : Phase.Def I (FlockOut I) Unit (openSpec I) (Seam.flock I) (fun _ _ ↦ True)` (draw `λ`, batch, one sumcheck on `W_λ · q`, the final evaluation query), and `Phase.Security.complete`.
- P8: `Phase.Security.rbr` with `(J − 1)/|E|` on `λ` (from #43's `card_false_batch_le`, restated in ArkLib's probability form) and `2/|E|` per round.

**Consumes:** the spine (`Seam.flock`, `openSpec`, `Pool`), G3's `Batch.Def`, G1's `Sumcheck.Def` (P8 also their `Security`), #38, #43.

**Tests:** the phase run on the toy instance; a claim value changed after `λ` is drawn rejected; the empty pool.

**Claim** by assigning yourself; P7 and P8 are separate pull requests.
