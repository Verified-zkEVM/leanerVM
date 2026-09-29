Tracks #12. Holes **G5** (definition and completeness) and **G6** (round-by-round knowledge soundness) of the spine; blueprint Layer 5, the GKR half (ledger A6). Generic: no leanVM object is mentioned.

**Produces** (`LeanerVM/Protocol/Generic/Gkr.lean`, module):
- G5: `ProductTree μ` (leaves; layers derived), `ProductTree.root`, `gkr nside μ : Gkr.Def` (radix 4 from the root down, one radix-2 layer first when `μ` is odd, a fresh combiner `λ` per layer, two combination challenges per radix-4 layer, degree-5 round polynomials, the three trees sharing every challenge and ending at one `ζ`), `gkrError`, and `Gkr.Security.complete`.
- G6: `Gkr.Security.rbr` with `gkrError` = `(nside − 1)/|E|` per `λ`, `5/|E|` per sumcheck round, `2/|E|` per combination pair.

**Consumes:** the spine's `Gkr.Def`/`Gkr.Security` shapes; G1's `Sumcheck.Def` (the layer sumchecks); ArkLib Schwartz–Zippel counting.

**Tests:** `gkr 1 2` and `gkr 3 3` honest runs accepted by `#guard`; a leaf changed after the root is sent rejected; the message count for odd `μ` (acceptance test 17).

**Upstream watch:** ArkLib #818 (GKR with perfect completeness, Thaler's line reduction, radix 2; inherits composition sorries) is a pattern for the layer-as-reduction shape, not an adoptable protocol; ArkLib #1 is the sumcheck umbrella. Write in ArkLib's shape under `Protocol/Generic/` and upstream as `ProofSystem/GKR/GrandProduct` (ledger A6).

**Claim** by assigning yourself; G5 and G6 are separate pull requests.
