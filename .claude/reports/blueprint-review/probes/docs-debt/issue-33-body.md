Take the generic fingerprint algebra needed by Layer 5's `fingerprint` and
`sideProduct_poly_eq_iff`, tracked by [leanerVM #12](https://github.com/Verified-zkEVM/leanerVM/issues/12)
and [ArkLib #901](https://github.com/Verified-zkEVM/ArkLib/issues/901).

Exact declarations: `fingerprintPoly`, `eval₂_fingerprintPoly`,
`eval_fingerprintPoly_boolVec`, `fingerprintPoly_injective`, `totalDegree_fingerprintPoly`,
`map_fingerprintPoly`, `mapped_fingerprint_ne`, `fingerprintFactorPoly`,
`eval₂_fingerprintFactorPoly`, and `totalDegree_fingerprintFactorPoly`.

Base: PR #18 at `41b79b3cf6a663a2cbc9e73aedd984c7198aac9d`, using its
`Protocol.Multilinear` API and unchanged dependency pins. Category A source: leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, §5.2. Port source: the fingerprint declarations
in `Logup.lean:275-444` catalogued in `docs/roadmap/leanth-reuse.md`, leanth revision
`23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`, Apache-2.0; preserve its original notice.

The first consumer is the multiset-product slice, then Layer 6's bus. Controls cover degree four
for sixteen coordinates, the separate beta variable, Boolean and off-cube evaluation, low-bit-first
indexing, coordinate zero, dimension zero, and noninjective coefficient maps. Require the focused
tests, full repository validation, and standard-only transitive axiom audit. Concrete `K`/`E` bus
assembly, grand-product injectivity/collisions, and GKR are separate subsets.

Take the generic algebra behind Layer 5's `sideProduct_poly_eq_iff` and
`sideProduct_collision`, tracked by [leanerVM #12](https://github.com/Verified-zkEVM/leanerVM/issues/12)
and [ArkLib #901](https://github.com/Verified-zkEVM/ArkLib/issues/901).

Exact declarations: `grandProductUnivariate`, `grandProductPoly`,
`optionEquivLeft_rename_some`, `optionEquivLeft_grandProductPoly`, `eval₂_grandProductPoly`,
`map_grandProductPoly`, `map_tupleMultiset_injective`, `totalDegree_grandProductPoly`,
`roots_grandProductUnivariate`, `natDegree_grandProductUnivariate`,
`grandProductPoly_injective`, `grandProduct_difference_ne_zero`,
`mapped_grandProduct_difference_ne_zero`, `totalDegree_grandProduct_difference_le`,
`card_grandProduct_collision_le`, `prob_grandProduct_collision_le`,
`uniform_grandProduct_collision_fraction_le`, and
`uniform_grandProduct16_collision_fraction_le`.

Depends on the corrected fingerprint slice over PR #18. Category A source: leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, §5.2, Lemma 5.2 and Theorem 5.1. The product
argument is new for that specification and uses Mathlib's roots-of-products theorem and the
pinned ArkLib Schwartz-Zippel counting API; fingerprint provenance remains in its own module.

The first consumers are Layer 5's concrete bus interfaces and Layer 6. Controls cover natural
multiplicities in characteristic two, different cardinalities, empty products, dimension zero,
coefficient-map transport, and collisions caused by correlated beta. Require focused tests, full
repository validation, and standard-only transitive axiom audits. The probability statement fixes
both multisets before a uniform joint sample and gives `4 * cap / |F|` for sixteen coordinates.
Concrete `K`/`E` assembly, GKR, and conditional freshness for recycled challenges remain open.
The second PR must target the actual adopted fingerprint parent; keep it unpublished if that stacked base is unavailable.
