import FORS.Main
import Sphincs.Bridge

/-!
# leanSPHINCS in the random-permutation model

**The end theorem.** `Sphincs.leanSphincsStronglyUnforgeable` proves
`Sphincs.LeanSphincsStronglyUnforgeable` (`Statement/LeanSphincs.lean`): up to `1,182,000,000`
signatures, an adversary whose game makes at most `Q` permutation calls, `Q ≥ 1`, forges with
probability at most `(Q + 1) · 2^-127`. The route: upstream's random-oracle theorem
`FORS.h26_layered` (127 bits for `q` hash calls, the model `FORS.Scheme` at the deployed
configuration, leanVM PR #724 head `873ee6d8`), moved to the crate's key generation and signer in the model's
hash monad (`FORS.Crate`: the same keys and signatures on every answer function, with at least the
model's hash calls; `Common.SufCma.StaticSwap.romBound`), then to the random-permutation model by
`Common.SufCma.rpm_bound` (`Sphincs.Model.crateScheme_stronglyUnforgeable`), then to the statement's
scheme, which is the crate's copy with each hash query answered by Keccak-256 over `π`
(`Sphincs.Model.stronglyUnforgeable_of_model`).
-/

namespace Sphincs

/-- **leanSPHINCS is strongly unforgeable in the random-permutation model**, at 127 bits up to
`1,182,000,000` signatures. -/
theorem leanSphincsStronglyUnforgeable : LeanSphincsStronglyUnforgeable :=
  Model.stronglyUnforgeable_of_model FORS.h26_layered

end Sphincs
