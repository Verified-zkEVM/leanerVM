import Sphincs.Axioms

/-! # The end theorem of leanSPHINCS

`Sphincs.leanSphincsStronglyUnforgeable` proves `Sphincs.LeanSphincsStronglyUnforgeable`
(`Statement/LeanSphincs.lean`): in the random-permutation model, up to `1,182,000,000` signatures,
an adversary whose game makes at most `Q` permutation calls, for every `Q ≥ 1`, forges with
probability at most `(Q + 1) · 2^-127` (from `Q / 2^127 + Q² / 2^509`, the sponge's
indifferentiability added). Its proof passes through the random-oracle model (upstream's
`FORS.h26_layered`, a step) and upstream's model of the scheme (`FORS.Scheme`, leanVM `5e3ade21`),
then the crate's key generation and signer in the model's hash monad (`FORS.Crate`, by
`Common.SufCma.StaticSwap`), the statement's scheme through the maps of `Sphincs/Model.lean`.
`Sphincs/Axioms.lean` and `FORS/Axioms.lean` pin the axiom footprints; the build fails if the
end theorem's grows beyond Lean's three. -/

example : Sphincs.LeanSphincsStronglyUnforgeable := Sphincs.leanSphincsStronglyUnforgeable

/-- info: 'Sphincs.leanSphincsStronglyUnforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sphincs.leanSphincsStronglyUnforgeable
