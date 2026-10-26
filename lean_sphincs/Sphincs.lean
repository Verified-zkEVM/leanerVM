import Sphincs.Axioms

/-! # The end theorem of leanSPHINCS

`Sphincs.Lifetimes.requestedSecurityRpm` proves `Sphincs.Lifetimes.RequestedSecurityRpm`
(`Statement/LeanSphincs.lean`): in the random-permutation model, at every proved lifetime, an
adversary whose game makes at most `Q` permutation calls, `1 ≤ Q ≤ 2^128`, forges with probability
at most `(Q + 1) · 2^-127` (from `Q / 2^127 + Q² / 2^509`, the sponge's indifferentiability
added). Its proof passes through the random-oracle model
(`SphincsLayered.Lifetimes.requestedSecurity`, a step) and the layered presentation of the scheme,
the statement's scheme through a bijection of the signatures (`Sphincs.OneLayer`).
`Sphincs/Axioms.lean` pins the axiom footprint of every theorem of the project; the build fails if
the end theorem's grows beyond Lean's three. -/

example : Sphincs.Lifetimes.RequestedSecurityRpm := Sphincs.Lifetimes.requestedSecurityRpm

/-- info: 'Sphincs.Lifetimes.requestedSecurityRpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sphincs.Lifetimes.requestedSecurityRpm
