import Sphincs.Axioms

/-! # The end theorem of leanSPHINCS

`Sphincs.Lifetimes.requestedSecurityRpm` proves `Sphincs.Lifetimes.RequestedSecurityRpm`
(`Statement/LeanSphincs.lean`): in the random-permutation model, at every proved lifetime, an
adversary whose game makes at most `Q` permutation calls, `1 ≤ Q ≤ 2^128`, forges with probability
at most `Q / 2^127 + Q · 2^-381` (the sponge's `Q² / 2^509`, linear under the cap). Its proof passes through the random-oracle model
(`Sphincs.Lifetimes.requestedSecurity`, a step). `Sphincs/Axioms.lean` pins the axiom footprint of
every theorem of the project; the build fails if the end theorem's grows beyond Lean's three. -/

example : Sphincs.Lifetimes.RequestedSecurityRpm := Sphincs.Lifetimes.requestedSecurityRpm

/-- info: 'Sphincs.Lifetimes.requestedSecurityRpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sphincs.Lifetimes.requestedSecurityRpm
