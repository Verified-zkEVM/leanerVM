import LeanXmss.Statement
import XmssSecurity.Proof.Bridge.Security
import XmssSecurity.Rpm

/-! # The end theorem of leanXMSS

`XmssSecurity.leanXmss_rpm_security` (`XmssSecurity/Rpm.lean`) proves
`LeanXmss.Rpm.LeanXmssStronglyUnforgeable` (`Statement/LeanXmss.lean`): in the
random-permutation model, an adversary whose game makes at most `Q` permutation calls,
`1 ≤ Q ≤ 2^128`, forges with probability at most `(Q + 1) · 2^-127` (from
`Q / 2^127 + Q² / 2^509`, the sponge's indifferentiability added). Its proof passes through the random-oracle
model (`leanXmss_has_127_bits_of_classical_security`, a step). -/

example : LeanXmss.Rpm.LeanXmssStronglyUnforgeable := XmssSecurity.leanXmss_rpm_security

namespace XmssSecurity

/-- leanXMSS has 127 bits of classical security in the random-oracle model: the step of the proof
of the end statement, `leanXmss_rpm_security` (`XmssSecurity/Rpm.lean`), in the
random-permutation model. -/
theorem leanXmss_has_127_bits_of_classical_security : LeanXmss.LeanXmssSecurityStatement :=
  Bridge.leanXmss_security

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'XmssSecurity.leanXmss_has_127_bits_of_classical_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leanXmss_has_127_bits_of_classical_security

/-- info: 'XmssSecurity.leanXmss_rpm_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leanXmss_rpm_security

/-- info: 'XmssSecurity.leanXmss_rpm_security_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leanXmss_rpm_security_calls

end XmssSecurity
