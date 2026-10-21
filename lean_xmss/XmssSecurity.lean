import LeanXmss.Statement
import LeanXmss.MultiUserStatement
import XmssSecurity.Proof.Bridge.Security
import XmssSecurity.Proof.Bridge.AttributedSecurity
import XmssSecurity.Proof.MultiUser.Security

namespace XmssSecurity

/-- leanXMSS has 127 bits of classical security. -/
theorem leanXmss_has_127_bits_of_classical_security : LeanXmss.LeanXmssSecurityStatement :=
  Bridge.leanXmss_security

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'XmssSecurity.leanXmss_has_127_bits_of_classical_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leanXmss_has_127_bits_of_classical_security

/-- leanXMSS has its attributed security: two units per expected hash call attributable to the key. -/
theorem leanXmss_has_attributed_security : LeanXmss.LeanXmssAttributedSecurityStatement :=
  Bridge.leanXmss_attributedSecurity

/-- info: 'XmssSecurity.leanXmss_has_attributed_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leanXmss_has_attributed_security

/-- leanXMSS has multi-user security: `n` keys and `q` hash calls in all cost `q / 2^127`, a pair term
`n^2 / 2^127` and a second-order term `q^2 / 2^252`. -/
theorem leanXmss_has_multi_user_security : LeanXmss.LeanXmssMultiUserSecurityStatement :=
  MultiUser.leanXmss_multiUserSecurity

/-- info: 'XmssSecurity.leanXmss_has_multi_user_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leanXmss_has_multi_user_security

end XmssSecurity
