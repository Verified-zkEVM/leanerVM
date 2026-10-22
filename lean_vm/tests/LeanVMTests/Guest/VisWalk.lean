import LeanVM.E2E.Vis.WalkSphincs

/-!
# Tests: the scheme walks (W-vis, P2b and P2c)

Every query of leanXMSS's and leanSPHINCS's key generation, signer and verifier is a derivation or
a scheme input of the key's parameter (`SchemeInput`: `P ‖ A ‖ …`, at least 48 bytes). The shapes
are checked on concrete inputs, and the walks rest on Lean's three standard axioms only.
-/

open LeanVM.E2E

/-- A key's parameter, `16` bytes. -/
def visWalkP : List UInt8 := List.replicate 16 7

-- a chain step's input is a scheme input of its key, not shaped as a derivation
#guard decide (SchemeInputN visWalkP
  (visWalkP ++ LeanXmss.fieldBytes (LeanXmss.tweakFields 1 2 0 5) ++ List.replicate 32 0))
#guard decide (SchemeInputN visWalkP
  (visWalkP ++ Sphincs.fieldBytes (Sphincs.tweakFields 15 3 9 5) ++ List.replicate 16 0))
-- not of another key's parameter
#guard !decide (SchemeInput (List.replicate 16 8)
  (visWalkP ++ LeanXmss.fieldBytes (LeanXmss.tweakFields 1 2 0 5) ++ List.replicate 32 0))
-- too short: a 16-byte payload is the least
#guard !decide (SchemeInput visWalkP
  (visWalkP ++ LeanXmss.fieldBytes (LeanXmss.tweakFields 1 2 0 5) ++ List.replicate 8 0))
-- a non-zero byte in the address's last 8: not an address
#guard !decide (ParamPrefixed visWalkP
  (visWalkP ++ List.replicate 15 0 ++ [1] ++ List.replicate 32 0))
-- the parameter derivation under parameter `0` is a derivation, not a scheme input of `0^16`
#guard decide (DerivShape (paramPrefix ++ List.replicate 32 3))
#guard !decide (SchemeInputN (List.replicate 16 0) (paramPrefix ++ List.replicate 32 3))

example : paramPrefix.length = 32 := paramPrefix_length

/-- info: 'LeanVM.E2E.xmss_sign_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.xmss_sign_queries

/-- info: 'LeanVM.E2E.xmss_sign_queriesN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.xmss_sign_queriesN

/-- info: 'LeanVM.E2E.xmss_verify_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.xmss_verify_queries

/-- info: 'LeanVM.E2E.xmss_verify_queriesN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.xmss_verify_queriesN

/-- info: 'LeanVM.E2E.xmss_keygen_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.xmss_keygen_queries

/-- info: 'LeanVM.E2E.xmss_keygen_queriesN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.xmss_keygen_queriesN

/-- info: 'LeanVM.E2E.xmss_keygen_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.xmss_keygen_param

/-- info: 'LeanVM.E2E.xmss_keygen_deriv_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.xmss_keygen_deriv_count

/-- info: 'LeanVM.E2E.sphincs_sign_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincs_sign_queries

/-- info: 'LeanVM.E2E.sphincs_sign_queriesN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincs_sign_queriesN

/-- info: 'LeanVM.E2E.sphincs_verify_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincs_verify_queries

/-- info: 'LeanVM.E2E.sphincs_verify_queriesN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincs_verify_queriesN

/-- info: 'LeanVM.E2E.sphincs_keygen_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincs_keygen_queries

/-- info: 'LeanVM.E2E.sphincs_keygen_queriesN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincs_keygen_queriesN

/-- info: 'LeanVM.E2E.sphincs_keygen_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincs_keygen_param

/-- info: 'LeanVM.E2E.sphincs_keygen_deriv_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincs_keygen_deriv_count
