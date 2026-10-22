import LeanVM.E2E.Complete.Count.Xmss
import LeanVM.E2E.Complete.Count.Sphincs

/-!
# Tests: a held signature's log count (L17, B1 and B2)

A held leanXMSS signature's verification logs at most `xmssVerifyBlocks = 384 · 14 = 5376` block
prefixes, a leanSPHINCS one at most `sphincsVerifyBlocks = 686 · 16 = 10976`; both caps are below
`2^20` (by `decide`, on `propext` alone), and the bounds rest on Lean's three standard axioms only.
-/

open LeanVM.E2E LeanVM.E2E.Complete

example : xmssQueryLen = 960 := by decide
example : xmssVerifyBlocks = 5376 := by decide
example : sphincsQueryLen = 1056 := by decide
example : sphincsVerifyBlocks = 10976 := by decide

/-- info: 'LeanVM.E2E.Complete.prefixCount_xmssVerifyWith_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.prefixCount_xmssVerifyWith_le

/-- info: 'LeanVM.E2E.Complete.xmssVerifyBlocks_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.xmssVerifyBlocks_le

/-- info: 'LeanVM.E2E.Complete.xmssVerify_allQueriesSatisfy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.xmssVerify_allQueriesSatisfy

/-- info: 'LeanVM.E2E.Complete.prefixCount_sphincsVerifyWith_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.prefixCount_sphincsVerifyWith_le

/-- info: 'LeanVM.E2E.Complete.sphincsVerifyBlocks_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.sphincsVerifyBlocks_le

/-- info: 'LeanVM.E2E.Complete.sphincsVerify_allQueriesSatisfy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.sphincsVerify_allQueriesSatisfy
