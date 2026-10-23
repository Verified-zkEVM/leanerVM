import LeanVM.Protocol.LeanVM

/-! The theorems: the verifier's, `LeanVM.KnowledgeSoundness` and `LeanVM.Completeness`
(`LeanVM/Spec/Statement.lean`), for leanVM at `keccak-gkr` (Keccak-256 and Keccak-f[1600] as
independent random oracles). The build fails if their axiom footprint ever grows beyond Lean's
three standard axioms. -/

/-- info: 'LeanVM.knowledgeSoundness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.knowledgeSoundness_holds

/-- info: 'LeanVM.candidates_ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.candidates_ncard_le

/-- info: 'LeanVM.soundnessError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.soundnessError_le

/-- info: 'LeanVM.completenessError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completenessError_le

/-- info: 'LeanVM.completeness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_holds
