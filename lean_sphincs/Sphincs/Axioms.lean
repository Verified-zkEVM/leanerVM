import Sphincs.Security

/-! **The axioms of this project's theorems.** The end theorem and the steps of its route depend on
`propext`, `Classical.choice` and `Quot.sound` alone; `FORS/Axioms.lean` pins the model's. -/

/-- info: 'Sphincs.leanSphincsStronglyUnforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sphincs.leanSphincsStronglyUnforgeable

/-- info: 'Sphincs.Model.stronglyUnforgeable_of_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sphincs.Model.stronglyUnforgeable_of_model

/-- info: 'Sphincs.Model.modelScheme_stronglyUnforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sphincs.Model.modelScheme_stronglyUnforgeable

/-- info: 'Sphincs.Model.simulateQ_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sphincs.Model.simulateQ_verify

/-- info: 'Sphincs.Model.simulateQ_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sphincs.Model.simulateQ_keygen

/-- info: 'Sphincs.Model.simulateQ_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sphincs.Model.simulateQ_sign

/-- info: 'Sphincs.Transport.forgeryGame_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sphincs.Transport.forgeryGame_eq
