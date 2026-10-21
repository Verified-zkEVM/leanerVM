import LeanVM.E2E.Guest

/-!
# Tests: T2 and T4 without hypotheses

The guest's open callees hold over every hash model; T2 and T4 then need no hypothesis. Their
axioms are Lean's three. -/

/-- info: 'LeanVM.E2E.guestHypsM_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.guestHypsM_model

/-- info: 'LeanVM.E2E.guest_knowledge_model_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.guest_knowledge_model_all

/-- info: 'LeanVM.E2E.aggregate_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_knowledge

/-- info: 'LeanVM.E2E.prEvent_game_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_game_aggregate

/-- The deployed hash model is one of the models T2 covers. -/
example : LeanVM.Guest.Located.GuestHypsM LeanVM.Guest.Value.HashModel.deployed :=
  LeanVM.E2E.guestHypsM_model _
