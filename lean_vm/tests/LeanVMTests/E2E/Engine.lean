import LeanVM.E2E.Engine

/-!
# Tests: the game's engine

* The end lemmas of the game's engine rest on Lean's three axioms.
* The game's oracle answers no coin from its state and records nothing for one; a hash query is
  the log's lookup.
* Only hash queries are counted.
-/

namespace LeanVMTests.E2E.Engine

open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.E2E

/-- info: 'LeanVM.E2E.gameImpl_isLazySampler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gameImpl_isLazySampler

/-- info: 'LeanVM.E2E.prEvent_game_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prEvent_game_le

/-- info: 'LeanVM.E2E.prEvent_game_le_of_freshStepBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prEvent_game_le_of_freshStepBelow

/-- info: 'LeanVM.E2E.isQueryBoundP_idealVerify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isQueryBoundP_idealVerify

/-- info: 'LeanVM.E2E.isQueryBoundP_gameComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isQueryBoundP_gameComp

/-- A coin query is never answered by the log. -/
example (ℓ : Log) (n : ℕ) : gameLookup ℓ (.inl n) = none := rfl

/-- A coin query records nothing. -/
example (ℓ : Log) (n : ℕ) (u : Fin (n + 1)) : gameRecord ℓ (.inl n) u = ℓ := rfl

/-- A hash query is the log's lookup and appends the fresh entry. -/
example (ℓ : Log) (x : Bytes) (u : Digest) :
    gameLookup ℓ (.inr x) = look ℓ x ∧ gameRecord ℓ (.inr x) u = ℓ ++ [(x, u)] := ⟨rfl, rfl⟩

/-- Hash queries are counted, coins are not. -/
example (x : Bytes) (n : ℕ) : IsHash (.inr x) ∧ ¬ IsHash (.inl n) := ⟨trivial, id⟩

end LeanVMTests.E2E.Engine

/-! The outer check's bytecode part is implied by the deployed one. -/

/-- info: 'LeanVM.Node.DeferredClaim.bytecodeHolds_of_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Node.DeferredClaim.bytecodeHolds_of_holds
