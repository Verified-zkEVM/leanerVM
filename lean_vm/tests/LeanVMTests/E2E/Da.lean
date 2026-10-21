import LeanVM.E2E.Da

/-!
# Tests: the DA leg in the random-oracle model

* The end lemmas of the DA leg rest on Lean's three axioms.
* **The anchor is the chain's.** The membership challenges observe the root's halves with the
  blocks `obsBlock ρ 0` and `obsBlock ρ 1`, and the entry observing the second half, after the
  one observing the first, completes the root (`DaRootOf`).
* The empty log has potential zero and no failure; a repeated answer is a failure.
-/

namespace LeanVMTests.E2E.Da

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom
open LeanVM.E2E

/-- info: 'LeanVM.E2E.daBacked_of_not_daBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms daBacked_of_not_daBad

/-- info: 'LeanVM.E2E.prEvent_game_daBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prEvent_game_daBad_le

/-- info: 'LeanVM.E2E.prEvent_game_daUnbacked_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prEvent_game_daUnbacked_le

/-- info: 'LeanVM.E2E.prEvent_game_daUnbacked_le_of_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prEvent_game_daUnbacked_le_of_costs

/-- info: 'LeanVM.E2E.daPot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms daPot_step

/-- info: 'LeanVM.E2E.rows_eq_of_colTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rows_eq_of_colTree

/-- info: 'LeanVM.E2E.colTree_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms colTree_take

/-- info: 'LeanVM.E2E.sum_daChallenge_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_daChallenge_div

/-- The chain's first observation hashes the state and `obsBlock ρ 0`. -/
example {m : Type → Type} [Monad m] (HD : List UInt8 → m LeanDa.Digest) (s ρ : LeanDa.Digest) :
    LeanVM.Da.compressWordsWith HD s [LeanDa.word ρ 0, LeanDa.word ρ 1, 0, LeanDa.K.ofBits 1] =
      HD (s.toList ++ obsBlock ρ 0) := rfl

/-- The chain's second observation hashes the state and `obsBlock ρ 1`. -/
example {m : Type → Type} [Monad m] (HD : List UInt8 → m LeanDa.Digest) (s ρ : LeanDa.Digest) :
    LeanVM.Da.compressWordsWith HD s [LeanDa.word ρ 2, LeanDa.word ρ 3, 0, LeanDa.K.ofBits 1] =
      HD (s.toList ++ obsBlock ρ 1) := rfl

/-- A squeeze hashes the state and the squeeze block. -/
example (ℓ : Log) (d : Digest) :
    LeanVM.Da.compressWordsWith (LeanVM.Da.daHash (look ℓ)) (LeanVM.Da.toBytes d)
      [0, 0, 0, LeanDa.K.ofBits 2] = LeanVM.Da.daHash (look ℓ) (sqIn d) := rfl

/-- **The anchor**: after the first observation, the second completes the root. -/
example (d0 d1 : Digest) (ρ : LeanDa.Digest) :
    DaRootOf [(digestBytes d0 ++ obsBlock ρ 0, d1)] (digestBytes d1 ++ obsBlock ρ 1) ρ :=
  ⟨d1, (digestBytes d0 ++ obsBlock ρ 0, d1), rfl, by simp, List.drop_left' (digestBytes_length d0)⟩

/-- The empty log has potential zero. -/
example (pc : LeanDa.Digest) : daPot pc [] = 0 := daPot_nil pc

/-- The empty log has not failed. -/
example (pc : LeanDa.Digest) : ¬ FailDA pc [] := not_failDA_nil pc

/-- A repeated answer fails. -/
example (pc : LeanDa.Digest) (x t : Bytes) (u : Digest) : FailDA pc [(x, u), (t, u)] :=
  ⟨1, by simp, Or.inl ⟨(x, u), by simp, rfl⟩⟩

/-- An answer equal to the padding digest fails. -/
example (t : Bytes) (u : Digest) : FailDA (LeanVM.Da.toBytes u) [(t, u)] :=
  ⟨0, by simp, Or.inr (Or.inl rfl)⟩

end LeanVMTests.E2E.Da
