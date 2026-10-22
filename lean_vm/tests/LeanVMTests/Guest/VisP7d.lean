import LeanVM.E2E.Vis.PerKey.Coll

/-!
# Tests: key coincidences in key generation (W-vis, P7d)

The bound on key `idx`'s coincidences in the key-generation phase and in the game with V_I's
trace, and its parts: a parameter is hit by at most `2^128` answers, settling a parameter input
keeps the core a supermartingale, key generation draws its seeds first, and two of `m` uniform
seeds coincide with probability at most `2^-256`. They rest on Lean's three standard axioms only.
-/

open LeanVM.E2E LeanVM.Protocol.Compile.Rom
open scoped ENNReal

-- the parameter input is 64 bytes, and no seed input is
example (S : LeanVM.Protocol.Digest) : (kcParamIn S).length = 64 := length_kcParamIn S

example (sx : Fin 2 → LeanXmss.MasterSeed) (ss : Fin 3 → Sphincs.MasterSeed) (i : Fin 5) :
    (kcSeedIn sx ss i).length ≠ 64 :=
  length_kcSeedIn_ne sx ss i

-- with no key determined, the pending checks are `2n - 1`
example : kcPend (2 : Fin 4) (fun _ ↦ (none : Option LeanVM.Protocol.Digest)) = 7 := by
  unfold kcPend; simp

-- the empty log has not failed
example : ¬ KcGlob [] := not_kcGlob_nil

/-- info: 'LeanVM.E2E.kc_sum_parBytes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.kc_sum_parBytes_le

/-- info: 'LeanVM.E2E.kc_sum_core_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.kc_sum_core_le

/-- info: 'LeanVM.E2E.kc_sum_hidPot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.kc_sum_hidPot_le

/-- info: 'LeanVM.E2E.kc_sum_globPot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.kc_sum_globPot_le

/-- info: 'LeanVM.E2E.kc_prEvent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.kc_prEvent_le

/-- info: 'LeanVM.E2E.kcKeygenFrom_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.kcKeygenFrom_post

/-- info: 'LeanVM.E2E.keygenPhase_seedsFirst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.keygenPhase_seedsFirst

/-- info: 'LeanVM.E2E.prEvent_seeds_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_seeds_eq_le

/-- info: 'LeanVM.E2E.prEvent_kcKeygenFrom_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_kcKeygenFrom_le

/-- info: 'LeanVM.E2E.prEvent_keygenPhase_keyCollAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_keygenPhase_keyCollAt_le

/-- info: 'LeanVM.E2E.prEvent_gameRec_keyCollAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_gameRec_keyCollAt_le
