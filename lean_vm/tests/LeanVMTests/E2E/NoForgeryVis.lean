import LeanVM.E2E.Vis.Deployed

/-!
# Tests: no forgery with the visible accounting (W-vis), the end theorem

* The end theorem, its form against §0 (`ε(Q_v)` plus the deviations), today's event, the
  deployed instances at every proved leanSPHINCS parameter set, the one-slot and lifetime values
  rest on Lean's three axioms.
* **The hypotheses hold together**: an adversary that asks nothing meets every query bound at
  zero, and the deployed theorem applies to it.
* **The query bounds are load-bearing**: with `qH = 2^127` hash queries the bound is at least `1`,
  so the theorem says nothing without them; with `2^64` it is below `2^-41`.
-/

namespace LeanVMTests.E2E.NoForgeryVis

open OracleComp OracleSpec LeanVM LeanVM.E2E LeanVM.Node LeanVM.Protocol.Compile.Rom
open scoped ENNReal

section Inhabitant

attribute [local instance] Sphincs.Lifetimes.full

/-- The adversary that asks nothing and outputs a fixed statement and proof. -/
noncomputable def idleAdv (nx ns : ℕ) (out : NodeStatement × IdealProof) : GameAdversary nx ns :=
  fun _ _ ↦ pure out

-- every hypothesis of the deployed theorem holds for it, at zero queries
example (nx ns fuel budget : ℕ) (out : NodeStatement × IdealProof) :
    Pr{let p ← gameRec Guest.guest fuel budget (idleAdv nx ns out)}[BreaksVis p.1.1 p.1.2] ≤
      sec0ErrorGame nx ns 13434881 15166603265 8630239197 23756655991 384 686 0 budget 0 0 0 0 :=
  aggregate_no_forgery_vis_deployed_full fuel budget (idleAdv nx ns out)
    (fun _ _ ↦ isQueryBoundP_pure _ _ _) (fun _ _ ↦ isQueryBoundP_pure _ _ _)
    (fun _ _ ↦ isQueryBoundP_pure _ _ _) (fun _ _ _ ↦ isQueryBoundP_pure _ _ _)
    (fun _ _ _ ↦ isQueryBoundP_pure _ _ _)

end Inhabitant

-- the visible budget is load-bearing: at `qH = 2^127` the bound is trivial
example (budget : ℕ) :
    1 ≤ sec0ErrorGame 1 0 13434881 15166603265 8630239197 23756655991 384 686 (2 ^ 127) budget 0 0 0
      0 := by
  rw [sec0ErrorGame, sec0Error_eq_num, ENNReal.le_div_iff_mul_le (by simp) (by simp), one_mul]
  have h : 2 ^ 256 ≤ closedNum0 (2 ^ 127 + budget)
      (1 * 13434881 + 0 * 15166603265 + (2 ^ 127 + 0 * 8630239197 + 0 * 23756655991) + budget) 1 0
      (2 * (1 + 0) + 13434881 + 0 * 8630239197 + 384) (2 * (1 + 0) + 15166603265 + 0 * 23756655991 + 686)
      (1 * 13434881 + 0 * 15166603265) := by
    unfold closedNum0
    nlinarith [Nat.zero_le budget]
  exact_mod_cast h

-- and at `qH + budget ≤ 2^64` (a lifetime) it is below `2^-41`
example {qH budget : ℕ} (hQ : qH + budget ≤ 2 ^ 64) :
    sec0ErrorGame (2 ^ 20) (2 ^ 20) 13434881 15166603265 8630239197 23756655991 384 686 qH budget
      (2 ^ 44) (2 ^ 44) (2 ^ 24) (2 ^ 24) ≤ (2 : ℝ≥0∞)⁻¹ ^ 41 :=
  sec0ErrorGame_lifetime_le (by norm_num) (by norm_num) hQ le_rfl le_rfl le_rfl le_rfl

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_eps0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_eps0

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_game

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_game_eps0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_game_eps0

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_at

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_game_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_game_at

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_full

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_full_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_full_game

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned20

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned20_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned20_game

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned14

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned14_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned14_game

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned13

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned13_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned13_game

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned12

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned12_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned12_game

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned10

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned10_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned10_game

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned8

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned8_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned8_game

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_full_eps0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_full_eps0

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned20_eps0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_deployed_pruned20_eps0

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_one_slot_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_one_slot_full

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_one_slot_pruned20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_one_slot_pruned20

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_lifetime_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_lifetime_full

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_lifetime_pruned20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_lifetime_pruned20

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_lifetime_full_eps0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_lifetime_full_eps0

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_lifetime_xmss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_lifetime_xmss

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis_lifetime_xmss_56' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery_vis_lifetime_xmss_56

end LeanVMTests.E2E.NoForgeryVis
