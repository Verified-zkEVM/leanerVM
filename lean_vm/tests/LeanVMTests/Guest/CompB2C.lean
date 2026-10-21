import LeanVM.Guest.B2C.B2FinalB
import LeanVM.Guest.B2C.CntWeightB

/-!
# Tests: the B2C layer under any `BLAKE2S` semantics (L2, B2C)

* The generic lemmas of `Guest/B2C/*B.lean` (counted runs, the completeness walk, the sharing
  check, the honest frames, B2) and `Guest/B2C/SemDeployed.lean` rest on Lean's three axioms.
* **At the deployed semantics they are the deployed ones**: `cplRunB_of`, `countB_eq_of_runC`
  and `b2B_complete` at `blakeDeployed`, through the `…B_deployed` lemmas, give `cplRun_of`,
  `count_eq_of_runC` and `b2_complete`; `b2cB2_of_B`, `b2cCount_of_B` re-derive `b2cB2`,
  `b2cCount` (`B2FinalB.lean`).
-/

namespace LeanVMTests.Guest.CompB2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.B2C.runCountB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.runCountB_deployed

/-- info: 'LeanVM.Guest.B2C.runCB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.runCB_deployed

/-- info: 'LeanVM.Guest.B2C.countB_eq_of_runC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.countB_eq_of_runC

/-- info: 'LeanVM.Guest.B2C.execB_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.execB_completeC

/-- info: 'LeanVM.Guest.B2C.execWinB_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.execWinB_completeC

/-- info: 'LeanVM.Guest.B2C.segGoodCB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.segGoodCB_deployed

/-- info: 'LeanVM.Guest.B2C.execWinB_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.execWinB_z

/-- info: 'LeanVM.Guest.B2C.segZB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.segZB_deployed

/-- info: 'LeanVM.Guest.B2C.kidsRunB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.kidsRunB_deployed

/-- info: 'LeanVM.Guest.B2C.cplRunB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.cplRunB_deployed

/-- info: 'LeanVM.Guest.B2C.lHoldsB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.lHoldsB_deployed

/-- info: 'LeanVM.Guest.B2C.cwOkB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.cwOkB_deployed

/-- info: 'LeanVM.Guest.B2C.justIB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.justIB_sound

/-- info: 'LeanVM.Guest.B2C.passLB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.passLB_sound

/-- info: 'LeanVM.Guest.B2C.walkB_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.walkB_Z

/-- info: 'LeanVM.Guest.B2C.whB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.whB_deployed

/-- info: 'LeanVM.Guest.B2C.fnHB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.fnHB_deployed

/-- info: 'LeanVM.Guest.B2C.cplB_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.cplB_run

/-- info: 'LeanVM.Guest.B2C.cplGoalB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.cplGoalB_deployed

/-- info: 'LeanVM.Guest.B2C.cplRunB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.cplRunB_of

/-- info: 'LeanVM.Guest.B2C.KeyHoldsB.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.KeyHoldsB.unique

/-- info: 'LeanVM.Guest.B2C.semFunctional_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.semFunctional_deployed

/-- info: 'LeanVM.Guest.B2C.keyHoldsB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.keyHoldsB_deployed

/-- info: 'LeanVM.Guest.B2C.invB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.invB_deployed

/-- info: 'LeanVM.Guest.B2C.shareOkB_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.shareOkB_path

/-- info: 'LeanVM.Guest.B2C.readB_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.readB_val

/-- info: 'LeanVM.Guest.B2C.readB_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.readB_stat

/-- info: 'LeanVM.Guest.B2C.frameHoldsB_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.frameHoldsB_all

/-- info: 'LeanVM.Guest.B2C.jumpTablesB_honestC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.jumpTablesB_honestC

/-- info: 'LeanVM.Guest.B2C.cntB_le_weight_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.cntB_le_weight_valid

/-- info: 'LeanVM.Guest.B2C.cntB_le_weight_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.cntB_le_weight_arm

/-- info: 'LeanVM.Guest.B2C.b2B_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.b2B_complete

/-- info: 'LeanVM.Guest.B2C.b2B_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.b2B_count

/-- info: 'LeanVM.Guest.B2C.b2HypsB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.b2HypsB_deployed

/-- info: 'LeanVM.Guest.B2C.instRunsB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.instRunsB_deployed

/-- info: 'LeanVM.Guest.B2C.cplRunB_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.cplRunB_all

/-- info: 'LeanVM.Guest.B2C.b2HypsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.b2HypsB

/-- info: 'LeanVM.Guest.B2C.b2cB2B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.b2cB2B

/-- info: 'LeanVM.Guest.B2C.b2cCountB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.b2cCountB

/-- info: 'LeanVM.Guest.B2C.b2cB2B_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.b2cB2B_deployed

/-- info: 'LeanVM.Guest.B2C.b2cCountB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.b2cCountB_deployed

/-- info: 'LeanVM.Guest.B2C.b2cB2_of_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.b2cB2_of_B

/-- info: 'LeanVM.Guest.B2C.b2cCount_of_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.b2cCount_of_B

/-- info: 'LeanVM.Guest.holdsB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.holdsB_deployed

/-- info: 'LeanVM.Guest.reachB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.reachB_deployed

/-- info: 'LeanVM.Guest.Exec.followsB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Exec.followsB_deployed

/-- info: 'LeanVM.Guest.Exec.runKB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Exec.runKB_deployed

/-! ## At the deployed semantics -/

/-- `cplRunB_of` at `blakeDeployed` is `cplRun_of`. -/
example {j : ℕ} (h1 : 1 ≤ j) (hj : j < nFns) (hok : CplOk j) : CplRun j := by
  rw [← cplRunB_deployed]
  exact cplRunB_of h1 hj hok

/-- `countB_eq_of_runC` at `blakeDeployed` is `count_eq_of_runC`. -/
example {κ : ℕ} {prog : LeanVM.Semantics.Program} {L : MemImage κ} {n : ℕ} {c : Opcode → ℕ}
    (hc : RunC prog L Regs.initial (Regs.final prog) c)
    (hn : run prog L n Regs.initial = some (Regs.final prog)) (op : Opcode) :
    (⟨κ, L, n⟩ : Trace prog).count op = c op := by
  rw [← runCountB_deployed_count]
  exact countB_eq_of_runC (by rwa [runCB_deployed]) (by rwa [runB_deployed]) op

/-- `b2B_complete` at `blakeDeployed` is `b2_complete`. -/
example (h : B2Hyps) : B2cB2 := by
  rw [← b2cB2B_deployed]
  exact b2B_complete (by rwa [b2HypsB_deployed])

end LeanVMTests.Guest.CompB2C
