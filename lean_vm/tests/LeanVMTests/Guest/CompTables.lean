import LeanVM.Guest.B1.Comp.Tables.CompletesB
import LeanVM.Guest.B1.Comp.Tables.DeployedC
import LeanVM.Guest.B1.Comp.Tables.RunInv
import LeanVM.Guest.B1.Comp.Tables.RunFrameM
import LeanVM.Guest.B1.Comp.Tables.FlockAllC
import LeanVM.Guest.B1.Comp.Tables.GkrAllC
import LeanVM.Guest.B1.Comp.Tables.FwdIC
import LeanVM.Guest.B1.Comp.Tables.VtTraceC
import LeanVM.Guest.B1.Comp.Tables.VtLoopsC
import LeanVM.Guest.B1.Comp.Tables.VtWindowsC
import LeanVM.Guest.B1.Comp.Tables.VtChainC
import LeanVM.Guest.B1.Comp.Tables.VtAtB
import LeanVM.Guest.B1.Comp.Tables.VtBodyC
import LeanVM.Guest.B1.Comp.Tables.VtAllC
import LeanVM.Guest.B1.Comp.Tables.FlockAtC
import LeanVM.Guest.B1.Comp.Tables.GkrAtC
import LeanVM.Guest.B1.Comp.Tables.VtPlacedC
import LeanVM.Guest.B1.Comp.Tables.VtKidsC
import LeanVM.Guest.B1.Comp.Tables.VtPlacedB
import LeanVM.Guest.B1.Comp.Tables.ShapesWS
import LeanVM.Guest.B1.Comp.Tables.IfaceC
import LeanVM.Guest.B1.Comp.Tables.CalleesC

/-!
# Tests: the tables over a completeness model, their axioms

The completeness over a `CompModel` of the guest's `verify_flock`, `verify_bus_gkr` and
`verify_tables` (`LeanVM.Guest.B1.Comp.Tables`), at the relation and in the placed form within
weights, and the deployed completeness lemmas recovered from them at `CompModel.deployed`, rest on
Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.Sig.Completes.toB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.Completes.toB

/-- info: 'LeanVM.Guest.B1.Sig.Completes.toBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.Completes.toBC

/-- info: 'LeanVM.Guest.B1.Sig.Completes.toRelB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.Completes.toRelB

/-- info: 'LeanVM.Guest.B1.Sig.CompletesB.toDeployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.CompletesB.toDeployed

/-- info: 'LeanVM.Guest.B1.RunsToM.sumcheck_eq_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.RunsToM.sumcheck_eq_inv

/-- info: 'LeanVM.Guest.B1.RunsToM.sumcheck_plain_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.RunsToM.sumcheck_plain_inv

/-- info: 'LeanVM.Guest.B1.runM_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.runM_frame

/-- info: 'LeanVM.Guest.B1.RunsToM.bind_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.RunsToM.bind_inv

/-- info: 'LeanVM.Guest.B1.flock_invC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.flock_invC

/-- info: 'LeanVM.Guest.B1.loop81_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.loop81_completeC

/-- info: 'LeanVM.Guest.B1.loop82_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.loop82_completeC

/-- info: 'LeanVM.Guest.B1.flock_body_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.flock_body_completeC

/-- info: 'LeanVM.Guest.B1.verify_flock_relC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_flock_relC

/-- info: 'LeanVM.Guest.B1.verify_flock_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_flock_completeC

/-- info: 'LeanVM.Guest.B1.loop81_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.loop81_complete_of_comp

/-- info: 'LeanVM.Guest.B1.loop82_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.loop82_complete_of_comp

/-- info: 'LeanVM.Guest.B1.verify_flock_rel_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_flock_rel_of_comp

/-- info: 'LeanVM.Guest.B1.verify_flock_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_flock_complete_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.RunsToM.gkrPhase_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.RunsToM.gkrPhase_inv

/-- info: 'LeanVM.Guest.B1.VerifySub.exists_traceM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.exists_traceM

/-- info: 'LeanVM.Guest.B1.VerifySub.loop10_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.loop10_completeC

/-- info: 'LeanVM.Guest.B1.VerifySub.loop101_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.loop101_completeC

/-- info: 'LeanVM.Guest.B1.VerifySub.vbg_holdsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vbg_holdsC

/-- info: 'LeanVM.Guest.B1.VerifySub.gkr_loop10C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.gkr_loop10C

/-- info: 'LeanVM.Guest.B1.VerifySub.gkr_loop11C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.gkr_loop11C

/-- info: 'LeanVM.Guest.B1.VerifySub.gkr_holdsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.gkr_holdsC

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_bus_gkr_relC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_bus_gkr_relC

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_bus_gkr_runC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_bus_gkr_runC

/-- info: 'LeanVM.Guest.B1.VerifySub.gkr_loop10_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.gkr_loop10_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.gkr_loop11_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.gkr_loop11_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.gkr_holds_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.gkr_holds_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.completes_itemsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.completes_itemsC

/-- info: 'LeanVM.Guest.B1.VerifySub.fRunIC_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.fRunIC_holds

/-- info: 'LeanVM.Guest.B1.VerifySub.RunsToM.tablesSeg_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.RunsToM.tablesSeg_trace

/-- info: 'LeanVM.Guest.B1.VerifySub.loop79_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.loop79_completeC

/-- info: 'LeanVM.Guest.B1.VerifySub.vt_ev_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vt_ev_completeC

/-- info: 'LeanVM.Guest.B1.VerifySub.vt_zc_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vt_zc_completeC

/-- info: 'LeanVM.Guest.B1.VerifySub.vt_c_tailC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vt_c_tailC

/-- info: 'LeanVM.Guest.B1.VerifySub.vt_phaseDC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vt_phaseDC

/-- info: 'LeanVM.Guest.B1.VerifySub.vt_final_cB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vt_final_cB

/-- info: 'LeanVM.Guest.B1.VerifySub.vt_bodyC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vt_bodyC

/-- info: 'LeanVM.Guest.B1.VerifySub.vt_body_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vt_body_of_comp

/-- info: 'LeanVM.Guest.B1.completeAtS_straightW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_straightW

/-- info: 'LeanVM.Guest.B1.completeAtS_flatW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_flatW

/-- info: 'LeanVM.Guest.B1.vtcS_completeAt_of_rel_lowW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.vtcS_completeAt_of_rel_lowW

/-- info: 'LeanVM.Guest.B1.vtcS_completeAt_iteW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.vtcS_completeAt_iteW

/-- info: 'LeanVM.Guest.B1.l81S_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.l81S_total

/-- info: 'LeanVM.Guest.B1.l82S_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.l82S_total

/-- info: 'LeanVM.Guest.B1.flMemC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.flMemC_of

/-- info: 'LeanVM.Guest.B1.verify_flock_completeAtWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_flock_completeAtWC

/-- info: 'LeanVM.Guest.B1.verify_flock_completeAtW_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_flock_completeAtW_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.vtcS_l10_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vtcS_l10_total

/-- info: 'LeanVM.Guest.B1.VerifySub.gkrMemC_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.gkrMemC_at

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_bus_gkr_completeAtWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_bus_gkr_completeAtWC

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_bus_gkr_completeAtW_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_bus_gkr_completeAtW_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.vt_placed_okB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vt_placed_okB

/-- info: 'LeanVM.Guest.B1.VerifySub.vtcS_l79_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vtcS_l79_total

/-- info: 'LeanVM.Guest.B1.VerifySub.loop79_completeAtWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.loop79_completeAtWC

/-- info: 'LeanVM.Guest.B1.VerifySub.vtc_zcRound_honestM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vtc_zcRound_honestM

/-- info: 'LeanVM.Guest.B1.VerifySub.vt_kids_completeWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vt_kids_completeWC

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_tables_completeAtWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_tables_completeAtWC

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_tables_relC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_tables_relC

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_tables_completeAtW_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_tables_completeAtW_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteGkrAtWC.toDeployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteGkrAtWC.toDeployed

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteTablesAtWC.toDeployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteTablesAtWC.toDeployed

/-- info: 'LeanVM.Guest.B1.VerifySub.CompleteFlockAtWC.toDeployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.CompleteFlockAtWC.toDeployed

/-- info: 'LeanVM.Guest.B2C.gkrC_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.gkrC_b2c

/-- info: 'LeanVM.Guest.B2C.tablesC_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.tablesC_b2c

/-- info: 'LeanVM.Guest.B2C.flockC_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B2C.flockC_b2c
