import LeanVM.E2E.Vis.PerKey.SphincsRest

/-!
# Tests: W-vis P7b (leanSPHINCS), its axioms

The per-key leanSPHINCS reduction (`LeanVM.E2E.Vis.PerKey.Sphincs`), its run under the single-key
game's oracles (`SphincsRun`) and its rest being the class-routed game (`SphincsRest`) rest on
Lean's standard axioms only (`run_sphincsFwdJ` needs no choice).
-/

/-- info: 'LeanVM.E2E.PerKeyS.fst_signingOracleDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.fst_signingOracleDet

/-- info: 'LeanVM.E2E.PerKeyS.simulateQ_σJS_liftSig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.simulateQ_σJS_liftSig

/-- info: 'LeanVM.E2E.PerKeyS.ΦJS_signQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.ΦJS_signQuery

/-- info: 'LeanVM.E2E.PerKeyS.ΦJS_rcS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.ΦJS_rcS

/-- info: 'LeanVM.E2E.PerKeyS.ΦJS_rpS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.ΦJS_rpS

/-- info: 'LeanVM.E2E.PerKeyS.run_sphincsFwdJ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.run_sphincsFwdJ

/-- info: 'LeanVM.E2E.PerKeyS.route_sLift_sign_jS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.route_sLift_sign_jS

/-- info: 'LeanVM.E2E.PerKeyS.stMap_ΦJS_advImplJS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.stMap_ΦJS_advImplJS

/-- info: 'LeanVM.E2E.PerKeyS.ΦJS_adv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.ΦJS_adv

/-- info: 'LeanVM.E2E.PerKeyS.map_ΦJS_restJS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.map_ΦJS_restJS
