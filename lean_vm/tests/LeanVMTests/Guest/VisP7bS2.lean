import LeanVM.E2E.Vis.PerKey.SphincsKeygen

/-!
# Tests: W-vis P7b (leanSPHINCS, the other keys' generation), its axioms

The per-key leanSPHINCS reduction's generations of the other keys, under the single-key game's
oracles (`LeanVM.E2E.Vis.PerKey.SphincsKeygen`), rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.E2E.PerKeyS.ΦJS_xKeygenRS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.ΦJS_xKeygenRS

/-- info: 'LeanVM.E2E.PerKeyS.ΦJS_sKeygenRS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.ΦJS_sKeygenRS

/-- info: 'LeanVM.E2E.PerKeyS.agreeOn_xKeygenS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.agreeOn_xKeygenS

/-- info: 'LeanVM.E2E.PerKeyS.agreeOn_sKeygenS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.agreeOn_sKeygenS
