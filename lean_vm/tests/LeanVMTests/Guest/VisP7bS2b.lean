import LeanVM.E2E.Vis.PerKey.SphincsView

/-!
# Tests: W-vis P7b (leanSPHINCS, the reduction's view), its axioms

The per-key leanSPHINCS reduction's view (`LeanVM.E2E.Vis.PerKey.SphincsView`: the key generations
agree on good keys, and the class-routed game after key `j` and the reduction's run give events
forcing good keys the same probability) rests on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.E2E.PerKeyS.agreeOn_keysS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.agreeOn_keysS

/-- info: 'LeanVM.E2E.PerKeyS.gKeysS_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.gKeysS_slot

/-- info: 'LeanVM.E2E.PerKeyS.ΦJS_restJS_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.ΦJS_restJS_keys

/-- info: 'LeanVM.E2E.PerKeyS.prEvent_viewS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.prEvent_viewS
