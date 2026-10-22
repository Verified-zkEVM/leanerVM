import LeanVM.E2E.Vis.PerKey.XmssView

/-!
# Tests: W-vis P7b (leanXMSS), its axioms

The per-key leanXMSS reduction: its rest being the class-routed game (`XmssRest`), its key
generations agreeing with the class-routed ones (`XmssKeygen`) and the view equality after key
`j`'s generation (`XmssView`) rest on Lean's standard axioms only.
-/

/-- info: 'LeanVM.E2E.PerKeyX.map_ΦJ_restJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.map_ΦJ_restJ

/-- info: 'LeanVM.E2E.PerKeyX.agreeOn_xKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.agreeOn_xKeygen

/-- info: 'LeanVM.E2E.PerKeyX.agreeOn_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.agreeOn_keys

/-- info: 'LeanVM.E2E.PerKeyX.prEvent_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.prEvent_view
