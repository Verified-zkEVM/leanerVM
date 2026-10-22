import LeanVM.E2E.Vis.PerKey.SphincsCount

/-!
# Tests: W-vis P7f, the per-key reductions' query counts

The per-key reductions' hash-call budgets in the schemes' single-key games,
`PerKeyX.hasHashQueryBound_xRedJ` and `PerKeyS.hasHashQueryBound_sRedJ`, and their steps: a
simulation costs its steps, a private computation nothing, the reduction's run two per other key,
the adversary's queries and V_I's budget. They rest on Lean's three standard axioms only.
-/

open LeanVM.E2E OracleSpec OracleComp

-- a pure computation costs nothing, from every private cache
example : CostR 0 (pure 0 : StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) ℕ) :=
  costR_pure 0

/-- info: 'LeanVM.E2E.costR_simulateQ_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.costR_simulateQ_run

/-- info: 'LeanVM.E2E.costR_sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.costR_sequenceFin

/-- info: 'LeanVM.E2E.costR_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.costR_route

/-- info: 'LeanVM.E2E.costR_route_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.costR_route_all

/-- info: 'LeanVM.E2E.PerKeyX.costR_ΦJ_advImplJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.costR_ΦJ_advImplJ

/-- info: 'LeanVM.E2E.PerKeyX.costR_ΦJ_xBodyJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.costR_ΦJ_xBodyJ

/-- info: 'LeanVM.E2E.PerKeyX.isQueryBoundP_gameCore_xRedJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.isQueryBoundP_gameCore_xRedJ

/-- info: 'LeanVM.E2E.PerKeyX.hasHashQueryBound_xRedJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyX.hasHashQueryBound_xRedJ

/-- info: 'LeanVM.E2E.PerKeyS.costR_ΦJS_advImplJS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.costR_ΦJS_advImplJS

/-- info: 'LeanVM.E2E.PerKeyS.costR_ΦJS_sBodyJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.costR_ΦJS_sBodyJ

/-- info: 'LeanVM.E2E.PerKeyS.isQueryBoundP_gameCore_sRedJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.isQueryBoundP_gameCore_sRedJ

/-- info: 'LeanVM.E2E.PerKeyS.hasHashQueryBound_sRedJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.PerKeyS.hasHashQueryBound_sRedJ
