import LeanVM.E2E.Vis.PerKey.Partition

/-!
# Tests: the partition lemma (W-vis, P7a)

Two lazy random oracles on a static partition of the inputs are one (`evalDistEq_route`), routing
is transparent on a computation that never asks the private class (`simulateQ_route_of_sat`), and
it forwards only the hash queries outside it (`isQueryBoundP_route`), checked on the class of
inputs starting with byte `7`. The lemmas rest on Lean's three standard axioms only.
-/

open LeanVM.E2E OracleSpec OracleComp

/-- A private class: inputs starting with byte `7`. -/
def visP7aPr (x : List UInt8) : Prop := x.head? = some 7

instance : DecidablePred visP7aPr := fun x ↦ inferInstanceAs (Decidable (x.head? = some 7))

-- the merged cache reads the private cache on the class and the public one off it
example (cPriv cPub : QueryCache LeanXmss.HashSpec) :
    mergeCache visP7aPr cPriv cPub [7, 1] = cPriv [7, 1] ∧
      mergeCache visP7aPr cPriv cPub [8, 1] = cPub [8, 1] := by
  simp [mergeCache_apply, visP7aPr]

-- a query outside the class is forwarded unchanged
example (c : QueryCache LeanXmss.HashSpec) :
    (simulateQ (routeImpl visP7aPr) (liftM (OW.query (.inr [8])) : OracleComp OW _)).run c =
      (·, c) <$> (liftM (OW.query (.inr [8])) : OracleComp OW _) :=
  simulateQ_route_of_sat visP7aPr (by
    rw [queriesSat_iff]
    exact (allQueriesSatisfy_query_iff _ _).mpr (by simp [OffPr, visP7aPr])) c

-- the partition lemma from the empty public cache
example {α : Type} (oa : OracleComp OW α) :
    (fun z ↦ (z.1.1, mergeCache visP7aPr z.1.2 z.2)) <$>
      (simulateQ owImpl ((simulateQ (routeImpl visP7aPr) oa).run ∅)).run ∅ =ᵈ
    (simulateQ owImpl oa).run ∅ :=
  evalDistEq_route visP7aPr oa ∅ fun _ _ ↦ rfl

/-- info: 'LeanVM.E2E.mergeCache_empty' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.mergeCache_empty

/-- info: 'LeanVM.E2E.evalDistEq_route_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.evalDistEq_route_step

/-- info: 'LeanVM.E2E.evalDistEq_route_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.evalDistEq_route_run

/-- info: 'LeanVM.E2E.evalDistEq_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.evalDistEq_route

/-- info: 'LeanVM.E2E.simulateQ_route_of_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.simulateQ_route_of_sat

/-- info: 'LeanVM.E2E.isQueryBoundP_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.isQueryBoundP_route
