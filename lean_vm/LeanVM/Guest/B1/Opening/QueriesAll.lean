/-
  LeanVM.Guest.B1.Opening.QueriesAll

  Every deployed specialization of `opening_queries` is its meaning.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody0
public import LeanVM.Guest.B1.Opening.QueriesBody1
public import LeanVM.Guest.B1.Opening.QueriesBody2
public import LeanVM.Guest.B1.Opening.QueriesBody3

/-!
# `opening_queries`, every specialization (TRIAGE G #40)

`opening_queries_all_holds`: each of the 56 deployed shapes (`openingQueriesShapes`) is its
meaning (`opening_queries_Spec`): when its bit pointers point to bits, the function's relation is
`MeaningOpeningQueries` (`oqMain1_iff`, `oqMain0_iff`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **Every deployed `opening_queries` is its meaning.** -/
theorem opening_queries_all_holds : opening_queries_all_Spec := by
  intro sh hsh
  simp only [openingQueriesShapes, List.mem_cons, List.not_mem_nil, or_false] at hsh
  rcases hsh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqSpec_413
  · exact oqSpec_533
  · exact oqSpec_433
  · exact oqSpec_542
  · exact oqSpec_449
  · exact oqSpec_692
  · exact oqSpec_551
  · exact oqSpec_468
  · exact oqSpec_701
  · exact oqSpec_563
  · exact oqSpec_487
  · exact oqSpec_710
  · exact oqSpec_575
  · exact oqSpec_721
  · exact oqSpec_586
  · exact oqSpec_732
  · exact oqSpec_598
  · exact oqSpec_743
  · exact oqSpec_755
  · exact oqSpec_614
  · exact oqSpec_623
  · exact oqSpec_632
  · exact oqSpec_643
  · exact oqSpec_501
  · exact oqSpec_654
  · exact oqSpec_515
  · exact oqSpec_665
  · exact oqSpec_676
  · exact oqSpec_425
  · exact oqSpec_422
  · exact oqSpec_556
  · exact oqSpec_439
  · exact oqSpec_418
  · exact oqSpec_568
  · exact oqSpec_455
  · exact oqSpec_436
  · exact oqSpec_524
  · exact oqSpec_474
  · exact oqSpec_452
  · exact oqSpec_591
  · exact oqSpec_491
  · exact oqSpec_471
  · exact oqSpec_605
  · exact oqSpec_505
  · exact oqSpec_489
  · exact oqSpec_683
  · exact oqSpec_519
  · exact oqSpec_503
  · exact oqSpec_761
  · exact oqSpec_602
  · exact oqSpec_517
  · exact oqSpec_680
  · exact oqSpec_600
  · exact oqSpec_745
  · exact oqSpec_678
  · exact oqSpec_757

end
end LeanVM.Guest.B1
