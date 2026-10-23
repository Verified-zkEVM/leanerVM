/-
  LeanVM.Guest.B1.Opening.QueriesAll

  Every deployed specialization of `opening_queries` is sound.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody0
public import LeanVM.Guest.B1.Opening.QueriesBody1
public import LeanVM.Guest.B1.Opening.QueriesBody2
public import LeanVM.Guest.B1.Opening.QueriesBody3

/-!
# `opening_queries`, every specialization (TRIAGE G #40)

`opening_queries_sound_all`: for each of the 56 deployed shapes (`openingQueriesShapes`), the
function's relation gives `MeaningOpeningQueries` when its bit pointers point to bits — the
soundness direction of `opening_queries_all_Spec`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-- The soundness direction of `opening_queries_Spec`. -/
def opening_queries_sound_Spec (name : String) (odd base I depth cd : ℕ) : Prop :=
  ∀ (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E),
    (∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount odd base N) depth) →
    coreProgram.Rel rd name [cap, flags, lam, lamN, qptrs, wp, nG] rets →
      MeaningOpeningQueries odd base I depth cd rd [cap, flags, lam, lamN, qptrs, wp, nG] rets

/-- **Every deployed `opening_queries` is sound.** -/
theorem opening_queries_sound_all : ∀ sh ∈ openingQueriesShapes,
    opening_queries_sound_Spec sh.1 sh.2.1 sh.2.2.1 sh.2.2.2.1 sh.2.2.2.2.2.1 sh.2.2.2.2.2.2 := by
  intro sh hsh
  simp only [openingQueriesShapes, List.mem_cons, List.not_mem_nil, or_false] at hsh
  rcases hsh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqSound_413
  · exact oqSound_533
  · exact oqSound_433
  · exact oqSound_542
  · exact oqSound_449
  · exact oqSound_692
  · exact oqSound_551
  · exact oqSound_468
  · exact oqSound_701
  · exact oqSound_563
  · exact oqSound_487
  · exact oqSound_710
  · exact oqSound_575
  · exact oqSound_721
  · exact oqSound_586
  · exact oqSound_732
  · exact oqSound_598
  · exact oqSound_743
  · exact oqSound_755
  · exact oqSound_614
  · exact oqSound_623
  · exact oqSound_632
  · exact oqSound_643
  · exact oqSound_501
  · exact oqSound_654
  · exact oqSound_515
  · exact oqSound_665
  · exact oqSound_676
  · exact oqSound_425
  · exact oqSound_422
  · exact oqSound_556
  · exact oqSound_439
  · exact oqSound_418
  · exact oqSound_568
  · exact oqSound_455
  · exact oqSound_436
  · exact oqSound_524
  · exact oqSound_474
  · exact oqSound_452
  · exact oqSound_591
  · exact oqSound_491
  · exact oqSound_471
  · exact oqSound_605
  · exact oqSound_505
  · exact oqSound_489
  · exact oqSound_683
  · exact oqSound_519
  · exact oqSound_503
  · exact oqSound_761
  · exact oqSound_602
  · exact oqSound_517
  · exact oqSound_680
  · exact oqSound_600
  · exact oqSound_745
  · exact oqSound_678
  · exact oqSound_757

end
end LeanVM.Guest.B1
