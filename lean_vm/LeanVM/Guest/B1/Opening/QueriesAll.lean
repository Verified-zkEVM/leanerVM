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

end
end LeanVM.Guest.B1
