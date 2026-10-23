/-
  LeanVM.Guest.B1.Tables.Vt.FormsTie3

  Table 3's push and pull flushes are the guest's baked coordinate terms, by kernel evaluation
  of their canonical forms over `K`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsTie0

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (canon pySideC FormC)

@[expose] public section

theorem vtTie03 : vtTieCheck (pySideC 3 .push) vtBTerms03 = true := by decide +kernel

theorem vtTie13 : vtTieCheck (pySideC 3 .pull) vtBTerms13 = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
