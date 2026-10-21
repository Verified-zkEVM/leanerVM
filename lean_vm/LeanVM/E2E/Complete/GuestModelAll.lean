/-
  LeanVM.E2E.Complete.GuestModelAll

  The guest's completeness over every completeness model, its executions: group B1's facts over
  every model hold, so `GuestCompleteModelExec` holds outright.
-/

module

public import LeanVM.E2E.Complete.GuestModel
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsAllC

/-!
# `GuestCompleteModel`'s executions, unconditionally

`B1CompHyps CM` is `open_stacked` placed over the model at the caps' agreement `CapAgreesC CM`:
the Whir group's `open_stacked_completeAtBC_b2c`. So `guestCompleteModelExec`: for every
completeness model, a node relation answered by its hash within the deployed limits, the caps and
the budget has a valid execution under its semantics within the committed size.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Guest.B1.Main (CalleesOpenC)

@[expose] public section

/-- **What group B1 owes the guest's completeness, over every completeness model.** -/
theorem b1CompHyps_all (CM : CompModel) : B1CompHyps CM :=
  ⟨⟨LeanVM.Guest.B1.open_stacked_completeAtBC_b2c CM⟩⟩

/-- **The guest's completeness over every completeness model, its executions** (L2 without the
decoding). -/
theorem guestCompleteModelExec : GuestCompleteModelExec :=
  guestCompleteModelExec_of b1CompHyps_all

end
end LeanVM.E2E.Complete
