/-
  LeanVM.Guest.B1.Sig.SphincsCompleteHolds

  leanSPHINCS's guest functions are complete: `sp_wots` and `verify_sig_lean_sphincs`, as `main`'s
  completeness takes them (`SphincsCompleteSpecs`).
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsComplete
public import LeanVM.Guest.B1.Sig.SphincsComplete

namespace LeanVM.Guest.B1.Sig

@[expose] public section

/-- **leanSPHINCS's guest functions are complete**: `sp_wots` (`sp_wots_complete`) and
`verify_sig_lean_sphincs` with its loads (`verify_sig_lean_sphincs_complete_loads`). -/
theorem sphincs_complete : SphincsCompleteSpecs :=
  ⟨sp_wots_complete, verify_sig_lean_sphincs_complete_loads⟩

end
end LeanVM.Guest.B1.Sig
