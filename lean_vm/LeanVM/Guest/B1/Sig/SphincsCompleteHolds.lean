/-
  LeanVM.Guest.B1.Sig.SphincsCompleteHolds

  leanSPHINCS's guest functions at leanVM 834e6614 are complete (`SphincsCompleteSpecs`): `sp_wots`
  and `verify_sig_lean_sphincs`, given the completeness of the latter's FORS block and layers.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsCompleteStmt
public import LeanVM.Guest.B1.Sig.SphincsComplete

namespace LeanVM.Guest.B1.Sig

@[expose] public section

/-- **leanSPHINCS's guest functions are complete**: `sp_wots` (`sp_wots_complete`) and
`verify_sig_lean_sphincs` (`verify_sig_lean_sphincs_complete_loads_of`), given its blocks'
completeness. -/
theorem sphincs_complete_of (hB : SphincsBlocksComplete) : SphincsCompleteSpecs :=
  ⟨sp_wots_complete, verify_sig_lean_sphincs_complete_loads_of hB⟩

end
end LeanVM.Guest.B1.Sig
