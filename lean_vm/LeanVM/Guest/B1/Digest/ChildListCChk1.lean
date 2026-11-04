/-
  LeanVM.Guest.B1.Digest.ChildListCChk1

  `child_claim_list_any`'s big frame loop `__loop17` (136 records), evaluated: `anycOk`'s parts,
  each a kernel check of its own (`anycSide`, `anycRecs` still to split by record windows, `monoOf`
  over each record's window as `ChildListDefs.recordsWin` does: as one check each exceeds 20 GB).
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
theorem any136c_head : anycHead (coreProgram.getD 350 default) "__loop17" = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem any136c_canon : anycCanon (coreProgram.getD 350 default) 136 22 1924 = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
