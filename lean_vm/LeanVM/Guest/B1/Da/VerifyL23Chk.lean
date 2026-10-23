/-
  LeanVM.Guest.B1.Da.VerifyL23Chk

  `__loop23`, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem l23_ok : (l23Ok (coreProgram.getD 365 default) && decide (coreProgram.indexOf? "__loop23" = some 365)) = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
