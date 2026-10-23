/-
  LeanVM.Guest.B1.Da.VerifyChk

  `da_verify`'s block, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem dv_ok : dvOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
