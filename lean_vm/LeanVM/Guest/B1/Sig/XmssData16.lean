/-
  LeanVM.Guest.B1.Sig.XmssData16

  `verify_lean_xmss` in the guest's core IR agrees with the template `xBody` from statement 594 on.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.XmssT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xBody_drop_594 : Data.core19.body.drop 594 = xBody.drop 594 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
