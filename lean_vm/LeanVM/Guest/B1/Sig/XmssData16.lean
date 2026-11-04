/-
  LeanVM.Guest.B1.Sig.XmssData16

  `verify_lean_xmss` in the guest's core IR agrees with the template `xBody` from statement 634 on.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.XmssT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xBody_drop_634 : Data.core19.body.drop 634 = xBody.drop 634 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
