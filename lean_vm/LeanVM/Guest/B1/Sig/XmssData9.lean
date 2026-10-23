/-
  LeanVM.Guest.B1.Sig.XmssData9

  `verify_lean_xmss` in the guest's core IR agrees with the template `xBody` on statements 517 to 528.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.XmssT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xBody_slice_517 : (Data.core19.body.drop 517).take 12 = (xBody.drop 517).take 12 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
